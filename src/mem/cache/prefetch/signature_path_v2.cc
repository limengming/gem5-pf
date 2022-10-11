/**
 * Copyright (c) 2018 Metempsy Technology Consulting
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met: redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer;
 * redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution;
 * neither the name of the copyright holders nor the names of its
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include "mem/cache/prefetch/signature_path_v2.hh"

#include <cassert>

#include "debug/HWPrefetch.hh"
#include "mem/cache/prefetch/associative_set_impl.hh"
#include "params/SignaturePathPrefetcherV2.hh"

namespace gem5
{

GEM5_DEPRECATED_NAMESPACE(Prefetcher, prefetch);
namespace prefetch
{

SignaturePathV2::SignaturePathV2(const SignaturePathPrefetcherV2Params &p)
    : SignaturePath(p),
      globalHistoryRegister(p.global_history_register_entries,
                            p.global_history_register_entries,
                            p.global_history_register_indexing_policy,
                            p.global_history_register_replacement_policy,
                            GlobalHistoryEntry())
{
}

void
SignaturePathV2::handleSignatureTableMiss(stride_t current_block,
    signature_t &new_signature, double &new_conf, stride_t &new_stride)
{
    bool found = false;

    // This should return all entries of the GHR, since it is a fully
    // associative table
    std::vector<GlobalHistoryEntry *> all_ghr_entries =
             globalHistoryRegister.getPossibleEntries(0 /* any value works */);

    for (auto gh_entry : all_ghr_entries) {
        if (gh_entry->lastBlock + gh_entry->delta == current_block) {
            new_signature = gh_entry->signature;
            new_conf = gh_entry->confidence;
            new_stride = gh_entry->delta;
            found = true;
            globalHistoryRegister.accessEntry(gh_entry);
            break;
        }
    }
    if (!found) {
        new_signature = current_block;
        new_conf = 1.0;
        new_stride = current_block;
    }
}

double
SignaturePathV2::calculateLookaheadConfidence(
        PatternEntry const &sig, PatternStrideEntry const &lookahead) const
{
    if (sig.counter == 0) return 0.0;
    return 0.9 * (((double) lookahead.counter / sig.counter));
}

double
SignaturePathV2::calculatePrefetchConfidence(PatternEntry const &sig,
        PatternStrideEntry const &entry) const
{
    if (sig.counter == 0) return 0.0;
    return ((double) entry.counter) / sig.counter;
}

void
SignaturePathV2::increasePatternEntryCounter(
        PatternEntry &pattern_entry, PatternStrideEntry &pstride_entry)
{
    if (pattern_entry.counter.isSaturated()) {
        pattern_entry.counter >>= 1;
        for (auto &entry : pattern_entry.strideEntries) {
            entry.counter >>= 1;
        }
    }
    if (pstride_entry.counter.isSaturated()) {
        pattern_entry.counter >>= 1;
        for (auto &entry : pattern_entry.strideEntries) {
            entry.counter >>= 1;
        }
    }
    pattern_entry.counter++;
    pstride_entry.counter++;
}

void
SignaturePathV2::handlePageCrossingLookahead(signature_t signature,
            stride_t last_offset, stride_t delta, double path_confidence)
{
    // Always use the replacement policy to assign new entries, as all
    // of them are unique, there are never "hits" in the GHR
    GlobalHistoryEntry *gh_entry = globalHistoryRegister.findVictim(0);
    assert(gh_entry != nullptr);
    // Any address value works, as it is never used
    globalHistoryRegister.insertEntry(0, false, gh_entry);

    gh_entry->signature = signature;
    gh_entry->lastBlock = last_offset;
    gh_entry->delta = delta;
    gh_entry->confidence = path_confidence;
}

void
SignaturePathV2::calculatePrefetch(const PrefetchInfo &pfi,
                                 std::vector<AddrPriority> &addresses)
{
    Addr request_addr = pfi.getAddr();
    Addr ppn = request_addr / pageBytes;
    stride_t current_block = (request_addr % pageBytes) / blkSize;
    stride_t stride;
    bool is_secure = pfi.isSecure();
    double initial_confidence = 1.0;

    // Get the SignatureEntry of this page to:
    // - compute the current stride
    // - obtain the current signature of accesses
    bool miss;
    SignatureEntry &signature_entry = getSignatureEntry(ppn, is_secure,
            current_block, miss, stride, initial_confidence);

    if (miss) {
        // No history for this page, can't continue
        return;
    }

    if (stride == 0) {
        // Can't continue with a stride 0
        return;
    }

    // Update the confidence of the current signature
    updatePatternTable(signature_entry.signature, stride);

    // Update the current SignatureEntry signature
    signature_entry.signature =
        updateSignature(signature_entry.signature, stride);

    signature_t current_signature = signature_entry.signature;
    double current_confidence = initial_confidence;
    stride_t current_stride = signature_entry.lastBlock;

    // Look for prefetch candidates while the current path confidence is
    // high enough
    while (current_confidence > lookaheadConfidenceThreshold) {
        // With the updated signature, attempt to generate prefetches
        // - search the PatternTable and select all entries with enough
        //   confidence, these are prefetch candidates
        // - select the entry with the highest counter as the "lookahead"
        PatternEntry *current_pattern_entry =
            patternTable.findEntry(current_signature, false);
        PatternStrideEntry const *lookahead = nullptr;
        double prefetch_confidence = 0.0;
        if (current_pattern_entry != nullptr) {
            unsigned long max_counter = 0;
            for (auto const &entry : current_pattern_entry->strideEntries) {
                //select the entry with the maximum counter value as lookahead
                if (max_counter < entry.counter) {
                    max_counter = entry.counter;
                    lookahead = &entry;
                }
                double confidence =
                    calculatePrefetchConfidence(*current_pattern_entry, entry);
                if (confidence > prefetch_confidence)
                    prefetch_confidence = confidence;
            }
        }

        if (lookahead != nullptr) {
            if (prefetch_confidence >= prefetchConfidenceThreshold) {
                assert(lookahead->stride != 0);
                addPrefetch(ppn, current_stride, lookahead->stride,
                                current_confidence, current_signature,
                                is_secure, addresses);
            }
            current_confidence *= calculateLookaheadConfidence(
                    *current_pattern_entry, *lookahead);
            current_signature =
                updateSignature(current_signature, lookahead->stride);
            current_stride += lookahead->stride;
        } else {
            current_confidence = 0.0;
        }
    }

    auxiliaryPrefetcher(ppn, current_block, is_secure, addresses);
}

} // namespace prefetch
} // namespace gem5
