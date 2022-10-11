/*
 * Copyright (c) 2018 Inria
 * Copyright (c) 2012-2013, 2015 ARM Limited
 * All rights reserved
 *
 * The license below extends only to copyright in the software and shall
 * not be construed as granting a license to any other intellectual
 * property including but not limited to intellectual property relating
 * to a hardware implementation of the functionality of the software
 * licensed hereunder.  You may use the software subject to the license
 * terms below provided that you ensure that this notice is replicated
 * unmodified and in its entirety in all distributions of the software,
 * modified or unmodified, in source code or in binary form.
 *
 * Copyright (c) 2005 The Regents of The University of Michigan
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

/**
 * @file
 * Stride Prefetcher template instantiations.
 */

#include "mem/cache/prefetch/ipcp.hh"

#include <cassert>

#include "base/intmath.hh"
#include "base/logging.hh"
#include "base/random.hh"
#include "base/trace.hh"
#include "debug/HWPrefetch.hh"
#include "mem/cache/prefetch/associative_set_impl.hh"
#include "mem/cache/replacement_policies/base.hh"
#include "params/IPCPPrefetcher.hh"

namespace gem5
{

GEM5_DEPRECATED_NAMESPACE(Prefetcher, prefetch);
namespace prefetch
{

IPCP::StrideEntry::StrideEntry(int init_confidence)
  : TaggedEntry(), confidence(init_confidence)
{
    invalidate();
}

void
IPCP::StrideEntry::invalidate()
{
    TaggedEntry::invalidate();
    lastLineAddr = 0;
    stride = 0;
    confidence = 0;
    streamValid = false;
    forward = false;
}

IPCP::RSTEntry::RSTEntry(int rSize, int pnCounts)
  : TaggedEntry(), regionSize(rSize),
  pnCountBits(pnCounts),
  pnCount(pnCountBits, (1 << (pnCountBits - 1)))
{
    invalidate();
}

void
IPCP::RSTEntry::invalidate()
{
    TaggedEntry::invalidate();
    lastLineOffset = 0;
    bitVector.resize(regionSize/64, false);
    pnCount.reset();
    dense = false;
    trained = false;
    tentative = false;
    direction = 0;
}

IPCP::IPCP(const IPCPPrefetcherParams &p)
  : Queued(p),
    initConfidence(p.initial_confidence),
    threshConf(p.confidence_threshold),
    useRequestorId(p.use_requestor_id),
    maxDegree(p.degree),
    maxDegreeCS(p.degree_cs),
    filled(0),
    adjustInterval(p.adjust_interval),
    currentDegree(2),
    regionSize(p.rst_region_size)
{
    pcTable = new AssociativeSet<StrideEntry>(p.table_assoc, p.table_entries,
        p.table_indexing_policy, p.table_replacement_policy,
        StrideEntry(initConfidence));
    rstTable = new AssociativeSet<RSTEntry>(p.rst_assoc, p.rst_entries,
        p.rst_indexing_policy, p.rst_replacement_policy,
        RSTEntry(p.rst_region_size, p.pn_count_bits));
}


void
IPCP::calculatePrefetch(const PrefetchInfo &pfi,
                                    std::vector<AddrPriority> &addresses)
{
    if (!pfi.hasPC()) {
        DPRINTF(HWPrefetch, "Ignoring request with no PC.\n");
        return;
    }

    // Get required packet info
    Addr pf_addr = pfi.getAddr();
    Addr line_addr = pf_addr >> lBlkSize;
    Addr pc = pfi.getPC();
    bool is_secure = pfi.isSecure();
    bool issueGS = false;
    bool issueCS = false;

    // Search for entry in the pc table and rst table
    StrideEntry *sentry = pcTable->findEntry(pc, is_secure);
    RSTEntry * rentry = rstTable->findEntry(pf_addr, is_secure);

    if (rentry == nullptr) {
        rentry = rstTable->findVictim(pf_addr);

        rentry->lastLineOffset = lineOffset(line_addr);

        // May come to a new region
        if (sentry) {
            Addr faddr = sentry->lastLineAddr << lBlkSize;
            RSTEntry * last = rstTable->findEntry(faddr, is_secure);
            if (last && last->trained) {
                rentry->tentative = true;
                rentry->direction = last->direction;
            }
        }
         else {
            rentry->bitVector[rentry->lastLineOffset] = true;
        }
        rstTable->insertEntry(pf_addr, is_secure, rentry);
    }
    else {
        rstTable->accessEntry(rentry);

        // Only update rentry when region is not dense
        if (!rentry->trained && !rentry->tentative) {
            Addr currentLineOffset = lineOffset(line_addr);
            rentry->bitVector[currentLineOffset] = true;
            if (currentLineOffset - rentry->lastLineOffset != 0) {
                if (currentLineOffset - rentry->lastLineOffset > 0)
                    rentry->pnCount++;
                else
                    rentry->pnCount--;
            }
            double ratio = (double) std::count(rentry->bitVector.begin(),
                                rentry->bitVector.end(), true)
                                    / rentry->bitVector.size();
            if (ratio >= 0.75) {
                rentry->trained = true;
                double sat = rentry->pnCount.calcSaturation();
                rentry->direction =  sat > 0.5 ? 1 : -1;
            }
        }
    }

    if (sentry == nullptr) {
        // Miss in pc table, only consider issue GS prefetch request

        sentry = pcTable->findVictim(pc);

        // Insert new entry's data
        sentry->lastLineAddr = line_addr;
        if (!sentry->streamValid && (rentry->trained || rentry->tentative)) {
            promoteGS(sentry, rentry);
            issueGS = true;
        }
        pcTable->insertEntry(pc, is_secure, sentry);
    }
    else {
        pcTable->accessEntry(sentry);

        //update stride entry
        updateStrideInfo(sentry, line_addr);

        if (!sameRegion(sentry->lastLineAddr << lBlkSize, pf_addr)) {
            if (rentry->tentative || rentry->trained) {
                promoteGS(sentry, rentry);
            }
            else {
                sentry->streamValid = false;
            }
        }
        else if (rentry->tentative || rentry->trained) {
            promoteGS(sentry, rentry);
        }

        //choose prefetching requests
        if (sentry->streamValid) {
            issueGS = true;
        }
        if (sentry->confidence >= threshConf){
            assert(sentry->confidence == threshConf);
            issueCS = true;
        }
    }

    //decide to issue
    if (issueGS) {
        for (int d = 1; d <= std::min(currentDegree, maxDegree) ; d++) {
            int direct = sentry->forward? 1 : -1;
            Addr new_addr = (line_addr + d * direct) << lBlkSize;
            if (samePage(pf_addr, new_addr))
                addresses.push_back(AddrPriority(new_addr, 0));
        }
    }
    else if (issueCS) {
        // Generate up to degree prefetches
        for (int d = 1; d <= std::min(currentDegree, maxDegreeCS); d++) {
            int prefetch_stride = sentry->stride;

            Addr new_addr = (line_addr + prefetch_stride * d) << lBlkSize;
            if (samePage(pf_addr, new_addr))
                addresses.push_back(AddrPriority(new_addr, 0));
        }
    }
}

void
IPCP::promoteGS(StrideEntry * sentry, RSTEntry * rentry)
{
    assert(rentry->direction != 0);
    sentry->streamValid = true;
    sentry->forward = rentry->direction == 1? true : false;
}

void
IPCP::updateStrideInfo(StrideEntry * sentry, Addr currentLine) {
    int new_stride = currentLine - sentry->lastLineAddr;
    bool stride_match = (new_stride == sentry->stride);
    if (stride_match && new_stride != 0) {
        if (sentry->confidence < threshConf) {
            sentry->confidence++;
        }
    } else {
        if (sentry->confidence == 0) {
            sentry->stride = new_stride;
        }
        else {
            sentry->confidence--;
        }
    }
    sentry->lastLineAddr = currentLine;
}

void
IPCP::notifyFill(const PacketPtr& pkt)
{
    // Only insert into the RR right way if it's the pkt is a HWP
    if (!pkt->cmd.isHWPrefetch()) return;

    filled++;
    if (filled >= adjustInterval) {
        double accuracy = (double) usefulPrefetches / issuedPrefetches;
        if (accuracy > 0.4 && currentDegree < maxDegree) {
            currentDegree++;
        }
        else if (accuracy < 0.15 && currentDegree > 1) {
            currentDegree--;
        }
        filled = 0;
    }
}



uint32_t
IPCPPrefetcherHashedSetAssociative::extractSet(const Addr pc) const
{
    const Addr hash1 = pc >> 1;
    const Addr hash2 = hash1 >> tagShift;
    return (hash1 ^ hash2) & setMask;
}

Addr
IPCPPrefetcherHashedSetAssociative::extractTag(const Addr addr) const
{
    return addr;
}

} // namespace prefetch
} // namespace gem5
