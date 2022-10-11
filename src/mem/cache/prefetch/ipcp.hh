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
 * Describes a strided prefetcher.
 */

#ifndef __MEM_CACHE_PREFETCH_IPCP_HH__
#define __MEM_CACHE_PREFETCH_IPCP_HH__

#include <string>
#include <unordered_map>
#include <vector>

#include "base/sat_counter.hh"
#include "base/types.hh"
#include "mem/cache/prefetch/associative_set.hh"
#include "mem/cache/prefetch/queued.hh"
#include "mem/cache/replacement_policies/replaceable_entry.hh"
#include "mem/cache/tags/indexing_policies/set_associative.hh"
#include "mem/cache/tags/tagged_entry.hh"
#include "mem/packet.hh"
#include "params/IPCPPrefetcherHashedSetAssociative.hh"

namespace gem5
{

class BaseIndexingPolicy;
GEM5_DEPRECATED_NAMESPACE(ReplacementPolicy, replacement_policy);
namespace replacement_policy
{
    class Base;
}
struct IPCPPrefetcherParams;

GEM5_DEPRECATED_NAMESPACE(Prefetcher, prefetch);
namespace prefetch
{

/**
 * Override the default set associative to apply a specific hash function
 * when extracting a set.
 */
class IPCPPrefetcherHashedSetAssociative : public SetAssociative
{
  protected:
    uint32_t extractSet(const Addr addr) const override;
    Addr extractTag(const Addr addr) const override;

  public:
    IPCPPrefetcherHashedSetAssociative(
        const IPCPPrefetcherHashedSetAssociativeParams &p)
      : SetAssociative(p)
    {
    }
    ~IPCPPrefetcherHashedSetAssociative() = default;
};

class IPCP : public Queued
{
  protected:
    /** Initial confidence counter value for the pc tables. */
    const int initConfidence;

    /** Confidence threshold for prefetch generation. */
    const int threshConf;

    const bool useRequestorId;

    const int maxDegree;

    const int maxDegreeCS;

    int filled;

    const int adjustInterval;

    int currentDegree;

    const int regionSize;

    /** Tagged by hashed PCs. */
    struct StrideEntry : public TaggedEntry
    {
        StrideEntry(int init_confidence);

        void invalidate() override;

        Addr lastLineAddr;
        int stride;
        int confidence;
        bool streamValid;
        bool forward;
    };
    AssociativeSet<StrideEntry>* pcTable;

    struct RSTEntry : public TaggedEntry
    {
        RSTEntry(int rSize, int pnCounts);

        const int regionSize;
        const int pnCountBits;
        void invalidate() override;

        Addr lastLineOffset;
        std::vector<bool> bitVector;
        SatCounter8 pnCount;
        bool dense;
        bool trained;
        bool tentative;
        int direction;
    };
    AssociativeSet<RSTEntry>* rstTable;

    bool sameBlock(Addr a, Addr b) {
        Addr mask = ~((1 << lBlkSize) - 1);
        return (a & mask) == (b & mask);
    }

    //input: full physical address
    bool sameRegion(Addr a, Addr b) {
        return (a >> 11) == (b >> 11);
    }

    Addr lineOffset(Addr lineAddr) {
        return lineAddr & ((1 << (floorLog2(regionSize) - lBlkSize)) - 1);
    }

    void promoteGS(StrideEntry * sentry, RSTEntry * rentry);
    void updateStrideInfo(StrideEntry * sentry, Addr currentLine);
    void notifyFill(const PacketPtr& pkt) override;

  public:
    IPCP(const IPCPPrefetcherParams &p);

    void calculatePrefetch(const PrefetchInfo &pfi,
                           std::vector<AddrPriority> &addresses) override;
};

} // namespace prefetch
} // namespace gem5

#endif // __MEM_CACHE_PREFETCH_STRIDE_HH__
