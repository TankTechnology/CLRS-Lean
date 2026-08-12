#!/usr/bin/env python3
"""Empirical analysis of the hnotE mechanism (the Q''-exclusion at window
faults) — see DESIGN.md "hnotE (still open)".  Mirrors the Lean semantics
exactly (search_b2.py) and runs the full iteration, checking at every B2
window (t2, J] with the past-pair set P:

- `kept`:  sigma[s] = q''_i at a later request s > n_i  ==>  q''_i in D_s
  (the DESIGN's "requested at n_i <= s, kept" mechanism).  REFUTED: 172 of
  180 later requests have q''_i NOT in D_s — d evicts q''_i in between
  (e.g. sigma=[1,1,3,4,1,3,2,3], B2 at 6: d(6)=3=q''_i, a real eviction).
- `ehit`:  at d-faults s in (t2, J] with s not in P, sigma[s] in E_s
  (the hnotE conclusion).  HOLDS: 0 of 15548.
- `half2`/`kept_viol`: e/d evict q''_i at s' in (n_i, J] (the "never evicts
  after its request" claim).  REFUTED: 60 / 128 occurrences.
- `alive_iff`: for ALIVE pairs, at all window positions off P after n_i:
  q''_i in E_s  <->  q''_i in D_s.  HOLDS: 0 mismatches of 408 — this is the
  correct invariant behind hnotE.
- `hitagree`: at window positions off P, d and e hit/fault identically
  (sigma[s] in D_s <-> sigma[s] in E_s).  HOLDS: 0 of 0 mismatches.

Usage:  python3 search_hnot.py
"""
import sys, os
from itertools import product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search_b2 as s

def repair_schedule(e, t, qp, nop):
    return lambda x: qp if (x == t or x == nop) else e(x)

stats = {"later": 0, "kept_viol": 0, "ehit_notP": 0, "win_faults": 0,
         "half2_viol": 0, "alive_pos": 0, "alive_inE_notD": 0, "alive_inD_notE": 0,
         "hit_mismatch": 0, "pos": 0}

def run(sig, C0, d0):
    n = len(sig)
    d = d0
    t0 = 0
    hnb = 0
    pairs = []  # (t_i, q''_i, nop_i, alive)
    exch = None
    while True:
        t = None
        for tpos in range(t0, n):
            if s.sched_cache(d, sig, C0, tpos + 1) != s.sched_cache_fifo(sig, C0, tpos + 1):
                t = tpos
                break
        if t is None:
            return
        if t >= hnb:
            q = d(t)
            qp = s.fifo_evict(s.sched_cache(d, sig, C0, t), sig, t)
            jp = s.next_use(sig, t + 1, qp)
            if jp is not None:
                jp -= t + 1
            d = s.exchange_schedule(d, t, q, qp, sig, C0)
            exch = (d, t, q, qp)
            pairs = []
            t0 = t + 1
            if jp is not None:
                hnb = max(hnb, t + 1 + jp + 1)
        else:
            cache_t = s.sched_cache(d, sig, C0, t)
            if d(t) not in cache_t:
                qp = s.fifo_evict(cache_t, sig, t)
                jp = s.next_use(sig, t + 1, qp)
                if jp is not None:
                    jp -= t + 1
                nop = t + 1 + jp if jp is not None else t
                d = repair_schedule(d, t, qp, nop)
                pairs.append((t, qp, nop, jp is not None))
                t0 = t + 1
                if jp is not None:
                    hnb = max(hnb, t + 1 + jp + 1)
            else:
                q = d(t)
                qp = s.fifo_evict(cache_t, sig, t)
                j = s.next_use(sig, t + 1, q)
                jp = s.next_use(sig, t + 1, qp)
                if j is not None:
                    j -= t + 1
                if jp is not None:
                    jp -= t + 1
                e, t0x, q0, q0p = exch
                if j is not None:
                    J = t + 1 + j
                    Pset = set()
                    for (ti, qpi, ni, alive) in pairs:
                        Pset.add(ti)
                        if ni is not None:
                            Pset.add(ni)
                    for ss in range(t + 1, J + 1):
                        inP = ss in Pset
                        Es = s.sched_cache(e, sig, C0, ss)
                        Ds = s.sched_cache(d, sig, C0, ss)
                        if sig[ss] in Ds:
                            stats["pos"] += 1
                            if sig[ss] not in Es:
                                stats["hit_mismatch"] += 1  # d-hit at e-fault
                        else:
                            stats["win_faults"] += 1
                            if sig[ss] in Es:
                                if not inP:
                                    stats["ehit_notP"] += 1
                        if not inP:
                            for (ti, qpi, ni, alive) in pairs:
                                if alive and ni < ss:
                                    stats["alive_pos"] += 1
                                    inE = qpi in Es
                                    inD = qpi in Ds
                                    if inE != inD:
                                        if inE:
                                            stats["alive_inE_notD"] += 1
                                        else:
                                            stats["alive_inD_notE"] += 1
                                if alive and ni < ss and sig[ss] == qpi:
                                    stats["later"] += 1
                                    if qpi not in Ds:
                                        stats["kept_viol"] += 1
                                if alive and ni < ss and sig[ss] not in Es:
                                    if e(ss) == qpi:
                                        stats["half2_viol"] += 1
                nop = t + 1 + jp if jp is not None else t
                d = repair_schedule(d, t, qp, nop)
                pairs.append((t, qp, nop, jp is not None))
                t0 = t + 1
                if jp is not None:
                    hnb = max(hnb, t + 1 + jp + 1)

alpha = [1, 2, 3, 4]
for n in range(4, 10):
    for sig_t in product(alpha, repeat=n):
        sig = list(sig_t)
        if sig[0] not in (1, 2):
            continue
        for C0 in ({1, 2}, {1, 2, 3}):
            if not all(x in C0 for x in sig[0:2]):
                continue
            for d0, name in ((s.d0_of(sig, C0), 'min'),):
                run(sig, C0, d0)
print(stats)
