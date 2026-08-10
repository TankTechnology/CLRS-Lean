#!/usr/bin/env python3
"""Check at B2 positions: q = d(t) in E_t?  e(t) == d(t)?  past nop/repair
positions inside (t, J]?  d(s) == e(s) at faults in (t, J]?"""
import sys, os
from itertools import product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search_b2 as s
from search_iter import repair_schedule, d0_of_max

def main():
    alpha = [1, 2, 3, 4]
    stats = {"B2": 0, "q_not_in_E": 0, "e_ne_d_at_t": 0,
             "nop_in_window": 0, "fault_d_ne_e": 0, "faults": 0}
    for n in range(4, 10):
        for sig_t in product(alpha, repeat=n):
            sig = list(sig_t)
            if sig[0] not in (1, 2):
                continue
            for C0 in ({1, 2}, {1, 2, 3}):
                if not all(x in C0 for x in sig[0:2]):
                    continue
                for (d0, name) in ((s.d0_of(sig, C0), 'min'), (d0_of_max(sig, C0), 'max')):
                    d = d0
                    t0 = 0
                    hnb = 0
                    modified = set()  # past repair/nop positions
                    exch = None
                    while True:
                        t = None
                        for tpos in range(t0, n):
                            if s.sched_cache(d, sig, C0, tpos + 1) != s.sched_cache_fifo(sig, C0, tpos + 1):
                                t = tpos
                                break
                        if t is None:
                            break
                        if t >= hnb:
                            q = d(t)
                            qp = s.fifo_evict(s.sched_cache(d, sig, C0, t), sig, t)
                            jp = s.next_use(sig, t + 1, qp)
                            if jp is not None:
                                jp -= t + 1
                            d = s.exchange_schedule(d, t, q, qp, sig, C0)
                            exch = (d, t, q, qp)
                            modified = set()
                            t0 = t + 1
                            if jp is not None:
                                hnb = max(hnb, t + 1 + jp + 1)
                        else:
                            cache_t = s.sched_cache(d, sig, C0, t)
                            isB2 = d(t) in cache_t
                            qp = s.fifo_evict(cache_t, sig, t)
                            jp = s.next_use(sig, t + 1, qp)
                            if jp is not None:
                                jp -= t + 1
                            nop = t + 1 + jp if jp is not None else t
                            if isB2:
                                stats["B2"] += 1
                                e, t0x, q0, q0p = exch
                                q = d(t)
                                j = s.next_use(sig, t + 1, q)
                                if j is not None:
                                    j -= t + 1
                                J = t + 1 + j if j is not None else None
                                if q not in s.sched_cache(e, sig, C0, t):
                                    stats["q_not_in_E"] += 1
                                if e(t) != d(t):
                                    stats["e_ne_d_at_t"] += 1
                                if J is not None:
                                    for pos in range(t + 1, J + 1):
                                        if pos in modified:
                                            stats["nop_in_window"] += 1
                                            break
                                    # faults in (t, J]
                                    for pos in range(t + 1, J + 1):
                                        stats["faults"] += 1
                                        if sig[pos] not in s.sched_cache(e, sig, C0, pos):
                                            if d(pos) != e(pos):
                                                stats["fault_d_ne_e"] += 1
                            # advance
                            if isB2:
                                j = s.next_use(sig, t + 1, d(t))
                                if j is not None:
                                    j -= t + 1
                                d = repair_schedule(d, t, qp, nop)
                            else:
                                d = repair_schedule(d, t, qp, nop)
                            modified |= {t, nop}
                            t0 = t + 1
                            if jp is not None:
                                hnb = max(hnb, t + 1 + jp + 1)
    print("stats:", stats)

if __name__ == '__main__':
    main()
