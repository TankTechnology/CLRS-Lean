#!/usr/bin/env python3
"""Analyze B2 disagreements: sigma[t] vs past repair pages Q'', t vs J''_i,
and what makes non-B2 disagreements B1.  Mirrors search_iter.py exactly."""
import sys, os
from itertools import product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search_b2 as s
from search_iter import repair_schedule, d0_of_max

def analyze():
    alpha = [1, 2, 3, 4]
    stats = {"B2": 0, "B2_sig_in_Q": 0, "B2_sig_in_E": 0, "disagree": 0,
             "sig_in_Q_eq_Jpp": 0, "sig_in_Q_after_Jpp": 0,
             "sig_in_Q_before_Jpp": 0, "sig_in_Q_dead": 0}
    examples_after = []
    examples_eq = []
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
                    repairs = []  # (t_i, q''_i, J''_i or None)
                    exch = None
                    while True:
                        t = None
                        for tpos in range(t0, n):
                            if s.sched_cache(d, sig, C0, tpos + 1) != s.sched_cache_fifo(sig, C0, tpos + 1):
                                t = tpos
                                break
                        if t is None:
                            break
                        stats["disagree"] += 1
                        if t >= hnb:
                            q = d(t)
                            qp = s.fifo_evict(s.sched_cache(d, sig, C0, t), sig, t)
                            jp = s.next_use(sig, t + 1, qp)
                            if jp is not None:
                                jp -= t + 1
                            d = s.exchange_schedule(d, t, q, qp, sig, C0)
                            exch = (d, t, q, qp)
                            repairs = []  # new window: fresh Q''
                            t0 = t + 1
                            if jp is not None:
                                hnb = max(hnb, t + 1 + jp + 1)
                        else:
                            cache_t = s.sched_cache(d, sig, C0, t)
                            sig_t = sig[t]
                            Q = {r[1] for r in repairs}
                            isB2 = d(t) in cache_t
                            if isB2:
                                stats["B2"] += 1
                                e, t0x, q0, q0p = exch
                                if sig_t in s.sched_cache(e, sig, C0, t):
                                    stats["B2_sig_in_E"] += 1
                                if sig_t in Q:
                                    stats["B2_sig_in_Q"] += 1
                                    rel = "?"
                                    for (ti, qp, Jpp) in repairs:
                                        if qp == sig_t:
                                            rel = ("dead" if Jpp is None else
                                                   "eq" if t == Jpp else "after" if t > Jpp else "before")
                                    print(f"B2-SIG-IN-Q sigma={sig} C0={sorted(C0)} d0={name} t={t} sig[t]={sig_t} "
                                          f"rel={rel} repairs={repairs}")
                            else:
                                # B1 disagreement
                                if sig_t in Q:
                                    rel = "?"
                                    J = None
                                    for (ti, qp, Jpp) in repairs:
                                        if qp == sig_t:
                                            J = Jpp
                                            rel = ("dead" if Jpp is None else
                                                   "eq" if t == Jpp else "after" if t > Jpp else "before")
                                    if rel == "eq":
                                        stats["sig_in_Q_eq_Jpp"] += 1
                                        if len(examples_eq) < 3:
                                            examples_eq.append((sig, C0, name, t, sig_t, repairs))
                                    elif rel == "after":
                                        stats["sig_in_Q_after_Jpp"] += 1
                                        if len(examples_after) < 3:
                                            examples_after.append((sig, C0, name, t, sig_t, repairs))
                                    elif rel == "dead":
                                        stats["sig_in_Q_dead"] += 1
                                    else:
                                        stats["sig_in_Q_before_Jpp"] += 1
                            # advance
                            qp = s.fifo_evict(cache_t, sig, t)
                            jp = s.next_use(sig, t + 1, qp)
                            if jp is not None:
                                jp -= t + 1
                            nop = t + 1 + jp if jp is not None else t
                            if isB2:
                                q = d(t)
                                j = s.next_use(sig, t + 1, q)
                                r = repair_schedule(d, t, qp, nop)
                                d = r
                                repairs.append((t, qp, nop if jp is not None else None))
                            else:
                                d = repair_schedule(d, t, qp, nop)
                                repairs.append((t, qp, nop if jp is not None else None))
                            t0 = t + 1
                            if jp is not None:
                                hnb = max(hnb, t + 1 + jp + 1)
    print("stats:", stats)
    print("--- t = J''_i examples (B1) ---")
    for ex in examples_eq:
        print(ex)
    print("--- t > J''_i examples (B1) ---")
    for ex in examples_after:
        print(ex)

if __name__ == '__main__':
    analyze()
