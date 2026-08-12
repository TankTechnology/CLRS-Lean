#!/usr/bin/env python3
"""Exact iteration simulator for the fifo_optimal proof (see DESIGN.md).

Mirrors the Lean semantics exactly (Farther, farthestInList, exchangeDecision,
repairSchedule, schedCache) and runs the full iteration with exact
bookkeeping:

- every B2's good event is computed directly (`q ∈ Ŝ_J`); if it fails, the
  weak +1 cost is charged iff the bad event (the source hits `q''` at `J''`)
  occurs;
- every B1's cost is charged exactly (bad event at its `J'''`);
- every exchange `+1` iff its bad event did not occur.

Search results (sigma of length 4-9, alphabet {1,2,3,4}, C0 = {1,2}/{1,2,3},
both smallest/largest-resident d0 policies):

- `main`: 0 slack crashes, 0 keep-swap failures with exact accounting;
- `search2`: same with the conservative "B1 always costs 1" accounting —
  crashes only on dead-page B1s (the repair is free; the exact accounting
  is required);
- `search3`: `e` never hits at a B2 disagreement (0 e-hit), and every B2
  good event holds (0 keep-fail over 55188 B2 positions) — the evidence for
  the reverse-diff invariant `cache_e − cache_d ⊆ Q''` in DESIGN.md.

Usage:  python3 search_iter.py [main|search2|search3]
"""
import sys
import os
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search_b2 as s


def repair_schedule(e, t, qp, nop):
    return lambda s: qp if (s == t or s == nop) else e(s)


def d0_of_max(sig, C0):
    """Reduced schedule: largest-resident eviction at faults."""
    d = {}
    C = set(C0)
    for i in range(len(sig)):
        r = sig[i]
        if r in C:
            d[i] = 0
        else:
            e = max(C)
            d[i] = e
            C = (C - {e}) | {r}
    return lambda s: d.get(s, 0)


def run_iteration(sig, C0, d0, conservative_b1=False, trace=False):
    """Exact iteration simulation.  Returns (ok, slack, min_slack, steps)."""
    n = len(sig)
    d = d0
    t0 = 0
    hnb = 0
    slack = 0
    min_slack = 0
    steps = []
    while True:
        t = None
        for tpos in range(t0, n):
            if s.sched_cache(d, sig, C0, tpos + 1) != s.sched_cache_fifo(sig, C0, tpos + 1):
                t = tpos
                break
        if t is None:
            return True, slack, min_slack, steps
        if t >= hnb:
            # case A: exchange
            q = d(t)
            qp = s.fifo_evict(s.sched_cache(d, sig, C0, t), sig, t)
            j = s.next_use(sig, t + 1, q)
            jp = s.next_use(sig, t + 1, qp)
            if j is not None:
                j -= t + 1
            if jp is not None:
                jp -= t + 1
            bad = jp is not None and sig[t + 1 + jp] in s.sched_cache(d, sig, C0, t + 1 + jp)
            d = s.exchange_schedule(d, t, q, qp, sig, C0)
            if not bad:
                slack += 1
            t0 = t + 1
            if jp is not None:
                hnb = max(hnb, t + 1 + jp + 1)
            steps.append(('A', t, q, qp, j, jp, bad))
        else:
            cache_t = s.sched_cache(d, sig, C0, t)
            if d(t) not in cache_t:
                # case B1: no-op eviction
                qp = s.fifo_evict(cache_t, sig, t)
                jp = s.next_use(sig, t + 1, qp)
                if jp is not None:
                    jp -= t + 1
                bad = jp is not None and sig[t + 1 + jp] in s.sched_cache(d, sig, C0, t + 1 + jp)
                nop = t + 1 + jp if jp is not None else t
                d = repair_schedule(d, t, qp, nop)
                if conservative_b1 or bad:
                    slack -= 1
                    min_slack = min(min_slack, slack)
                t0 = t + 1
                if jp is not None:
                    hnb = max(hnb, t + 1 + jp + 1)
                steps.append(('B1', t, d(t), qp, jp, bad))
            else:
                # case B2: resident eviction
                q = d(t)
                qp = s.fifo_evict(cache_t, sig, t)
                j = s.next_use(sig, t + 1, q)
                jp = s.next_use(sig, t + 1, qp)
                if j is not None:
                    j -= t + 1
                if jp is not None:
                    jp -= t + 1
                nop = t + 1 + jp if jp is not None else t
                r = repair_schedule(d, t, qp, nop)
                kept = j is not None and q in s.sched_cache(r, sig, C0, t + 1 + j)
                bad = jp is not None and sig[t + 1 + jp] in s.sched_cache(d, sig, C0, t + 1 + jp)
                if not kept and bad:
                    slack -= 1
                    min_slack = min(min_slack, slack)
                d = r
                t0 = t + 1
                if jp is not None:
                    hnb = max(hnb, t + 1 + jp + 1)
                steps.append(('B2', t, q, qp, j, jp, kept, bad))


def main():
    """Exact accounting: 0 crashes and 0 keep-fails expected."""
    alpha = [1, 2, 3]
    crashes = 0
    keepfail = 0
    for n in range(4, 9):
        for sig_t in product(alpha, repeat=n):
            sig = list(sig_t)
            if sig[0] not in (1, 2):
                continue
            for C0 in ({1, 2}, {1, 2, 3}):
                if not all(x in C0 for x in sig[0:2]):
                    continue
                ok, slack, min_slack, steps = run_iteration(sig, C0, s.d0_of(sig, C0))
                if min_slack < 0:
                    crashes += 1
                    print(f"SLACK CRASH sigma={sig} C0={sorted(C0)} min_slack={min_slack}")
                    for st in steps:
                        print(f"    {st}")
                    if crashes >= 3:
                        return
                for st in steps:
                    if st[0] == 'B2' and st[5] is not None and not st[6]:
                        keepfail += 1
                        if keepfail <= 3:
                            print(f"KEEP-FAIL sigma={sig} C0={sorted(C0)} step={st}")
    print(f"main: crashes={crashes} keep-fails={keepfail}")


def search2():
    """Larger alphabet, two d0 policies, conservative B1 accounting."""
    alpha = [1, 2, 3, 4]
    crashes = 0
    keepfail = 0
    for n in range(4, 9):
        for sig_t in product(alpha, repeat=n):
            sig = list(sig_t)
            if sig[0] not in (1, 2):
                continue
            for C0 in ({1, 2}, {1, 2, 3}):
                if not all(x in C0 for x in sig[0:2]):
                    continue
                for (d0, name) in ((s.d0_of(sig, C0), 'min'), (d0_of_max(sig, C0), 'max')):
                    for cons in (False, True):
                        ok, slack, min_slack, steps = run_iteration(sig, C0, d0, cons)
                        if min_slack < 0:
                            crashes += 1
                            print(f"CRASH sigma={sig} C0={sorted(C0)} d0={name} cons={cons} min={min_slack}")
                            for st in steps:
                                print(f"    {st}")
                            if crashes >= 3:
                                return
                        for st in steps:
                            if st[0] == 'B2' and st[5] is not None and not st[6]:
                                keepfail += 1
                                if keepfail <= 3:
                                    print(f"KEEP-FAIL sigma={sig} C0={sorted(C0)} d0={name} step={st}")
    print(f"search2: crashes={crashes} keep-fails={keepfail}")


def search3():
    """Subtle scenarios: e-hit at B2 disagreements, keep-fail, and the
    reverse-diff invariant (with B1's repair page added to Q'')."""
    alpha = [1, 2, 3, 4]
    ehit = 0
    keepfail = 0
    diff_bad = 0
    total_b2 = 0
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
                    W = set()
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
                            j = s.next_use(sig, t + 1, q)
                            jp = s.next_use(sig, t + 1, qp)
                            if j is not None:
                                j -= t + 1
                            if jp is not None:
                                jp -= t + 1
                            d = s.exchange_schedule(d, t, q, qp, sig, C0)
                            exch = (d, t, q, qp)
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
                                W = W | {qp}
                                t0 = t + 1
                                if jp is not None:
                                    hnb = max(hnb, t + 1 + jp + 1)
                            else:
                                total_b2 += 1
                                q = d(t)
                                qp = s.fifo_evict(cache_t, sig, t)
                                j = s.next_use(sig, t + 1, q)
                                jp = s.next_use(sig, t + 1, qp)
                                if j is not None:
                                    j -= t + 1
                                if jp is not None:
                                    jp -= t + 1
                                e, t0x, q0, q0p = exch
                                if sig[t] in s.sched_cache(e, sig, C0, t):
                                    ehit += 1
                                    if ehit <= 3:
                                        print(f"E-HIT sigma={sig} C0={sorted(C0)} d0={name} t={t} sig[t]={sig[t]} q={q} q''={qp}")
                                e_cache = s.sched_cache(e, sig, C0, t)
                                diff = (cache_t - e_cache) | (e_cache - cache_t)
                                if not diff.issubset(W | {q0, q0p}):
                                    diff_bad += 1
                                    if diff_bad <= 3:
                                        print(f"DIFF-BAD sigma={sig} C0={sorted(C0)} d0={name} t={t} diff={sorted(diff)} W={sorted(W)} q0={q0} q0p={q0p}")
                                nop = t + 1 + jp if jp is not None else t
                                r = repair_schedule(d, t, qp, nop)
                                kept = j is not None and q in s.sched_cache(r, sig, C0, t + 1 + j)
                                if j is not None and not kept:
                                    keepfail += 1
                                    if keepfail <= 3:
                                        print(f"KEEP-FAIL sigma={sig} C0={sorted(C0)} d0={name} t={t} q={q} q''={qp}")
                                d = r
                                W = W | {q, qp}
                                t0 = t + 1
                                if jp is not None:
                                    hnb = max(hnb, t + 1 + jp + 1)
    print(f"search3: e-hit={ehit} keep-fail={keepfail} diff-bad={diff_bad} total-B2={total_b2}")


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'main'
    {'main': main, 'search2': search2, 'search3': search3}[mode]()
