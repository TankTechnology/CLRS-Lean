#!/usr/bin/env python3
"""Empirical analysis of the hQ-extension blocker (see DESIGN.md
"hQ-extension blocker").  Mirrors the Lean semantics exactly
(search_b2.py) and runs the full iteration with the full-history pair
set Q (repair pairs since the last case A, with their nop positions):

- `nop==t2+1 at a step`: an old pair's nop is exactly at t2+1 — the
  strict `t2+1 < n_i` of the new state's hQ field fails for it;
- `nop<=t2 at a step`: an old pair's nop is at/before t2 — hQ fails;
- `B2 reached with hQ'-broken state`: a B2 step whose incoming state's
  hQ field (bound t0, full-history Q) already fails;
- `chain fails with pruned Q`: the reverse diff `E_s - D_s` escapes the
  pages of the pruned (alive, nop <= t0) pair set — the chain needs the
  full page history (all positions, and future positions >= t0);
- `B2 with sigma[t] = pruned pair's page`: the hQ consumers' worst case
  (never happens — the consulted pair is never broken).

Usage:  python3 search_hq.py
"""
import sys, os
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search_b2 as s


def repair_schedule(e, t, qp, nop):
    return lambda x: qp if (x == t or x == nop) else e(x)


def d0_of_max(sig, C0):
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
    return lambda x: d.get(x, 0)


def run(sig, C0, d0):
    """Full iteration with full-history Q; returns the counters."""
    n = len(sig)
    d = d0
    t0 = 0
    hnb = 0
    Q = []  # (t_i, q''_i, nop_i or None for dead)
    exch = None
    cnt = {'nop_t2p1': 0, 'nop_le_t2': 0, 'b2_broken': 0,
           'chain_pruned_all': 0, 'chain_pruned_future': 0,
           'b2_pruned_page': 0}
    while True:
        t = None
        for tp in range(t0, n):
            if s.sched_cache(d, sig, C0, tp + 1) != s.sched_cache_fifo(sig, C0, tp + 1):
                t = tp
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
            t0 = t + 1
            if jp is not None:
                hnb = max(hnb, t + 1 + jp + 1)
            Q = []
        else:
            cache_t = s.sched_cache(d, sig, C0, t)
            is_b2 = d(t) in cache_t
            for (ti, qpi, nop) in Q:
                if nop is not None:
                    if nop == t + 1:
                        cnt['nop_t2p1'] += 1
                    if nop <= t:
                        cnt['nop_le_t2'] += 1
            broken = any(nop is not None and nop <= t + 1 for (ti, qpi, nop) in Q)
            if is_b2:
                if broken:
                    cnt['b2_broken'] += 1
                pruned = set(qp for (ti, qpi, nop) in Q if nop is not None and nop <= t0)
                if sig[t] in pruned:
                    cnt['b2_pruned_page'] += 1
            qp = s.fifo_evict(cache_t, sig, t)
            jp = s.next_use(sig, t + 1, qp)
            if jp is not None:
                jp -= t + 1
            nop = t + 1 + jp if jp is not None else t
            d = repair_schedule(d, t, qp, nop)
            Q.append((t, qp, nop if jp is not None else None))
            t0 = t + 1
            if jp is not None:
                hnb = max(hnb, t + 1 + jp + 1)
            if exch is not None:
                e2 = exch[0]
                pages = set(qp for (ti, qpi, nop) in Q if nop is None) | \
                        set(qp for (ti, qpi, nop) in Q if nop is not None and nop > t0)
                for tpos in range(n + 1):
                    diff = s.sched_cache(e2, sig, C0, tpos) - s.sched_cache(d, sig, C0, tpos)
                    if not diff.issubset(pages):
                        cnt['chain_pruned_all'] += 1
                        if tpos >= t0:
                            cnt['chain_pruned_future'] += 1
    return cnt


def main():
    totals = {'nop_t2p1': 0, 'nop_le_t2': 0, 'b2_broken': 0,
              'chain_pruned_all': 0, 'chain_pruned_future': 0,
              'b2_pruned_page': 0}
    alpha = [1, 2, 3, 4]
    for n in range(4, 10):
        for sig_t in product(alpha, repeat=n):
            sig = list(sig_t)
            if sig[0] not in (1, 2):
                continue
            for C0 in ({1, 2}, {1, 2, 3}):
                if not all(x in C0 for x in sig[0:2]):
                    continue
                for (d0, name) in ((s.d0_of(sig, C0), 'min'),
                                   (d0_of_max(sig, C0), 'max')):
                    cnt = run(sig, C0, d0)
                    for k in totals:
                        totals[k] += cnt[k]
    print(totals)


if __name__ == '__main__':
    main()
