#!/usr/bin/env python3
"""Exact-accounting slack analysis for the B1 step (see DESIGN.md
"slack-accounting blocker").  Mirrors the Lean semantics exactly
(search_b2.py) and runs the full iteration with the DESIGN's exact
bookkeeping: each exchange `+1` iff its bad event did not occur
(`sigma[J'] not in D_{J'}`), each B1 `-bad` (`bad = sigma[J'''] in
D_{J'''}`), B2 repairs free.

Findings over sigma of length 4-9, alphabet {1,2,3,4}, C0 = {1,2}/
{1,2,3}, both smallest/largest-resident d0 policies:

- the exact accounting **crashes 492 times** (`slack` goes negative) —
  the DESIGN's "0 slack crashes" claim is stale (search_iter.search2
  stops after the first 3 conservative-accounting crashes and never
  reaches them).  Minimal counterexample:
  sigma=[1,1,3,2,4,1,2,4], C0={1,2}, max: A at 2 (bad, slack 0),
  B2 at 4 (q'' dead, free), B1 at 5 with bad (sigma[7]=4 in D_7),
  slack 0 -> -1.  The B1 step itself is legal (hftd: sigma[5]=1 not in
  {2,4}; hnoop: d 5 = 3 not in cache) and its bad event is real
  (the B2 at 4 re-kept 4 in the cache).
- the branch-1 supply (`window_branch1_once` +
  `evicted_page_absent_until_request`, B5, kernel-checked) covers
  **exactly** the B1-bads with `d t2 = q'_0` (the window page):
  cross-tab of the 3836 B1-bads: 2796 with `d t2 = q'_0` — all with
  the exchange's bad NOT occurring and slack >= 1; 1040 with
  `d t2 != q'_0` — 492 with slack 0 (the crashes; 172 at old nop
  positions `t2 in P`).  So `bad <= slack` is provable for the q'_0
  B1s but false in general; the `d t2 != q'_0` B1s (`d t2` a past
  pair's page, by `exchange_evict_mem_or_q'` + the chain) need a new
  supply argument.
- crediting the B2-q''-dead's exact saving (the repair keeps `q`, so
  `schedMisses r + 1 <= schedMisses d` at the good event `J`) reduces
  the crashes to 228 but does not close the gap.

Usage:  python3 search_slack.py
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


def run(sig, C0, d0, credit_b2qpd):
    """Full iteration with the exact accounting.  Returns
    (crashes, b1_bad, q0p_noexchbad, q0p_exchbad, other_noexchbad,
    other_exchbad, q0p_slack0, other_slack0)."""
    n = len(sig)
    d = d0
    t0 = 0
    hnb = 0
    slack = 0
    exch = None  # (q', bad')
    out = [0, 0, 0, 0, 0, 0, 0, 0]
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
            bad = jp is not None and sig[t + 1 + jp] in s.sched_cache(d, sig, C0, t + 1 + jp)
            d = s.exchange_schedule(d, t, q, qp, sig, C0)
            if not bad:
                slack += 1
            t0 = t + 1
            if jp is not None:
                hnb = max(hnb, t + 1 + jp + 1)
            exch = (qp, bad)
        else:
            cache_t = s.sched_cache(d, sig, C0, t)
            if d(t) not in cache_t:
                # B1
                qp = s.fifo_evict(cache_t, sig, t)
                jp = s.next_use(sig, t + 1, qp)
                if jp is not None:
                    jp -= t + 1
                bad = jp is not None and sig[t + 1 + jp] in s.sched_cache(d, sig, C0, t + 1 + jp)
                if bad:
                    out[1] += 1
                    qpx, badx = exch
                    if d(t) == qpx:
                        if badx:
                            out[3] += 1
                        else:
                            out[2] += 1
                        if slack < 1:
                            out[6] += 1
                    else:
                        if badx:
                            out[5] += 1
                        else:
                            out[4] += 1
                        if slack < 1:
                            out[7] += 1
                nop = t + 1 + jp if jp is not None else t
                d = repair_schedule(d, t, qp, nop)
                if bad:
                    slack -= 1
                    if slack < 0:
                        out[0] += 1
                t0 = t + 1
                if jp is not None:
                    hnb = max(hnb, t + 1 + jp + 1)
            else:
                # B2
                q = d(t)
                qp = s.fifo_evict(cache_t, sig, t)
                j = s.next_use(sig, t + 1, q)
                jp = s.next_use(sig, t + 1, qp)
                if j is not None:
                    j -= t + 1
                if jp is not None:
                    jp -= t + 1
                nop = t + 1 + jp if jp is not None else t
                d = repair_schedule(d, t, qp, nop)
                if credit_b2qpd and j is not None and jp is None:
                    slack += 1
                t0 = t + 1
                if jp is not None:
                    hnb = max(hnb, t + 1 + jp + 1)
    return out


def main():
    alpha = [1, 2, 3, 4]
    totals = [0] * 8
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
                    out = run(sig, C0, d0, credit_b2qpd=False)
                    for i in range(8):
                        totals[i] += out[i]
    names = ['crashes', 'b1_bad', 'q0p_noexchbad', 'q0p_exchbad',
             'other_noexchbad', 'other_exchbad', 'q0p_slack0',
             'other_slack0']
    print(dict(zip(names, totals)))


if __name__ == '__main__':
    main()


def run_pp(sig, C0, d0):
    """The per-page credit accounting (DESIGN.md "Non-q0' B1 pairing
    proposal", Dev/B13_PerPageCredit.lean): each exchange resets the
    per-page credits to the window's good (the kept page `q`), each
    alive-alive B2 (not bad) / B2-q''-dead credits its kept page, the
    q0'-B1s draw from the slack (the exchange's +1), and the non-q0'
    B1s draw from their page's credit first.  Returns
    (crashes, pp_draws, slack_draws)."""
    n = len(sig)
    d = d0
    t0 = 0
    hnb = 0
    slack = 0
    credit = {}
    win = None
    crashes = 0
    pp = 0
    sl = 0
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
            win = (t, q, qp)
            credit = {}
            if j is not None:
                credit[q] = 1  # the exchange's good on the kept page
            if jp is not None:
                hnb = max(hnb, t + 1 + jp + 1)
        else:
            cache_t = s.sched_cache(d, sig, C0, t)
            qp = s.fifo_evict(cache_t, sig, t)
            jp = s.next_use(sig, t + 1, qp)
            if jp is not None:
                jp -= t + 1
            bad = jp is not None and sig[t + 1 + jp] in s.sched_cache(d, sig, C0, t + 1 + jp)
            dt2 = d(t)
            resident = dt2 in cache_t
            if not resident:
                if bad:
                    if dt2 == win[2]:
                        # q0'-B1: the exchange's +1 (the slack pool)
                        slack -= 1
                        if slack < 0:
                            crashes += 1
                    else:
                        # non-q0'-B1: the page's pending good first
                        c = credit.get(qp, 0)
                        if c >= 1:
                            credit[qp] = c - 1
                            pp += 1
                        else:
                            slack -= 1
                            sl += 1
                            if slack < 0:
                                crashes += 1
                nop = t + 1 + jp if jp is not None else t
                d = repair_schedule(d, t, qp, nop)
                t0 = t + 1
                if jp is not None:
                    hnb = max(hnb, t + 1 + jp + 1)
            else:
                q = d(t)
                j = s.next_use(sig, t + 1, q)
                if j is not None:
                    j -= t + 1
                if j is not None and jp is not None and j < jp:
                    if not bad:
                        credit[q] = credit.get(q, 0) + 1
                elif j is not None and jp is None:
                    credit[q] = credit.get(q, 0) + 1
                nop = t + 1 + jp if jp is not None else t
                d = repair_schedule(d, t, qp, nop)
                t0 = t + 1
                if jp is not None:
                    hnb = max(hnb, t + 1 + jp + 1)
    return crashes, pp, sl


def main_pp():
    """The per-page credit accounting's crash scan (the DESIGN's
    candidate-C residual is 164; the per-page form reduces the plain 492
    to 336)."""
    alpha = [1, 2, 3, 4]
    tot = [0, 0, 0]
    for n in range(4, 10):
        for sig_t in product(alpha, repeat=n):
            sig = list(sig_t)
            if sig[0] not in (1, 2):
                continue
            for C0 in ({1, 2}, {1, 2, 3}):
                if not all(x in C0 for x in sig[0:2]):
                    continue
                for d0 in (s.d0_of(sig, C0), d0_of_max(sig, C0)):
                    out = run_pp(sig, C0, d0)
                    for i in range(3):
                        tot[i] += out[i]
    names = ['crashes', 'pp_draws', 'slack_draws']
    print('per-page:', dict(zip(names, tot)))
