#!/usr/bin/env python3
"""Search: the case-one exchange's branch-1 at-most-once (DESIGN.md "Case one").

At a case-one exchange (nextUse q' = none, q' never requested again), the
OR-form `e s ∈ E_s ∨ d s = q'` holds at exchange faults.  The state's hdred
field needs `hnb'` past the branch-1 position; this requires:

  (a) at most one exchange-fault s > t with d s = q' (branch-1 spot);
  (b) each branch-1 spot is a d-fault (a real eviction of q' — the
      window_branch1_once mechanism: after it, q' leaves D forever);
  (c) D_s − E_s ⊆ {q'} throughout the case-one exchange (the mechanism for
      exchange-fault ⟹ d-fault: σ[s] ∈ D−E with σ[s] ≠ q' impossible);
  (d) after a case-one step, the next disagreement t₂ (if any) satisfies
      t₂ ≥ s₁ + 1 (the new hnb' = past the branch-1 spot) — so the next
      step is case A and never needs a window (win = none).

The junk danger: at d-hits, an arbitrary policy's eviction is unconstrained,
so `d s = q'` at d-hits is possible in principle.  The search therefore runs
several d0 junk policies, including an adversarial one that evicts a dead
page at every hit while one is in cache — the worst case for (a)/(b).
"""
import sys, os
from itertools import product
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import search_b2 as s
from search_iter import repair_schedule


def d0_of_junk(sig, C0, junk):
    """Reduced schedule with a custom junk value on hits."""
    d = {}
    C = set(C0)
    for i in range(len(sig)):
        r = sig[i]
        if r in C:
            d[i] = junk(C, i)
        else:
            e = min(C)
            d[i] = e
            C = (C - {e}) | {r}
    return lambda x: d.get(x, 0)


def d0_min(sig, C0):
    return d0_of_junk(sig, C0, lambda C, i: 0)


def d0_min_evictC(sig, C0):
    return d0_of_junk(sig, C0, lambda C, i: min(C))


def d0_max(sig, C0):
    """Largest-resident eviction at faults, junk 0 on hits."""
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


def d0_adversarial(sig, C0):
    """At hits, evict a dead page of the cache (smallest); else min(C).
    A legitimate policy (at hits the eviction is unconstrained), which
    maximizes the chance that d s = q' at d-hits."""
    def junk(C, i):
        dead = [p for p in C if s.next_use(sig, i + 1, p) is None]
        if dead:
            return min(dead)
        return min(C)
    return d0_of_junk(sig, C0, junk)


def run(sig, C0, d0, stats, tag):
    n = len(sig)
    d = d0
    t0 = 0
    hnb = 0
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
            j = s.next_use(sig, t + 1, q)
            jp = s.next_use(sig, t + 1, qp)
            if j is not None:
                j -= t + 1
            if jp is not None:
                jp -= t + 1
            e = s.exchange_schedule(d, t, q, qp, sig, C0)
            if jp is None:
                # ---- case-one exchange: measure branch-1 spots ----
                st = stats[tag]
                st["caseone"] += 1
                spots = []
                for pos in range(t + 1, n):
                    E = s.sched_cache(e, sig, C0, pos)
                    dFault = sig[pos] not in s.sched_cache(d, sig, C0, pos)
                    if sig[pos] not in E and d(pos) == qp:
                        spots.append((pos, dFault))
                    # (c): D − E ⊆ {q'}
                    D = s.sched_cache(d, sig, C0, pos)
                    if D - E - {qp}:
                        st["diffDE_bad"] += 1
                        if st["diffDE_bad"] <= 3:
                            print(f"  [D-E-BAD] {tag} sigma={sig} C0={sorted(C0)} t={t} "
                                  f"q={q} q'={qp} pos={pos} D-E={sorted(D - E)}")
                    # exchange-fault at a d-hit
                    if sig[pos] not in E and not dFault:
                        st["exFault_dHit"] += 1
                        if st["exFault_dHit"] <= 3:
                            print(f"  [EXF-DHIT] {tag} sigma={sig} C0={sorted(C0)} t={t} "
                                  f"q={q} q'={qp} pos={pos} sig[pos]={sig[pos]} in D")
                st["branch1_total"] += len(spots)
                if len(spots) > 1:
                    st["branch1_multi"] += 1
                    if st["branch1_multi"] <= 3:
                        print(f"  [MULTI] {tag} sigma={sig} C0={sorted(C0)} t={t} q={q} q'={qp} "
                              f"spots={[(p, 'd-fault' if f else 'd-hit') for p, f in spots]}")
                for (p, isdFault) in spots:
                    if not isdFault:
                        st["branch1_dHit"] += 1
                        if st["branch1_dHit"] <= 3:
                            print(f"  [SPOT-DHIT] {tag} sigma={sig} C0={sorted(C0)} t={t} "
                                  f"q={q} q'={qp} spot={p} (d hit: sig[{p}]={sig[p]} in D)")
                # (d): next disagreement vs the new hnb' = past the spot
                hnbp = (spots[0][0] + 1) if spots else t + 1
                for t2 in range(t + 1, n):
                    if s.sched_cache(e, sig, C0, t2 + 1) != s.sched_cache_fifo(sig, C0, t2 + 1):
                        if t2 < hnbp:
                            st["next_below_hnbp"] += 1
                            if st["next_below_hnbp"] <= 3:
                                print(f"  [NEXT<hnb'] {tag} sigma={sig} C0={sorted(C0)} t={t} "
                                      f"q={q} q'={qp} spot={spots} t2={t2} hnbp={hnbp}")
                        if t2 < hnb:
                            st["next_below_hnb"] += 1
                        break
            d = e
            t0 = t + 1
            if jp is not None:
                hnb = max(hnb, t + 1 + jp + 1)
        else:
            cache_t = s.sched_cache(d, sig, C0, t)
            qp = s.fifo_evict(cache_t, sig, t)
            jp = s.next_use(sig, t + 1, qp)
            if jp is not None:
                jp -= t + 1
            nop = t + 1 + jp if jp is not None else t
            d = repair_schedule(d, t, qp, nop)
            t0 = t + 1
            if jp is not None:
                hnb = max(hnb, t + 1 + jp + 1)


def main():
    alpha = [1, 2, 3, 4]
    stats = {}
    tags = [("min-junk0", d0_min), ("min-junkC", d0_min_evictC),
            ("max-junk0", d0_max), ("adversarial", d0_adversarial)]
    for (tag, mk) in tags:
        stats[tag] = {"caseone": 0, "branch1_total": 0, "branch1_multi": 0,
                      "branch1_dHit": 0, "diffDE_bad": 0, "exFault_dHit": 0,
                      "next_below_hnb": 0, "next_below_hnbp": 0}
    for n in range(4, 10):
        for sig_t in product(alpha, repeat=n):
            sig = list(sig_t)
            if sig[0] not in (1, 2):
                continue
            for C0 in ({1, 2}, {1, 2, 3}):
                if not all(x in C0 for x in sig[0:2]):
                    continue
                for (tag, mk) in tags:
                    run(sig, C0, mk(sig, C0), stats, tag)
    for tag in stats:
        st = stats[tag]
        print(f"{tag}: case-one={st['caseone']} branch1={st['branch1_total']} "
              f"multi={st['branch1_multi']} spot-dHit={st['branch1_dHit']} "
              f"D-E-bad={st['diffDE_bad']} exFault-dHit={st['exFault_dHit']} "
              f"next<hnb={st['next_below_hnb']} next<hnb'={st['next_below_hnbp']}")


if __name__ == '__main__':
    main()
