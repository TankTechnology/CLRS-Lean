#!/usr/bin/env python3
"""Search for a concrete B2-before-s1 trace of the fifo_optimal iteration.

Mirrors the Lean semantics exactly:

- `Farther none _ = True`; `Farther (some i) none = False`;
  `Farther (some i) (some j) = (j <= i)`.
- `farthestInList`: p::rest -> if rest = [] then p
  else if Farther (f p) (f (farthestInList f rest)) then p else q
  (ties toward the left).
- `exchangeDecision d t q q' s`:
    if s < t: d s
    else if s = t: q'
    else if d s = q': q'
    else if (σ[s] == q' or σ[s] == q) and σ[s] in d-cache s: multiset(C' \\ d-cache s, ≠q' preferred)
    else if d s in C': d s
    else: multiset(C' \\ d-cache s, any)
- `schedCache`: hit -> unchanged; fault -> insert σ[s] (C.erase (d s)).
- d0 = a reduced schedule (at a fault, d0 evicts a resident page).
"""
from itertools import product

def next_use(sig, i, p):
    for k in range(i, len(sig)):
        if sig[k] == p:
            return k
    return None

def farther(a, b):
    if a is None:
        return True
    if b is None:
        return False
    return b <= a

def farthest_in_list(f, lst):
    if not lst:
        return 0
    p, rest = lst[0], lst[1:]
    if not rest:
        return p
    q = farthest_in_list(f, rest)
    return p if farther(f(p), f(q)) else q

def fifo_evict(cache, sig, i):
    return farthest_in_list(lambda p: next_use(sig, i + 1, p), sorted(cache))

def sched_cache(d, sig, C0, s):
    C = set(C0)
    for i in range(min(s, len(sig))):
        r = sig[i]
        if r not in C:
            C = (C - {d(i)}) | {r}
    return C

def sched_cache_fifo(sig, C0, s):
    C = set(C0)
    for i in range(min(s, len(sig))):
        r = sig[i]
        if r not in C:
            C = (C - {fifo_evict(C, sig, i)}) | {r}
    return C

def exchange_schedule(d, t, q, qp, sig, C0):
    n = len(sig)

    def decision(s, C):
        r = sig[s] if s < n else 0  # σ.getD s 0
        if s < t:
            return d(s)
        if s == t:
            return qp
        if d(s) == qp:
            return qp
        ds_cache = sched_cache(d, sig, C0, s)
        if (r == qp or r == q) and r in ds_cache:
            M = C - ds_cache
            Mf = {x for x in M if x != qp}
            if Mf:
                return sorted(Mf)[0]
            if M:
                return sorted(M)[0]
            return 0
        if d(s) in C:
            return d(s)
        M = C - ds_cache
        if M:
            return sorted(M)[0]
        return 0
    C = set(C0)
    decisions = []
    for s in range(0, n + 1):
        decisions.append(decision(s, C))
        if s < n:
            r = sig[s]
            if r not in C:
                C = (C - {decisions[s]}) | {r}
    return lambda s: decisions[s] if s <= n else 0

def find_b2_before_s1(sig, C0):
    """Return (trace, diagnosis) if the first exchange produces a B2
    disagreement before the window's branch-1 spot; else None."""
    n = len(sig)
    d = d0_of(sig, C0)

    def cache(s):
        return sched_cache(d, sig, C0, s)

    def fifo_cache(s):
        return sched_cache_fifo(sig, C0, s)

    # first disagreement (must be a fault for d and FIF, caches differ)
    t = None
    for s in range(n):
        if cache(s + 1) != fifo_cache(s + 1):
            t = s
            break
    if t is None:
        return None
    r = sig[t]
    if r in cache(t):
        return None  # not a fault — skip
    q = d(t)
    if q not in cache(t):
        return None  # not reduced
    qp = fifo_evict(cache(t), sig, t)
    if qp == q or qp not in cache(t):
        return None
    jp = next_use(sig, t + 1, qp)
    if jp is None:
        return None  # case-one exchange — not the scenario
    jp -= t + 1
    Jp = t + 1 + jp
    if Jp >= n:
        return None
    # exchange
    d1 = exchange_schedule(d, t, q, qp, sig, C0)

    def cache1(s):
        return sched_cache(d1, sig, C0, s)

    # first disagreement after t
    t2 = None
    for s in range(t + 1, n):
        if cache1(s + 1) != fifo_cache(s + 1):
            t2 = s
            break
    if t2 is None or t2 >= Jp:
        return None  # no case-B disagreement in the window
    if d1(t2) in cache1(t2):
        # B2 candidate: need a future no-op fault (branch-1 spot) in (t2, Jp]
        s1 = None
        for s in range(t2 + 1, Jp + 1):
            if sig[s] not in cache1(s) and d1(s) not in cache1(s):
                s1 = s
                break
        if s1 is not None:
            return (sig, C0, t, q, qp, jp, t2, s1, d, d1)
        return None
    return None

def d0_of(sig, C0):
    """Reduced schedule: smallest-resident eviction at faults, junk on hits."""
    d = {}
    C = set(C0)
    for i in range(len(sig)):
        r = sig[i]
        if r in C:
            d[i] = 0
        else:
            e = min(C)
            d[i] = e
            C = (C - {e}) | {r}
    return lambda s: d.get(s, 0)


def check_design_example():
    print("=== DESIGN.md example sigma=[1,2,3,4,5,1] ===")
    sig = [1, 2, 3, 4, 5, 1]
    C0 = {1, 2}
    for i in range(len(sig) + 1):
        print(f"  FIF cache {i}: {sorted(sched_cache_fifo(sig, C0, i))}")
    ev = fifo_evict({1, 2}, sig, 2)
    print(f"  FIF evicts at position 2: page {ev}  (design says 1 -> WRONG)")


def main():
    check_design_example()
    print()
    print("=== search for B2-before-s1 (with future branch-1 no-op spot) ===")
    alpha = [1, 2, 3, 4]
    found = 0
    for n in range(5, 10):
        for sig_t in product(alpha, repeat=n):
            sig = list(sig_t)
            if sig[0] not in (1, 2):
                continue
            for C0 in ({1, 2}, {1, 2, 3}):
                if not all(x in C0 for x in sig[0:2]):
                    continue
                res = find_b2_before_s1(sig, C0)
                if res is not None:
                    (sig, C0, t, q, qp, jp, t2, s1, d, d1) = res
                    print(f"\n  FOUND sigma={sig} C0={sorted(C0)}")
                    print(f"    exchange at t={t}: q={q} q'={qp} J'={t+1+jp}")
                    print(f"    B2 at t2={t2} (d1 t2 = {d1(t2)} resident, "
                          f"FIF evicts {fifo_evict(sched_cache(d1, sig, C0, t2), sig, t2)})")
                    print(f"    branch-1 no-op spot s1={s1} (d1 s1 = {d1(s1)})")
                    for s in range(n + 1):
                        print(f"      cache {s}: d1={sorted(sched_cache(d1, sig, C0, s))} "
                              f"FIF={sorted(sched_cache_fifo(sig, C0, s))}")
                    found += 1
                    if found >= 3:
                        return
    print(f"  none found in range")


if __name__ == '__main__':
    main()

def find_keepswap_scenario(sig, C0):
    """Search: exchange at t0, then a B2 at t2 with J0' <= J2 (q's next use
    beyond the window end) AND the bad event at J0' (d hits q0') AND
    q in C'_J0' \\ E_J0' (multiset could evict q). Returns the trace info."""
    n = len(sig)
    d = d0_of(sig, C0)

    def cache(s):
        return sched_cache(d, sig, C0, s)

    def fifo_cache(s):
        return sched_cache_fifo(sig, C0, s)

    t = None
    for s in range(n):
        if cache(s + 1) != fifo_cache(s + 1):
            t = s
            break
    if t is None:
        return None
    if sig[t] in cache(t):
        return None
    q0 = d(t)
    if q0 not in cache(t):
        return None
    q0p = fifo_evict(cache(t), sig, t)
    if q0p == q0 or q0p not in cache(t):
        return None
    j0 = next_use(sig, t + 1, q0)
    j0p = next_use(sig, t + 1, q0p)
    if j0 is None or j0p is None:
        return None
    j0 -= t + 1
    j0p -= t + 1
    J0p = t + 1 + j0p
    if J0p >= n:
        return None
    d1 = exchange_schedule(d, t, q0, q0p, sig, C0)

    def cache1(s):
        return sched_cache(d1, sig, C0, s)

    # first disagreement after t
    t2 = None
    for s in range(t + 1, n):
        if cache1(s + 1) != fifo_cache(s + 1):
            t2 = s
            break
    if t2 is None or t2 >= J0p:
        return None
    q = d1(t2)
    if q not in cache1(t2):
        return None  # not B2
    # bad event at J0p: q0p in d's cache at J0p
    if sig[J0p] not in cache(J0p):
        return None  # bad event did not occur
    # J2 = next use of q after t2
    j2 = next_use(sig, t2 + 1, q)
    if j2 is None:
        return None
    j2 -= t2 + 1
    J2 = t2 + 1 + j2
    if J0p > J2:
        return None  # q's next use before window end — no conflict
    # q in C'_J0p \ E_J0p?
    if q not in cache1(J0p) or q in cache1(J0p) and q not in sched_cache(d1, sig, C0, J0p):
        pass
    C1 = cache1(J0p)
    E1 = cache1(J0p)  # same — e IS the exchange
    # hmm — C' and E are the same set (e = exchange). Need q in C' \ E — impossible!
    # So q in C'_J0p \ E_J0p means q in cache1(J0p) and q not in cache1(J0p) — contradiction!
    # The real question: does the multiset branch at J0p fire, and can its choice be q?
    return (sig, C0, t, q0, q0p, J0p, t2, q, J2, d, d1)


def search_keepswap():
    print("=== search: multiset-at-J0' could evict q (J0' <= J2, bad event) ===")
    alpha = [1, 2, 3, 4]
    found = 0
    for n in range(6, 10):
        for sig_t in product(alpha, repeat=n):
            sig = list(sig_t)
            if sig[0] not in (1, 2):
                continue
            for C0 in ({1, 2}, {1, 2, 3}):
                if not all(x in C0 for x in sig[0:2]):
                    continue
                res = find_keepswap_scenario(sig, C0)
                if res is not None:
                    (sig, C0, t, q0, q0p, J0p, t2, q, J2, d, d1) = res
                    print(f"\n  FOUND sigma={sig} C0={sorted(C0)}")
                    print(f"    exchange at t={t}: q0={q0} q0'={q0p} J0'={J0p}")
                    print(f"    B2 at t2={t2}: q={q} J2={J2}  (J0'={J0p} <= J2={J2})")
                    print(f"    bad event at J0': d hits q0'={q0p}")
                    print(f"    d1 evicts at J0': {d1(J0p)} (q={q}? {d1(J0p)==q})")
                    found += 1
                    if found >= 3:
                        return
    print("  none found")


if __name__ == '__main__':
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else 'main'
    if mode == 'keepswap':
        search_keepswap()
    else:
        main()
