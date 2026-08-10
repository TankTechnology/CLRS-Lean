import CLRSLean.FourthEdition.Chapter_27.Section_27_1_Waiting_For_Elevator

/-!
# Chapter 27 — Online Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Section 27.1 (Waiting for an elevator) is formalized natively in
`CLRSLean.FourthEdition.Chapter_27.Section_27_1_Waiting_For_Elevator`: the
rent-or-buy (ski rental) problem — the cost of the deterministic
rent-`a`-days-then-buy strategy, the optimal offline cost, Theorem 27.1 (any
strategy with `a * r < p ≤ (a + 1) * r` is `2`-competitive), and the elevator
corollary whose wait-`S - E`-then-take-the-stairs strategy is `2`-competitive
with worst-case ratio `2 - E/S`.  No legacy source is promoted into this
chapter.

- [Waiting-for-an-elevator section](CLRSLean/FourthEdition/Chapter_27/Section_27_1_Waiting_For_Elevator/)

## Coverage boundary

Status: `partial`.  Represented section 27.1 (Waiting for an elevator) — the
rent-or-buy cost and the offline optimum `min (T*r) p`, Theorem 27.1 (the
`2`-competitive upper bound), and the elevator corollary with its worst-case
competitive ratio.  The lower bound that no deterministic strategy beats
`2 - r/p` is recorded as a gap in the section.  Sections 27.2 (Maintaining a
search list) and 27.3 (Online caching) are not yet represented.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
