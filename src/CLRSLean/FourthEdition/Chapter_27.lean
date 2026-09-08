import CLRSLean.FourthEdition.Chapter_27.Section_27_1_Waiting_For_Elevator
import CLRSLean.FourthEdition.Chapter_27.Section_27_2_Maintaining_A_Search_List
import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching
import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.Competitive
import CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching.LowerBound

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
with worst-case ratio `2 - E/S`.

Section 27.2 (Maintaining a search list) is formalized natively in
`CLRSLean.FourthEdition.Chapter_27.Section_27_2_Maintaining_A_Search_List`:
the list-update problem, the MOVE-TO-FRONT strategy with its per-request cost,
the inversion-distance potential, and Theorem 27.2 (MOVE-TO-FRONT is
`4`-competitive against any list-update strategy that keeps its list a
permutation of the initial set).

Section 27.3 (Online caching) is formalized natively in
`CLRSLean.FourthEdition.Chapter_27.Section_27_3_Online_Caching`: the paging
model with the least-recently-used (LRU) policy as a most-recent-first list,
the legacy memoryless {lit}`Algorithm` with legal-state capacity/hit laws,
and the new {lit}`Policy` interface with arbitrary auxiliary state. An inhabited
LRU policy preserves recency order, so equal resident sets can produce different
evictions. {lit}`Schedule` describes future-dependent offline traces separately.

{lit}`Schedule.lru_k_competitive` proves the actual LRU miss bound against every
legal offline schedule. {lit}`Policy.lru_k_competitive` follows for actual online
policy runs. The actual phase-based offline execution is a valid schedule.
{lit}`Policy.no_real_competitive` proves that for every real ratio
{lit}`0 ≤ c < k` and every real additive constant there is a nonempty request
sequence defeating that ratio. The witness length grows with the constant;
this theorem permits arbitrary hidden history and requires positive capacity.


No legacy source is promoted into this chapter.

- [Waiting-for-an-elevator section](CLRSLean/FourthEdition/Chapter_27/Section_27_1_Waiting_For_Elevator/)
- [Maintaining-a-search-list section](CLRSLean/FourthEdition/Chapter_27/Section_27_2_Maintaining_A_Search_List/)
- [Online-caching section](CLRSLean/FourthEdition/Chapter_27/Section_27_3_Online_Caching/)

## Coverage boundary

The represented rental lower bounds retain positive horizons and strictly
positive offline costs; {lit}`skiRental_not_competitive_below` rules out every
strictly smaller ratio. The list-update theorem uses equality of distinct-key
sets. Physical index and adjacent-swap interpretations require duplicate-free
permutations; arbitrary offline list traces are not covered by its strategy
interface. Paging uses explicit valid states, history-dependent online policies,
and separately validated offline schedules. These are abstract competitive
cost models, not machine-runtime bounds.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
