import CLRSLean.FourthEdition.Chapter_35.Section_35_1_The_Vertex_Cover_Problem
import CLRSLean.FourthEdition.Chapter_35.Section_35_2_The_Traveling_Salesperson_Problem
import CLRSLean.FourthEdition.Chapter_35.Section_35_3_The_Set_Covering_Problem
import CLRSLean.FourthEdition.Chapter_35.Section_35_4_Randomization_And_Linear_Programming

/-!
# Chapter 35 — Approximation Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

No legacy source is promoted into this chapter.

## Coverage boundary

Status: partial.

Section 35.1 (the vertex-cover problem) is a native fourth-edition section: it
formalizes the vertex-cover problem, the greedy APPROX-VERTEX-COVER algorithm,
and its 2-approximation guarantee (Lemma 35.1 and Theorem 35.1).  It is
imported through
[Section 35.1](CLRSLean/FourthEdition/Chapter_35/Section_35_1_The_Vertex_Cover_Problem/).

Section 35.2 (the traveling-salesperson problem) is also a native fourth-edition
section: it models APPROX-TSP-TOUR with a rooted tree (a minimum spanning tree),
proves that the depth-first walk costs exactly twice the tree (Lemma 35.2), that
the preorder tour visits every vertex exactly once, that shortcutting the walk
costs no more than the walk (triangle inequality), and — combining these with
Lemma 35.3 (an MST costs no more than any tour) — that APPROX-TSP-TOUR returns a
tour within a factor of two of any tour (Theorem 35.2).  It is imported through
[Section 35.2](CLRSLean/FourthEdition/Chapter_35/Section_35_2_The_Traveling_Salesperson_Problem/).

Section 35.3 (the set-covering problem) is a native fourth-edition section: it
models the universe and family of GREEDY-SET-COVER, the greedy pick, the
returned family, and — via the harmonic charging argument — proves that the
number of sets picked is at most `H(d)` times the size of any cover, where `d`
bounds the set sizes (Theorem 35.3), and — via the iterated multiplicative
shrink of the uncovered set — that GREEDY-SET-COVER is an `O(lg |X|)`-
approximation algorithm (Theorem 35.4).  It is imported through
[Section 35.3](CLRSLean/FourthEdition/Chapter_35/Section_35_3_The_Set_Covering_Problem/).

Section 35.4 (randomization and linear programming) is a native fourth-edition
section: it proves the randomized `8/7`-approximation of MAX-3-CNF (Theorem
35.5), where a clause with three literals over distinct variables is satisfied
with probability `7/8` under a uniformly random assignment and linearity of
expectation gives the `7/8 · |F|` bound, and the factor-two LP-rounding
approximation of minimum-weight vertex cover (Theorem 35.6), where rounding the
fractional cover `x` up at the `1/2` threshold costs at most twice the LP
objective.  It is imported through
[Section 35.4](CLRSLean/FourthEdition/Chapter_35/Section_35_4_Randomization_And_Linear_Programming/).

The remaining section — 35.5 (the subset-sum FPTAS) — is not yet represented.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
