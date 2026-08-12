import CLRSLean.FourthEdition.Chapter_35.Section_35_1_The_Vertex_Cover_Problem
import CLRSLean.FourthEdition.Chapter_35.Section_35_2_The_Traveling_Salesperson_Problem

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

The remaining sections — 35.3 (set cover) and 35.4-35.5 (randomized rounding and
the subset-sum FPTAS) — are not yet represented.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
