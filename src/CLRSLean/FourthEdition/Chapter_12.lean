import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees
import CLRSLean.FourthEdition.Chapter_12.Section_12_2_Querying_A_Binary_Search_Tree
import CLRSLean.FourthEdition.Chapter_12.Section_12_3_Insertion_And_Deletion
import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees.ExpectedHeight

/-!
# Chapter 12 — Binary Search Trees

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 12.1--12.3 each have a canonical reader page for the BST model,
queries, and updates. They share one theorem-bearing implementation, together
with focused random-construction and expected-height companion modules.
Declarations retain
the `CLRS.Chapter12` namespace during the compatibility period; the
third-edition-numbered imports {lit}`CLRSLean.Chapter_12` and
{lit}`CLRSLean.Chapter_12.Section_12_*` forward to this source.

## Coverage boundary

The functional binary-search-tree development is shared by the three
fourth-edition reader sections. Strict ordering and duplicate-key
suppression give set semantics for natural-number keys. The pointer-heap
representation preserves child structure and disjoint footprints; it does not
require stored parent fields to agree with all incoming child edges.

A supplementary random-construction analysis, inherited from the older edition
and outside the fourth-edition §12.1–12.3 section inventory, proves the expected height of a uniformly randomly built BST is at most
{lit}`30 Hₙ ≤ 30(1 + log n)`.

## Implementation details

* [Random-construction height bridge](CLRSLean/FourthEdition/Chapter_12/Section_12_1_Binary_Search_Trees/RandomConstruction/)
* [Expected-height theorem](CLRSLean/FourthEdition/Chapter_12/Section_12_1_Binary_Search_Trees/ExpectedHeight/)

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
