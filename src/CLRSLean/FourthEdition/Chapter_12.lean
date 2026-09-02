import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees
import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees.ExpectedHeight

/-!
# Chapter 12 — Binary Search Trees

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 12.1--12.3 are native fourth-edition sections, sourced from the single
[Section 12.1](CLRSLean/FourthEdition/Chapter_12/Section_12_1_Binary_Search_Trees/)
module, together with focused random-construction and expected-height companion
modules (what is a binary search tree, querying a binary search tree, and
insertion and deletion share the main theorem-bearing body).  Declarations retain
the `CLRS.Chapter12` namespace during the compatibility period; the
third-edition-numbered imports {lit}`CLRSLean.Chapter_12` and
{lit}`CLRSLean.Chapter_12.Section_12_*` forward to this source.

## Coverage boundary

The existing functional binary-search-tree development is reused across the
fourth-edition three-section organization.  The Section 12.4 analysis proves
the expected height of a uniformly randomly built BST is at most
{lit}`30 Hₙ ≤ 30(1 + log n)`.

## Implementation details

* [Random-construction height bridge](CLRSLean/FourthEdition/Chapter_12/Section_12_1_Binary_Search_Trees/RandomConstruction/)
* [Expected-height theorem](CLRSLean/FourthEdition/Chapter_12/Section_12_1_Binary_Search_Trees/ExpectedHeight/)

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
