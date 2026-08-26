import CLRSLean.Chapter_16
import CLRSLean.FourthEdition.Chapter_15.Section_15_1_Activity_Selection
import CLRSLean.FourthEdition.Chapter_15.Section_15_1_Activity_Selection.TextbookModel
import CLRSLean.FourthEdition.Chapter_15.Section_15_1_Activity_Selection.Iterative
import CLRSLean.FourthEdition.Chapter_15.Section_15_2_Greedy_Meta
import CLRSLean.FourthEdition.Chapter_15.Section_15_2_Greedy_Meta.ActivitySelection
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.TextbookCost
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.TextbookLemmas
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.Complexity
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching

/-!
# Chapter 15 — Greedy Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 15.1--15.3 are native fourth-edition sections (activity selection,
the greedy-choice/optimal-substructure meta-theorems, and Huffman codes).
Their textbook-facing companion modules add the iterative activity selector and
exact scan count, a concrete activity-selection instance of the meta-theorem,
Huffman equation (15.4), named Lemma 15.2/15.3 interfaces, and explicit cost
models.  They are imported directly from
[Section 15.1](CLRSLean/FourthEdition/Chapter_15/Section_15_1_Activity_Selection/),
[Section 15.2](CLRSLean/FourthEdition/Chapter_15/Section_15_2_Greedy_Meta/),
and
[Section 15.3](CLRSLean/FourthEdition/Chapter_15/Section_15_3_Huffman_Codes/).
Declarations keep their legacy namespaces (`CLRS.ActivitySelection`,
`CLRS.GreedyMeta`, `CLRS.HuffmanV2`); the third-edition-numbered imports
{lit}`CLRSLean.Chapter_16` and {lit}`CLRSLean.Chapter_16.Section_16_*` forward to
these sources during the compatibility period.

## Coverage boundary

Section 15.4 (offline caching) is a native fourth-edition section.  Its finite
cache model, farthest-in-future policy, legal-trace exchange construction, and
public optimality theorems `CLRS.Caching.fifo_optimal` and
`CLRS.Caching.fifo_optimal_from_empty` complete CLRS Theorem 15.5 for every
finite request sequence at both the nonempty eviction-phase boundary and the
literal empty start of the core transition semantics.  It is imported through
[Section 15.4](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/).
The section is split into the sub-modules:

* [Cache Model](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S1_Cache_Model/)
* [Farthest-In-Future Eviction](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S2_Farthest_In_Future/)
* [Optimality](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S3_Optimality/)
* [Empty-start bridge](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/EmptyStart/)

This completion is at the mathematical cache-policy level.  Pointer/RAM
implementations and hardware caching costs remain optional refinements outside
the advertised theorem boundary.  An arbitrary-capacity compulsory-fill phase
is represented by the policy-independent `compulsoryFillCost` bridge rather
than by an unverified mutable cache implementation.

The third-edition Sections 16.4 (matroids) and 16.5 (task scheduling) are
retained as supplementary online material (reachable through
{lit}`CLRSLean.OnlineMaterial`).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
