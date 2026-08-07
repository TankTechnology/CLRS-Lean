/-!
# Proof Status

This page gives a concise reader-facing interpretation of CLRS-Lean's canonical
fourth-edition proof state.  The generated **Progress Dashboard** owns chapter
counts and status rows; {lit}`docs/clrs-fourth-edition-map.csv` owns the bridge
to current theorem-bearing sources; section modules own formal truth; and
{lit}`docs/proof-map.md` records theorem-level legacy-source detail.

## Edition And Compatibility Contract

Chapter numbers on this page mean CLRS fourth edition.  New work should import
{lit}`CLRSLean.FourthEdition.Chapter_NN`.  Existing unqualified
{lit}`CLRSLean.Chapter_NN` imports and their public declarations keep their
third-edition meanings through all {lit}`1.x` releases and for at least six
months after the facade release.  Removal is possible only in {lit}`2.0` or
later, after both gates pass.  Declaration namespaces migrate chapter by
chapter; {lit}`docs/migrations/clrs4.md` records the current mapping.

## Status Labels

* {lit}`main-proof-complete`: the advertised main theorem stack is complete for
  the current model.
* {lit}`main-proof-complete-for-correctness`: algorithm correctness is complete;
  explicit work, RAM, or imperative refinement remains.
* {lit}`selected-section-complete`: represented sections are complete without a
  claim about the unrepresented remainder of the chapter.
* {lit}`partial`: meaningful theorem infrastructure exists, but the edition map
  names a central textbook theorem, section, or refinement gap.
* {lit}`not-started`: no section is represented in the canonical chapter.
* {lit}`expository`: a guide page with no theorem target.

The proved/tracked fraction is a selected proof-inventory metric.  Even a
complete fraction can accompany {lit}`partial` when the fourth-edition map names
an obligation that has not yet been selected into that inventory.

## Fourth-Edition Snapshot

The canonical ledger contains 35 chapter rows.  Thirty chapters currently reuse
represented theorem content; Chapters 25, 27, and 33--35 are honestly
{lit}`not-started`.  The generated dashboard owns live theorem totals and status
counts, so this prose does not freeze a completed-prefix milestone.

The edition map currently records these fourth-edition gaps:

* **Chapter 4, Divide-and-Conquer:** Sections 4.1 and 4.6 are partial; Section
  4.7 is not started.  Maximum subarray is retained as online material.
* **Chapter 7, Quicksort:** Section 7.4 remains partial.
* **Chapter 10, Elementary Data Structures:** Section 10.1 remains partial.
* **Chapter 11, Hash Tables:** Section 11.5 is not started in the canonical
  chapter; the old perfect-hashing development is supplementary material.
* **Chapter 13, Red-Black Trees:** Sections 13.2--13.4 remain partial because the
  color/black-height shape results are not yet combined with BST preservation
  and textbook update/cost refinements.
* **Chapter 14, Dynamic Programming:** all five sections remain partial at the
  tabulated/memoized algorithm and cost boundary; §14.3 additionally lacks a
  generic dynamic-programming interface.
* **Chapter 15, Greedy Algorithms:** Section 15.4, offline caching, is not
  started; retained matroid and task-scheduling results are supplementary.
* **Chapter 17, Augmenting Data Structures:** all three sections remain partial:
  OS-RANK, the augmentation-cost theorem, and the dynamic/static interval-tree
  bridge are the principal gaps.
* **Chapter 29, Linear Programming:** Sections 29.1--29.3 remain partial for
  general-form normalization, finite formulation bridges, and canonical
  declaration ownership; detailed SIMPLEX material remains available online.
* **Chapter 32, String Matching:** Section 32.1 is represented; Sections
  32.2--32.5 are not started.

All other represented chapters retain their more specific complete,
correctness-complete, selected-section-complete, or expository labels from the
progress ledger.  Such a label applies only to the advertised Lean model and
represented fourth-edition sections, never automatically to exercises,
chapter-end Problems, pointer/RAM models, or floating-point implementations.

## Not-Started Chapters

* **Chapter 25, Matchings in Bipartite Graphs:** no legacy source is promoted;
  maximum-flow matching results are cross-references only.
* **Chapter 27, Online Algorithms:** no canonical theorem-bearing source yet.
* **Chapter 33, Machine-Learning Algorithms:** no canonical theorem-bearing
  source yet.
* **Chapters 34--35, NP-Completeness and Approximation Algorithms:** guide-only,
  with whole-chapter inventories pending.

These rows have zero canonical tracked theorem entries even when a legacy
source directory with the same number exists.

## Online And Supplementary Material

The separate {lit}`CLRSLean.OnlineMaterial` catalog retains 467 tracked theorem
groups: 421 from the three wholly excluded third-edition Chapters 19, 20, and
33, plus 46 from moved section-level developments such as maximum subarray,
perfect hashing, matroids and task scheduling, detailed SIMPLEX, iterative FFT,
and integer factorization.  Those 46 groups have been removed from the
canonical chapter totals, so the 1,326 canonical and 467 online entries are
disjoint.  {lit}`docs/clrs-online-material.csv` owns the topic-level counts and
source modules; compatibility imports do not duplicate either ledger.

## Reader Contract

A {lit}`proved` or complete label always refers to a named Lean theorem for an
explicit model.  A {lit}`partial` label names the remaining mathematical or
representation layer.  Compatibility facades preserve theorem availability;
they do not by themselves prove every obligation in the new edition.  Dated
audits are historical evidence rather than live status sources.
-/
