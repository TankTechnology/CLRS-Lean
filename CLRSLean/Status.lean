/-!
# Proof Status

This page gives a concise reader-facing interpretation of CLRS-Lean's canonical
fourth-edition proof state.  The generated **Progress Dashboard** owns chapter
counts and status rows; {lit}`docs/clrs-fourth-edition-map.csv` owns the bridge
to current theorem-bearing sources; section modules and interface tests own
formal truth; and {lit}`docs/scope.md` records the project-wide claim boundary.

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

## Whole-Book Snapshot

The canonical ledger contains 35 chapter rows.  All 35 chapters are represented
in Lean: 34 chapters are {lit}`main-proof-complete` for their advertised models,
and Chapter 1 is {lit}`expository`.  No chapter remains {lit}`partial` or
{lit}`not-started`, and the generated dashboard reports all 1,609 selected
reader-facing theorem entries proved with zero edition-coverage gap units.

This is a selected, reviewed theorem inventory.  It does not claim every
exercise, chapter-end Problem, pointer/RAM model, or floating-point
implementation.  The generated dashboard owns the live totals; this page
explains how to read them.

## Chapter 34 Flagship

Chapter 34 is now {lit}`main-proof-complete` at its advertised boundary.
Section 34.5 closes the selected textbook chain through VERTEX-COVER,
HAM-CYCLE, decision-TSP, and SUBSET-SUM.  Each public decision problem has its
honest serialized language and certificate interface, fixed polynomial-time
reduction and verifier machines, exact semantic bridge, and NP-completeness
wrapper.

* Sections 34.1--34.3 provide the complexity framework, {lit}`P ⊆ NP`, and
  polynomial-reduction infrastructure.
* Section 34.4 closes the semantic Cook--Levin tableau circuit, polynomial
  size bounds, exact function-level reduction, and fixed polynomial-time TM2;
  {lit}`cookLevin_theorem` and {lit}`generalCircuitSAT_npComplete` are the public
  closure points.
* The concrete chain continues through SAT, 3-CNF-SAT, and honest general
  graph-plus-{lit}`k` CLIQUE, including fixed verifiers and reduction machines.
* Section 34.5 closes VERTEX-COVER, HAM-CYCLE, decision-TSP, and SUBSET-SUM with
  exact semantic bridges, bounded certificates, fixed machines, and the public
  {lit}`VERTEXCOVER_npComplete`, {lit}`HAMCYCLE_npComplete`,
  {lit}`TSP_npComplete`, and {lit}`SUBSETSUM_npComplete` theorems.

A standalone SAT verifier and direct concrete machines for the empty and
universal languages remain optional refinements; they do not reopen the chapter
boundary.  The Chapter 34 guide and section pages own the construction-level
details.

All other represented chapters retain their more specific complete,
correctness-complete, selected-section-complete, or expository labels from the
progress ledger.  Such a label applies only to the advertised Lean model and
represented fourth-edition sections, never automatically to exercises,
chapter-end Problems, pointer/RAM models, or floating-point implementations.

Chapter 15 is no longer an edition-map gap: the native §15.4 finite-cache model
now exposes `CLRS.Caching.fifo_optimal`, the unconditional farthest-in-future
optimality theorem for nonempty initial caches and finite request sequences.

## Not-Started Chapters

No chapter is {lit}`not-started`: every canonical chapter has at least one
represented section or an expository guide.

## Online And Supplementary Material

The separate {lit}`CLRSLean.OnlineMaterial` catalog retains 465 tracked theorem
groups: 421 from the three wholly excluded third-edition Chapters 19, 20, and
33, plus 44 from moved section-level developments such as maximum subarray,
matroids and task scheduling, detailed SIMPLEX, iterative FFT, and integer
factorization.  Those 44 groups are disjoint from the 1,609 canonical tracked
theorem entries.
{lit}`docs/clrs-online-material.csv` owns the topic-level counts and source
modules; compatibility imports do not duplicate either ledger.

## Reader Contract

A {lit}`proved` or complete label always refers to a named Lean theorem for an
explicit model.  A {lit}`partial` label names the remaining mathematical or
representation layer.  Compatibility facades preserve theorem availability;
they do not by themselves prove every obligation in the new edition.  Dated
audits are historical evidence rather than live status sources.
-/
