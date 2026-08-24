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

The canonical ledger contains 35 chapter rows.  All 35 chapters are represented
in Lean; no chapter remains {lit}`not-started`.  The generated dashboard owns
live theorem totals and status counts, so this prose does not freeze a
completed-prefix milestone.

The edition map records one partially represented coverage unit in Chapter 34:
§34.5 has typed VERTEX-COVER complement semantics but not yet the serialized
language, polynomial-time machines, or later reductions.  Chapter 34 is the
sole repository row whose status remains {lit}`partial`.

* **Chapter 34, NP-Completeness:** Sections 34.1--34.3 provide the complexity
  framework, `P ⊆ NP`, and polynomial-reduction infrastructure.  Section 34.4
  proves the represented concrete reductions, the semantic Cook--Levin
  whole-tableau circuit, its polynomial gate/input/encoding bounds, the exact
  function-level map, and finite-certificate semantics for
  `GeneralCircuitSAT`.  A concrete TM2 now computes the exact certificate-
  checker Boolean on every input, and all successful, rejecting, and malformed
  routes share an explicit polynomial runtime bound, proving
  `GeneralCircuitSAT ∈ NP`.  The explicit Cook--Levin map, semantic equivalence,
  and polynomial output-length bound yield the separately named
  {lit}`cookLevin_textbookCircuitization` semantic-and-size package.  A fixed
  polynomial-time TM2 now computes that exact map, so
  {lit}`cookLevin_theorem`, {lit}`generalCircuitSAT_npHard`, and
  {lit}`generalCircuitSAT_npComplete` close the Cook--Levin main theorem.
  The direct textbook general-circuit-to-SAT formula is also semantically
  exact; its total raw map preserves language membership and has a cubic
  output-length bound.  A fixed polynomial-time TM2 computes this raw map,
  yielding {lit}`GeneralCircuitSAT ≤p SAT` and transporting universal
  NP-hardness through the concrete SAT-to-3-CNF reduction.  General
  graph-plus-{lit}`k` CLIQUE has an honest raw encoding, exact certificate
  semantics, a concrete polynomial-time verifier, membership in NP, and a
  concrete polynomial-time 3-CNF-SAT reduction; {lit}`CLIQUE` is therefore
  NP-complete.  Section 34.5 now proves the typed equivalence between a
  size-{lit}`k` clique and a size-at-most-{lit}`|V|-k` vertex cover of the
  deterministic complement.  Raw language semantics, concrete reduction and
  verifier machines, VERTEX-COVER NP-completeness, and the remaining §34.5
  problems are open.  A standalone concrete SAT NP verifier is an optional
  refinement, not a dependency of the completed hardness chain.

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

The separate {lit}`CLRSLean.OnlineMaterial` catalog retains 464 tracked theorem
groups: 421 from the three wholly excluded third-edition Chapters 19, 20, and
33, plus 43 from moved section-level developments such as maximum subarray,
matroids and task scheduling, detailed SIMPLEX, iterative FFT, and integer
factorization.  Those 43 groups are disjoint from the 1,523 canonical tracked
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
