import CLRSLean.ProofPatterns
import CLRSLean.Probability
import CLRSLean.FourthEdition
import CLRSLean.OnlineMaterial
import CLRSLean.Chapter_01
import CLRSLean.Chapter_02
import CLRSLean.Chapter_03
import CLRSLean.Chapter_04
import CLRSLean.Chapter_05
import CLRSLean.Chapter_06
import CLRSLean.Chapter_07
import CLRSLean.Chapter_08
import CLRSLean.Chapter_09
import CLRSLean.Chapter_10
import CLRSLean.Chapter_11
import CLRSLean.Chapter_12
import CLRSLean.Chapter_13
import CLRSLean.Chapter_14
import CLRSLean.Chapter_15
import CLRSLean.Chapter_16
import CLRSLean.Chapter_17
import CLRSLean.Chapter_18
import CLRSLean.Chapter_19
-- Keep registered Chapter 19 compatibility pages in Verso's module set while
-- the chapter aggregator itself exposes only canonical textbook sections.
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts
import CLRSLean.Chapter_20
import CLRSLean.Chapter_21
import CLRSLean.Chapter_22
import CLRSLean.Chapter_23
import CLRSLean.Chapter_24
import CLRSLean.Chapter_25
import CLRSLean.Chapter_26
import CLRSLean.Chapter_27
import CLRSLean.Chapter_28
import CLRSLean.Chapter_29
import CLRSLean.Chapter_30
import CLRSLean.Chapter_31
import CLRSLean.Chapter_32
import CLRSLean.Chapter_33
import CLRSLean.Chapter_34
import CLRSLean.Extensions
import CLRSLean.Progress
import CLRSLean.Status
import CLRSLean.Workflow

/-!
# CLRS-Lean

CLRS-Lean is a fourth-edition-primary Lean 4 companion for CLRS-style algorithm
proofs.  It is organized as an online book: canonical guides under
{lit}`CLRSLean.FourthEdition` explain each formalization boundary, and current
theorem-bearing source modules contain the definitions, executable models,
interfaces, and proofs.

## Whole-Book Snapshot

The current reviewed ledger represents all 35 fourth-edition chapters.  Of
these, 34 chapters are {lit}`main-proof-complete` for their advertised Lean
models and Chapter 1 is an {lit}`expository` project guide.  All 1,658 selected
reader-facing theorem entries are proved, with zero edition-coverage gap units;
465 separately tracked entries belong to online or supplementary material.

The Lean-native trust gate audits a flagship declaration for every chapter and
permits only Lean's standard {lit}`propext`, {lit}`Classical.choice`, and
{lit}`Quot.sound` axioms.  These counts describe the reviewed theorem inventory:
they do not claim every exercise, end-of-chapter problem, RAM implementation,
or low-level refinement.  Open **Progress Dashboard** for the chapter matrix and
**Proof Status** for the exact interpretation.

## Project Aim

The first target is the mathematical content of CLRS: loop invariants,
sortedness and permutation arguments, exchange proofs, cut properties,
recurrences, optimal substructure, and graph-algorithm correctness.  Pointer
mutation, RAM costs, and line-by-line pseudocode refinement are separate layers
unless a chapter's main theorem depends on them.

This distinction lets a chapter be complete for its advertised model without
claiming that every implementation detail or exercise has been formalized.

## Start Here

There are four useful reading routes:

1. **Algorithms:** choose a fourth-edition chapter guide, read its scope, then
   follow its current source link to a represented section.
2. **Progress:** open **Progress Dashboard** for the generated chapter matrix.
3. **Planning:** open **Proof Status** for completed, partial, and missing proof
   groups.
4. **Contributing:** open **Workflow**, then use the relevant chapter guide and
   focused interface test.

The **Reusable CLRS proof patterns** page collects the small cross-chapter APIs
for boundary shifts, exchange certificates, fibers, and interval geometry.

## Fourth-Edition Primary View

The canonical public chapter sequence is CLRS fourth edition, Chapters 1--35.
{lit}`docs/clrs-fourth-edition-map.csv` owns the section-level bridge from that
sequence to current theorem-bearing sources.  All 35 chapter guides now point
to represented source.  Chapter 34 is main-proof-complete at its advertised
textbook boundary: the checked chain reaches Cook--Levin, GeneralCircuitSAT,
SAT, 3-CNF-SAT, general CLIQUE, VERTEX-COVER, HAM-CYCLE, decision-TSP, and
SUBSET-SUM.  Third-edition-only Fibonacci heaps, van Emde Boas trees,
computational geometry, and moved section material live under
{lit}`CLRSLean.OnlineMaterial`.  Progress counts are
selected theorem inventories rather than counts of every fourth-edition
textbook obligation.

Existing {lit}`CLRSLean.Chapter_NN` imports and declarations keep their current
meanings through all {lit}`1.x` releases and for at least six months after the
facade release.  They may be removed only in {lit}`2.0` or later, after both
gates pass.  See {lit}`docs/migrations/clrs4.md` for shifted chapter imports,
current declaration namespaces, and the cleanup policy.

## Status Meaning

* {lit}`main-proof-complete`: the advertised theorem stack is complete for its
  current model.
* {lit}`main-proof-complete-for-correctness`: correctness is complete, while
  explicit work or RAM refinement remains.
* {lit}`selected-section-complete`: represented sections are complete; the
  entire textbook chapter is not claimed.
* {lit}`partial`: useful proofs exist, but a central theorem or refinement
  target remains.
* {lit}`not-started`: no represented section exists on the current main branch.
* {lit}`expository`: the chapter is a guide with no theorem target.

The machine-readable source for chapter rows is
{lit}`docs/clrs-proof-progress.csv`, interpreted through
{lit}`docs/clrs-fourth-edition-map.csv`.  The public **Progress Dashboard** is
generated from the progress CSV.  Exact theorem names and boundaries live in
the section modules and their focused interface tests; {lit}`docs/scope.md`
states the project-wide claim boundary.

## Library Shape

* {lit}`CLRSLean.lean`: library root and landing page.
* {lit}`CLRSLean/FourthEdition/Chapter_XX.lean`: canonical chapter guide.
* {lit}`CLRSLean/OnlineMaterial.lean`: online/supplementary compatibility catalog.
* {lit}`CLRSLean/ProofPatterns.lean`: reusable pattern aggregator.
* {lit}`CLRSLean/Chapter_XX.lean`: current compatibility source aggregator.
* {lit}`CLRSLean/Chapter_XX/Section_XX_Y_Name.lean`: current formal source.
* {lit}`CLRSLean/Progress.lean`: generated progress dashboard.
* {lit}`CLRSLean/Status.lean`: reader-facing status interpretation.
* {lit}`CLRSLean/Workflow.lean`: contributor workflow.
* {lit}`Tests/Chapter_XX_Interface.lean`: public interface checks.

Chapter guides aggregate section modules.  Section modules own formal facts.
Interface tests protect the public surface.  Progress prose never replaces a
kernel-checked theorem.

## Verification

For local repository checks:

* {lit}`uv run python scripts/check_repository.py`
* {lit}`lake build CLRSLean`

For a reader-facing or navigation change, also build the Verso site:

Run {lit}`lake build :literateHtml`.

Generated HTML is deployed by GitHub Actions and is not committed as source.
-/
