import CLRSLean.ProofPatterns
import CLRSLean.Probability
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
import CLRSLean.Chapter_20
import CLRSLean.Chapter_21
import CLRSLean.Chapter_22
import CLRSLean.Chapter_23
import CLRSLean.Chapter_24
import CLRSLean.Chapter_25
import CLRSLean.Chapter_26
import CLRSLean.Chapter_27
import CLRSLean.Chapter_33
import CLRSLean.Progress
import CLRSLean.Status
import CLRSLean.Workflow

/-!
# CLRS-Lean

CLRS-Lean is a Lean 4 companion for CLRS-style algorithm proofs.  It is
organized as an online book: chapter pages explain each formalization boundary,
and section pages contain the definitions, executable models, theorem
interfaces, and proofs.

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

1. **Algorithms:** choose a chapter in the sidebar, read its scope, then open a
   represented section.
2. **Progress:** open **Progress Dashboard** for the generated chapter matrix.
3. **Planning:** open **Proof Status** for completed, partial, and missing proof
   groups.
4. **Contributing:** open **Workflow**, then use the relevant chapter guide and
   focused interface test.

The **Reusable CLRS proof patterns** page collects the small cross-chapter APIs
for boundary shifts, exchange certificates, fibers, and interval geometry.

## Current Milestones

The strongest completed boundaries on the current main branch are:

* Chapter 2 sorting correctness and selected cost/recurrence results.
* Chapter 6 heap, heapify, build-heap, heapsort, and priority-queue correctness
  for the represented array and functional models.
* Chapter 8 correctness for the represented counting-sort, radix-sort, and
  bucket-sort models.
* Chapter 16 activity-selection and Huffman optimality for the represented
  finite models.
* Chapter 22 main functional correctness, formally sealed for BFS shortest
  paths and predecessor trees, DFS theory and edge classification, Kahn and DFS
  topological sorting, and Kosaraju SCC decomposition.

Several other chapters contain substantial theorem stacks while remaining
honestly partial.  In particular, Chapters 3 and 4 contain the asymptotic and
Master-theorem infrastructure; Chapters 7, 9, and 11 expose the remaining
probability-model gap; Chapters 12-15 cover functional tree and dynamic-
programming interfaces; Chapters 17-20 cover advanced data structures at
mathematical or size-level specifications; Chapter 21 supplies disjoint-set
semantics, executable union-find correctness, and its Kruskal bridge; and
Chapter 23 contains the current MST cut/exchange/Kruskal layer.

Use the generated dashboard for counts.  Use chapter pages and the proof map
for exact theorem boundaries.

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
{lit}`docs/clrs-proof-progress.csv`.  The public **Progress Dashboard** is
generated from it.  The longer maintainer theorem ledger is
{lit}`docs/proof-map.md`.

## Library Shape

* {lit}`CLRSLean.lean`: library root and landing page.
* {lit}`CLRSLean/ProofPatterns.lean`: reusable pattern aggregator.
* {lit}`CLRSLean/Chapter_XX.lean`: chapter guide and section aggregator.
* {lit}`CLRSLean/Chapter_XX/Section_XX_Y_Name.lean`: formal section content.
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
