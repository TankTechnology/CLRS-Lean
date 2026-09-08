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

Machine-checked algorithms, chapter by chapter.

CLRS-Lean formalizes the selected mathematical core of *Introduction to
Algorithms*, fourth edition, in Lean 4. Explore executable definitions,
correctness proofs, invariants, and cost bounds alongside the chapters of CLRS.

## Start Here

* **Read the book:** [Chapters 1–35](CLRSLean/FourthEdition/) groups the chapter
  guides by topic. Start with [Getting Started](CLRSLean/FourthEdition/Chapter_02/)
  to follow insertion sort from an executable algorithm to its correctness proof.
* **Explore the proofs:** [Progress Dashboard](CLRSLean/Progress/) lists chapter
  coverage; [Proof Status](CLRSLean/Status/) explains what completion means and
  how the proofs are checked.
* **Contribute:** [Contributor Guide](CLRSLean/Workflow/) explains how to build,
  extend, and verify the library.

## Whole-Book Snapshot

The reviewed inventory spans 35 fourth-edition chapters: 34 chapters are
{lit}`main-proof-complete` for their advertised Lean models, and Chapter 1 is an
{lit}`expository` guide. All 1,689 selected theorem entries are proved, with
zero edition-coverage gap units in the current ledger. A separate
[Online Material](CLRSLean/OnlineMaterial/) catalog retains 470 supplementary
entries, including Fibonacci heaps, van Emde Boas trees, and computational
geometry.

The Lean-native trust gate checks a flagship declaration for every chapter and
allows only the standard {lit}`propext`, {lit}`Classical.choice`, and
{lit}`Quot.sound` axioms. Completion refers to this reviewed theorem inventory
and its explicit models. It does not include every exercise, chapter-end
problem, or low-level implementation refinement.

The September 8 source audit and its chapter-by-chapter repair record are kept
separately in {lit}`docs/audits/2026-09-08-chapter-review/` and
{lit}`docs/plans/2026-09-08-chapter-repairs/`. The original audit describes its
base commit; the repair record links later execution refinements, regressions,
and clarified cost models. It does not establish an independent page-by-page
verification against the textbook.

## Explore by Topic

* [Sorting](CLRSLean/FourthEdition/Chapter_02/): sortedness, permutation
  preservation, and algorithm cost.
* [Greedy algorithms](CLRSLean/FourthEdition/Chapter_15/): activity selection,
  exchange arguments, and Huffman coding.
* [Graph algorithms](CLRSLean/FourthEdition/Chapter_20/): traversal,
  shortest paths, spanning trees, and flows.
* [Parallel algorithms](CLRSLean/FourthEdition/Chapter_26/): correctness,
  work, span, and scheduling.
* [NP-completeness](CLRSLean/FourthEdition/Chapter_34/): Cook–Levin and the
  selected reduction chain, with serialized languages and machine bounds.

Each chapter guide states its scope and links to section proofs. Section pages
expose the definitions and theorem statements; implementation details remain
available from those pages and site search.

## Beyond the Chapters

[Proof Patterns](CLRSLean/ProofPatterns/) and the
[Finite Probability Toolkit](CLRSLean/Probability/) collect reusable proof APIs.
[Research Extensions](CLRSLean/Extensions/) contains developments beyond the
book's selected theorem inventory.

The [repository](https://github.com/TankTechnology/CLRS-Lean) contains the Lean
sources, interface tests, and machine-readable coverage ledgers. See the
[scope statement](https://github.com/TankTechnology/CLRS-Lean/blob/main/docs/scope.md)
for the project-wide boundary and the
[documentation index](https://github.com/TankTechnology/CLRS-Lean/blob/main/docs/index.md)
for maintainer references.

## Using the Library

New code imports {lit}`CLRSLean.FourthEdition.Chapter_NN`. Existing
{lit}`CLRSLean.Chapter_NN` imports retain their third-edition meanings through
all {lit}`1.x` releases and for at least six months after the facade release.
The [migration guide](https://github.com/TankTechnology/CLRS-Lean/blob/main/docs/migrations/clrs4.md)
explains chapter numbering and declaration namespaces.
-/
