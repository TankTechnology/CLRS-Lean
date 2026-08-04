# Chapter 27 Main-Text Completion Design

## Goal

Complete the main-text algorithm and theorem boundary of CLRS third-edition
Chapter 27, *Multithreaded Algorithms*, and seal that boundary as
`main-proof-complete` in CLRS-Lean.

The completed chapter must contain:

- the dynamic-multithreading work/span model;
- a total executable greedy scheduler for finite computation DAGs and the
  Graham-Brent greedy-scheduling bound;
- balanced parallel loops with a complete logarithmic-depth bound;
- executable parallel matrix addition and multiplication, with functional
  correctness and execution-attached work/span theorems;
- executable CLRS P-MERGE, including binary-search partitioning, sortedness,
  element preservation, the three-quarter subproblem bound, and work/span
  analysis; and
- executable P-MERGE-SORT, with sortedness, element preservation, and
  execution-attached work/span analysis.

The scope deliberately excludes chapter-end exercises, mutable-array and RAM
semantics, allocator costs, cache behavior, and hardware scheduling.  Existing
parallel-Strassen recurrence results remain available as a useful extension,
but they are not presented as a nonexistent Section 27.4 and are not part of
the main-text closure condition.

## Textbook-Boundary Correction

The current Chapter 27 recurrence file needs two truth corrections before the
chapter can be sealed.

First, its P-MERGE recurrence divides the total input into floor and ceiling
halves.  The CLRS algorithm instead takes a middle element from the longer
input, finds its rank in the other input by binary search, and recursively
merges the two induced pairs in parallel.  The two child sizes add to one less
than the parent size, and either child is bounded by the ceiling of three
quarters of the parent size.  The balanced recurrence can remain as a stable
comparison scale, but it cannot be described as the exact execution cost of
CLRS P-MERGE.

Second, the current P-MATMUL span recurrence charges only a constant combine
step.  The main-text algorithm recursively computes matrix addition with
span `Theta(log n)`, so parallel matrix multiplication has
`M_inf(n) = M_inf(n / 2) + Theta(log n) = Theta(log^2 n)`.  The existing
logarithmic recurrence can remain as an explicitly named idealized recurrence,
but the chapter headline must use the executable P-ADD/P-MATMUL cost.

These corrections preserve existing public declarations for compatibility.
They change their descriptions and add execution-connected theorem families
instead of deleting or silently weakening old results.

## Design Principles

- Formalize the actual main-text control structure, not an easier adjacent
  algorithm with the same asymptotic class.
- Use pure executable refinements over lists and finite block matrices.  The
  refinement must expose the binary-search split, parallel recursive branches,
  matrix-addition stage, and scheduler-ready-set invariant.
- Attach work and span to executions.  A recurrence that has no theorem
  connecting it to an algorithm is supporting analysis, not completion.
- Preserve elements and structural meaning explicitly: merge and merge sort
  prove `List.Perm`; matrix algorithms prove equality with mathematical matrix
  operations; schedules prove completion of the original DAG work.
- Keep every source file focused and reviewable.  Aggregator files own imports
  and reader guidance, while definitions, correctness, and cost proofs live in
  separate submodules.
- Preserve all current public theorem names unless a name is demonstrably
  false.  New headline theorems make the corrected main-text boundary clear.
- Do not commit `sorry`, `admit`, project axioms, or theorem statements whose
  hypotheses hide the algorithm's central invariant.

## Module Layout

The two existing Chapter 27 section files become small aggregators.  Existing
declarations move without namespace changes, so importing `CLRSLean.Chapter_27`
continues to expose the old API.

```text
CLRSLean/Chapter_27/
  Section_27_1_Multithreading_Model.lean
  Section_27_1_Multithreading_Model/
    S1_ComputationDAG.lean
    S2_ReadyExecution.lean
    S3_GreedyAccounting.lean
    S4_ExecutableScheduler.lean
    S5_SpawnTreeAndLoops.lean

  Section_27_2_4_Algorithms.lean
  Section_27_2_4_Algorithms/
    S1_CostModel.lean
    S2_Recurrences.lean
    S3_AllInputBounds.lean
    ParallelMatrix/
      Definitions.lean
      Correctness.lean
      Costs.lean
    ParallelMerge/
      Definitions.lean
      Correctness.lean
      Costs.lean
    ParallelMergeSort/
      Definitions.lean
      Correctness.lean
      Costs.lean
    ParallelStrassen/
      Recurrences.lean
```

The historical `Section_27_2_4_Algorithms` module name remains for import
compatibility even though Chapter 27's main text ends at Section 27.3.  Its
reader-facing title and prose distinguish Sections 27.2-27.3 from the retained
parallel-Strassen extension.

Aggregator files contain imports and module documentation only.  New proof
files should normally remain below roughly 400 lines.  A file that approaches
that size is split by definition, semantic correctness, or cost responsibility
rather than by arbitrary line ranges.

## Shared Execution-Cost Model

`S1_CostModel.lean` defines the small public execution wrapper:

```lean
structure Costed (alpha : Type) where
  value : alpha
  work : Nat
  span : Nat
```

The module also defines explicit zero-cost mapping, sequential composition,
and parallel composition.  Parallel composition adds the child work and the
stated spawn/sync overhead while taking the maximum child span.  Algorithms
charge nonrecursive work explicitly; list primitives and block operations do
not acquire hidden costs merely because Lean evaluates them.

Every algorithm exposes equations for `value`, `work`, and `span`.  Correctness
theorems talk about `value`; runtime theorems talk about the exact attached
fields.  This makes erasure immediate while preventing a proof about an
unrelated recurrence from being labeled algorithm runtime.

The cost model is mathematical rather than a RAM model.  Its primitive charges
are documented beside each algorithm: comparisons and output placements for
merge, scalar additions/multiplications and spawn/sync nodes for matrices, and
one unit of strand work per scheduler transition.

## Section 27.1: Executable Scheduling

### Existing foundation

The existing computation DAG already has forward edges, total work, an honest
longest weighted path, residual work/span, computed ready sets, one-unit
execution, maximally busy step certificates, completed schedule certificates,
and conditional greedy-schedule bounds.

### New executable constructor

`S4_ExecutableScheduler.lean` defines a deterministic run selector that takes
the first `min processors ready.card` ready vertices in vertex order.  For a
positive processor count it constructs a `DAGSchedule` recursively, using
remaining work as the termination measure.

The proof stack establishes:

- positive residual work implies a nonempty ready set;
- a positive-processor greedy step selects at least one ready vertex;
- executing the selected run strictly decreases residual work;
- recursion therefore reaches a zero-work state; and
- the resulting schedule satisfies the existing complete/incomplete-step
  accounting interface.

The public surface contains an executable constructor and a direct theorem
whose only scheduling premise is processor positivity.  Callers no longer
have to supply a completed schedule certificate before using the greedy bound.

### Parallel-loop closure

The spawn-tree module retains exact loop work and span.  It adds the missing
all-input upper bound

```lean
parallelLoopDepth n <= Nat.log 2 n + 1
```

and a direct logarithmic-span wrapper for `parallelLoopTree`.  An exact
`Nat.clog` characterization is outside the acceptance boundary; it may be
added only if it is a short corollary of the required proof.

## Section 27.2: Parallel Matrix Algorithms

### Representation

The implementation reuses `CLRS.Chapter04.SqMat`, whose depth `k` represents a
`2^k` square as recursively nested `2 x 2` blocks.  This representation makes
the CLRS partition operation definitional while preserving equality with
ordinary matrix addition and multiplication through its ring instance.

### Parallel matrix addition

The executable P-ADD recursively adds the four block pairs in parallel.  It
proves equality with ordinary addition and exact work/span equations at size
`2^k`.  Its main cost theorems are work `Theta(n^2)` and span `Theta(log n)` in
the chapter's discrete comparison scales.

### Parallel matrix multiplication

The executable P-MATMUL uses eight parallel recursive products, stores the
second four products in a functional temporary block matrix, and invokes
P-ADD to combine the two product matrices.  This mirrors the race-free
main-text algorithm.

Correctness proves that the returned block matrix equals ordinary matrix
multiplication over an arbitrary ring.  Cost theorems connect the exact
execution equations to work `Theta(n^3)` and span `Theta(log^2 n)` on
power-of-two matrices, with an all-input comparison wrapper obtained through
the established adjacent-power transfer layer.

The old `pMatMulSpan` declaration remains available but is documented as the
idealized constant-combine recurrence.  It is not cited as the runtime of the
new executable main-text P-MATMUL.

## Section 27.3: Parallel Merge

### Binary-search partition

`ParallelMerge/Definitions.lean` defines an executable lower-bound binary
search over an indexed functional list segment.  On a sorted input it returns
an index that partitions the list into values below the pivot and values at
least the pivot.  It exposes correctness, range, strict-interval-decrease, and
logarithmic-comparison theorems.

### P-MERGE execution

P-MERGE first places the longer list in the primary position.  For a nontrivial
input it chooses the primary midpoint, obtains the pivot rank in the secondary
list by binary search, recursively merges the lower partitions and upper
partitions in parallel, and assembles

```text
lower result ++ [pivot] ++ upper result
```

The recursion measure is the sum of input lengths.  Both recursive calls have
strictly smaller total size.

### Correctness and structure

The main bundled correctness theorem assumes sorted inputs and proves:

- the output is sorted;
- the output is a permutation of `xs ++ ys`; and
- the output length is `xs.length + ys.length`.

Direct sortedness, permutation, and length wrappers remain public for routine
downstream use.  Supporting lemmas prove the lower-result/pivot and
pivot/upper-result boundaries rather than making sortedness true by choosing a
pre-sorted specification function.

The cost layer proves that the child sizes add to one less than the parent and
that each child is at most `n - n / 4`, the natural-number form of the CLRS
three-quarter bound.

### Work and span

Each execution charges binary-search comparisons, pivot placement, output
copying in base cases, and spawn/sync overhead.  For all sorted inputs of total
size `n`, the proof gives linear lower and upper work bounds and a
`O(log^2 n)` span upper bound.  An explicit family of interleaved sorted inputs
provides the matching worst-case span lower bound.  Together these results
state the main-text worst-case work `Theta(n)` and span `Theta(log^2 n)` without
pretending the child sizes are always equal.

The old balanced `pMergeWork` and `pMergeSpan` functions remain compatibility
comparison scales.  Documentation and theorem names do not call them exact
P-MERGE execution costs.

## Section 27.3: Parallel Merge Sort

P-MERGE-SORT recursively splits the input with `take` and `drop`, sorts the two
parts in parallel, and invokes executable P-MERGE.  Termination uses input
length, including explicit empty and singleton cases.

The bundled correctness theorem proves sortedness, permutation preservation,
and length preservation.  The cost proof composes the exact recursive-sort and
P-MERGE execution fields.  It establishes worst-case work
`Theta(n log n)` and span `Theta(log^3 n)`, with pointwise upper bounds for all
inputs and a concrete worst-case family for the lower span direction.

The existing balanced merge-sort recurrences remain useful comparison scales.
The new theorems state precisely how execution is bounded by those scales or
by corrected three-quarter envelopes; they do not claim false definitional
equalities.

## Parallel-Strassen Extension

Chapter 4 already proves recursive Strassen correctness.  Chapter 27 keeps its
current natural-valued parallel-Strassen work/span recurrence theorems and
all-input asymptotic wrappers.  They move into a small extension module and
remain import-compatible.

The chapter guide labels this material as an extension associated with the
matrix-algorithm exercises, not as Section 27.4.  A new execution bridge is not
required for main-text closure.  No existing theorem is removed or downgraded.

## Test Design

Tests follow existing sealed-chapter conventions rather than introducing a
new hierarchy:

```text
Tests/Chapter_27_Interface.lean
Tests/Chapter_27_Scheduler_Interface.lean
Tests/Chapter_27_ParallelMerge_Interface.lean
Tests/Chapter_27_Matrix_Interface.lean
Tests/Chapter_27_Closure.lean
```

`Chapter_27_Interface.lean` retains legacy API checks, recurrence closed forms,
and a small number of compatibility examples.  The three focused interface
files check the new executable surfaces and instantiate representative
theorems.  Concrete examples cover zero-work DAGs, chains, forks, several
processor counts, empty merge inputs, one-element and odd-length inputs,
duplicates, interleaved lists, scalar matrices, and one recursive matrix
level.

`Chapter_27_Closure.lean` imports only `CLRSLean.Chapter_27`, checks the
headline theorem from each main-text obligation, and prints their axioms.  A
separate axioms test is unnecessary because the repository's mature closure
files combine headline interface and axiom inspection.

Every public theorem family starts with a RED interface edit.  The focused
test must fail because the requested declaration is absent, not because of a
parse, namespace, or import error.  The corresponding production declaration
is then implemented and the same test rerun to GREEN before the next family is
started.

## Documentation and Status Closure

Completion updates all live status owners:

- `CLRSLean/Chapter_27.lean` describes Sections 27.1-27.3 and the separate
  Strassen extension accurately;
- `CLRSLean/Status.lean` moves Chapter 27 out of the partial section;
- `docs/proof-map.md` records the executable theorem surface and exact cost
  boundary;
- `docs/clrs-proof-progress.csv` changes the status to
  `main-proof-complete`, removes the missing core group, and receives the new
  theorem-group counts;
- `CLRSLean/Progress.lean` and the README table are regenerated from the CSV;
- `docs/proof-status-board.md` removes Chapter 27 from the active proof queue;
- `docs/index.md` and `literate.toml` register every new source module; and
- `docs/proof-audits/chapter-27-closure-2026-08-04.md` records the sealed
  theorem boundary and verification commands.

The Chapter 27 skill iteration log receives one reusable lesson: large chapter
sections should become aggregator pages over small definition, correctness,
and execution-cost modules, and an asymptotic recurrence is not an algorithm
runtime until an execution-refinement theorem connects them.

## Verification Boundary

Development uses the narrowest relevant command after every file:

```text
lake build +CLRSLean.Chapter_27.<focused-module>
lake env lean Tests/Chapter_27_<focused-test>.lean
```

The final closure gate requires:

```text
lake env lean Tests/Chapter_27_Interface.lean
lake env lean Tests/Chapter_27_Scheduler_Interface.lean
lake env lean Tests/Chapter_27_ParallelMerge_Interface.lean
lake env lean Tests/Chapter_27_Matrix_Interface.lean
lake env lean Tests/Chapter_27_Closure.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_27 -g '*.lean'
uv run python scripts/check_repository.py
git diff --check
lake build CLRSLean
lake build :literateHtml
```

The closure test's `#print axioms` output is inspected for every headline
theorem.  Only the repository-accepted standard logical dependencies such as
`propext`, `Classical.choice`, and `Quot.sound` may appear; `sorryAx` and
project axioms are forbidden.

## Rejected Alternatives

Keeping the balanced P-MERGE recurrence as the implementation would prove the
wrong algorithm.  Replacing P-MERGE with `List.mergeSort` would prove a sorting
specification while bypassing the median/binary-search partition and the
three-quarter invariant.  Treating matrix block addition as a constant-span
primitive would preserve the old logarithmic P-MATMUL recurrence but omit the
main-text P-ADD computation.  A general work/span monad or parallel-language
semantics would broaden the project without being needed for the Chapter 27
theorems.  Mutable arrays and RAM semantics would likewise add a lower-level
refinement that the agreed completion boundary does not require.

## Acceptance Criteria

Chapter 27 is complete only when all of the following hold:

1. a deterministic positive-processor greedy scheduler is executable for every
   finite `CompDAG`, terminates at zero residual work, and satisfies the direct
   Graham-Brent bound;
2. parallel-loop depth has the missing all-input logarithmic upper bound;
3. executable P-ADD and race-free temporary-matrix P-MATMUL compute ordinary
   matrix addition and multiplication and have execution-connected
   `Theta(n^2)`/`Theta(log n)` and `Theta(n^3)`/`Theta(log^2 n)` work/span
   theorems;
4. executable P-MERGE performs the CLRS midpoint/binary-search partition,
   preserves sortedness and elements, proves the three-quarter child bound,
   and has execution-connected worst-case `Theta(n)` work and
   `Theta(log^2 n)` span;
5. executable P-MERGE-SORT preserves sortedness and elements and has
   execution-connected worst-case `Theta(n log n)` work and
   `Theta(log^3 n)` span;
6. legacy recurrence and parallel-Strassen declarations continue to compile
   but are described with their honest compatibility/extension status;
7. the new small-module structure is registered in imports, site navigation,
   tests, and status documents, with no new oversized section file;
8. all focused, closure, repository, root-library, and literate-site checks
   pass without unfinished proofs or nonstandard axioms; and
9. the generated dashboard and reader-facing pages consistently label Chapter
   27 `main-proof-complete` for the agreed pure functional main-text model.
