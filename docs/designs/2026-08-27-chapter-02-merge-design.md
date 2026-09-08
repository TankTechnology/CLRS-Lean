# Chapter 2 Explicit MERGE Design

## Goal

Formalize the CLRS Section 2.3 `MERGE` procedure as an executable Lean
function and prove that one costed execution returns a sorted permutation of
its two sorted inputs with a linear comparison bound and exactly one output
write per input element.

## Approaches considered

1. Define an explicit two-list recursive merge whose result record contains
   the output list, number of head comparisons, and number of output writes.
   This is the chosen approach because the executable value and the cost
   theorems share one source of truth.
2. Re-export `List.merge` and attach an independent recurrence counter. This
   would be short, but it would retain the current audit objection that the
   central MERGE procedure is delegated rather than formalized locally.
3. Model the three textbook while-loops over temporary arrays. This is closest
   to the pseudocode, but it introduces mutation, bounds checks, and allocation
   accounting that the project explicitly excludes from the current scope.

## Architecture

The proof is split below the existing Section 2.3 guide:

- `Merge/Definitions.lean` defines `MergeExecution`, `mergeWithCost`, and the
  value-only `merge` projection.
- `Merge/Correctness.lean` proves erasure, length, permutation, and sortedness.
- `Merge/Cost.lean` proves that head comparisons are at most the sum of the two
  input lengths, proves that output writes equal that sum, and packages the
  full public contract.
- `Merge.lean` is the stable facade imported by the Section 2.3 guide.

The recursive step compares the two current heads, emits the smaller one, and
recurses after removing exactly one input element. Empty-input branches append
the remaining list without further element comparisons. Termination and the
linear bound therefore use the same decreasing measure
`left.length + right.length`.

## Public contract

The public interface will expose:

- `mergeWithCost_value`: the value projection agrees with `merge`;
- `merge_perm`: the output is a permutation of `left ++ right`;
- `merge_sorted`: sorted inputs produce a sorted output;
- `merge_comparisons_le`: the execution performs at most
  `left.length + right.length` head comparisons;
- `merge_outputWrites_eq`: the execution writes exactly
  `left.length + right.length` output elements;
- `merge_correct`: a bundled theorem containing sortedness, permutation, and
  both cost facts.

An executable example and all six theorem names are pinned before production
implementation in a focused Chapter 2 interface test. The headline bundled
theorem is also registered in the Chapter 2 native axiom audit.

## Boundary

This milestone closes the mathematical and list-level linear-work content of
MERGE.
It does not claim allocation costs for temporary arrays or a word-RAM
instruction count. The next milestone will add the Section 2.2 pseudocode-line
cost model and relate it to the existing comparison counter.

## Verification

The focused module, Chapter 2 interface tests, Chapter 2 trust gate, Chapter 2
root build, repository consistency checker, unfinished-proof scan, and
`git diff --check` must all pass before the milestone is committed.
