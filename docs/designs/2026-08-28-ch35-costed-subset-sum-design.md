# Chapter 35 Costed APPROX-SUBSET-SUM Design

## Status and decision

Approved direction: route A, an execution-derived unit-cost proof for CLRS
Theorem 35.8.  The existing semantic development remains the source of truth
for subset sums, trimming, and approximation quality.  The new layer executes
the same stages and records the work actually performed by each recursive
scan; it does not define work from the desired closed-form upper bound.

## Problem being closed

`approxSubsetSum_approx_lt` proves the approximation guarantee and
`approxLists_length_bound` proves the mathematical list-size argument.  The
current theorem `approxSubsetSum_fptas` instantiates that list-size argument,
but it does not count an execution of MERGE-LISTS, TRIM, the outer loop, or the
final maximum scan.  Consequently it is evidence needed by a runtime proof,
not by itself a runtime theorem.

The closure must provide all of the following:

1. costed executions of map-add, MERGE-LISTS, TRIM, threshold filtering, and
   maximum selection;
2. erasure theorems identifying their values with the existing operations;
3. linear local work bounds derived by recursion;
4. one costed outer APPROX-SUBSET-SUM execution whose value erases to
   `approxSum`;
5. a uniform bound for every intermediate trimmed list under the single trim
   parameter chosen from the original input length;
6. a total polynomial work theorem; and
7. a public theorem bundling validity, target feasibility, approximation
   quality, and execution-derived work.

## Cost model

The counter uses the textbook unit-cost model:

- one unit for each mapped addition;
- one unit for each head comparison made by MERGE-LISTS;
- one unit for each multiplicative threshold comparison made by TRIM;
- one unit for each comparison with the target during filtering;
- one unit for each comparison during the final maximum scan; and
- one unit of outer-loop control per processed input element.

List construction and pattern matching are covered by those scan charges.
Natural-number and exact-real arithmetic operations are unit operations in this
model.  The result is therefore a CLRS-level operation count, not a bit-cost,
floating-point, allocation, or cache theorem.  This boundary will be stated in
the Chapter 35 guide and progress ledger.

## Architecture and file boundaries

The existing 1,000-line section file is not enlarged.  The new development is
split behind a stable facade:

- `.../Section_35_5_The_Subset_Sum_Problem/Costed/Definitions.lean`
  defines small execution records and the five local recursive scans.
- `.../Costed/LocalCorrectness.lean` proves erasure, exact elementary costs,
  and linear bounds for the scans.
- `.../Costed/Execution.lean` defines the costed outer list construction and
  the final maximum-producing wrapper, then proves value erasure.
- `.../Costed/Bounds.lean` proves the uniform intermediate-list bound, the
  outer recurrence bound, the final polynomial bound, and the FPTAS bundle.
- `.../Section_35_5_The_Subset_Sum_Problem/Costed.lean` is the public facade.

The canonical Chapter 35 guide imports only the facade.  This avoids an import
cycle because every costed child imports the original section, while the
original section does not import its child facade.

## Execution data flow

For one outer iteration with previous list `L`, the execution performs exactly
this pipeline:

```text
mapAddWithCost x L
  -> mergeWithCost L shifted
  -> trimWithCost delta merged
  -> filterAtMostWithCost t trimmed
```

The recursive outer execution adds the work of the previous call, these four
stage counters, and one control unit.  The top-level wrapper then runs a
recursive maximum scan over the final list.  Erasure is proved stage by stage,
so the final value is propositionally equal to the existing `approxSum`; no
parallel specification-only result is substituted for the execution.

## Main theorem interfaces

Names may receive implicit-argument adjustments required by elaboration, but
the public logical content is fixed as follows:

```lean
theorem mergeWithCost_value (L M : List Nat) :
  (mergeWithCost L M).value = merge L M

theorem mergeWithCost_work_le (L M : List Nat) :
  (mergeWithCost L M).work <= L.length + M.length

theorem trimWithCost_value (delta : Real) (L : List Nat) :
  (trimWithCost delta L).value = trim delta L

theorem trimWithCost_work_le (delta : Real) (L : List Nat) :
  (trimWithCost delta L).work <= L.length

theorem approxListsWithCost_value (delta : Real) (t : Nat) (xs : List Nat) :
  (approxListsWithCost delta t xs).value = approxLists delta t xs

theorem approxSubsetSumWithCost_value (xs : List Nat) (t : Nat) (epsilon : Real) :
  (approxSubsetSumWithCost xs t epsilon).value = approxSum xs t epsilon
```

Let `n = xs.length`.  The total-work theorem will use the edge-safe textbook
input-size expression `log t + 1`:

```lean
theorem approxSubsetSumWithCost_work_le
    (h_epsilon_pos : 0 < epsilon) (h_epsilon_one : epsilon <= 1)
    (h_target : 1 <= t) :
  ((approxSubsetSumWithCost xs t epsilon).work : Real) <=
    48 * ((xs.length : Real) + 1)^2 *
      (Real.log (t : Real) + 1) / epsilon
```

The `+1` terms make the statement valid for the empty input and `t = 1`
without pretending that a positive scan is bounded by zero.  For ordinary
positive instances this is the advertised
`O(n^2 * (1 + log t) / epsilon)` unit-operation bound and hence polynomial in
the encoded target length and `1/epsilon`.

The final public closure theorem is a conjunction (or an equivalent record):

```lean
theorem approxSubsetSumWithCost_fptas
    (h_epsilon_pos : 0 < epsilon) (h_epsilon_one : epsilon <= 1)
    (h_target : 1 <= t) :
  let run := approxSubsetSumWithCost xs t epsilon
  run.value ∈ subsetSums xs ∧
  run.value <= t ∧
  (optimalSum xs t : Real) <= (1 + epsilon) * (run.value : Real) ∧
  (run.work : Real) <=
    48 * ((xs.length : Real) + 1)^2 *
      (Real.log (t : Real) + 1) / epsilon
```

The existing `approxSubsetSum_fptas` declaration is retained for compatibility
and documented precisely as the instantiated trimmed-list bound.  The new
`approxSubsetSumWithCost_fptas` becomes the flagship Theorem 35.8 trust target.

## Proof strategy for the total bound

For a fixed original input length `n`, set
`delta = epsilon / (2*n)`.  The existing separated-list proof gives every
intermediate list, not merely the final one, a common real length bound

```text
B = 4*n*log(t)/epsilon + 2.
```

The local erasure and length lemmas give at most `7*|L| + 1` work for one
outer iteration.  Induction on the processed input therefore gives an outer
work bound of `n*(7*B + 1)`; the final maximum scan adds at most `B`.  Positivity
of epsilon, `epsilon <= 1`, `1 <= t`, and `n <= n+1` then yield the stated
constant-48 polynomial envelope.  The empty-input case is discharged directly
before using positivity of `delta`.

## Verification and acceptance

Development follows red-green proof engineering:

1. a focused `Tests/Chapter_35_Costed_SubsetSum_Interface.lean` first checks
   the intended names and must fail because they are absent;
2. each new source file elaborates independently before the next file is
   added;
3. small concrete executions test merge, trim, outer erasure, and counters;
4. `Tests/Trust/Chapter_35.lean` audits the value-erasure, work, and bundled
   FPTAS theorems with `#assert_axioms`;
5. the Chapter 35 facade, focused interface, global axiom audit, progress
   consistency, repository check, and whitespace check must all pass before
   the batch is committed or issue #341 is closed.

No theorem is accepted merely because the final list is short.  The public
runtime claim must refer to the counter produced by the costed execution.
