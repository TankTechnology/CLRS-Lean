# Chapter 2 Insertion-Sort Line-Cost Design

## Goal

Formalize the CLRS Section 2.2 insertion-sort cost table: independent costs
`c₁`, `c₂`, `c₄`, `c₅`, `c₆`, `c₇`, and `c₈`; the execution count of each
pseudocode line; and the exact textbook sum for `T(n)`.  Specializing the loop
test counts must recover the best- and worst-case tables.

## Representation

The formalization uses three small modules below Section 2.2:

- `LineCost/Definitions.lean` defines the line-cost record, execution-count
  record, loop trace, and the functions that aggregate one trace;
- `LineCost/Formula.lean` proves that evaluating the two records expands to the
  textbook `cᵢ × execution-count` sum;
- `LineCost/BestWorst.lean` instantiates the trace with `tᵢ = 1` and `tᵢ = i`
  and proves the resulting count tables and running-time formulas;
- `LineCost.lean` is the stable facade imported by the Section 2.2 reader page.

The outer iterations are indexed by `k ∈ range (n - 1)`, corresponding to the
textbook index `i = k + 2`.  A trace is therefore a function `Nat → Nat`, read
at `k + 2`.  This avoids fragile interval-bound arithmetic while retaining the
exact `Σ(i = 2..n)` meaning.

## Public contract

The public surface exposes:

- `InsertionSortLineCosts` with fields `c₁`, `c₂`, `c₄`, `c₅`, `c₆`, `c₇`,
  and `c₈`;
- `InsertionSortLineCounts` with one field for every charged pseudocode line;
- `insertionSortLineCounts`, which derives the complete execution table from
  `n` and the loop-test trace `t`;
- `insertionSortRunningTime`, which evaluates costs against that table;
- `insertionSortRunningTime_eq_textbook_sum`, the exact full `T(n)` formula;
- `insertionSortLineCounts_best_case` and
  `insertionSortLineCounts_worst_case`, the two textbook substitutions;
- `insertionSortRunningTime_best_case` and
  `insertionSortRunningTime_worst_case`, the corresponding complete formulas.

The existing triangular comparison model remains available and is shared by
the worst-case count table instead of duplicated.

## Boundary

This is a symbolic unit-cost analysis of the seven executable pseudocode
lines, exactly matching the level of CLRS Section 2.2.  It is not a machine
semantics for array storage, integer word size, cache behavior, or allocation.
Those stronger implementation models are not implied by the theorem names.

## Verification

The focused interface test must first fail on the absent declarations.  The
three implementation modules, both Chapter 2 roots, the Chapter 2 trust gate,
repository consistency checker, and whitespace check must pass before the
milestone is integrated.
