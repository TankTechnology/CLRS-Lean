# Chapter 28 Executable LUP Design

## Objective

Close the gap between `exists_lup_decomposition` and CLRS
`LUP-DECOMPOSITION` with a total recursive execution that returns either a
permutation and triangular factors or failure, plus a work counter produced by
that same execution.

The implementation must not obtain factors with `Classical.choose` from the
existing existence theorem.  The existence theorem remains proof
infrastructure; pivot search, row permutation, elimination, and recursion are
explicit data-producing functions.

## Scope and computational boundary

The executable interface is polymorphic over a field `F` with
`DecidableEq F`.  This is the exact-algebra boundary needed to decide whether a
candidate pivot is zero.  The algorithm chooses the first nonzero entry in the
current first column.  It does not claim numerically stable partial pivoting,
floating-point roundoff bounds, mutable-array storage, or RAM instruction
counts.

The cost model counts:

- each tested pivot candidate;
- each field division, multiplication, and subtraction performed by the
  pointwise elimination execution;
- the corresponding recursive child work.

Row reindexing and construction of the block views are structural and carry no
field-operation charge.  Every charged quantity is stored in the execution
record that also stores the computed value.

## Public data and functions

```lean
structure LUPFactors (n : Nat) (F : Type) where
  perm : Equiv.Perm (Fin n)
  lower : Matrix (Fin n) (Fin n) F
  upper : Matrix (Fin n) (Fin n) F

structure LUPExecution (n : Nat) (F : Type) where
  result : Option (LUPFactors n F)
  work : Nat

def findPivotWithCost ...
def eliminateWithCost ...
def lupDecomposeWithCost ... : LUPExecution n F
```

The top-level recursion is on the matrix dimension.

- Dimension zero succeeds with identity factors.
- At dimension `n + 1`, the pivot scan either fails or supplies a row whose
  first-column value is nonzero.
- The selected row is moved to row zero by direct row lookup.
- The elimination execution computes each entry of the matrix obtained by
  zeroing the first column below the pivot.
- The trailing `Fin n × Fin n` block is recursively decomposed.
- Successful child factors are assembled with `finOneSumFin`-style block
  reindexing into the parent factors.

## Proof surface

The closure is divided into the following contracts.

1. Pivot search:
   found rows are nonzero, failure means the entire first column is zero, and
   comparisons are bounded by the dimension.
2. Elimination:
   erasure agrees pointwise with `elimination B h * B`, the first column below
   the pivot is zero, and work is at most three times the number of entries.
3. Successful-result soundness:
   `lower` is unit lower triangular, `upper` is upper triangular, and
   `perm.permMatrix F * A = lower * upper`.
4. Nonsingular completeness:
   if `A.det ≠ 0`, `lupDecomposeWithCost A` returns factors.  Consequently,
   failure implies singularity.
5. Work:
   every execution, including a failing one, satisfies
   `work ≤ 4 * n^3` under the declared unit-cost model.
6. Solver refinement:
   costed forward and backward substitution erase to `lupSolve`, preserve its
   correctness theorem, and have execution-derived quadratic work.

The public bundle for a nonsingular input exposes factors, both triangular
invariants, the factorization equation, and the cubic work bound from one
execution.

## File layout

The existing large Section 28.1 file remains stable.  New proof obligations
are isolated behind:

```text
Section_28_1_Linear_Equations/
  ExecutableLUP/
    Basic.lean
    Pivot.lean
    Elimination.lean
    Execution.lean
    Correctness.lean
    Cost.lean
    SolveCost.lean
  ExecutableLUP.lean
```

Only the facade is imported by the canonical Chapter 28 guide.  Focused tests
import the canonical guide, so they detect a missing public import.

## Acceptance gate

- Each child file elaborates independently without new warnings.
- Concrete rational examples demonstrate success, failure, and factorization.
- The Chapter 28 focused interface and trust audit pass.
- The global native axiom audit and repository checks pass.
- The progress ledger distinguishes the former abstract cost formulas from
  the new execution-derived theorems.
