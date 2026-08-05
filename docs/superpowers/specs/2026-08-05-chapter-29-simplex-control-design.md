# Chapter 29 Executable SIMPLEX Design

Date: 2026-08-05

## Goal

Complete the main theorem stack of CLRS Section 29.3 above the already proved
dictionary and PIVOT layer.  The implementation must expose the textbook
three-way step (optimal, unbounded, or pivot), use Bland's smallest-variable
tie breaking, preserve the represented LP and basic feasibility, and terminate
after finitely many distinct bases.

This milestone does not initialize an infeasible initial dictionary.  Section
29.5 will construct the first basic-feasible dictionary before invoking this
SIMPLEX core.

## Canonical Variable Order

`LPVar m n = Fin n ⊕ Fin m` already records original and slack identities.
Define a canonical zero-based index

```text
original j ↦ j
slack i    ↦ n + i.
```

Prove this map injective.  Bland comparisons use variable identities through
this index, never the mutable row or column slot number.

## Bland Selectors

An entering candidate is a nonbasic slot with positive reduced cost.  The
Bland entering predicate requires both positivity and the least variable index
among all positive-reduced-cost nonbasic variables.

A leaving candidate must satisfy the existing `IsMinimumRatio` predicate.  The
Bland leaving predicate additionally chooses the least basic-variable index
among all rows attaining the minimum ratio.

Finite candidate sets provide deterministic selectors:

```lean
blandEntering? : Dictionary m n → Option (Fin n)
blandLeaving?  : Dictionary m n → Fin n → Option (Fin m)
```

The public specification proves:

- entering returns `none` exactly when every reduced cost is nonpositive;
- a returned entering slot satisfies the Bland predicate;
- leaving returns `none` exactly when no row has a positive coefficient in the
  entering column;
- a returned leaving row satisfies the minimum-ratio and Bland tie-break
  predicates.

The implementation may be `noncomputable` because comparisons over `ℝ` are
classical in this project; its result is nevertheless a fully specified finite
algorithm.

## One SIMPLEX Step

Define a dependent result indexed by its input dictionary:

```lean
inductive SimplexStepResult (D : Dictionary m n)
| optimal   (allReducedCostsNonpositive : ∀ j, D.c j ≤ 0)
| unbounded (entering : Fin n)
    (enteringImproves : 0 < D.c entering)
    (columnNonpositive : ∀ i, D.a i entering ≤ 0)
| pivot     (entering : Fin n) (leaving : Fin m)
    (enteringIsBland : D.IsBlandEntering entering)
    (leavingIsBland : D.IsBlandLeaving entering leaving)
```

`simplexStep` first calls `blandEntering?`, then `blandLeaving?`.  The pivoted
dictionary is reconstructed from the certificates already stored in the
result, so no unrelated state can be returned.

## Exit Semantics

Define dictionary-level specifications:

- `IsOptimalAssignment D x`: `x` is nonnegative, satisfies `D`, and dominates
  every other nonnegative satisfying assignment;
- `IsUnbounded D`: for every real bound there is a nonnegative satisfying
  assignment with larger objective value.

For the optimal branch, every term `c_j x_j` is nonpositive, while the basic
assignment has objective `v`.  This proves the basic assignment optimal.

For the unbounded branch, define the textbook ray at parameter `t ≥ 0`:

```text
x_e       = t
x_j       = 0                        for other nonbasic variables
x_basic i = b_i - a_i,e t.
```

Basic feasibility and a nonpositive entering column make the ray
nonnegative.  Its objective is `v + c_e t`, so positive `c_e` makes the
represented problem unbounded.

## Problem Equivalence

Define `Dictionary.Equivalent D E` to state:

1. `D` and `E` have exactly the same satisfying assignments;
2. their objective expressions agree on those assignments.

Prove reflexivity, symmetry, transitivity, and `pivot_equivalent`.  This is the
loop invariant connecting every terminal dictionary back to the input.

The basic assignment is unique among satisfying assignments whose nonbasic
variables are zero.  Consequently, equivalent dictionaries with the same
basic-variable set have the same basic assignment and the same constant
objective value.  These facts are the semantic core of the cycling argument.

## Runs

Define a fuelled internal runner with explicit outcomes:

```text
optimal terminal
unbounded terminal entering
exhausted terminal
```

Every recursive pivot consumes one unit of fuel.  Prove independently of the
termination bound that:

- all visited dictionaries are equivalent to the input;
- basic feasibility is preserved;
- an optimal result gives an input-problem optimal assignment;
- an unbounded result proves the input problem unbounded.

The public `simplex` uses the finite basis bound after Bland no-cycling has
been proved; its public result omits the impossible exhausted case.

## Bland No-Cycling

Follow the textbook fickle-variable proof rather than assuming a generic
termination certificate.

For a hypothetical repeated-basis segment:

1. equivalent equal-basis endpoints have the same basic assignment and value;
2. objective monotonicity forces every pivot in the segment to be degenerate;
3. choose the greatest-index variable that changes basis status;
4. choose one step where it leaves and one where it enters;
5. compare the two equivalent objective expressions on the assignment that
   varies only the first step's entering variable;
6. obtain a smaller-index basic row with a positive entering coefficient and
   zero ratio;
7. contradict Bland's leaving tie break.

Separate files cover trace combinatorics, objective-coefficient algebra, and
the final contradiction.  No file should exceed roughly 250 lines without a
further theorem-role split.

Since a basis contains `m` variables chosen from the finite `m+n` variable
universe, no repeated basis implies finite termination.  A simple cardinality
bound is sufficient; the public theorem need not normalize the bound to a
closed binomial formula until the correctness stack is stable.

## File Layout

```text
.../Simplex.lean
.../Simplex/VariableOrder.lean
.../Simplex/Entering.lean
.../Simplex/Leaving.lean
.../Simplex/Step.lean
.../Simplex/Optimality.lean
.../Simplex/Unboundedness.lean
.../Simplex/Equivalence.lean
.../Simplex/Run.lean
.../Simplex/Bland/Trace.lean
.../Simplex/Bland/Coefficients.lean
.../Simplex/Bland/NoCycle.lean
.../Simplex/Termination.lean
```

The Section 29.3 reader imports the `Simplex` aggregator; the chapter guide
continues to import every hidden module in literate depth-first order.

## Acceptance

`Tests/Chapter_29_Simplex_Interface.lean` checks the selectors, all step
branches, optimality, unboundedness, run correctness, Bland no-cycling, and
finite termination.  Main results receive `#print axioms` checks.  The focused
gate is Chapter 29 only, both Chapter 29 interfaces, the Section 29.3 literate
target, repository checks, marker scan, and `git diff --check`.

