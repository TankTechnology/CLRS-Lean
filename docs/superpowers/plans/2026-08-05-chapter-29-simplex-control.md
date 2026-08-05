# Chapter 29 Executable SIMPLEX Implementation Plan

Date: 2026-08-05

Design: `docs/superpowers/specs/2026-08-05-chapter-29-simplex-control-design.md`

Use RED-GREEN commits throughout.  Run only focused Chapter 29 builds and
tests; do not run the full library build.

## 1. Canonical variable identities

- Add RED checks for `variableIndex`, injectivity, and dictionary basic/nonbasic
  key injectivity.
- Create `Simplex/VariableOrder.lean`.
- Define original-before-slack indexing and prove injectivity by cases and
  finite-index arithmetic.
- Add it to `Simplex.lean`, build the module, run the interface, and commit.

## 2. Bland entering selection

- Add RED checks for `IsBlandEntering`, `enteringCandidates`, and
  `blandEntering?` specifications.
- Create `Simplex/Entering.lean`.
- Select the minimum candidate under the lifted order induced by the canonical
  variable index.
- Prove returned-candidate positivity/minimality and the `none` characterization.
- Run focused checks and commit.

## 3. Bland leaving selection

- Add RED checks for `IsBlandLeaving`, existence of a minimum-ratio row, and
  `blandLeaving?` specifications.
- Create `Simplex/Leaving.lean`.
- Prove a finite nonempty set of positive-column rows contains a minimum ratio.
- Select the least variable identity among all minimum-ratio rows.
- Prove returned-row and `none` specifications, then commit.

## 4. Three-way step

- Add RED checks for `SimplexStepResult` and `simplexStep`.
- Create `Simplex/Step.lean`.
- Branch in textbook order: no entering candidate is optimal; an entering
  column without a positive row is unbounded; otherwise return a certified
  Bland pivot.
- Prove branch eliminators that expose the stored certificates and commit.

## 5. Optimal exit

- Add RED checks for `IsOptimalAssignment` and
  `basicAssignment_optimal_of_reducedCosts_nonpos`.
- Create `Simplex/Optimality.lean`.
- Prove every objective summand is nonpositive and the basic assignment has
  value `v`.
- Derive correctness of the `optimal` step branch, audit axioms, and commit.

## 6. Unbounded ray

- Add RED checks for `enteringRay`, its basic/nonbasic projections,
  satisfaction, nonnegativity, objective formula, and `IsUnbounded`.
- Create `Simplex/Unboundedness.lean`.
- Prove the ray formulas, choose an explicit real parameter beyond any bound,
  and derive correctness of the `unbounded` step branch.
- Audit axioms and commit.

## 7. Dictionary equivalence

- Add RED checks for `Equivalent`, equivalence laws, and `pivot_equivalent`.
- Create `Simplex/Equivalence.lean`.
- Add uniqueness of a satisfying assignment with all nonbasic values zero.
- Define the finite basic-variable set and prove equal-basis equivalent
  dictionaries have equal basic assignments and equal `v`.
- Build, audit, and commit.

## 8. Fuelled run correctness

- Add RED checks for run outcomes, the internal fuelled runner, semantic
  preservation, feasibility preservation, optimal correctness, and unbounded
  correctness.
- Create `Simplex/Run.lean`.
- Prove the invariants by induction on fuel and transitivity of equivalence.
- Keep exhaustion explicit; do not claim termination here.
- Audit and commit.

## 9. Bland trace combinatorics

- Create `Simplex/Bland/Trace.lean` with finite traces, adjacency by certified
  Bland pivots, bases, repeated-basis segments, and fickle variables.
- Prove extraction of a greatest fickle variable and steps where it leaves and
  enters.
- Prove equal-basis endpoints plus monotone objective values force every step
  in the segment degenerate.
- Add focused trace-interface checks and commit.

## 10. Bland coefficient comparison

- Create `Simplex/Bland/Coefficients.lean`.
- Define an objective coefficient for every original/slack variable, zero on
  basic variables.
- Prove full-variable objective expansion.
- Evaluate equivalent dictionaries on a one-nonbasic-variable assignment and
  derive the textbook coefficient identity used by the fickle-variable proof.
- Add sign and negative-summand helper theorems; audit and commit.

## 11. Bland no-cycling

- Add RED checks for the no-repeat theorem.
- Create `Simplex/Bland/NoCycle.lean`.
- Combine greatest-fickle extraction, coefficient comparison, degeneracy, and
  the two Bland tie breakers to contradict a repeated basis.
- Print axioms for the theorem, run focused checks, and commit.

## 12. Finite termination and public SIMPLEX

- Add RED checks for the finite basis bound, non-exhaustion, `simplex`, and its
  optimal-or-unbounded correctness theorem.
- Create `Simplex/Termination.lean`.
- Bound a run by the number of possible finite basic-variable sets, apply the
  no-repeat theorem, and eliminate exhaustion.
- Expose the public result without a fuel-exhausted constructor.
- Audit and commit.

## 13. Section integration

- Register the `Simplex` hierarchy in the Section 29.3 reader, chapter imports,
  `literate.toml`, and `docs/index.md`.
- Update the progress CSV, regenerate `Progress.lean`, and update `Status.lean`,
  proof map, and proof-status board.  Mark Section 29.3 complete only after the
  finite-termination and terminal-correctness theorems compile.
- Update issue #84 with exact theorem names and keep it open for Sections 29.2,
  29.4, and 29.5.
- Run the focused final gate and review the complete diff before integration.
