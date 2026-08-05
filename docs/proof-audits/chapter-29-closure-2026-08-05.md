# Chapter 29 Closure Audit

## 1. Date and Status

Date: 2026-08-05

Status: `main-proof-complete`

This audit seals the Chapter 29 main text, Sections 29.1--29.5, at the finite
real-matrix and pure-functional tableau boundary.

## 2. Acceptance Boundary

The accepted boundary includes:

- standard and slack forms, including existence and uniqueness of the
  nonnegative slack extension;
- the shortest-path, maximum-flow, minimum-cost-flow, and multicommodity-flow
  linear-programming formulations from Section 29.2;
- fixed-slot dictionaries, exact PIVOT semantics, Bland entering/leaving
  selection, certified optimal and unbounded exits, the textbook anti-cycling
  argument, and finite termination;
- weak duality, terminal dictionary dual certificates, strong duality, the
  exact duality-gap identity, and complementary slackness; and
- the auxiliary phase-I LP, the initial artificial pivot, the phase-I
  feasibility criterion, objective restoration, phase II, and the complete
  certified infeasible/optimal/unbounded solver.

The seal excludes mutable-array tableau storage, floating-point numerical
stability, concrete RAM constants, exercises, and chapter-end problems.  These
are implementation or extension tracks, not missing main-text proof groups.

The fixed-slot dictionary type cannot physically remove a column after phase
I.  The formalization therefore replaces the textbook deletion of the
artificial variable by an equivalent lock row `x₀ ≤ 0`.  Auxiliary
nonnegativity supplies `x₀ ≥ 0`, so the locked program has exactly `x₀ = 0`;
the proved projection theorems then recover precisely the original feasible
assignments, objectives, unboundedness witnesses, and dual certificates.

## 3. Source-Module Responsibilities

| Scope | Source group | Responsibility |
| --- | --- | --- |
| 29.1 | `Section_29_1_Standard_And_Slack_Forms/` | Standard-form model and canonical slack-variable equivalence |
| 29.2 | `Section_29_2_Formulating_Problems_As_Linear_Programs/` | Common gross-flow network model and the four textbook LP formulations |
| 29.3 dictionary | `Section_29_3_The_Simplex_Algorithm/Dictionary/` | Labels, assignments, dictionary semantics, and standard-LP initialization |
| 29.3 PIVOT | `Section_29_3_The_Simplex_Algorithm/Pivot/` | Exact algebra, semantic equivalence, feasibility, and objective progress |
| 29.3 SIMPLEX | `Section_29_3_The_Simplex_Algorithm/Simplex/` | Bland selectors, exits, anti-cycling, run semantics, and finite termination |
| 29.4 | `Section_29_4_Duality/` | Weak duality, gap identity, certificates, strong duality, and complementary slackness |
| 29.5 | `Section_29_5_The_Initial_Basic_Feasible_Solution/` | Artificial LP, two phases, projection, initialized solver, and general duality |
| Public entry | `CLRSLean/Chapter_29.lean` | Single chapter import and reader-facing completion boundary |
| Closure contract | `Tests/Chapter_29_Closure.lean` | Aggregator-only headline checks and axiom inspection |

## 4. Requirement-to-Evidence Audit

| Requirement | Evidence | Result |
| --- | --- | --- |
| Standard/slack equivalence | `StandardLP.existsUnique_slackExtension_iff` | Complete |
| Shortest-path LP correctness | `ShortestPathLP.feasible_le_walkWeight`, `optimal_of_attained_walk` | Complete |
| Maximum-flow LP | `MaximumFlowLP.isFeasible_iff`, `isOptimal_iff` | Complete |
| Minimum-cost-flow LP | `MinimumCostFlowLP.isFeasible_iff`, `isOptimal_iff` | Complete |
| Multicommodity-flow LP | `MulticommodityFlowLP.isFeasible_iff`, `isMinimumCost_iff` | Complete |
| Exact PIVOT semantics | `Dictionary.pivot_satisfies_iff`, `pivot_objectiveRhs_eq` | Complete |
| Bland anti-cycling | `Dictionary.bland_no_repeated_basis`, `bland_acyclic` | Complete |
| Finite terminal SIMPLEX | `simplexRun_basisCount_not_exhausted`, `simplex_optimal_or_unbounded` | Complete |
| Weak duality | `StandardLP.weak_duality` (Theorem 29.8) | Complete |
| Terminal dual certificate | `dualCertificate_isDualFeasible`, `dualCertificate_objective_eq_v` | Complete |
| Strong duality | `StandardLP.strongDuality`, `strongDuality_of_isOptimal` (Theorem 29.9) | Complete |
| Complementary slackness | `dualityGap_eq_slackSums`, `complementarySlackness_iff_optimal` (Theorem 29.10) | Complete |
| Phase-I feasibility decision | `isFeasible_iff_phaseOneTerminal_v_eq_zero` | Complete |
| Phase-II basic-feasible start | `phaseTwoStart_isBasicFeasible`, `phaseTwoStart_equivalent_lockedAuxiliary` | Complete |
| Complete initialized solver | `initializedSimplex_complete` | Complete |

## 5. Verification and Axiom Boundary

The closure audit uses focused Chapter 29 verification rather than a full
repository build:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
lake env lean Tests/Chapter_29_Formulations_Interface.lean
lake env lean Tests/Chapter_29_Simplex_Interface.lean
lake env lean Tests/Chapter_29_Initialization_Interface.lean
lake env lean Tests/Chapter_29_Closure.lean
lake build CLRSLean.Chapter_29:literate
lake build CLRSLean.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs:literate
lake build CLRSLean.Chapter_29.Section_29_4_Duality:literate
lake build CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution:literate
rg -n '\b(sorry|admit|axiom)\b|TODO|FIXME|placeholder' \
  CLRSLean/Chapter_29 Tests/Chapter_29*.lean -g '*.lean'
uv run python scripts/check_repository.py
git diff --check
```

The focused build and all interface tests exit successfully.  The closure
test's `#print axioms` output contains only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or project-defined axiom occurs among the inspected
headline results.  The focused reader modules render successfully with no new
Chapter 29 warnings; pre-existing dependency and SubVerso compatibility
warnings are outside this chapter.  The marker scan has no matches, and the
repository metadata, navigation, documentation, placeholder, and local-link
checks pass.

## 6. Optional Refinements

- Refine the functional dictionaries to a mutable tableau implementation.
- Add exact arithmetic-operation or RAM-cost accounting for PIVOT and SIMPLEX.
- Study floating-point pivoting and numerical stability in a separate model.
- Formalize selected exercises and chapter-end problems without reopening the
  completed main-text boundary.
