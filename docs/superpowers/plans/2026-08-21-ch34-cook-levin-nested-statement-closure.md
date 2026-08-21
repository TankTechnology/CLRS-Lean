# Ch34 Cook--Levin Nested Statement Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the one-branch statement-generator boundary with a recursive,
fully verified compiler for every finite TM2 statement and connect it to the
fixed polynomial-time Cook--Levin circuit encoder.

**Architecture:** Preserve the existing affine-context and terminal-route
layers.  Add a canonical route for any statement whose linear spine ends in a
branch, then define a recursive plan whose leaves reuse the branch-free
compiler and whose branch nodes recursively compile both arms before emitting
the parent whole-row mux.  Flatten that proof-carrying plan to the existing
fixed affine-statement controller alphabet, and only then lift it from one
statement to all program labels and transition rows.

**Tech Stack:** Lean 4, Mathlib Turing machines, Chapter 34 `PolyBuilder`,
focused `lake env lean` interface checks, staged Git commits.

---

### Task 1: Canonical output route for arbitrary branch-ending statements

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionStatementAffineContextBranchRoute.lean`
- Create: `Tests/Chapter_34_CookLevin_TransitionStmtBranchRoute.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`

- [x] Add unresolved `#check` declarations for
  `transitionStmtBranchRouteValues` and
  `transitionStmtBranchRouteValues_eq_output`; run Lean and observe the missing
  identifiers.
- [x] Define the route as the stride-three output progression of the final mux,
  based on the current affine statement context and the final-branch offset.
- [x] Prove its length is `cfgBitCount` and its values equal
  `transitionCfgWireValues ... (transitionStmtOutputWires ...)` by reusing
  `transitionStmtOutputWires_eq_finalBranchMux`.
- [x] Run the focused test, inspect theorem axioms, update the facade, and
  commit the checkpoint.

### Task 2: Recursive statement plan and total compiler

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionStatementAffineContextRecursivePlan.lean`
- Create: `Tests/Chapter_34_CookLevin_TransitionStmtRecursivePlan.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`

- [ ] Add failing interface checks for `TransitionStmtRecursivePlan`,
  `transitionStmtRecursivePlan`, and `transitionStmtRecursivePlan_isSome`.
- [ ] Define plan leaves carrying the existing branch-free forms/result and
  branch nodes carrying the predicate phase, recursively compiled arms, and
  the parent mux descriptor.
- [ ] Define prefix insertion for `load`, `push`, `peek`, and `pop`, keeping
  source order and affine contexts exact.
- [ ] Define the compiler by structural recursion on `TM2.Stmt`; recursive
  calls occur only on syntactic continuations or branch arms.
- [ ] Prove totality for every statement satisfying the reachable-alphabet
  support invariant; run the focused test and commit.

### Task 3: Exact recursive phase and output semantics

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionStatementAffineContextRecursiveSemantics.lean`
- Create: `Tests/Chapter_34_CookLevin_TransitionStmtRecursiveSemantics.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`

- [ ] Add failing checks for the exact complete-phase and output-route theorems.
- [ ] Define `completePhases` in depth-first circuit-construction order:
  prefix/predicate, true arm, false arm, then parent mux.
- [ ] Prove by plan induction that `completePhases` is byte-for-byte the
  existing `transitionStmtScript`, including nested branches.
- [ ] Prove each plan's canonical output route equals the semantic statement
  output; branch leaves use Task 1 and terminal leaves reuse
  `TransitionStmtLinearResult.completeRouteValues`.
- [ ] Run focused tests, audit for `sorry`/`admit`/new axioms, and commit.

### Task 4: Fixed-controller source stream for recursive plans

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorTransitionStatementAffineContextRecursiveSource.lean`
- Create: `Tests/Chapter_34_CookLevin_TransitionStmtRecursiveSource.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`

- [ ] Add a failing check for the recursive source/controller output theorem.
- [ ] Flatten fixed affine-form blocks and tagged variable-width mux invocation
  segments in exactly the recursive phase order.
- [ ] Reuse the affine statement controller and mux-segment controller rather
  than introducing a verifier-specific machine.
- [ ] Prove the concatenated controller frames equal
  `encodeAffineStmtControllerScript plan.completePhases`.
- [ ] Establish a polynomial bound in encoded recursive source length; run the
  focused controller test and commit.

### Task 5: All labels, all transition rows, and raw-input generation

**Files:**
- Create focused modules under
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/`
  for label-family assembly, row-family assembly, and raw-input source bounds.
- Create matching `Tests/Chapter_34_CookLevin_*` interface files.
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`

- [ ] Compile one recursive plan per fixed verifier label and prove exact
  equality with the semantic dispatch statement scripts.
- [ ] Assemble every label into one transition row and every adjacent tableau
  pair into the full transition stream.
- [ ] Generate every runtime affine seed and recursive source packet from the
  raw input using fixed TM2 programs.
- [ ] Convert component bounds to one polynomial in `input.length`; commit each
  independently verifiable row/family checkpoint.

### Task 6: Cook--Levin and GeneralCircuitSAT closure

**Files:**
- Modify or add the final reduction-machine modules under
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/` and
  `GeneralCircuit/`.
- Modify: `CLRSLean/Chapter_34.lean`
- Modify the Chapter 34 proof/status audit documents that name the old gap.

- [ ] Compose header/input/pool, validity rows, transition rows, and verified
  tail into one fixed TM2 that emits `encodeCircuit (verifierCircuit W x)`.
- [ ] Prove total correctness and one input-length polynomial runtime bound.
- [ ] Close the concrete Cook--Levin reduction theorem and derive
  `GeneralCircuitSAT` NP-hardness and NP-completeness.
- [ ] Run all focused tests, `lake build CLRSLean.Chapter_34`, the unfinished
  marker scan, axiom audit, and `git diff --check`.
- [ ] Commit and push the final verifiable checkpoint; do not report closure
  unless all of these checks pass.
