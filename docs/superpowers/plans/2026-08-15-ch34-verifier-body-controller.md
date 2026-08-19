# Ch34 Verifier Body Controller Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build one fixed controller that continuously emits the complete
Cook--Levin verifier body after the shared Boolean pool: every validity row,
every adjacent transition, and the already verified post-transition tail.

**Architecture:** Use `AffineStmtScriptSym` as the common runtime alphabet.
Pure-unary validity and tail operands are embedded as `.data`; the transition
family already uses this alphabet. Add only a suffix-preserving transition
family check interface, then reserve `.data .separator` at the enclosing body
boundary. The semantic wrapper proves that the pool prefix plus the generated
body is exactly `encodeCircuit (verifierCircuit W x)`.

**Tech Stack:** Lean 4, Mathlib `StateTransition`, the Chapter 34
`PolyBuilder` fixed-program framework, focused `lake env lean` checks.

---

### Task 1: Suffix-preserving transition-family body

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/TransitionFamilyController.lean`
- Test: `Tests/Chapter_34_PolyBuilder_TransitionFamilyController.lean`

- [x] Add an unresolved test check for
  `affineTransitionFamily_runToCheckWithTail` and observe failure.
- [x] Define the exact recursive body step count, excluding the final family
  check that interprets end-of-input.
- [x] Prove that the existing family controller consumes every encoded local
  script and reaches `affineTransitionFamilyLoopCfg tail ...` without reading
  `tail`.
- [x] Prove the inherited linear bound in the exact family encoding.
- [x] Run the focused transition-family test and audit headline axioms.
- [x] Commit the independently useful interface.

### Task 2: Continuous verifier-body controller

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/VerifierBodyController.lean`
- Create: `Tests/Chapter_34_PolyBuilder_VerifierBodyController.lean`

- [x] Add unresolved checks for `AffineVerifierBodyScript`,
  `affineVerifierBody_run`, and `affineVerifierBody_steps_le`; observe failure.
- [x] Define a script containing validity frames, transition scripts, and a
  verifier-tail script. Encode validity and tail symbols with `.data`, and put
  `.data .separator` between transition and tail.
- [x] Define one finite program with `validity`, `transition`, and `tail`
  label embeddings. Intercept only the transition check on the reserved
  separator; keep all reusable component programs unchanged.
- [x] Prove exact structural lifting for unary components and same-alphabet
  transition configurations, restricted at the intercepted boundary.
- [x] Compose the three exact runs into `affineVerifierBody_run`, preserving
  byte order and proving halt with the combined reversed stream.
- [x] Prove a coarse polynomial envelope
  `steps ≤ 10000 * encoded.length^2 + 200`.
- [x] Run the focused body test and audit headline axioms.
- [x] Commit the generic controller.

### Task 3: Semantic Cook--Levin specialization

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorBody.lean`
- Create: `Tests/Chapter_34_CookLevin_GeneratorBody.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `docs/proof-audits/2026-08-15-ch34-local-transition-controller.md`

- [x] Add unresolved checks for `compileVerifierBodyScript_gateStream_eq`,
  `verifierCircuitPoolPrefix_append_body`, and `verifierCircuitBody_run`;
  observe failure.
- [x] Compile canonical validity-row frames, transition-family scripts, and
  the verifier tail into the generic body script.
- [x] Prove byte-for-byte equality with
  `verifierValidityGateStream ++ verifierTransitionGateStream ++
  verifierCircuitTailGateStream`.
- [x] Prove that `verifierCircuitPoolPrefix` followed by this body is exactly
  `encodeCircuit (verifierCircuit W x)`.
- [x] Specialize the exact execution and polynomial runtime theorems.
- [x] Record any rejected composition route and the remaining prefix-to-body
  compiler boundary in the audit document.
- [x] Run focused component tests, root `CLRSLean/Chapter_34.lean`,
  `git diff --check`, and a `sorry`/`admit` scan; do not run a full build.
- [x] Commit and push the checkpoint.
