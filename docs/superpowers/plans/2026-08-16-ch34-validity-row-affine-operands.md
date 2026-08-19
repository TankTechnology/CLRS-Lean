# Validity Row Affine Operands Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build fixed polynomial-time TM2s that map the raw verifier input to the delimiter-bearing unary `rowBase` and validity-gate-start operands of every Cook--Levin validity row.

**Architecture:** First verify a reusable finite-control TM2 that consumes unary `(base, step, count)`, maintains the current affine value in work counters, and emits `base, base + step, ...` as a unary frame stream. Compose it with the existing exact-polynomial source compiler, then instantiate the three input polynomials with the Cook--Levin row formulas and prove exact agreement with the actual validity-row frame family.

**Tech Stack:** Lean 4, Mathlib polynomials, CLRS-Lean TM2 semantics and `comp_scratch`, focused public-interface and axiom-audit tests.

---

### Task 1: Runtime affine unary progression controller

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/AffineUnaryProgression.lean`
- Test: `Tests/Chapter_34_PolyBuilder_AffineUnaryProgression.lean`

- [x] **Step 1: Define the structured input and exact output semantics**

Represent the runtime input as unary `base`, `step`, and `count` fields and specify the output as the delimiter-bearing unary frame stream for the affine progression.

- [x] **Step 2: Implement the fixed finite-control TM2**

Parse all three operands, maintain the current value and persistent step in work counters, emit one unary value per iteration, increment the current value by the saved step, and halt with clean scratch tapes.

- [x] **Step 3: Prove the exact run and polynomial bound**

Prove that the controller emits precisely the reversed requested stream, derive a cubic step bound in the encoded input length, and compose with the verified reverse machine to obtain the forward stream.

- [x] **Step 4: Verify the public interface**

Run:

```bash
lake env lean Tests/Chapter_34_PolyBuilder_AffineUnaryProgression.lean
```

Expected: exit zero, with only the repository's standard `propext`, `Classical.choice`, and `Quot.sound` axiom surface.

### Task 2: Exact-polynomial source compilation

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactPolynomialAffineUnaryProgression.lean`
- Test: `Tests/Chapter_34_PolyBuilder_ExactPolynomialAffineUnaryProgression.lean`

- [x] **Step 1: Compile the three runtime operands from the raw word**

Reuse the exact-polynomial unary-field compiler to generate the `(base, step, count)` encoding from three natural-coefficient polynomials evaluated at the raw input length.

- [x] **Step 2: Compose source and affine controllers**

Use `comp_scratch` to connect the exact source machine to the verified affine progression machine and prove its output encoder agrees exactly with the structured source word.

- [x] **Step 3: Verify the public interface**

Run:

```bash
lake env lean Tests/Chapter_34_PolyBuilder_ExactPolynomialAffineUnaryProgression.lean
```

Expected: exit zero and the standard axiom surface only.

### Task 3: Cook--Levin validity-row specialization

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowAffineOperands.lean`
- Test: `Tests/Chapter_34_CookLevin_ValidityRowAffineOperands.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [x] **Step 1: Instantiate the exact row formulas**

Compile the row-base progression with base `0`, step `cfgBitCount`, and count `horizon + 1`; compile the validity-gate-start progression with base `tableauInputCount + 2`, step `validCfgGateCost`, and the same count.

- [x] **Step 2: Bridge to the actual frame family**

Prove the row-base values equal `haltedLeft` in every member of `verifierValidityRowFramesByLength`, rather than only showing a length or asymptotic bound.

- [x] **Step 3: Integrate and verify the chapter**

Run the three focused tests, the Chapter 34 root build, status/progress/literate audits, and `git diff --check`. The known pre-existing site metadata failures may remain, but the checker must not report any new module from this checkpoint.

- [x] **Step 4: Review, commit, and push**

Request an independent proof review, fix every Critical or Important finding, and commit with:

```bash
git commit -m "feat(ch34): compile affine validity row operands"
git push origin codex/ch34-textbook-closure
```
