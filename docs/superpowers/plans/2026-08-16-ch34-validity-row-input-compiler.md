# Chapter 34 Validity-Row Input Compiler Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct a fixed polynomial-time TM2 that maps a raw verifier word `x` to the exact canonical `encodeAffineValidityRowFamilyInput (verifierValidityRowFramesByLength W x.length)` consumed by the Cook--Levin validity-row controller.

**Architecture:** Build the compiler bottom-up in three independently reviewable slices. First compile and assemble the fixed row-level scalar operands. Then add the runtime-height one-hot and stack/cell subfamilies with exact row-major encodings. Finally compose the canonical script compiler with the already verified validity-row controller and expose the raw-input polynomial-time theorem. Runtime dimensions remain unary tape data; no input-dependent value is embedded in finite control.

**Tech Stack:** Lean 4, Mathlib `TM2ComputableInPolyTime`, Chapter 34 `PolyBuilder` programs and `comp_scratch`, focused interface tests and axiom audits.

---

### Task 1: Pin the final public proof surface

**Files:**
- Create: `Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowInputCompiler.lean`

- [ ] **Step 1: Write the failing interface test**

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler

open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check verifierValidityRowFamilyInput
#check verifierValidityRowFamilyInput_eq_canonical
#check verifierValidityRowFamilyInput_computableInPolyTime

#print axioms verifierValidityRowFamilyInput_eq_canonical
#print axioms verifierValidityRowFamilyInput_computableInPolyTime
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake env lean Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean
```

Expected: failure because `GeneratorValidityRowInputCompiler` does not yet exist.

- [ ] **Step 3: Fix the target signatures in the production module**

The completed module must expose:

```lean
def verifierValidityRowFamilyInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List UnaryFrameSym

theorem verifierValidityRowFamilyInput_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    verifierValidityRowFamilyInput W x =
      encodeAffineValidityRowFamilyInput
        (verifierValidityRowFramesByLength W x.length)

noncomputable def verifierValidityRowFamilyInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowFamilyInput W)
```

The implementation definition must denote the output of the concrete source
pipeline, rather than defining the target canonical encoding and proving
computability by an unrelated oracle premise.

### Task 2: Package the existing structured validity-row controller

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ValidityRowFamily.lean`
- Modify: `Tests/Chapter_34_CookLevin_GeneratorValidityRows.lean`

- [x] **Step 1: Add RED checks for the compiled structured controller**

```lean
#check affineValidityRowFamilyRev_computableInPolyTime
#check affineValidityRowFamilyGateStream_computableInPolyTime
#print axioms affineValidityRowFamilyGateStream_computableInPolyTime
```

Run the focused test and confirm the missing-name failure.

- [x] **Step 2: Compile the exact reverse run**

Package `affineValidityRowFamily_run frames []` with `compile_evalsToInTime`
and `affineValidityRowFamilyRev_steps_le` into a quadratic
`TM2ComputableInPolyTime encodeAffineValidityRowFamilyInput id` machine whose
output is `(affineValidityRowFamilyGateStream frames).reverse`.

- [x] **Step 3: Obtain the forward structured controller**

Compose the reverse-output machine with
`reverse_computableInPolyTime (Γ := CircuitSym)` using `comp_scratch`, then run
the focused test, source module, axiom audit, unfinished-proof scan, and
`git diff --check`.

- [x] **Step 4: Commit the controller checkpoint**

```bash
git commit -m "feat(ch34): package validity row family controller"
```

### Task 3: Row-level scalar stream and row-major assembler

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ValidityRowScalarAssembler.lean`
- Create: `Tests/Chapter_34_PolyBuilder_ValidityRowScalarAssembler.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowInputCompiler.lean`

- [ ] **Step 1: Add a RED test for the structured assembler**

Check the exact semantic function, exact run theorem, polynomial step bound,
and `TM2ComputableInPolyTime` declaration for the assembler.  The test must
include `#print axioms` for the exact-output and computability declarations.

- [ ] **Step 2: Define the structured scalar source**

Use one exact-polynomial unary field family for every base, stride, fixed count,
and row count needed by the scalar part.  Reuse the established formulas:

```lean
verifierValidityRowCountPolynomial W
verifierCfgBitCountPolynomial W
verifierTableauInputPolynomial W + 2
verifierValidityRowCostPolynomial W
verifierFirstValidityRowStartPolynomial W
rawOneHotGatePolynomial W.machine.tm
```

Prove direct field-to-frame equalities for both gate starts and halted triples;
do not rely only on equal lengths.

- [ ] **Step 3: Implement the fixed row-major assembler**

The controller consumes canonical unary source fields, emits one leading
`.tick` per row, places the scalar operands at the exact boundaries prescribed
by `encodeAffineValidityRowFrame`, advances all affine values, and ends with the
single outer `.frameEnd`.  Prove the exact independent-semantics run and a
polynomial bound in the structured input length.

- [ ] **Step 4: Compose the scalar source and assembler**

Use only `TM2Comp.TM2ComputableInPolyTime.comp_scratch` and the verified reverse
machine where forward output is required.  Prove byte-for-byte agreement with
the scalar projection of every member of
`verifierValidityRowFramesByLength W x.length`.

- [ ] **Step 5: Verify and commit the scalar checkpoint**

Run the focused PolyBuilder and Cook--Levin tests, the two production modules,
the touched-file unfinished-proof scan, and `git diff --check`.  Commit with:

```bash
git commit -m "feat(ch34): assemble validity row scalar operands"
```

### Task 4: Runtime-height one-hot frame compiler

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/AffineExactlyOneRowFamilySource.lean`
- Create: `Tests/Chapter_34_PolyBuilder_AffineExactlyOneRowFamilySource.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowOneHotOperands.lean`
- Create: `Tests/Chapter_34_CookLevin_ValidityRowOneHotOperands.lean`

- [ ] **Step 1: Add RED checks for the one-hot source compiler**

The public surface must include the concrete row-major byte stream, its exact
equality to:

```lean
(verifierValidityRowFramesByLength W x.length).flatMap
  (fun frame => encodeAffineExactlyOneFamily frame.oneHotFrames)
```

and a raw-input `TM2ComputableInPolyTime` theorem.

- [ ] **Step 2: Compile the fixed group prefix and runtime-height stack groups**

Emit label and state groups first, then for each fixed machine stack emit its
height group followed by all `H` cell-symbol groups.  Generate each four-field
`AffineExactlyOneFrame` in controller order `(start, start + 2, rowBase, count)`.
The row and cell loops are runtime counters; fixed stack/alphabet cases may be
finite-control tags because they depend only on `W.machine.tm`.

- [ ] **Step 3: Prove semantic equality to `arithmeticRawOneHotFrames`**

Use `cfgOneHotGroupEquivFin`, `arithmeticCfgOneHotGroupWireBase`, and
`arithmeticCfgOneHotGroupWireCount` to identify every emitted frame, including
the `H = 0` case and the transition between adjacent rows.

- [ ] **Step 4: Prove and package polynomial runtime**

Bound the nested row/group/cell loops by polynomials in the structured source
length, compose them after the exact-polynomial source, and expose a fixed raw-
input TM2.

- [ ] **Step 5: Verify and commit the one-hot checkpoint**

Run focused tests, both production modules, `#print axioms`, unfinished-proof
scan, and `git diff --check`.  Commit with:

```bash
git commit -m "feat(ch34): compile validity row one-hot operands"
```

### Task 5: Runtime-height stack, cell, and conjunction compiler

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/AffineValidityTailRowFamilySource.lean`
- Create: `Tests/Chapter_34_PolyBuilder_AffineValidityTailRowFamilySource.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowTailOperands.lean`
- Create: `Tests/Chapter_34_CookLevin_ValidityRowTailOperands.lean`

- [ ] **Step 1: Add RED checks for the tail source compiler**

Pin exact output equality to the row-major flattening of
`encodeAffineValidityTailFrame frame.tailFrame` and pin a concrete raw-input
`TM2ComputableInPolyTime` theorem.

- [ ] **Step 2: Emit every fixed stack frame and runtime-height cell family**

For each row and fixed machine stack, emit the three mask fields, every cell's
`right/left/blank` fields in `Fin H` order, and the stack-family `.frameEnd`.
Bridge each operand to `arithmeticStackFrame` and
`arithmeticStackCellFrames` exactly.

- [ ] **Step 3: Emit the final conjunction frame**

Generate `arithmeticValidityFinalStart` followed by the reversed
`arithmeticValidityConstraintWires` order required by
`encodeAffineConjunctionFrame`, then emit its `.frameEnd`.  Prove the order,
not only the multiset or length.

- [ ] **Step 4: Prove and package polynomial runtime**

Bound the fixed-stack and runtime-height cell loops and compose the exact source
pipeline into the raw-input TM2 theorem.

- [ ] **Step 5: Verify and commit the tail checkpoint**

Run focused tests, source builds, axiom and unfinished-proof scans, and
`git diff --check`.  Commit with:

```bash
git commit -m "feat(ch34): compile validity row tail operands"
```

### Task 6: Complete canonical row input and compose with the validity controller

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowInputCompiler.lean`
- Modify: `Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [ ] **Step 1: Interleave the three verified row fragments**

Use a fixed assembler with explicit fragment terminators to emit, per row, the
canonical `.tick`, one-hot frame family, halted triple, validity tail, and the
outer family terminator.  Prove structural equality by induction on the actual
row-frame list.

- [ ] **Step 2: Complete the final semantic and computability theorems**

Prove `verifierValidityRowFamilyInput_eq_canonical` and obtain
`verifierValidityRowFamilyInput_computableInPolyTime` solely by composing
concrete source and assembler machines.

- [ ] **Step 3: Compose with the existing row controller**

Add the downstream theorem:

```lean
noncomputable def verifierValidityGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Turing.TM2ComputableInPolyTime id id
      (verifierValidityGateStream W)
```

using `verifierValidityRowFamilyInput_computableInPolyTime`,
`affineValidityRowFamilyGateStream_computableInPolyTime`, and exact semantic
rewrites.

- [ ] **Step 4: Run the acceptance gate**

```bash
lake env lean Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean
lake env lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowInputCompiler.lean
lake env lean CLRSLean/Chapter_34.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean -g '*.lean'
git diff --check
```

Expected: focused Lean commands exit zero, no new unfinished proof or custom
axiom appears, and the headline declarations report only the repository's
standard axiom surface.

- [ ] **Step 5: Commit the completed validity-row input compiler**

```bash
git commit -m "feat(ch34): compile complete validity row input"
```

This commit closes only the validity-row source compiler.  Transition-family
and verifier-tail script compilers remain explicit blockers before
`compileVerifierBodyScript W` is available as a raw-input polynomial-time TM2.
