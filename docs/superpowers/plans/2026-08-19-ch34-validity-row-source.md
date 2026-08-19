# Chapter 34 Validity-Row Source Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct a fixed polynomial-time TM2 from the original verifier word to the exact canonical validity-row controller input, then compose it with the existing controller to compute all validity gates.

**Architecture:** Compile the existing row-major `(height, start, rowBase)` seed stream, consume one seed at a time in a delimiter-preserving source, and reuse the established one-hot, stack/cell, conjunction, and family-controller machines behind redirectable continuations.  The source emits `encodeAffineValidityRowFamilyInput` exactly; no independent whole-family streams are zipped and no input-dependent value is embedded in finite control.

**Tech Stack:** Lean 4, Mathlib `TM2ComputableInPolyTime`, Chapter 34 `PolyBuilder`, `StateTransition.EvalsToInTime`, `TM2Comp.comp_scratch`, focused `#check`/`#print axioms` interface tests.

---

## File structure

- Create `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/AffineStackOutputFamilySource.lean`: generic fixed-stack/runtime-height source for the stack-cell output-wire segment of a conjunction frame.
- Create `Tests/Chapter_34_PolyBuilder_AffineStackOutputFamilySource.lean`: exact-run, order, bound, and axiom interface for that source.
- Create `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/AffineValidityFinalConjunctionSource.lean`: continuous linker for start, reversed stack wires, halted wire, reversed one-hot outputs, and terminator.
- Create `Tests/Chapter_34_PolyBuilder_AffineValidityFinalConjunctionSource.lean`: public linker interface.
- Create `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowTailSource.lean`: Cook--Levin specialization, row-family lifting, and raw-input polynomial-time theorem for complete tail operands.
- Create `Tests/Chapter_34_CookLevin_ValidityRowTailSource.lean`: canonical equality and raw-input computability interface.
- Create `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowInputCompiler.lean`: delimiter-preserving row source and downstream gate-stream composition.
- Create `Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean`: final milestone interface and axiom audit.
- Modify the relevant Chapter 34 aggregate imports, `literate.toml`, and `docs/index.md` when each new production module becomes public.

### Task 1: Generic runtime stack-output source

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/AffineStackOutputFamilySource.lean`
- Create: `Tests/Chapter_34_PolyBuilder_AffineStackOutputFamilySource.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder.lean`

- [ ] **Step 1: Write the failing public interface test**

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineStackOutputFamilySource

open CLRS.Chapter34.Turing.PolyBuilder

#check affineStackOutputWires
#check encodeAffineStackOutputSourceInvocation
#check affineStackOutputFamilySourceRevProgram
#check affineStackOutputFamilySource_runToFinish
#check affineStackOutputFamilySource_steps_le

#print axioms affineStackOutputFamilySource_runToFinish
#print axioms affineStackOutputFamilySource_steps_le
```

- [ ] **Step 2: Run the test and verify the missing-module failure**

Run:

```bash
lake env lean Tests/Chapter_34_PolyBuilder_AffineStackOutputFamilySource.lean
```

Expected: Lean reports that `AffineStackOutputFamilySource` does not exist.

- [ ] **Step 3: Define the exact ordered semantic target and invocation**

```lean
def affineStackOutputWires (stackCount height base : Nat) : List Nat :=
  List.ofFn fun position : Fin (stackCount * height) =>
    let pair := (finProdFinEquiv (m := stackCount) (n := height)).symm position
    base + (height + 1 + 6 * height) * pair.1.val +
      (height + 1) + 6 * pair.2.val + 5

structure AffineStackOutputSourceFrame where
  height : Nat
  base : Nat

def encodeAffineStackOutputSourceInvocation
    (frame : AffineStackOutputSourceFrame) : List UnaryFrameSym :=
  encodeUnaryFrame [frame.height, frame.base]
```

The machine output is exactly:

```lean
encodeAffineConjunctionSources
  (affineStackOutputWires stackCount frame.height frame.base).reverse
```

- [ ] **Step 4: Implement the fixed nested controller and exact run theorem**

Use a finite outer stack phase `Fin stackCount`, a runtime `height` tick loop,
and three unary counters for the current wire, saved height, and remaining
cells.  Iterate stacks and cells in public forward order while prepending each
`encodeUnaryFrameBlock`; the reverse-output accumulator then has exactly the
reverse conjunction-source segment.

Expose this exact interface:

```lean
def affineStackOutputFamilySource_runToFinish
    (stackCount : Nat) (frame : AffineStackOutputSourceFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceLoopCfg stackCount
        (encodeAffineStackOutputSourceInvocation frame ++ tail) output)
      (some (affineStackOutputFamilySourceFinishCfg stackCount tail
        ((encodeAffineConjunctionSources
          (affineStackOutputWires stackCount frame.height frame.base).reverse).reverse ++ output)))
      (affineStackOutputFamilySourceSteps stackCount frame)
```

Malformed separators and truncated two-field frames branch to `.invalid`,
which halts.

- [ ] **Step 5: Prove the uniform quadratic runtime bound**

Expose:

```lean
theorem affineStackOutputFamilySource_steps_le
    (stackCount : Nat) (frame : AffineStackOutputSourceFrame) :
    affineStackOutputFamilySourceSteps stackCount frame ≤
      (200 * (stackCount + 1)) *
        (encodeAffineStackOutputSourceInvocation frame).length ^ 2 + 20
```

Prove it from the exact nested-loop recurrence, `encodeUnaryFrame_length`,
and monotonicity of squaring.

- [ ] **Step 6: Run focused verification**

```bash
lake env lean Tests/Chapter_34_PolyBuilder_AffineStackOutputFamilySource.lean
lake env lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/AffineStackOutputFamilySource.lean
git diff --check
```

Expected: all commands exit zero and the two audited declarations report only
`propext`, `Classical.choice`, and `Quot.sound` when those axioms are required.

### Task 2: Continuous final-conjunction linker

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/AffineValidityFinalConjunctionSource.lean`
- Create: `Tests/Chapter_34_PolyBuilder_AffineValidityFinalConjunctionSource.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowTailOperands.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [ ] **Step 1: Write the failing linker interface test**

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityFinalConjunctionSource

open CLRS.Chapter34.Turing.PolyBuilder

#check AffineValidityFinalConjunctionSourceFrame
#check encodeAffineValidityFinalConjunctionSourceInvocation
#check affineValidityFinalConjunctionSource_runToFinish
#check affineValidityFinalConjunctionSource_steps_le

#print axioms affineValidityFinalConjunctionSource_runToFinish
#print axioms affineValidityFinalConjunctionSource_steps_le
```

- [ ] **Step 2: Run RED**

Run:

```bash
lake env lean Tests/Chapter_34_PolyBuilder_AffineValidityFinalConjunctionSource.lean
```

Expected: missing-module failure.

- [ ] **Step 3: Define the generic source frame and its exact target**

```lean
structure AffineValidityFinalConjunctionSourceFrame where
  rawFrames : List AffineExactlyOneFrame
  haltedWire : Nat
  stackFrame : AffineStackOutputSourceFrame
  finalStart : Nat

def affineValidityFinalConjunctionWires (stackCount : Nat)
    (frame : AffineValidityFinalConjunctionSourceFrame) : List Nat :=
  frame.rawFrames.map affineExactlyOneFrameOutputWire ++
    frame.haltedWire ::
      affineStackOutputWires stackCount
        frame.stackFrame.height frame.stackFrame.base

def affineValidityFinalConjunctionFrame (stackCount : Nat)
    (frame : AffineValidityFinalConjunctionSourceFrame) :
    AffineConjunctionFrame :=
  { start := frame.finalStart
    wires := affineValidityFinalConjunctionWires stackCount frame }
```

Encode the raw frames for `affineExactlyOneOutputFamilySourceRevProgram`, then
the two-field stack source frame, the halted wire, and the final start with
explicit `frameEnd` boundaries.

- [ ] **Step 4: Relabel and connect existing component programs**

The combined program runs these phases without an intermediate halt:

```text
emit finalStart block
-> stack-output family source
-> emit haltedWire block
-> exactly-one output-family source over rawFrames.reverse
-> emit final frameEnd
-> finish
```

Redirect each component's public finish label to the next phase.  Prove the
exact run against:

```lean
(encodeAffineConjunctionFrame
  (affineValidityFinalConjunctionFrame stackCount frame)).reverse ++ output
```

using `List.reverse_append` at every bridge.

- [ ] **Step 5: Prove the combined bound**

Expose:

```lean
theorem affineValidityFinalConjunctionSource_steps_le
    (stackCount : Nat)
    (frame : AffineValidityFinalConjunctionSourceFrame) :
    affineValidityFinalConjunctionSourceSteps stackCount frame ≤
      affineValidityFinalConjunctionSourceStepCoeff stackCount *
        (encodeAffineValidityFinalConjunctionSourceInvocation frame).length ^ 2 + 50
```

The coefficient depends only on fixed `stackCount`; combine the two established
component bounds and the linear unary-block emissions.

- [ ] **Step 6: Specialize to the Cook--Levin arithmetic frame**

Add:

```lean
noncomputable def arithmeticValidityFinalConjunctionSourceFrame
    (tm : Turing.FinTM2) (H start rowBase : Nat) :
    AffineValidityFinalConjunctionSourceFrame

theorem arithmeticValidityFinalConjunctionSourceFrame_eq
    (tm : Turing.FinTM2) (H start rowBase : Nat) :
    affineValidityFinalConjunctionFrame (arithmeticStackCount tm)
      (arithmeticValidityFinalConjunctionSourceFrame tm H start rowBase) =
    (arithmeticValidityTailFrame tm H start rowBase).finalFrame
```

Use `arithmeticFinalConjunctionWires_eq_semantic`; prove stack-wire equality
definitionally from `affineStackOutputWires` and
`arithmeticFinalConjunctionStackWires`.

- [ ] **Step 7: Verify and commit checkpoint 1**

```bash
lake env lean Tests/Chapter_34_PolyBuilder_AffineStackOutputFamilySource.lean
lake env lean Tests/Chapter_34_PolyBuilder_AffineValidityFinalConjunctionSource.lean
lake env lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowTailOperands.lean
lake build CLRSLean.Chapter_34
rg -n '^\s*(sorry|admit|axiom)\b' CLRSLean/Chapter_34 -g '*.lean'
git diff --check
git add CLRSLean/Chapter_34 Tests/Chapter_34_PolyBuilder_AffineStackOutputFamilySource.lean Tests/Chapter_34_PolyBuilder_AffineValidityFinalConjunctionSource.lean literate.toml docs/index.md
git commit -m "feat(ch34): link validity final conjunction source"
```

Expected: all Lean commands exit zero, the unfinished-declaration scan has no
matches, and the commit contains only checkpoint-1 files.

### Task 3: Complete validity-tail source from the raw word

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowTailSource.lean`
- Create: `Tests/Chapter_34_CookLevin_ValidityRowTailSource.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [ ] **Step 1: Pin the final public interface and run RED**

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource

open CLRS.Chapter34.Turing.CookLevin

#check verifierValidityRowTailOperandFrames_eq_canonical
#check verifierValidityRowTailOperandFrames_computableInPolyTime
#print axioms verifierValidityRowTailOperandFrames_computableInPolyTime
```

Run:

```bash
lake env lean Tests/Chapter_34_CookLevin_ValidityRowTailSource.lean
```

Expected: the computability declaration is missing.

- [ ] **Step 2: Define the one-row seed source**

```lean
def encodeValidityRowTailSourceSeed
    (seed : ValidityRowSeed) : List UnaryFrameSym :=
  encodeUnaryFrame [seed.height, seed.start, seed.rowBase]

def verifierValidityRowTailSourceProgram
    (tm : Turing.FinTM2) : Program UnaryFrameSym UnaryFrameSym
```

The program loads the three seed fields once.  Its fixed verifier-dependent
phases derive the six counters of each
`arithmeticRuntimeStackSourceSeed tm seed.height seed.start seed.rowBase k`,
redirect the existing runtime stack source, and then redirect the final-
conjunction source built from
`arithmeticValidityFinalConjunctionSourceFrame tm seed.height seed.start
seed.rowBase`.  Expose an exact one-row run whose output is:

```lean
(encodeAffineValidityTailFrame
  (validityRowSeedTailFrame tm seed)).reverse ++ output
```

- [ ] **Step 3: Lift the one-row source to the canonical seed family**

Use a family controller which loads one encoded `ValidityRowSeed`, runs the
complete tail source, clears its counters, and continues at the next seed.
Its exact family output is:

```lean
(verifierValidityRowSeeds W x).flatMap
  (fun seed => encodeAffineValidityTailFrame
    (validityRowSeedTailFrame W.machine.tm seed))
```

Rewrite with `validityRowSeedTailFamily_eq_canonical`.

- [ ] **Step 4: Package raw-input polynomial-time computation**

Compose the existing seed compiler with the seed-family tail source and expose:

```lean
noncomputable def verifierValidityRowTailOperandFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowTailOperandFrames W)
```

- [ ] **Step 5: Verify and commit checkpoint 2**

```bash
lake env lean Tests/Chapter_34_CookLevin_ValidityRowTailSource.lean
lake build CLRSLean.Chapter_34
rg -n '^\s*(sorry|admit|axiom)\b' CLRSLean/Chapter_34 -g '*.lean'
git diff --check
git add CLRSLean/Chapter_34 Tests/Chapter_34_CookLevin_ValidityRowTailSource.lean literate.toml docs/index.md
git commit -m "feat(ch34): compile validity row tail operands"
```

### Task 4: Delimiter-preserving complete row input

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowInputCompiler.lean`
- Create: `Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [ ] **Step 1: Write and run the failing milestone test**

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler

open CLRS.Chapter34.Turing.CookLevin

#check verifierValidityRowFamilyInput
#check verifierValidityRowFamilyInput_eq_canonical
#check verifierValidityRowFamilyInput_computableInPolyTime
#check verifierValidityRowFrames_computableInPolyTime

#print axioms verifierValidityRowFamilyInput_eq_canonical
#print axioms verifierValidityRowFamilyInput_computableInPolyTime
#print axioms verifierValidityRowFrames_computableInPolyTime
```

Run:

```bash
lake env lean Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean
```

Expected: missing-module failure.

- [ ] **Step 2: Implement the row-at-a-time source program**

Define a label sum containing the existing unary seed loader, structured
one-hot source, compact-frame expander, halted-triple emitter, complete tail
source, and counter-clear phases.  Its canonical public output function is:

```lean
noncomputable def verifierValidityRowFamilyInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List UnaryFrameSym :=
  verifierValidityRowSourceOutput W (verifierValidityRowSeeds W x)
```

Define the concrete source's semantic output recursively, before the verifier
specialization:

```lean
noncomputable def validityRowSeedFamilyInput
    (tm : Turing.FinTM2) : List ValidityRowSeed → List UnaryFrameSym
  | [] => [.frameEnd]
  | seed :: rest =>
      .tick ::
        (encodeAffineValidityRowFrame (expandValidityRowSeed tm seed) ++
          validityRowSeedFamilyInput tm rest)

noncomputable def verifierValidityRowSourceOutput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (seeds : List ValidityRowSeed) : List UnaryFrameSym :=
  validityRowSeedFamilyInput W.machine.tm seeds
```

For each seed, the exact-run theorem emits `.tick` followed by the one-hot
family, the two internal `frameEnd` bytes, the halted triple, and the complete
tail.  The empty seed tail emits exactly the final outer `frameEnd`.

- [ ] **Step 3: Prove exact canonical equality**

```lean
theorem verifierValidityRowFamilyInput_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    verifierValidityRowFamilyInput W x =
      encodeAffineValidityRowFamilyInput
        (verifierValidityRowFramesByLength W x.length)
```

Induct on `verifierValidityRowSeeds W x`, use
`verifierValidityRowSeeds_expand_eq_frames`, and rewrite each fragment with the
existing one-hot, halted, and tail canonical equalities.

- [ ] **Step 4: Prove and package polynomial runtime**

Bound one row by the sum of the reused component bounds plus counter clearing;
bound the row family by the square of its seed/source input length.  Compose
with `verifierValidityRowSeedFrames_computableInPolyTime W`.  Package the same
concrete source under both the byte-level public function and the structured
codomain required by the downstream controller:

```lean
noncomputable def verifierValidityRowFamilyInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowFamilyInput W)

noncomputable def verifierValidityRowFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Turing.TM2ComputableInPolyTime id
      encodeAffineValidityRowFamilyInput
      (fun x => verifierValidityRowFramesByLength W x.length)
```

The second declaration reuses the first declaration's machine, alphabets,
time polynomial, and `outputsFun`; its output proof rewrites through
`verifierValidityRowFamilyInput_eq_canonical`.

- [ ] **Step 5: Verify and commit checkpoint 3**

```bash
lake env lean Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean
lake build CLRSLean.Chapter_34
rg -n '^\s*(sorry|admit|axiom)\b' CLRSLean/Chapter_34 -g '*.lean'
git diff --check
git add CLRSLean/Chapter_34 Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean literate.toml docs/index.md
git commit -m "feat(ch34): compile complete validity row input"
```

### Task 5: Compose the complete validity gate stream

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowInputCompiler.lean`
- Modify: `Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: `README.md`

- [ ] **Step 1: Add the failing downstream interface**

```lean
#check verifierValidityGateStream_computableInPolyTime
#print axioms verifierValidityGateStream_computableInPolyTime
```

Run the focused test and verify the missing-name failure.

- [ ] **Step 2: Compose the two concrete machines**

```lean
noncomputable def verifierValidityGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Turing.TM2ComputableInPolyTime id id
      (verifierValidityGateStream W) := by
  let composed := Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (verifierValidityRowFrames_computableInPolyTime W)
    affineValidityRowFamilyGateStream_computableInPolyTime
  simpa [Function.comp_def, verifierValidityRowFramesByLength,
    arithmeticValidityRowsGateStream_eq_semantic,
    verifierValidityGateStream_eq_byLength] using Classical.choice composed
```

- [ ] **Step 3: Refresh the public progress ledger**

Add the new theorem group to Chapter 34 in `docs/clrs-proof-progress.csv`, then
run:

```bash
python3 scripts/check_progress_csv.py --write-dashboard
python3 scripts/gen_readme_table.py
```

- [ ] **Step 4: Run the complete acceptance gate**

```bash
lake env lean Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean
lake build CLRSLean.Chapter_34
lake build CLRSLean
python3 scripts/check_repository.py
rg -n '^\s*(sorry|admit|axiom)\b' CLRSLean/Chapter_34 -g '*.lean'
git diff --check
```

Expected: both builds and all repository checks pass, the scan has no matches,
and the headline axiom audit contains only the standard three axioms.

- [ ] **Step 5: Commit and push checkpoint 4**

```bash
git add CLRSLean/Chapter_34 Tests/Chapter_34_CookLevin_ValidityRowInputCompiler.lean docs/clrs-proof-progress.csv CLRSLean/Progress.lean README.md literate.toml docs/index.md
git commit -m "feat(ch34): compute verifier validity gate stream"
git push origin codex/ch34-validity-row-source
```

After the push, verify that `git ls-remote --heads origin
codex/ch34-validity-row-source` equals `git rev-parse HEAD`.
