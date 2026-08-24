# Chapter 34 GeneralCircuitSAT-to-SAT Machine Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that `generalCircuitToSATMap` is computed by a fixed polynomial-time TM2, derive `GeneralCircuitSAT ≤p SAT`, and close `NPComplete CLIQUE` through the existing SAT-to-3-CNF-to-CLIQUE chain.

**Architecture:** Introduce a finite unary internal encoding for guarded, index-annotated circuits. A normalizer maps every raw circuit string to either one canonical valid record or one invalid sentinel; a formula emitter maps that record to the exact existing prefix-polish formula encoding. Compose the verified machines, then reuse the existing semantic theorem and reduction transitivity.

**Tech Stack:** Lean 4, Mathlib lists and polynomials, Chapter 34 `PolyTimeComputable` and `PolyTimeReducible`, Mathlib `FinTM2`, the repository's `PolyBuilder` reversal/composition infrastructure, and focused Lean interface tests.

---

## Checkpoint invariants

- Work only in `/home/ubuntu/clrs-lean-worktrees/codex/ch34-general-clique` on branch `codex/ch34-general-clique`.
- Keep semantic definitions, exact run proofs, and polynomial bounds in separate files.
- Preserve `generalCircuitToSATMap`, `CircuitSym`, `FormulaSym`, and all public language definitions.
- Introduce every public theorem through a failing `#check` before implementing it.
- Do not add `sorry`, `admit`, project axioms, or hypotheses that assume the intended output.
- Run each changed source and focused test before its commit, plus `git diff --check`.
- Do not publish `clique_npHard` or `clique_npComplete` until the composed all-input theorem is green.

## Task 1: Add the red public contract

**Files:**

- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_Machine.lean`
- Modify: `Tests/Chapter_34_GeneralClique_Interface.lean`

- [ ] Add the final API checks:

```lean
import CLRSLean.Chapter_34

namespace CLRS.Chapter34

#check Turing.GeneralCircuitToSAT.generalCircuitToSATMapComputableInPolyTime
#check Turing.GeneralCircuitToSAT.generalCircuitToSATRuntimePolynomial
#check Turing.GeneralCircuitToSAT.generalCircuitToSATMachine
#check Turing.GeneralCircuitToSAT.generalCircuitToSATMachine_outputs
#check generalCircuitSAT_reducible_to_SAT
#check clique_npHard
#check clique_npComplete

#print axioms Turing.GeneralCircuitToSAT.generalCircuitToSATMapComputableInPolyTime
#print axioms generalCircuitSAT_reducible_to_SAT
#print axioms clique_npComplete

end CLRS.Chapter34
```

- [ ] Run `lake env lean Tests/Chapter_34_GeneralCircuit_ToSAT_Machine.lean`; expect the first unknown identifier to be `generalCircuitToSATMapComputableInPolyTime`.
- [ ] Add the last three `#check`s to `Tests/Chapter_34_GeneralClique_Interface.lean`.
- [ ] Commit:

```bash
git add Tests/Chapter_34_GeneralCircuit_ToSAT_Machine.lean Tests/Chapter_34_GeneralClique_Interface.lean
git commit -m "test(ch34): specify circuit-to-SAT machine interface"
```

## Task 2: Define the guarded internal encoding

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/InternalEncoding/Basic.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/InternalEncoding/Parser.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/InternalEncoding/RoundTrip.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/InternalEncoding/Length.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/InternalEncoding.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_InternalEncoding.lean`

- [ ] Write failing checks for `NormalizedCircuitSym`, both codecs, both round-trip theorems, and `normalizeGeneralCircuit`.
- [ ] Define the finite work alphabet:

```lean
inductive NormalizedCircuitSym
  | invalidMark | validMark
  | inputCountMark | outputIndexMark | gateCountMark | gateRowMark
  | inputGateMark | constFalseMark | constTrueMark
  | notGateMark | andGateMark | orGateMark
  | tick | fieldEnd | rowEnd
  deriving DecidableEq, Repr, Fintype, Inhabited
```

- [ ] Encode a valid record as input count, output index, gate count, and chronological gate rows whose first unary field is the gate index. Implement a complete-consumption decoder that verifies the declared gate count and row indices.
- [ ] Prove:

```lean
theorem decode_encodeNormalizedCircuit (c : Circuit) :
    decodeNormalizedCircuit (encodeNormalizedCircuit c) = some c

def normalizeGeneralCircuit (input : List CircuitSym) :
    List NormalizedCircuitSym :=
  match decodeCircuit input with
  | some c => if c.WellFormed then encodeNormalizedCircuit c else [.invalidMark]
  | none => [.invalidMark]

theorem normalizeGeneralCircuit_eq_valid_iff (input) :
    (∃ c, normalizeGeneralCircuit input = encodeNormalizedCircuit c) ↔
      ∃ c, decodeCircuit input = some c ∧ c.WellFormed
```

- [ ] Prove coarse size bounds:

```lean
theorem encodeNormalizedCircuit_length_le (c : Circuit) :
    (encodeNormalizedCircuit c).length ≤ 8 * (encodeCircuit c).length + 8

theorem normalizeGeneralCircuit_length_le (input : List CircuitSym) :
    (normalizeGeneralCircuit input).length ≤ 8 * input.length + 8
```

- [ ] Run the focused test and facade build; commit `feat(ch34): define guarded circuit work encoding`.

## Task 3: Verify normalizer unary phases

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/Basic.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/Config.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/Steps.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/UnaryField.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/Cleanup.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_NormalizerUnary.lean`

- [ ] Add red checks for `program`, `inputCount_phase`, `operand_phase`, and `clearAndEmitInvalid_phase`.
- [ ] Define finite `Stack`, `Label`, and `State` types. Unbounded input count, gate count, gate index, operand, and saved values must live on unary `Unit` stacks; finite control stores only tags and optional symbol buffers.
- [ ] Prove local configuration equalities and the standard composition lemma:

```lean
theorem step_comp {A B C : Option machine.Cfg} (n₁ n₂ : Nat)
    (h₁ : transition^[n₁] A = B) (h₂ : transition^[n₂] B = C) :
    transition^[n₁ + n₂] A = C
```

- [ ] Prove exact parsing, copying, comparison, and restoration phases for unary fields, stating every touched stack in the postcondition.
- [ ] Route all failures through one cleanup theorem ending with output `[NormalizedCircuitSym.invalidMark]` and empty non-output stacks.
- [ ] Run the focused test and `Normalizer.UnaryField` build; commit `feat(ch34): verify circuit normalizer unary phases`.

## Task 4: Verify gate-row normalization

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/GateInput.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/GateConstant.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/GateUnary.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/GateBinary.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/GateFamily.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_NormalizerGates.lean`

- [ ] Add one failing phase check for each gate constructor and the complete family.
- [ ] Prove `.input i` succeeds exactly under `i < inputCount`; constants always append their fixed row and advance the gate counter.
- [ ] Prove `.not source`, `.and left right`, and `.or left right` succeed exactly when dependencies are below the current gate index.
- [ ] Prove each successful phase appends exactly `encodeNormalizedGateRow`, restores counters, and starts the next row. Prove the first-invalid-row rejection theorem separately.
- [ ] Lift the row theorem by induction to the whole gate list under `Circuit.WellFormed`'s gate-validity field.
- [ ] Run the focused test and `Normalizer.GateFamily` build; commit `proof(ch34): normalize well-formed circuit gate rows`.

## Task 5: Close all-input normalizer semantics

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/CanonicalRun.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/MalformedRun.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/Run.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_NormalizerRun.lean`

- [ ] Add red checks for `canonical_run`, `malformed_run`, and `outputs`.
- [ ] Prove a well-formed `encodeCircuit c` outputs `encodeNormalizedCircuit c` and an ill-formed canonical circuit outputs the invalid sentinel.
- [ ] For `decodeCircuit input = none`, follow the grammar to the first malformed phase and prove bounded cleanup; do not rely on executable fuel tests.
- [ ] Use `encodeCircuit_of_decodeCircuit_eq_some` to publish:

```lean
theorem outputs (input : List CircuitSym) :
    ∃ steps, _root_.Turing.TM2OutputsInTime machine input
      (some (normalizeGeneralCircuit input)) steps
```

- [ ] Run the focused test and normalizer facade build; commit `proof(ch34): close guarded circuit normalizer semantics`.

## Task 6: Prove the normalizer polynomial bound

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/Runtime.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/RejectBounds.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Normalizer/PolynomialRuntime.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_NormalizerRuntime.lean`

- [ ] Add red checks for `runtimePolynomial` and `computableInPolyTime`.
- [ ] Sum exact phase costs and dominate successful runs by the explicit sextic polynomial below in raw input length.
- [ ] Bound every malformed and ill-formed cleanup route by the same polynomial, including truncated fields, wrong tags, trailing garbage, invalid dependencies, and bad output indices.
- [ ] Package:

```lean
noncomputable def runtimePolynomial : Polynomial Nat :=
  1048576 * (Polynomial.X + 1) ^ 6 + 1048576

noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id normalizeGeneralCircuit :=
  { tm := machine
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := runtimePolynomial
    outputsFun := allInputsWithinPolynomial }
```

- [ ] Run the focused runtime test and build; commit `proof(ch34): bound guarded circuit normalization`.

## Task 7: Expose the exact list-level formula stream

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/Encoding.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/Semantics.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_EmitterEncoding.lean`

- [ ] Add red checks for the gate expression, gate formula, gate family, whole formula, and total emitter functions.
- [ ] Define `generalCircuitGateExprList`, `generalCircuitGateFormulaList`, and:

```lean
def generalCircuitGateFamilyList (c : Circuit) : List FormulaSym :=
  c.gates.zipIdx.flatMap
    (fun row => .andMark :: generalCircuitGateFormulaList c row.2 row.1) ++
    [.lit true]

def generalCircuitFormulaList (c : Circuit) : List FormulaSym :=
  .andMark :: (varEnc (c.inputCount + c.output) ++
    generalCircuitGateFamilyList c)
```

- [ ] Prove one expression lemma, one gate-formula lemma, and an indexed gate-list induction yielding:

```lean
theorem generalCircuitFormulaList_eq_enc (c : Circuit) :
    generalCircuitFormulaList c = enc (generalCircuitToFormula c)
```

- [ ] Define the total function and prove its bridge:

```lean
def emitNormalizedCircuitFormula (input : List NormalizedCircuitSym) :
    List FormulaSym :=
  match decodeNormalizedCircuit input with
  | some c => generalCircuitFormulaList c
  | none => enc (.const false)

theorem emit_normalize_eq (input : List CircuitSym) :
    emitNormalizedCircuitFormula (normalizeGeneralCircuit input) =
      generalCircuitToSATMap input
```

- [ ] Run the focused test and semantics build; commit `proof(ch34): expose exact general-circuit formula stream`.

## Task 8: Verify variable and gate emission

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/Basic.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/Config.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/Variable.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/GateInput.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/GateConstant.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/GateUnary.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/GateBinary.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_EmitterGate.lean`

- [ ] Add red checks for `variable_phase` and all six gate phases.
- [ ] Define a controller with separate unary stacks for input count, current gate index, and current operand, plus a staged reverse-output stack.
- [ ] Prove a restoring copy phase emits `varEnc (a + b)` while preserving both unary sources. Prove `varEnc i` separately for input gates, which do not use the input-count offset.
- [ ] Prove every gate phase emits exactly `generalCircuitGateFormulaList c i gate` and positions the parser at the next row. Reuse `variable_phase` instead of duplicating counter proofs.
- [ ] Run the focused test and `Emitter.GateBinary` build; commit `proof(ch34): verify circuit-to-formula gate emission`.

## Task 9: Close all-input formula emission

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/GateFamily.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/InvalidRun.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/CanonicalRun.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/Run.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_EmitterRun.lean`

- [ ] Add red checks for the family phase, invalid run, canonical run, and total output theorem.
- [ ] Induct over annotated gate rows, append `FormulaSym.lit true`, and invoke the existing verified reversal only at the final boundary.
- [ ] Prove canonical and invalid contracts:

```lean
theorem canonical_run (c : Circuit) :
    ∃ steps, _root_.Turing.TM2OutputsInTime machine
      (encodeNormalizedCircuit c) (some (generalCircuitFormulaList c)) steps

theorem invalid_run :
    ∃ steps, _root_.Turing.TM2OutputsInTime machine [.invalidMark]
      (some (enc (.const false))) steps
```

- [ ] Prove malformed internal records also produce `enc (.const false)` and publish total `outputs` for `emitNormalizedCircuitFormula`.
- [ ] Run the focused test and emitter facade build; commit `proof(ch34): close total circuit formula emission`.

## Task 10: Prove the emitter polynomial bound

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/Runtime.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/RejectBounds.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Emitter/PolynomialRuntime.lean`
- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT_EmitterRuntime.lean`

- [ ] Add red checks for `Emitter.runtimePolynomial` and `Emitter.computableInPolyTime`.
- [ ] Bound every restoring unary copy by internal input length, every row by a quadratic polynomial, and the complete family plus cleanup by `1048576 * (Polynomial.X + 1) ^ 6 + 1048576`.
- [ ] Package `TM2ComputableInPolyTime id id emitNormalizedCircuitFormula` exactly as in Task 6, using that fixed emitter runtime polynomial.
- [ ] Run the focused test and runtime build; commit `proof(ch34): bound circuit formula emission`.

## Task 11: Compose the exact reduction machine

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine/Composition.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Machine.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT.lean`
- Modify: `Tests/Chapter_34_GeneralCircuit_ToSAT_Machine.lean`

- [ ] Restate `emit_normalize_eq` at the composition namespace.
- [ ] Compose the concrete witnesses:

```lean
noncomputable def generalCircuitToSATMapComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id generalCircuitToSATMap := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      Normalizer.computableInPolyTime Emitter.computableInPolyTime
  obtain ⟨machine⟩ := composed
  simpa only [Function.comp_apply, emit_normalize_eq] using machine
```

- [ ] Publish the named polynomial, fixed machine, and exact output theorem:

```lean
noncomputable def generalCircuitToSATRuntimePolynomial : Polynomial Nat :=
  generalCircuitToSATMapComputableInPolyTime.time

noncomputable def generalCircuitToSATMachine : _root_.Turing.FinTM2 :=
  generalCircuitToSATMapComputableInPolyTime.tm
```

- [ ] Make the machine portion of the public contract green; commit `feat(ch34): compute general circuit reduction in polynomial time`.

## Task 12: Close the reduction and `NPComplete CLIQUE`

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Reduction.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique/Completeness.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralClique.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `Tests/Chapter_34_GeneralCircuit_ToSAT_Machine.lean`
- Modify: `Tests/Chapter_34_GeneralClique_Interface.lean`
- Modify: `Tests/Chapter_34_Interface.lean`

- [ ] Assemble the direct reduction:

```lean
theorem generalCircuitSAT_reducible_to_SAT :
    PolyTimeReducible GeneralCircuitSAT SAT := by
  refine ⟨generalCircuitToSATMap,
    ⟨Turing.GeneralCircuitToSAT.generalCircuitToSATMapComputableInPolyTime⟩,
    ?_⟩
  intro input
  exact (generalCircuitToSATMap_mem_SAT_iff input).symm
```

- [ ] Compose the chain and hardness:

```lean
theorem generalCircuitSAT_reducible_to_CLIQUE :
    PolyTimeReducible GeneralCircuitSAT CLIQUE :=
  (generalCircuitSAT_reducible_to_SAT.trans
    Turing.TM3CNF.sat_reducible_to_threeCNFSat).trans
      Turing.TMClique.threeCNFSat_reducible_to_CLIQUE

theorem clique_npHard : NPHard CLIQUE :=
  NPHard.of_reducible Turing.CookLevin.generalCircuitSAT_npHard
    generalCircuitSAT_reducible_to_CLIQUE

theorem clique_npComplete : NPComplete CLIQUE :=
  ⟨generalCLIQUE_polyTimeVerifiable, clique_npHard⟩
```

- [ ] Run `Tests/Chapter_34_GeneralCircuit_ToSAT_Machine.lean`, `Tests/Chapter_34_GeneralClique_Interface.lean`, and `Tests/Chapter_34_Interface.lean`; confirm the axiom audit contains no `sorryAx`.
- [ ] Commit `proof(ch34): prove general CLIQUE NP-complete`.

## Task 13: Documentation, navigation, and final audit

**Files:**

- Modify: `CLRSLean/FourthEdition/Chapter_34.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-status-board.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/migrations/clrs4.md`
- Modify: `docs/clrs-fourth-edition-map.csv`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Progress.lean`
- Modify: `README.md`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/superpowers/plans/2026-08-24-ch34-general-circuit-to-sat-machine.md`

- [ ] Record exactly that Section 34.4 has a concrete reduction chain and `NPComplete CLIQUE`; keep Section 34.5 problems explicitly open.
- [ ] Register every small module in Chapter 34 imports and `literate.toml`, then regenerate repository summaries with the checked-in scripts.
- [ ] Run the final gate:

```bash
lake env lean Tests/Chapter_34_GeneralCircuit_ToSAT_Machine.lean
lake env lean Tests/Chapter_34_GeneralClique_Interface.lean
lake env lean Tests/Chapter_34_Interface.lean
lake build CLRSLean.Chapter_34
lake build CLRSLean.FourthEdition.Chapter_34 CLRSLean.Status CLRSLean.Progress
python3 scripts/check_literate_config.py
python3 scripts/check_site_consistency.py
python3 scripts/check_repository.py
git diff --check
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT Tests/Chapter_34_GeneralCircuit_ToSAT_Machine.lean
```

- [ ] Review `git status --short --branch`, `git diff --stat origin/main...HEAD`, and `git diff --check origin/main...HEAD`.
- [ ] Commit `docs(ch34): record Section 34.4 reduction closure`.
- [ ] Stop before push, merge, or remote history mutation; report exact commands and remaining Section 34.5 gaps to the user.
