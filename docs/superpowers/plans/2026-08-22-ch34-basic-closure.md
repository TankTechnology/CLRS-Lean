# Chapter 34 Basic Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:executing-plans` to implement this plan task-by-task.  Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a truthful textbook-level semantic and polynomial-size reduction
bridge from honest serialized general-circuit satisfiability to SAT, then align
the Chapter 34 public interface and status documents with the proved boundary.

**Architecture:** Reuse the existing `Formula`, `FormulaSym`, `enc`, `decode`,
`Circuit`, `CircuitSym`, and `decodeCircuit` definitions.  Assign formula
variables `0 .. c.inputCount - 1` to circuit inputs and variables
`c.inputCount + j` to gate outputs; conjoin one gate equation per gate and assert
the designated output.  Keep semantic correctness and serialized size
accounting in separate small modules.

**Tech Stack:** Lean 4, Mathlib, `lake`, CLRS-Lean's Chapter 34 circuit and SAT
encodings, repository policy scripts.

---

### Task 1: Freeze the public interface with a failing test

**Files:**

- Create: `Tests/Chapter_34_GeneralCircuit_ToSAT.lean`

- [ ] **Step 1: Add the unresolved public interface test**

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT

open CLRS Chapter34

#check generalCircuitToFormula
#check generalCircuitSatisfiable_iff_satisfiable_generalCircuitToFormula
#check generalCircuitToSATMap
#check generalCircuitToSATMap_mem_SAT_iff
#check generalCircuitToSATMap_length_le

#print axioms generalCircuitSatisfiable_iff_satisfiable_generalCircuitToFormula
#print axioms generalCircuitToSATMap_mem_SAT_iff
#print axioms generalCircuitToSATMap_length_le
```

- [ ] **Step 2: Run the test and confirm the expected red state**

Run:

```bash
lake env lean Tests/Chapter_34_GeneralCircuit_ToSAT.lean
```

Expected: failure because
`CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT`
does not exist.

- [ ] **Step 3: Commit the red interface checkpoint**

```bash
git add Tests/Chapter_34_GeneralCircuit_ToSAT.lean
git commit -m "test(ch34): specify general-circuit to SAT bridge"
```

### Task 2: Prove direct general-circuit formula semantics

**Files:**

- Create:
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Semantics.lean`
- Test: `Tests/Chapter_34_GeneralCircuit_ToSAT.lean`

- [ ] **Step 1: Define the variable layout and gate formulas**

Add definitions with these exact public types:

```lean
def generalCircuitGateVar (c : Circuit) (gateIndex : Nat) : Nat :=
  c.inputCount + gateIndex

def generalCircuitGateExpr (c : Circuit) : CircuitGate → Formula
  | .input inputIndex => .var inputIndex
  | .const value => .const value
  | .not source => .not (.var (generalCircuitGateVar c source))
  | .and left right =>
      .and (.var (generalCircuitGateVar c left))
        (.var (generalCircuitGateVar c right))
  | .or left right =>
      .or (.var (generalCircuitGateVar c left))
        (.var (generalCircuitGateVar c right))

def generalCircuitGateFormula (c : Circuit) (gateIndex : Nat)
    (gate : CircuitGate) : Formula :=
  .iff (.var (generalCircuitGateVar c gateIndex))
    (generalCircuitGateExpr c gate)

def generalCircuitGateFormulasAux (c : Circuit) : Nat → List CircuitGate → Formula
  | _, [] => .const true
  | gateIndex, gate :: gates =>
      .and (generalCircuitGateFormula c gateIndex gate)
        (generalCircuitGateFormulasAux c (gateIndex + 1) gates)

def generalCircuitToFormula (c : Circuit) : Formula :=
  .and (.var (generalCircuitGateVar c c.output))
    (generalCircuitGateFormulasAux c 0 c.gates)
```

- [ ] **Step 2: Prove completeness under the canonical combined assignment**

Define the combined assignment by reading declared input variables below
`c.inputCount` and gate values at offsets above it.  Prove by list induction
that every generated gate equation evaluates to true under this assignment,
using `Circuit.evalValues_getElem_eq_gateEquation` for the five gate cases.

The public completeness lemma must have this type:

```lean
lemma generalCircuitSatisfiable_implies_formulaSatisfiable (c : Circuit) :
    GeneralCircuitSatisfiable c →
      Formula.Satisfiable (generalCircuitToFormula c)
```

- [ ] **Step 3: Prove soundness by gate-index induction**

From a satisfying formula assignment `tau`, first project every individual
gate equation from `generalCircuitGateFormulasAux`.  Then prove, by induction on
the gate list, that `tau (c.inputCount + j)` equals the evaluator's stored value
at gate `j`.  Use `CircuitGate.ValidAt` to justify all predecessor lookups and
`Circuit.eval_eq_getElem` to recover the designated output.

The public soundness lemma must have this type:

```lean
lemma formulaSatisfiable_implies_generalCircuitSatisfiable (c : Circuit)
    (hwellFormed : c.WellFormed) :
    Formula.Satisfiable (generalCircuitToFormula c) →
      GeneralCircuitSatisfiable c
```

- [ ] **Step 4: Assemble the textbook semantic equivalence**

```lean
theorem generalCircuitSatisfiable_iff_satisfiable_generalCircuitToFormula
    (c : Circuit) (hwellFormed : c.WellFormed) :
    GeneralCircuitSatisfiable c ↔
      Formula.Satisfiable (generalCircuitToFormula c) :=
  ⟨generalCircuitSatisfiable_implies_formulaSatisfiable c,
    formulaSatisfiable_implies_generalCircuitSatisfiable c hwellFormed⟩
```

- [ ] **Step 5: Run the focused source check**

```bash
lake env lean \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Semantics.lean
```

Expected: exit 0 with no proof errors.

- [ ] **Step 6: Commit the semantic bridge**

```bash
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Semantics.lean
git commit -m "feat(ch34): prove general-circuit SAT formula semantics"
```

### Task 3: Add the total serialized map and polynomial output bound

**Files:**

- Create:
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Encoding.lean`
- Test: `Tests/Chapter_34_GeneralCircuit_ToSAT.lean`

- [ ] **Step 1: Define the total map**

```lean
def generalCircuitToSATMap (input : List CircuitSym) : List FormulaSym :=
  match decodeCircuit input with
  | some c =>
      if h : c.WellFormed then enc (generalCircuitToFormula c)
      else enc (.const false)
  | none => enc (.const false)
```

- [ ] **Step 2: Prove canonical and raw-input membership semantics**

Use `decodeCircuit_encodeCircuit`, `encodeCircuit_of_decodeCircuit_eq_some`,
`decode_enc`, and the semantic theorem from Task 2.  Publish:

```lean
lemma generalCircuitToSATMap_encodeCircuit (c : Circuit)
    (h : c.WellFormed) :
    generalCircuitToSATMap (encodeCircuit c) =
      enc (generalCircuitToFormula c)

theorem generalCircuitToSATMap_mem_SAT_iff (input : List CircuitSym) :
    generalCircuitToSATMap input ∈ SAT ↔ input ∈ GeneralCircuitSAT
```

The `decodeCircuit = none` and decoded-but-ill-formed branches must reduce to
`Formula.const false`, so the theorem has no premises.

- [ ] **Step 3: Prove structural formula-encoding bounds**

Prove `varEnc` and each gate formula are bounded by an affine function of
`c.inputCount + c.gates.length`.  Sum over the gate list, then use
`inputCount_lt_length_of_decodeCircuit_eq_some` and a gate-count-from-decoding
lemma to obtain the public raw-input bound:

```lean
theorem generalCircuitToSATMap_length_le (input : List CircuitSym) :
    (generalCircuitToSATMap input).length ≤
      32 * (input.length + 1) ^ 3
```

The constant `32` is deliberately coarse; no tight encoding theorem is needed
for the textbook boundary.

- [ ] **Step 4: Run focused checks**

```bash
lake env lean \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Encoding.lean
```

Expected: exit 0.

- [ ] **Step 5: Commit the serialized bridge**

```bash
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT/Encoding.lean
git commit -m "feat(ch34): serialize general-circuit to SAT reduction"
```

### Task 4: Publish the facade and make the interface green

**Files:**

- Create:
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT.lean`
- Modify:
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `literate.toml`
- Test: `Tests/Chapter_34_GeneralCircuit_ToSAT.lean`

- [ ] **Step 1: Add the stable facade**

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Encoding

/-!
# General circuit satisfiability to SAT

This facade exports the textbook semantic translation and its total serialized
polynomial-size map.  A concrete polynomial-time TM2 for the map is a separate
refinement boundary.
-/
```

- [ ] **Step 2: Import the facade through Chapter 34 aggregators**

Add the `GeneralCircuit.ToSAT` import to the general-circuit facade, §34.4
facade, and `CLRSLean/Chapter_34.lean`.  Add the two child modules under the
facade's module list in `literate.toml`.

- [ ] **Step 3: Run the interface test and Chapter 34 build**

```bash
lake env lean Tests/Chapter_34_GeneralCircuit_ToSAT.lean
lake build CLRSLean.Chapter_34
```

Expected: both commands exit 0; `#print axioms` reports only standard Lean or
Mathlib foundations and no project-local axiom.

- [ ] **Step 4: Commit the public interface**

```bash
git add \
  CLRSLean/Chapter_34.lean \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit.lean \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/ToSAT.lean \
  Tests/Chapter_34_GeneralCircuit_ToSAT.lean \
  literate.toml
git commit -m "feat(ch34): publish general-circuit to SAT interface"
```

### Task 5: Reconcile Chapter 34 documentation

**Files:**

- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_34.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-map.md`
- Modify: `docs/proof-status-board.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/clrs-fourth-edition-map.csv`
- Modify: `docs/index.md`
- Modify:
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean`
- Modify:
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/SatTo3CNFSat.lean`
- Modify:
  `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/SatTo3CNFMachine.lean`

- [ ] **Step 1: Remove stale Cook--Levin gap claims**

Replace statements claiming that the concrete Cook--Levin generator,
`NPHard GeneralCircuitSAT`, or `NPComplete GeneralCircuitSAT` remain open with
the compiled theorem names `cookLevinMap_polyTimeComputable`,
`cookLevin_theorem`, `generalCircuitSAT_npHard`, and
`generalCircuitSAT_npComplete`.

- [ ] **Step 2: Record the new exact boundary**

State that the direct general-circuit-to-SAT semantic equivalence and total
polynomial-size serialized map are proved.  State separately that the fixed TM2
for this new map, SAT's concrete NP verifier, honest general graph-plus-`k`
CLIQUE, and Section 34.5 remain open.  Keep Chapter 34 status `partial`.

- [ ] **Step 3: Remove obsolete deferred-build prose**

Update the SAT-to-3-CNF source documentation that still says repository-wide
acceptance was deliberately deferred; the repository build has since passed.

- [ ] **Step 4: Run status and repository checks**

```bash
python3 scripts/check_progress_csv.py
python3 scripts/check_repository.py
git diff --check
```

Expected: all commands exit 0.

- [ ] **Step 5: Commit documentation reconciliation**

```bash
git add CLRSLean/Chapter_34.lean CLRSLean/FourthEdition/Chapter_34.lean \
  CLRSLean/Status.lean docs/proof-map.md docs/proof-status-board.md \
  docs/clrs-proof-progress.csv docs/clrs-fourth-edition-map.csv docs/index.md \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/SatTo3CNFSat.lean \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/SatTo3CNFMachine.lean
git commit -m "docs(ch34): record basic textbook closure boundary"
```

### Task 6: Final acceptance gate

**Files:**

- Verify all files changed by Tasks 1--5.

- [ ] **Step 1: Audit unfinished declarations**

```bash
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_34 \
  Tests/Chapter_34_GeneralCircuit_ToSAT.lean -g '*.lean'
```

Expected: no executable proof holes; comment-only occurrences, if any, are
reviewed and not counted as declarations.

- [ ] **Step 2: Run focused and repository verification**

```bash
lake env lean Tests/Chapter_34_GeneralCircuit_ToSAT.lean
lake env lean Tests/Chapter_34_CookLevin_MainTheorem.lean
python3 scripts/check_repository.py
git diff --check
lake build CLRSLean
```

Expected: every command exits 0.

- [ ] **Step 3: Review the final diff and commit any verification-only fixes**

```bash
git status --short
git diff --stat main...HEAD
git log --oneline --decorate main..HEAD
```

Expected: only the scoped Chapter 34 proof, tests, plan/spec, import metadata,
and status documents differ from `main`.
