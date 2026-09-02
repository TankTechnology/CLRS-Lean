import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader

/-!
# Exact Cook--Levin validity serialization prefix

The semantic validity builder now has a literal gate trace for every public
tableau row.  This module flattens that trace into the general-circuit wire
format, proves exact agreement with the proof-carrying validity family, and
advances the already verified header/input/pool prefix through the complete
validity phase.

Main results:

- {lit}`validCfgGatePolynomial_eval` and the validity cost/count clocks expose
  exact executable loop bounds for one row and the complete validity phase.
- {lit}`verifierRowWire_eq` and its field-specialized corollaries give closed
  arithmetic wire numbers for every verifier-row coordinate.
- {lit}`validityGateStreamAt_rows_eq` removes proof-carrying allocation data
  from the serializer target, leaving only height, horizon, row/gate bases,
  and explicit arithmetic row wires.
- {lit}`verifierValidityGateStream_rows_eq` exposes the complete validity
  phase as an exact row-major flattening with an explicit start index per row.
- {lit}`verifierValidityGateStream_eq_byLength` isolates the source-independent
  validity phase as a function of input length alone.
- {lit}`verifierValidityGateStream_eq` identifies the literal validity stream
  with the suffix appended by the semantic builder.
- {lit}`verifierCircuitValidityPrefix_eq` identifies the complete serialized
  prefix through row validity.
- {lit}`verifierCircuitValidityPrefix_isPrefix` proves that this stream is a
  literal prefix of the final verifier-circuit encoding.

Current gap:

- A concrete TM2 must compute the dimension-only arithmetic stream exposed by
  {lit}`validityGateStreamAt_rows_eq`; polynomial output length and exact clocks
  alone are deliberately not used as a computability argument.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing
open PolyBuilder

/-! ## Exact validity clocks -/

/-- Exact affine polynomial for the canonical-validity gate cost of one
bounded configuration row. -/
def validCfgGatePolynomial (tm : _root_.Turing.FinTM2) : Polynomial Nat := by
  letI : Fintype tm.K := tm.kFin
  exact Polynomial.C
      (3 * labelCount tm + 3 * stateCount tm + 20 +
        9 * Fintype.card tm.K) +
    Polynomial.C
      (∑ k : tm.K, (3 * (reachableAlphabet tm k).card + 19)) *
        Polynomial.X

/-- The affine polynomial agrees exactly with the semantic single-row gate
cost. -/
@[simp] theorem validCfgGatePolynomial_eval
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    (validCfgGatePolynomial tm).eval H = validCfgGateCost tm H := by
  letI : Fintype tm.K := tm.kFin
  simp only [validCfgGatePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  unfold validCfgGateCost
  rw [show
      (∑ k : tm.K,
        (H * (3 * (reachableAlphabet tm k).card + 19) + 9)) =
        H * (∑ k : tm.K,
          (3 * (reachableAlphabet tm k).card + 19)) +
          9 * Fintype.card tm.K by
    rw [Finset.sum_add_distrib]
    congr 1
    · exact (Finset.mul_sum Finset.univ
        (fun k : tm.K => 3 * (reachableAlphabet tm k).card + 19) H).symm
    · simp [Nat.mul_comm]]
  ring

/-- Exact input-length polynomial for one verifier row's validity-gate cost. -/
def verifierValidityRowCostPolynomial {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) : Polynomial Nat :=
  (validCfgGatePolynomial W.machine.tm).comp (verifierHeight W)

/-- Evaluation of the row-cost polynomial gives the semantic validity cost
at the verifier's exact height. -/
@[simp] theorem verifierValidityRowCostPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierValidityRowCostPolynomial W).eval n =
      validCfgGateCost W.machine.tm ((verifierHeight W).eval n) := by
  simp [verifierValidityRowCostPolynomial, Polynomial.eval_comp]

/-- Unary clock whose length is one exact verifier-row validity cost. -/
def verifierValidityRowCostClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock (verifierValidityRowCostPolynomial W) input

@[simp] theorem verifierValidityRowCostClock_length
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (verifierValidityRowCostClock W input).length =
      validCfgGateCost W.machine.tm
        ((verifierHeight W).eval input.length) := by
  simp [verifierValidityRowCostClock]

/-- Concrete polynomial-time TM2 producing the exact single-row cost clock. -/
noncomputable def verifierValidityRowCostClock_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierValidityRowCostClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime
    (verifierValidityRowCostPolynomial W)

/-- Exact polynomial for the number of gates in the complete row-validity
phase. -/
def verifierValidityGateCountPolynomial {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) : Polynomial Nat :=
  (verifierHorizon W + 1) * verifierValidityRowCostPolynomial W

/-- The total polynomial is exactly row count times exact single-row cost. -/
@[simp] theorem verifierValidityGateCountPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierValidityGateCountPolynomial W).eval n =
      tableauRowCount ((verifierHorizon W).eval n) *
        validCfgGateCost W.machine.tm ((verifierHeight W).eval n) := by
  simp [verifierValidityGateCountPolynomial, tableauRowCount,
    Polynomial.eval_add, Polynomial.eval_mul]

/-- Unary clock whose length is the exact number of validity gates across all
verifier tableau rows. -/
def verifierValidityGateCountClock {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List Unit :=
  exactPolynomialClock (verifierValidityGateCountPolynomial W) input

@[simp] theorem verifierValidityGateCountClock_length
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (verifierValidityGateCountClock W input).length =
      tableauRowCount ((verifierHorizon W).eval input.length) *
        validCfgGateCost W.machine.tm
          ((verifierHeight W).eval input.length) := by
  simp [verifierValidityGateCountClock]

/-- Concrete polynomial-time TM2 producing the exact complete validity gate
count clock. -/
noncomputable def verifierValidityGateCountClock_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TM2ComputableInPolyTime id id (verifierValidityGateCountClock W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialClock_computableInPolyTime
    (verifierValidityGateCountPolynomial W)

/-! ## Closed verifier-row wire formulas -/

/-- Pure arithmetic row-wire bundle at an arbitrary global wire base.  The
runtime height affects only the explicit local slot numbering. -/
def arithmeticCfgWires (tm : _root_.Turing.FinTM2) (H rowBase : Nat) :
    CfgWires tm H :=
  fun slot => rowBase + (cfgSlotEquivFin tm H slot).val

/-- The halted wire is the arithmetic row base. -/
@[simp] theorem arithmeticCfgWires_halted
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) :
    (arithmeticCfgWires tm H rowBase).halted = rowBase := by
  simp [arithmeticCfgWires, CfgBundle.halted]

/-- Arithmetic label-wire formula. -/
@[simp] theorem arithmeticCfgWires_label
    {tm : _root_.Turing.FinTM2} {H rowBase : Nat}
    (i : Fin (labelCount tm + 1)) :
    (arithmeticCfgWires tm H rowBase).label i =
      rowBase + (1 + i.val) := by
  simp [arithmeticCfgWires, CfgBundle.label]

/-- Arithmetic state-wire formula. -/
@[simp] theorem arithmeticCfgWires_state
    {tm : _root_.Turing.FinTM2} {H rowBase : Nat}
    (i : Fin (stateCount tm)) :
    (arithmeticCfgWires tm H rowBase).state i =
      rowBase + (1 + (labelCount tm + 1) + i.val) := by
  simp [arithmeticCfgWires, CfgBundle.state]

/-- Arithmetic stack-height wire formula. -/
@[simp] theorem arithmeticCfgWires_stackHeight
    {tm : _root_.Turing.FinTM2} {H rowBase : Nat}
    (k : tm.K) (i : Fin (H + 1)) :
    (arithmeticCfgWires tm H rowBase).stackHeight k i =
      rowBase + (1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H k + i.val) := by
  simp [arithmeticCfgWires, CfgBundle.stackHeight]

/-- Arithmetic stack-cell wire formula. -/
@[simp] theorem arithmeticCfgWires_stackCell
    {tm : _root_.Turing.FinTM2} {H rowBase : Nat}
    (k : tm.K) (i : Fin H)
    (a : Fin ((reachableAlphabet tm k).card + 1)) :
    (arithmeticCfgWires tm H rowBase).stackCell k i a =
      rowBase + (1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H k + (H + 1) +
          (a.val + ((reachableAlphabet tm k).card + 1) * i.val)) := by
  simp [arithmeticCfgWires, CfgBundle.stackCell, Nat.add_assoc]

/-- Every verifier-row coordinate has the closed global wire number obtained
by adding its explicit in-row coordinate to the row's fixed-width base. -/
theorem verifierRowWire_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length)))
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) :
    (verifierRows W input).rows row slot =
      row.val * cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length) +
        (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length) slot).val := by
  simpa [verifierRows, tableauStart, CircuitBuilder.empty] using
    (verifierRows W input).wire_eq row slot

/-- Canonical whole-tableau allocation is exactly the pure arithmetic bundle
at each fixed-width row base. -/
theorem allocateTableauRows_rows_eq_arithmetic
    (tm : _root_.Turing.FinTM2) (H T : Nat)
    (row : Fin (tableauRowCount T)) :
    (allocateTableauRows tm H T).rows row =
      arithmeticCfgWires tm H (row.val * cfgBitCount tm H) := by
  funext slot
  rw [(allocateTableauRows tm H T).wire_eq]
  simp [arithmeticCfgWires, tableauStart, CircuitBuilder.empty]

/-- The proof-carrying verifier allocation is pointwise identical to the pure
arithmetic bundle at the corresponding row base. -/
theorem verifierRowWires_eq_arithmetic {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length))) :
    (verifierRows W input).rows row =
      arithmeticCfgWires W.machine.tm
        ((verifierHeight W).eval input.length)
        (row.val * cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length)) := by
  funext slot
  rw [verifierRowWire_eq]
  rfl

/-- The halted bit is the first wire of its verifier tableau row. -/
theorem verifierRowHaltedWire_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length))) :
    (verifierRows W input).rows row
        (CfgSlot.halted W.machine.tm ((verifierHeight W).eval input.length)) =
      row.val * cfgBitCount W.machine.tm
        ((verifierHeight W).eval input.length) := by
  rw [verifierRowWire_eq, cfgSlotEquivFin_halted_val, Nat.add_zero]

/-- Label wires immediately follow the halted bit in every verifier row. -/
theorem verifierRowLabelWire_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length)))
    (i : Fin (labelCount W.machine.tm + 1)) :
    (verifierRows W input).rows row (CfgSlot.label i) =
      row.val * cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length) + (1 + i.val) := by
  rw [verifierRowWire_eq, cfgSlotEquivFin_label_val]

/-- State wires follow the halted and label blocks in every verifier row. -/
theorem verifierRowStateWire_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length)))
    (i : Fin (stateCount W.machine.tm)) :
    (verifierRows W input).rows row (CfgSlot.state i) =
      row.val * cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length) +
        (1 + (labelCount W.machine.tm + 1) + i.val) := by
  rw [verifierRowWire_eq, cfgSlotEquivFin_state_val]

/-- Stack-height wires have a fixed outer offset, the explicit stack prefix,
and their local height coordinate. -/
theorem verifierRowStackHeightWire_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length)))
    (k : W.machine.tm.K)
    (i : Fin ((verifierHeight W).eval input.length + 1)) :
    (verifierRows W input).rows row (CfgSlot.stackHeight k i) =
      row.val * cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length) +
        (1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
          cfgStackBitOffset W.machine.tm
            ((verifierHeight W).eval input.length) k + i.val) := by
  rw [verifierRowWire_eq, cfgSlotEquivFin_stackHeight_val]

/-- Stack-cell wires additionally include the height block and their
row-major cell/symbol coordinate. -/
theorem verifierRowStackCellWire_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length)))
    (k : W.machine.tm.K)
    (i : Fin ((verifierHeight W).eval input.length))
    (a : Fin ((reachableAlphabet W.machine.tm k).card + 1)) :
    (verifierRows W input).rows row (CfgSlot.stackCell k i a) =
      row.val * cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length) +
        (1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
          cfgStackBitOffset W.machine.tm
            ((verifierHeight W).eval input.length) k +
          (((verifierHeight W).eval input.length + 1) +
            (a.val + ((reachableAlphabet W.machine.tm k).card + 1) *
              i.val))) := by
  rw [verifierRowWire_eq, cfgSlotEquivFin_stackCell_val]
  simp only [Nat.add_assoc]

/-! ## Row-major validity layout -/

/-- The shared-pool builder has the exact tableau-input length plus its two
constant gates. -/
theorem verifierPoolGateCount_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (verifierPool W input).builder.gates.length =
      tableauInputCount W.machine.tm
          ((verifierHeight W).eval input.length)
          ((verifierHorizon W).eval input.length) + 2 := by
  rw [verifierPool, CircuitBuilder.allocateBoolWirePool_gate_delta]
  unfold verifierRows
  rw [allocateTableauRows_gate_delta]

/-- First fresh gate index assigned to one verifier row's canonical-validity
trace. -/
def verifierValidityRowStart {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length))) : Nat :=
  tableauInputCount W.machine.tm
      ((verifierHeight W).eval input.length)
      ((verifierHorizon W).eval input.length) + 2 +
    row.val * validCfgGateCost W.machine.tm
      ((verifierHeight W).eval input.length)

/-- Exact encoded validity-gate stream contributed by one verifier row. -/
def verifierRowValidityGateStream {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length))) :
    List CircuitSym :=
  (canonicalValidityGateTrace (verifierValidityRowStart W input row)
    ((verifierRows W input).rows row)).gates.flatMap encodeCircuitGate

/-- Exact one-row validity serialization from arithmetic dimensions only. -/
def validityRowGateStreamAt (tm : _root_.Turing.FinTM2)
    (H start rowBase : Nat) : List CircuitSym :=
  (canonicalValidityGateTrace start
    (arithmeticCfgWires tm H rowBase)).gates.flatMap encodeCircuitGate

/-- A verifier row's semantic stream is exactly the pure arithmetic row
serializer at its closed gate and wire bases. -/
theorem verifierRowValidityGateStream_eq_at
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval input.length))) :
    verifierRowValidityGateStream W input row =
      validityRowGateStreamAt W.machine.tm
        ((verifierHeight W).eval input.length)
        (verifierValidityRowStart W input row)
        (row.val * cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length)) := by
  simp only [verifierRowValidityGateStream, validityRowGateStreamAt]
  rw [verifierRowWires_eq_arithmetic]

private theorem flatMap_flatten_encodeCircuitGate
    (gateLists : List (List CircuitGate)) :
    gateLists.flatten.flatMap encodeCircuitGate =
      (gateLists.map (List.flatMap encodeCircuitGate)).flatten := by
  induction gateLists with
  | nil => rfl
  | cons gates rest ih => simp [ih]

/-! ## Literal validity gate stream -/

/-- Exact validity stream at explicit machine, height, and horizon dimensions.
It is independent of any source-alphabet symbols. -/
def validityGateStreamAt (tm : _root_.Turing.FinTM2) (H T : Nat) :
    List CircuitSym :=
  let rows := allocateTableauRows tm H T
  let pool := CircuitBuilder.allocateBoolWirePool rows.builder
  let trace := validCfgCircuitFamilyGateTrace pool.builder.gates.length
    (tableauRowCount T) rows.rows
  trace.gates.flatMap encodeCircuitGate

/-- The dimension-only validity stream is the row-major flattening of pure
arithmetic row serializers. -/
theorem validityGateStreamAt_rows_eq
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    validityGateStreamAt tm H T =
      (List.ofFn fun row : Fin (tableauRowCount T) =>
        validityRowGateStreamAt tm H
          (tableauInputCount tm H T + 2 +
            row.val * validCfgGateCost tm H)
          (row.val * cfgBitCount tm H)).flatten := by
  rw [validityGateStreamAt]
  rw [validCfgCircuitFamilyGateTrace_gates_eq_flatMap]
  rw [flatMap_flatten_encodeCircuitGate]
  rw [List.map_ofFn]
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext row
  simp only [validityRowGateStreamAt, Function.comp_apply]
  rw [CircuitBuilder.allocateBoolWirePool_gate_delta]
  rw [allocateTableauRows_gate_delta]
  rw [allocateTableauRows_rows_eq_arithmetic]

/-- The verifier validity stream as a function of source-input length only. -/
def verifierValidityGateStreamByLength {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (inputLength : Nat) : List CircuitSym :=
  validityGateStreamAt W.machine.tm
    ((verifierHeight W).eval inputLength)
    ((verifierHorizon W).eval inputLength)

/-- Serialized exact gate trace for canonical validity across all verifier
tableau rows. -/
def verifierValidityGateStream {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  let rows := verifierRows W input
  let pool := verifierPool W input
  let trace := validCfgCircuitFamilyGateTrace pool.builder.gates.length
    (tableauRowCount ((verifierHorizon W).eval input.length)) rows.rows
  trace.gates.flatMap encodeCircuitGate

/-- Canonical row validity depends on the source instance only through its
length; all source-symbol-dependent gates occur in later boundary phases. -/
theorem verifierValidityGateStream_eq_byLength {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierValidityGateStream W input =
      verifierValidityGateStreamByLength W input.length := by
  rfl

/-- The complete validity stream is a literal row-major flattening.  Row `r`
starts at the pool endpoint plus `r` exact single-row costs. -/
theorem verifierValidityGateStream_rows_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierValidityGateStream W input =
      (List.ofFn fun row :
          Fin (tableauRowCount ((verifierHorizon W).eval input.length)) =>
        verifierRowValidityGateStream W input row).flatten := by
  rw [verifierValidityGateStream]
  rw [validCfgCircuitFamilyGateTrace_gates_eq_flatMap]
  rw [flatMap_flatten_encodeCircuitGate]
  rw [List.map_ofFn]
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext row
  simp only [verifierRowValidityGateStream, verifierValidityRowStart]
  rw [verifierPoolGateCount_eq]
  rfl

/-- The literal stream is exactly the encoded suffix appended by the semantic
validity family. -/
theorem verifierValidityGateStream_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (verifierPool W input).builder.gates.flatMap encodeCircuitGate ++
        verifierValidityGateStream W input =
      (verifierValidity W input).builder.gates.flatMap encodeCircuitGate := by
  rw [verifierValidityGateStream, verifierValidity]
  rw [validCfgCircuitFamily_gates_eq, List.flatMap_append]

/-! ## Prefix through canonical row validity -/

/-- Exact circuit prefix through tableau inputs, the Boolean pool, and every
canonical row-validity gate. -/
def verifierCircuitValidityPrefix {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  verifierCircuitPoolPrefix W input ++ verifierValidityGateStream W input

/-- The generated stream agrees exactly with the semantic validity builder. -/
theorem verifierCircuitValidityPrefix_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitValidityPrefix W input =
      encNat (verifierCircuit W input).inputCount ++
        (verifierValidity W input).builder.gates.flatMap encodeCircuitGate := by
  rw [verifierCircuitValidityPrefix, verifierCircuitPoolPrefix_eq]
  rw [List.append_assoc, verifierValidityGateStream_eq]

/-- The validity builder remains an append-only prefix of the final
conjunction builder. -/
private theorem verifierValidity_extends_conjunction {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (input : List Γ) :
    (verifierValidity W input).builder.Extends
      (verifierConjunction W input).1 := by
  let transitionExtension := (verifierTransitions W input).extension
  let initialExtension := (verifierInitialBoundary W input).extension
  let inputExtension := (verifierInputBoundary W input).extension
  let acceptingExtension := (verifierAcceptingBoundary W input).extension
  let conjunctionExtension := CircuitBuilder.conjunction_extends
    (verifierAcceptingBoundary W input).builder
    (verifierConstraintWires W input) (verifierConstraintWires_valid W input)
  exact transitionExtension.trans (initialExtension.trans
    (inputExtension.trans (acceptingExtension.trans conjunctionExtension)))

/-- The exact validity-phase stream is a literal prefix of the complete
verifier-circuit encoding. -/
theorem verifierCircuitValidityPrefix_isPrefix
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitValidityPrefix W input <+:
      encodeCircuit (verifierCircuit W input) := by
  rcases (verifierValidity_extends_conjunction W input) with
    ⟨_, suffix, hgates⟩
  refine ⟨suffix.flatMap encodeCircuitGate ++
      .outputMark :: encNat (verifierCircuit W input).output, ?_⟩
  rw [verifierCircuitValidityPrefix_eq]
  change _ = encNat (verifierCircuit W input).inputCount ++
    (verifierCircuit W input).gates.flatMap encodeCircuitGate ++
      .outputMark :: encNat (verifierCircuit W input).output
  change (verifierCircuit W input).gates =
      (verifierValidity W input).builder.gates ++ suffix at hgates
  rw [hgates, List.flatMap_append]
  simp only [List.append_assoc]

end CLRS.Chapter34.Turing.CookLevin
