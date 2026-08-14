import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader

/-!
# Exact Cook--Levin validity serialization prefix

The semantic validity builder now has a literal gate trace for every public
tableau row.  This module flattens that trace into the general-circuit wire
format, proves exact agreement with the proof-carrying validity family, and
advances the already verified header/input/pool prefix through the complete
validity phase.

Main results:

- {lit}`verifierRowWire_eq` and its field-specialized corollaries give closed
  arithmetic wire numbers for every verifier-row coordinate.
- {lit}`verifierValidityGateStream_rows_eq` exposes the complete validity
  phase as an exact row-major flattening with an explicit start index per row.
- {lit}`verifierValidityGateStream_eq` identifies the literal validity stream
  with the suffix appended by the semantic builder.
- {lit}`verifierCircuitValidityPrefix_eq` identifies the complete serialized
  prefix through row validity.
- {lit}`verifierCircuitValidityPrefix_isPrefix` proves that this stream is a
  literal prefix of the final verifier-circuit encoding.

Current gap:

- A concrete TM2 must compute {lit}`verifierValidityGateStream`; polynomial
  output length alone is deliberately not used as a computability argument.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-! ## Closed verifier-row wire formulas -/

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

private theorem flatMap_flatten_encodeCircuitGate
    (gateLists : List (List CircuitGate)) :
    gateLists.flatten.flatMap encodeCircuitGate =
      (gateLists.map (List.flatMap encodeCircuitGate)).flatten := by
  induction gateLists with
  | nil => rfl
  | cons gates rest ih => simp [ih]

/-! ## Literal validity gate stream -/

/-- Serialized exact gate trace for canonical validity across all verifier
tableau rows. -/
def verifierValidityGateStream {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  let rows := verifierRows W input
  let pool := verifierPool W input
  let trace := validCfgCircuitFamilyGateTrace pool.builder.gates.length
    (tableauRowCount ((verifierHorizon W).eval input.length)) rows.rows
  trace.gates.flatMap encodeCircuitGate

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
