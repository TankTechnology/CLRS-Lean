import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Variable

/-! # General-circuit formula emitter: input, constant, and NOT gates -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open StateTransition

private abbrev transition := flip Option.bind step

private theorem replicate_end_append_cons (count : Nat)
    (output : List FormulaSym) :
    List.replicate count .endMark ++ .endMark :: output =
      .endMark :: (List.replicate count .endMark ++ output) := by
  induction count with
  | zero => simp
  | succ count ih => simp [List.replicate_succ, ih]

private theorem inputOperandTicks_phase (state : State) (inputIndex : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount : Nat) :
    transition^[inputIndex + 1]
      (some (cfg (some .parseInputOperand) state
        (encodeNormalizedNat inputIndex ++ input) output inputCount 0)) =
    some (cfg (some .expectRowEnd)
      { state with inputBuffer := some .fieldEnd } input
      (List.replicate (inputIndex + 1) .endMark ++ output) inputCount 0) := by
  induction inputIndex generalizing state output with
  | zero =>
      change step (cfg (some .parseInputOperand) state
        (.fieldEnd :: input) output inputCount 0) = _
      simpa [encodeNormalizedNat] using
        input_operand_end_step state input output inputCount 0
  | succ inputIndex ih =>
      have hfirst := input_operand_tick_step state
        (encodeNormalizedNat inputIndex ++ input) output inputCount 0
      have htail := ih { state with inputBuffer := some .tick }
        (.endMark :: output)
      have hfull := step_then (inputIndex + 1) hfirst htail
      simpa [encodeNormalizedNat, List.replicate_succ,
        replicate_end_append_cons, List.append_assoc] using hfull

/-- Direct unary variable used by an input gate (without the circuit-input
prefix offset). -/
theorem inputOperand_phase (state : State) (inputIndex : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount : Nat) :
    transition^[inputIndex + 1]
      (some (cfg (some .parseInputOperand) state
        (encodeNormalizedNat inputIndex ++ input) (.varMark :: output)
        inputCount 0)) =
    some (cfg (some .expectRowEnd)
      { state with inputBuffer := some .fieldEnd } input
      ((varEnc inputIndex).reverse ++ output) inputCount 0) := by
  simpa [varEnc, List.reverse_cons, List.append_assoc] using
    inputOperandTicks_phase state inputIndex input (.varMark :: output)
      inputCount

def inputGateSteps (inputIndex : Nat) : Nat := inputIndex + 2

theorem inputGate_phase (state : State) (inputCount inputIndex : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym) :
    ∃ finalState,
      transition^[inputGateSteps inputIndex]
        (some (cfg (some .gateTag) state
          (encodeNormalizedGate (.input inputIndex) ++ .rowEnd :: input)
          output inputCount 0)) =
      some (cfg (some .expectRowEnd) finalState (.rowEnd :: input)
        ((generalCircuitGateExprList inputCount (.input inputIndex)).reverse ++
          output) inputCount 0) := by
  have hfirst := gate_tag_input_step state
    (encodeNormalizedNat inputIndex ++ .rowEnd :: input) output inputCount 0
  have htail := inputOperand_phase
    { state with inputBuffer := some .inputGateMark } inputIndex
    (.rowEnd :: input) output inputCount
  refine ⟨{ state with inputBuffer := some .fieldEnd }, ?_⟩
  simpa [inputGateSteps, encodeNormalizedGate,
    generalCircuitGateExprList] using
      step_then (inputIndex + 1) hfirst htail

def constantGateSteps : Nat := 1

theorem constantGate_phase (state : State) (inputCount : Nat) (value : Bool)
    (input : List NormalizedCircuitSym) (output : List FormulaSym) :
    ∃ finalState,
      transition^[constantGateSteps]
        (some (cfg (some .gateTag) state
          (encodeNormalizedGate (.const value) ++ .rowEnd :: input)
          output inputCount 0)) =
      some (cfg (some .expectRowEnd) finalState (.rowEnd :: input)
        ((generalCircuitGateExprList inputCount (.const value)).reverse ++
          output) inputCount 0) := by
  cases value with
  | false =>
      refine ⟨{ state with inputBuffer := some .constFalseMark }, ?_⟩
      change step (cfg (some .gateTag) state
        (.constFalseMark :: .rowEnd :: input) output inputCount 0) = _
      simpa [constantGateSteps, encodeNormalizedGate,
        generalCircuitGateExprList] using
          gate_tag_const_false_step state (.rowEnd :: input) output inputCount 0
  | true =>
      refine ⟨{ state with inputBuffer := some .constTrueMark }, ?_⟩
      change step (cfg (some .gateTag) state
        (.constTrueMark :: .rowEnd :: input) output inputCount 0) = _
      simpa [constantGateSteps, encodeNormalizedGate,
        generalCircuitGateExprList] using
          gate_tag_const_true_step state (.rowEnd :: input) output inputCount 0

def notGateSteps (inputCount source : Nat) : Nat :=
  1 + ((2 * inputCount + 2) + (source + 1))

theorem notGate_phase (state : State) (inputCount source : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym) :
    ∃ finalState,
      transition^[notGateSteps inputCount source]
        (some (cfg (some .gateTag) state
          (encodeNormalizedGate (.not source) ++ .rowEnd :: input)
          output inputCount 0)) =
      some (cfg (some .expectRowEnd) finalState (.rowEnd :: input)
        ((generalCircuitGateExprList inputCount (.not source)).reverse ++
          output) inputCount 0) := by
  have hfirst := gate_tag_not_step state
    (encodeNormalizedNat source ++ .rowEnd :: input) output inputCount 0
  rcases variable_phase { state with inputBuffer := some .notGateMark }
      .notSource inputCount source (.rowEnd :: input) (.notMark :: output) with
    ⟨finalState, htail⟩
  refine ⟨finalState, ?_⟩
  have hfull := step_then ((2 * inputCount + 2) + (source + 1))
    hfirst htail
  simpa only [notGateSteps, encodeNormalizedGate,
    generalCircuitGateExprList, afterOffsetLabel, afterOffsetOutput, varEnc,
    List.reverse_cons, List.reverse_append, List.reverse_replicate,
    List.reverse_singleton, List.reverse_nil, List.singleton_append,
    List.nil_append, List.replicate_add, List.replicate_one, List.cons_append,
    List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
