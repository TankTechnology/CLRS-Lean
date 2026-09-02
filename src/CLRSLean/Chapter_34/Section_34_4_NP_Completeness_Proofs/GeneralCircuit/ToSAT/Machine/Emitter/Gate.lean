import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.GateBinary

/-! # General-circuit formula emitter: uniform gate rows -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open StateTransition

private abbrev transition := flip Option.bind step

def gateExprSteps (inputCount : Nat) : CircuitGate → Nat
  | .input inputIndex => inputGateSteps inputIndex
  | .const _ => constantGateSteps
  | .not source => notGateSteps inputCount source
  | .and left right | .or left right =>
      binaryGateSteps inputCount left right

theorem gateExpr_phase (state : State) (inputCount : Nat)
    (gate : CircuitGate) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[gateExprSteps inputCount gate]
        (some (cfg (some .gateTag) state
          (encodeNormalizedGate gate ++ .rowEnd :: input)
          output inputCount 0)) =
      some (cfg (some .expectRowEnd) finalState (.rowEnd :: input)
        ((generalCircuitGateExprList inputCount gate).reverse ++ output)
        inputCount 0) := by
  cases gate with
  | input inputIndex =>
      simpa [gateExprSteps] using
        inputGate_phase state inputCount inputIndex input output
  | const value =>
      simpa [gateExprSteps] using
        constantGate_phase state inputCount value input output
  | not source =>
      simpa [gateExprSteps] using
        notGate_phase state inputCount source input output
  | and left right =>
      simpa [gateExprSteps] using
        andGate_phase state inputCount left right input output
  | or left right =>
      simpa [gateExprSteps] using
        orGate_phase state inputCount left right input output

def gateRowSteps (inputCount gateIndex : Nat) (gate : CircuitGate) : Nat :=
  1 + ((2 * inputCount + 2) + (gateIndex + 1)) +
    gateExprSteps inputCount gate + 1

/-- One canonical indexed row emits one conjunction marker and its exact gate
equation, leaving the parser at the next row. -/
theorem gateRow_phase (state : State) (inputCount gateIndex : Nat)
    (gate : CircuitGate) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[gateRowSteps inputCount gateIndex gate]
        (some (cfg (some .rows) state
          (encodeNormalizedGateRow gateIndex gate ++ input)
          output inputCount 0)) =
      some (cfg (some .rows) finalState input
        ((.andMark ::
          generalCircuitGateFormulaList inputCount gateIndex gate).reverse ++
            output) inputCount 0) := by
  have hrow := rows_gate_step state
    (encodeNormalizedNat gateIndex ++ encodeNormalizedGate gate ++
      .rowEnd :: input) output inputCount 0
  rcases variable_phase
      { state with inputBuffer := some .gateRowMark } .row inputCount gateIndex
      (encodeNormalizedGate gate ++ .rowEnd :: input)
      (.iffMark :: .andMark :: output) with ⟨afterIndex, hindex⟩
  have hindex' :
      transition^[(2 * inputCount + 2) + (gateIndex + 1)]
        (some (cfg (some (.copyPrefix .row))
          { state with inputBuffer := some .gateRowMark }
          (encodeNormalizedNat gateIndex ++ encodeNormalizedGate gate ++
            .rowEnd :: input)
          (.varMark :: .iffMark :: .andMark :: output) inputCount 0)) =
      some (cfg (some .gateTag) afterIndex
        (encodeNormalizedGate gate ++ .rowEnd :: input)
        ((varEnc (inputCount + gateIndex)).reverse ++
          .iffMark :: .andMark :: output) inputCount 0) := by
    simpa only [afterOffsetLabel, afterOffsetOutput, varEnc, List.reverse_cons,
      List.reverse_append, List.reverse_replicate, List.reverse_singleton,
      List.reverse_nil, List.singleton_append, List.nil_append,
      List.replicate_add, List.replicate_one, List.cons_append,
      List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hindex
  rcases gateExpr_phase afterIndex inputCount gate input
      ((varEnc (inputCount + gateIndex)).reverse ++
        .iffMark :: .andMark :: output) with ⟨afterGate, hgate⟩
  have hend := row_end_step afterGate input
    ((generalCircuitGateExprList inputCount gate).reverse ++
      ((varEnc (inputCount + gateIndex)).reverse ++
        .iffMark :: .andMark :: output)) inputCount 0
  refine ⟨{ afterGate with inputBuffer := some .rowEnd }, ?_⟩
  have hbody := step_comp _ _ hindex' hgate
  have hbodyEnd := step_then 0 hend (by rfl)
  have htail := step_comp _ _ hbody hbodyEnd
  have hfull := step_then
    (((2 * inputCount + 2) + (gateIndex + 1)) +
      gateExprSteps inputCount gate + 1) hrow htail
  have hsteps :
      (((2 * inputCount + 2) + (gateIndex + 1)) +
          gateExprSteps inputCount gate + 1) + 1 =
        gateRowSteps inputCount gateIndex gate := by
    simp [gateRowSteps]
    omega
  rw [hsteps] at hfull
  simpa only [encodeNormalizedGateRow, generalCircuitGateFormulaList,
    Function.iterate_zero_apply, List.reverse_cons, List.reverse_append,
    List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc]
    using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
