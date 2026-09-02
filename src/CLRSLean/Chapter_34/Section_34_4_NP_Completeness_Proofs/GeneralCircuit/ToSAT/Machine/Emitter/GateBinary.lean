import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.GateSimple

/-! # General-circuit formula emitter: binary gates -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open StateTransition

private abbrev transition := flip Option.bind step

def binaryGateSteps (inputCount left right : Nat) : Nat :=
  1 + ((2 * inputCount + 2) + (left + 1)) +
    ((2 * inputCount + 2) + (right + 1))

private def leftOutputTail (inputCount left : Nat) (kind : FormulaSym)
    (output : List FormulaSym) : List FormulaSym :=
  .endMark :: (List.replicate left .endMark ++
    List.replicate inputCount .endMark ++ .varMark :: kind :: output)

theorem andGate_phase (state : State) (inputCount left right : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym) :
    ∃ finalState,
      transition^[binaryGateSteps inputCount left right]
        (some (cfg (some .gateTag) state
          (encodeNormalizedGate (.and left right) ++ .rowEnd :: input)
          output inputCount 0)) =
      some (cfg (some .expectRowEnd) finalState (.rowEnd :: input)
        ((generalCircuitGateExprList inputCount (.and left right)).reverse ++
          output) inputCount 0) := by
  have htag := gate_tag_and_step state
    (encodeNormalizedNat left ++ encodeNormalizedNat right ++
      .rowEnd :: input) output inputCount 0
  rcases variable_phase { state with inputBuffer := some .andGateMark }
      .andLeft inputCount left
      (encodeNormalizedNat right ++ .rowEnd :: input) (.andMark :: output) with
    ⟨afterLeft, hleft⟩
  have hleft' :
      transition^[(2 * inputCount + 2) + (left + 1)]
        (some (cfg (some (.copyPrefix .andLeft))
          { state with inputBuffer := some .andGateMark }
          (encodeNormalizedNat left ++ encodeNormalizedNat right ++
            .rowEnd :: input)
          (.varMark :: .andMark :: output) inputCount 0)) =
      some (cfg (some (.copyPrefix .andRight)) afterLeft
        (encodeNormalizedNat right ++ .rowEnd :: input)
        (.varMark :: leftOutputTail inputCount left .andMark output)
        inputCount 0) := by
    simpa [afterOffsetLabel, afterOffsetOutput, leftOutputTail,
      List.append_assoc] using hleft
  rcases variable_phase afterLeft .andRight inputCount right
      (.rowEnd :: input) (leftOutputTail inputCount left .andMark output) with
    ⟨finalState, hright⟩
  refine ⟨finalState, ?_⟩
  have hbody := step_comp _ _ hleft' hright
  have hfull := step_then
    (((2 * inputCount + 2) + (left + 1)) +
      ((2 * inputCount + 2) + (right + 1))) htag hbody
  simpa only [binaryGateSteps, encodeNormalizedGate,
    generalCircuitGateExprList, afterOffsetLabel, afterOffsetOutput,
    leftOutputTail, varEnc, List.reverse_cons, List.reverse_append,
    List.reverse_replicate, List.reverse_singleton, List.reverse_nil,
    List.singleton_append, List.nil_append, List.replicate_add,
    List.replicate_one, List.cons_append, List.append_assoc, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using hfull

theorem orGate_phase (state : State) (inputCount left right : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym) :
    ∃ finalState,
      transition^[binaryGateSteps inputCount left right]
        (some (cfg (some .gateTag) state
          (encodeNormalizedGate (.or left right) ++ .rowEnd :: input)
          output inputCount 0)) =
      some (cfg (some .expectRowEnd) finalState (.rowEnd :: input)
        ((generalCircuitGateExprList inputCount (.or left right)).reverse ++
          output) inputCount 0) := by
  have htag := gate_tag_or_step state
    (encodeNormalizedNat left ++ encodeNormalizedNat right ++
      .rowEnd :: input) output inputCount 0
  rcases variable_phase { state with inputBuffer := some .orGateMark }
      .orLeft inputCount left
      (encodeNormalizedNat right ++ .rowEnd :: input) (.orMark :: output) with
    ⟨afterLeft, hleft⟩
  have hleft' :
      transition^[(2 * inputCount + 2) + (left + 1)]
        (some (cfg (some (.copyPrefix .orLeft))
          { state with inputBuffer := some .orGateMark }
          (encodeNormalizedNat left ++ encodeNormalizedNat right ++
            .rowEnd :: input)
          (.varMark :: .orMark :: output) inputCount 0)) =
      some (cfg (some (.copyPrefix .orRight)) afterLeft
        (encodeNormalizedNat right ++ .rowEnd :: input)
        (.varMark :: leftOutputTail inputCount left .orMark output)
        inputCount 0) := by
    simpa [afterOffsetLabel, afterOffsetOutput, leftOutputTail,
      List.append_assoc] using hleft
  rcases variable_phase afterLeft .orRight inputCount right
      (.rowEnd :: input) (leftOutputTail inputCount left .orMark output) with
    ⟨finalState, hright⟩
  refine ⟨finalState, ?_⟩
  have hbody := step_comp _ _ hleft' hright
  have hfull := step_then
    (((2 * inputCount + 2) + (left + 1)) +
      ((2 * inputCount + 2) + (right + 1))) htag hbody
  simpa only [binaryGateSteps, encodeNormalizedGate,
    generalCircuitGateExprList, afterOffsetLabel, afterOffsetOutput,
    leftOutputTail, varEnc, List.reverse_cons, List.reverse_append,
    List.reverse_replicate, List.reverse_singleton, List.reverse_nil,
    List.singleton_append, List.nil_append, List.replicate_add,
    List.replicate_one, List.cons_append, List.append_assoc, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
