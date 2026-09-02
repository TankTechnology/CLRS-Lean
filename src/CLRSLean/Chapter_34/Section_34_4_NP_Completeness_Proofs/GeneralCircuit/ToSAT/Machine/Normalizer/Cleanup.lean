import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.UnaryField

/-!
# Guarded circuit normalizer: canonical invalid cleanup

Every failure label enters `clearInput`.  The theorem below clears every stack,
emits the single invalid sentinel, resets finite state, and halts.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

private theorem clearInput_phase (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    ∃ finalState,
      transition^[input.length + 1]
        (some (cfg (some .clearInput) state input output rows
          inputCount gateCount operand saved outputIndex)) =
        some (cfg (some .clearOutput) finalState [] output rows
          inputCount gateCount operand saved outputIndex) := by
  induction input generalizing state with
  | nil =>
      refine ⟨{ state with inputBuffer := none }, ?_⟩
      change step (cfg (some .clearInput) state [] output rows
        inputCount gateCount operand saved outputIndex) = _
      exact clear_input_done_step state output rows inputCount gateCount operand
        saved outputIndex
  | cons head input ih =>
      rcases ih { state with inputBuffer := some head } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_input_step state head input output rows inputCount
        gateCount operand saved outputIndex
      simpa [Nat.add_assoc] using step_then (input.length + 1) hfirst hrun

private theorem clearOutput_phase (state : State)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    ∃ finalState,
      transition^[output.length + 1]
        (some (cfg (some .clearOutput) state [] output rows
          inputCount gateCount operand saved outputIndex)) =
        some (cfg (some .clearRows) finalState [] [] rows
          inputCount gateCount operand saved outputIndex) := by
  induction output generalizing state with
  | nil =>
      refine ⟨{ state with normalizedBuffer := none }, ?_⟩
      change step (cfg (some .clearOutput) state [] [] rows
        inputCount gateCount operand saved outputIndex) = _
      exact clear_output_done_step state rows inputCount gateCount operand saved
        outputIndex
  | cons head output ih =>
      rcases ih { state with normalizedBuffer := some head } with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_output_step state head output rows inputCount gateCount
        operand saved outputIndex
      simpa [Nat.add_assoc] using step_then (output.length + 1) hfirst hrun

private theorem clearRows_phase (state : State)
    (rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    ∃ finalState,
      transition^[rows.length + 1]
        (some (cfg (some .clearRows) state [] [] rows
          inputCount gateCount operand saved outputIndex)) =
        some (cfg (some .clearInputCount) finalState [] [] []
          inputCount gateCount operand saved outputIndex) := by
  induction rows generalizing state with
  | nil =>
      refine ⟨{ state with normalizedBuffer := none }, ?_⟩
      change step (cfg (some .clearRows) state [] [] []
        inputCount gateCount operand saved outputIndex) = _
      exact clear_rows_done_step state inputCount gateCount operand saved outputIndex
  | cons head rows ih =>
      rcases ih { state with normalizedBuffer := some head } with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_rows_step state head rows inputCount gateCount operand
        saved outputIndex
      simpa [Nat.add_assoc] using step_then (rows.length + 1) hfirst hrun

private theorem clearInputCount_phase (state : State)
    (inputCount gateCount operand saved outputIndex : Nat) :
    ∃ finalState,
      transition^[inputCount + 1]
        (some (cfg (some .clearInputCount) state [] [] []
          inputCount gateCount operand saved outputIndex)) =
        some (cfg (some .clearGateCount) finalState [] [] []
          0 gateCount operand saved outputIndex) := by
  induction inputCount generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .clearInputCount) state [] [] []
        0 gateCount operand saved outputIndex) = _
      exact clear_input_count_done_step state gateCount operand saved outputIndex
  | succ inputCount ih =>
      rcases ih { state with counterPresent := true } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_input_count_tick_step state inputCount gateCount operand
        saved outputIndex
      simpa [Nat.add_assoc] using step_then (inputCount + 1) hfirst hrun

private theorem clearGateCount_phase (state : State)
    (gateCount operand saved outputIndex : Nat) :
    ∃ finalState,
      transition^[gateCount + 1]
        (some (cfg (some .clearGateCount) state [] [] []
          0 gateCount operand saved outputIndex)) =
        some (cfg (some .clearOperand) finalState [] [] []
          0 0 operand saved outputIndex) := by
  induction gateCount generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .clearGateCount) state [] [] []
        0 0 operand saved outputIndex) = _
      exact clear_gate_count_done_step state operand saved outputIndex
  | succ gateCount ih =>
      rcases ih { state with counterPresent := true } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_gate_count_tick_step state gateCount operand saved
        outputIndex
      simpa [Nat.add_assoc] using step_then (gateCount + 1) hfirst hrun

private theorem clearOperand_phase (state : State)
    (operand saved outputIndex : Nat) :
    ∃ finalState,
      transition^[operand + 1]
        (some (cfg (some .clearOperand) state [] [] []
          0 0 operand saved outputIndex)) =
        some (cfg (some .clearSaved) finalState [] [] []
          0 0 0 saved outputIndex) := by
  induction operand generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .clearOperand) state [] [] [] 0 0 0 saved outputIndex) = _
      exact clear_operand_done_step state saved outputIndex
  | succ operand ih =>
      rcases ih { state with counterPresent := true } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_operand_tick_step state operand saved outputIndex
      simpa [Nat.add_assoc] using step_then (operand + 1) hfirst hrun

private theorem clearSaved_phase (state : State) (saved outputIndex : Nat) :
    ∃ finalState,
      transition^[saved + 1]
        (some (cfg (some .clearSaved) state [] [] [] 0 0 0 saved outputIndex)) =
        some (cfg (some .clearOutputIndex) finalState [] [] []
          0 0 0 0 outputIndex) := by
  induction saved generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .clearSaved) state [] [] [] 0 0 0 0 outputIndex) = _
      exact clear_saved_done_step state outputIndex
  | succ saved ih =>
      rcases ih { state with counterPresent := true } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_saved_tick_step state saved outputIndex
      simpa [Nat.add_assoc] using step_then (saved + 1) hfirst hrun

private theorem clearOutputIndex_phase (state : State) (outputIndex : Nat) :
    ∃ finalState,
      transition^[outputIndex + 1]
        (some (cfg (some .clearOutputIndex) state [] [] [] 0 0 0 0 outputIndex)) =
        some (cfg (some .emitInvalid) finalState [] [] [] 0 0 0 0 0) := by
  induction outputIndex generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .clearOutputIndex) state [] [] [] 0 0 0 0 0) = _
      exact clear_output_index_done_step state
  | succ outputIndex ih =>
      rcases ih { state with counterPresent := true } with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := clear_output_index_tick_step state outputIndex
      simpa [Nat.add_assoc] using step_then (outputIndex + 1) hfirst hrun

/-- Exact duration of the shared invalid cleanup path. -/
def clearAndEmitInvalidSteps (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) : Nat :=
  (input.length + 1) + (output.length + 1) + (rows.length + 1) +
    (inputCount + 1) + (gateCount + 1) + (operand + 1) +
    (saved + 1) + (outputIndex + 1) + 2

/-- Every rejecting branch converges to the same one-symbol output and an
otherwise empty, reset halting configuration. -/
theorem clearAndEmitInvalid_phase (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    transition^[clearAndEmitInvalidSteps input output rows inputCount gateCount
        operand saved outputIndex]
      (some (cfg (some .clearInput) state input output rows
        inputCount gateCount operand saved outputIndex)) =
      some (_root_.Turing.haltList machine [.invalidMark]) := by
  rcases clearInput_phase state input output rows inputCount gateCount operand
      saved outputIndex with ⟨s₁, h₁⟩
  rcases clearOutput_phase s₁ output rows inputCount gateCount operand saved
      outputIndex with ⟨s₂, h₂⟩
  rcases clearRows_phase s₂ rows inputCount gateCount operand saved outputIndex with
    ⟨s₃, h₃⟩
  rcases clearInputCount_phase s₃ inputCount gateCount operand saved outputIndex with
    ⟨s₄, h₄⟩
  rcases clearGateCount_phase s₄ gateCount operand saved outputIndex with
    ⟨s₅, h₅⟩
  rcases clearOperand_phase s₅ operand saved outputIndex with ⟨s₆, h₆⟩
  rcases clearSaved_phase s₆ saved outputIndex with ⟨s₇, h₇⟩
  rcases clearOutputIndex_phase s₇ outputIndex with ⟨s₈, h₈⟩
  have h₉ : transition^[1]
      (some (cfg (some .emitInvalid) s₈ [] [] [] 0 0 0 0 0)) =
      some (cfg (some .done) s₈ [] [.invalidMark] [] 0 0 0 0 0) := by
    change step (cfg (some .emitInvalid) s₈ [] [] [] 0 0 0 0 0) = _
    exact emit_invalid_step s₈
  have h₁₀ : transition^[1]
      (some (cfg (some .done) s₈ [] [.invalidMark] [] 0 0 0 0 0)) =
      some (_root_.Turing.haltList machine [.invalidMark]) := by
    change step (cfg (some .done) s₈ [] [.invalidMark] [] 0 0 0 0 0) = _
    exact done_invalid_step s₈
  have h₁₂ := step_comp _ _ h₁ h₂
  have h₁₂₃ := step_comp _ _ h₁₂ h₃
  have h₁₂₃₄ := step_comp _ _ h₁₂₃ h₄
  have h₁₅ := step_comp _ _ h₁₂₃₄ h₅
  have h₁₆ := step_comp _ _ h₁₅ h₆
  have h₁₇ := step_comp _ _ h₁₆ h₇
  have h₁₈ := step_comp _ _ h₁₇ h₈
  have h₁₉ := step_comp _ _ h₁₈ h₉
  have hfull := step_comp _ _ h₁₉ h₁₀
  simpa [clearAndEmitInvalidSteps, Nat.add_assoc] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
