import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Steps

/-! # General-circuit formula emitter: restoring unary variables -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open StateTransition

private abbrev transition := flip Option.bind step

theorem step_comp {A B C : Option reverseMachine.Cfg} (n₁ n₂ : Nat)
    (h₁ : transition^[n₁] A = B) (h₂ : transition^[n₂] B = C) :
    transition^[n₁ + n₂] A = C := by
  simpa [Nat.add_comm] using (show transition^[n₂ + n₁] A = C by
    rw [Function.iterate_add_apply, h₁, h₂])

theorem step_then {A : Option reverseMachine.Cfg} {B C : reverseMachine.Cfg}
    (n : Nat) (h₁ : step B = some C)
    (h₂ : transition^[n] (some C) = A) :
    transition^[n + 1] (some B) = A := by
  rw [Function.iterate_add_apply]
  change transition^[n] (step B) = A
  rw [h₁]
  exact h₂

private theorem replicate_end_append_cons (count : Nat)
    (output : List FormulaSym) :
    List.replicate count .endMark ++ .endMark :: output =
      .endMark :: (List.replicate count .endMark ++ output) := by
  induction count with
  | zero => simp
  | succ count ih => simp [List.replicate_succ, ih]

private theorem copyPrefixMove_phase (state : State) (ret : OffsetReturn)
    (count saved : Nat) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some (.copyPrefix ret)) state input output count saved)) =
      some (cfg (some (.restorePrefix ret)) finalState input
        (List.replicate count .endMark ++ output) 0 (saved + count)) := by
  induction count generalizing state saved output with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some (.copyPrefix ret)) state input output 0 saved) = _
      simpa using copy_prefix_empty_step state ret input output saved
  | succ count ih =>
      have hfirst := copy_prefix_tick_step state ret input output count saved
      rcases ih { state with counterPresent := true } (saved + 1)
          (.endMark :: output) with ⟨finalState, htail⟩
      refine ⟨finalState, ?_⟩
      have hfull := step_then (count + 1) hfirst htail
      simpa [List.replicate_succ, replicate_end_append_cons,
        List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hfull

private theorem restorePrefixMove_phase (state : State) (ret : OffsetReturn)
    (count inputCount : Nat) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some (.restorePrefix ret)) state input output
          inputCount count)) =
      some (cfg (some (.parseOffset ret)) finalState input output
        (inputCount + count) 0) := by
  induction count generalizing state inputCount with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some (.restorePrefix ret)) state input output
        inputCount 0) = _
      simpa using restore_prefix_empty_step state ret input output inputCount
  | succ count ih =>
      have hfirst := restore_prefix_tick_step state ret input output inputCount
        count
      rcases ih { state with counterPresent := true } (inputCount + 1) with
        ⟨finalState, htail⟩
      refine ⟨finalState, ?_⟩
      have hfull := step_then (count + 1) hfirst htail
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

/-- Copy the permanent input-count prefix to output, restore it, and stop at
the beginning of the offset field. -/
theorem copyPrefix_phase (state : State) (ret : OffsetReturn)
    (inputCount : Nat) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[2 * inputCount + 2]
        (some (cfg (some (.copyPrefix ret)) state input output inputCount 0)) =
      some (cfg (some (.parseOffset ret)) finalState input
        (List.replicate inputCount .endMark ++ output) inputCount 0) := by
  rcases copyPrefixMove_phase state ret inputCount 0 input output with
    ⟨afterCopy, hcopy⟩
  rcases restorePrefixMove_phase afterCopy ret inputCount 0 input
      (List.replicate inputCount .endMark ++ output) with
    ⟨afterRestore, hrestore⟩
  refine ⟨afterRestore, ?_⟩
  have hfull := step_comp (inputCount + 1) (inputCount + 1) hcopy (by
    simpa using hrestore)
  have hsteps : inputCount + 1 + (inputCount + 1) =
      2 * inputCount + 2 := by omega
  rw [hsteps] at hfull
  exact hfull

/-- Consume a unary offset and emit its end markers, including the mandatory
final marker in `varEnc`. -/
theorem offset_phase (state : State) (ret : OffsetReturn) (offset : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount : Nat) :
    transition^[offset + 1]
      (some (cfg (some (.parseOffset ret)) state
        (encodeNormalizedNat offset ++ input) output inputCount 0)) =
    some (cfg (some (afterOffsetLabel ret))
      { state with inputBuffer := some .fieldEnd }
      input (afterOffsetOutput ret
        (List.replicate offset .endMark ++ output)) inputCount 0) := by
  induction offset generalizing state output with
  | zero =>
      change step (cfg (some (.parseOffset ret)) state
        (.fieldEnd :: input) output inputCount 0) = _
      simpa [encodeNormalizedNat] using
        parse_offset_end_step state ret input output inputCount 0
  | succ offset ih =>
      have h₁ := parse_offset_tick_step state ret
        (encodeNormalizedNat offset ++ input) output inputCount 0
      have htail := ih { state with inputBuffer := some .tick }
        (.endMark :: output)
      have hfull := step_then (offset + 1) h₁ htail
      simpa [encodeNormalizedNat, List.replicate_succ,
        replicate_end_append_cons, List.append_assoc]
        using hfull

/-- Restoring emission of `varEnc (inputCount + offset)`.  For continuations
that start a second operand, `afterOffsetOutput` additionally stages its
leading `varMark`. -/
theorem variable_phase (state : State) (ret : OffsetReturn)
    (inputCount offset : Nat) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[(2 * inputCount + 2) + (offset + 1)]
        (some (cfg (some (.copyPrefix ret)) state
          (encodeNormalizedNat offset ++ input) (.varMark :: output)
          inputCount 0)) =
      some (cfg (some (afterOffsetLabel ret)) finalState input
        (afterOffsetOutput ret
          (List.replicate offset .endMark ++
            List.replicate inputCount .endMark ++ .varMark :: output))
        inputCount 0) := by
  rcases copyPrefix_phase state ret inputCount
      (encodeNormalizedNat offset ++ input) (.varMark :: output) with
    ⟨afterCopy, hcopy⟩
  have hoffset := offset_phase afterCopy ret offset input
    (List.replicate inputCount .endMark ++ .varMark :: output) inputCount
  refine ⟨{ afterCopy with inputBuffer := some .fieldEnd }, ?_⟩
  simpa only [List.append_assoc] using
    step_comp _ _ hcopy hoffset

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
