import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Header

/-! # General-circuit formula emitter: canonical exact runs -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

theorem clearInputCount_phase (state : State) (count : Nat)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some .clearInputCount) state [] output count 0)) =
      some (cfg (some .done) finalState [] output 0 0) := by
  induction count generalizing state with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .clearInputCount) state [] output 0 0) = _
      exact clear_input_count_empty_step state output
  | succ count ih =>
      have hfirst := clear_input_count_tick_step state output count 0
      rcases ih { state with counterPresent := true } with
        ⟨finalState, htail⟩
      refine ⟨finalState, ?_⟩
      exact step_then (count + 1) hfirst htail

theorem gateFamilyList_eq_rows_append (inputCount gateIndex : Nat)
    (gates : List CircuitGate) :
    generalCircuitGateFamilyListFrom inputCount gateIndex gates =
      generalCircuitGateRowsListFrom inputCount gateIndex gates ++ [.lit true] := by
  induction gates generalizing gateIndex with
  | nil => simp [generalCircuitGateFamilyListFrom,
      generalCircuitGateRowsListFrom]
  | cons gate gates ih =>
      simp [generalCircuitGateFamilyListFrom,
        generalCircuitGateRowsListFrom, ih, List.append_assoc]

def reverseSuccessfulSteps (c : Circuit) : Nat :=
  headerSteps c + gateRowsStepsFrom c.inputCount 0 c.gates + 1 +
    (c.inputCount + 1) + 1

/-- The direct fixed controller outputs the reverse exact formula stream on a
canonical guarded circuit record. -/
theorem canonical_reverse_run (c : Circuit) :
    transition^[reverseSuccessfulSteps c]
      (some (initList reverseMachine (encodeNormalizedCircuit c))) =
    some (haltList reverseMachine (generalCircuitFormulaList c).reverse) := by
  rcases header_phase c with ⟨afterHeader, hheader⟩
  rcases gateRows_phase afterHeader c.inputCount 0 c.gates []
      ((.andMark :: varEnc (c.inputCount + c.output)).reverse) with
    ⟨afterRows, hrows⟩
  have hend := rows_empty_step afterRows
    ((generalCircuitGateRowsListFrom c.inputCount 0 c.gates).reverse ++
      (.andMark :: varEnc (c.inputCount + c.output)).reverse)
    c.inputCount 0
  rcases clearInputCount_phase { afterRows with inputBuffer := none }
      c.inputCount
      (.lit true ::
        (generalCircuitGateRowsListFrom c.inputCount 0 c.gates).reverse ++
        (.andMark :: varEnc (c.inputCount + c.output)).reverse) with
    ⟨afterClear, hclear⟩
  have hhalt := done_step afterClear
    (.lit true ::
      (generalCircuitGateRowsListFrom c.inputCount 0 c.gates).reverse ++
      (.andMark :: varEnc (c.inputCount + c.output)).reverse)
  have hend' := step_then 0 hend (by rfl)
  simp only [Nat.zero_add, Function.iterate_zero_apply] at hend'
  have hhalt' := step_then 0 hhalt (by rfl)
  simp only [Nat.zero_add, Function.iterate_zero_apply] at hhalt'
  have hrows' :
      transition^[gateRowsStepsFrom c.inputCount 0 c.gates]
        (some (cfg (some .rows) afterHeader
          (encodeNormalizedGateRowsFrom 0 c.gates)
          ((.andMark :: varEnc (c.inputCount + c.output)).reverse)
          c.inputCount 0)) =
        some (cfg (some .rows) afterRows []
          ((generalCircuitGateRowsListFrom c.inputCount 0 c.gates).reverse ++
            (.andMark :: varEnc (c.inputCount + c.output)).reverse)
          c.inputCount 0) := by
    simpa using hrows
  have h₁ := step_comp _ _ hheader hrows'
  have h₂ := step_comp _ _ h₁ hend'
  have h₃ := step_comp _ _ h₂ hclear
  have hfull := step_comp _ _ h₃ hhalt'
  have hsteps : headerSteps c + gateRowsStepsFrom c.inputCount 0 c.gates +
      1 + (c.inputCount + 1) + 1 = reverseSuccessfulSteps c := rfl
  rw [hsteps] at hfull
  simpa [generalCircuitFormulaList, gateFamilyList_eq_rows_append,
    List.reverse_append, List.reverse_cons, List.append_assoc] using hfull

def invalidReverseSteps : Nat := 2

/-- The canonical invalid sentinel emits the reverse false encoding (which is
the same singleton stream). -/
theorem invalid_reverse_run :
    transition^[invalidReverseSteps]
      (some (initList reverseMachine [.invalidMark])) =
    some (haltList reverseMachine (enc (.const false)).reverse) := by
  have hinit : initList reverseMachine [.invalidMark] =
      cfg (some .start) initialState [.invalidMark] [] 0 0 := by
    apply TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext stack
      cases stack <;>
        simp [cfg, reverseMachine, stackContents, initList]
  have hstart := start_invalid_step initialState
  have hhalt := done_step
    { initialState with inputBuffer := some .invalidMark } [.lit false]
  rw [hinit]
  change transition^[1 + 1]
    (some (cfg (some .start) initialState [.invalidMark] [] 0 0)) = _
  have hstart' := step_then 0 hstart (by rfl)
  simp only [Nat.zero_add, Function.iterate_zero_apply] at hstart'
  have hhalt' := step_then 0 hhalt (by rfl)
  simp only [Nat.zero_add, Function.iterate_zero_apply] at hhalt'
  simpa [invalidReverseSteps, enc] using step_comp 1 1 hstart' hhalt'

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
