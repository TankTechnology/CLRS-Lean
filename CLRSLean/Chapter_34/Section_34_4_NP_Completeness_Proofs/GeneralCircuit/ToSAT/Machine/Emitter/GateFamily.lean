import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Gate

/-! # General-circuit formula emitter: chronological gate families -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open StateTransition

private abbrev transition := flip Option.bind step

def gateRowsStepsFrom (inputCount : Nat) : Nat → List CircuitGate → Nat
  | _, [] => 0
  | gateIndex, gate :: gates =>
      gateRowSteps inputCount gateIndex gate +
        gateRowsStepsFrom inputCount (gateIndex + 1) gates

/-- Emit all canonical gate rows, stopping before the terminal true constant. -/
theorem gateRows_phase (state : State) (inputCount gateIndex : Nat)
    (gates : List CircuitGate) (input : List NormalizedCircuitSym)
    (output : List FormulaSym) :
    ∃ finalState,
      transition^[gateRowsStepsFrom inputCount gateIndex gates]
        (some (cfg (some .rows) state
          (encodeNormalizedGateRowsFrom gateIndex gates ++ input)
          output inputCount 0)) =
      some (cfg (some .rows) finalState input
        ((generalCircuitGateRowsListFrom inputCount gateIndex gates).reverse ++
          output) inputCount 0) := by
  induction gates generalizing state gateIndex output with
  | nil =>
      exact ⟨state, by simp [gateRowsStepsFrom, encodeNormalizedGateRowsFrom,
        generalCircuitGateRowsListFrom]⟩
  | cons gate gates ih =>
      rcases gateRow_phase state inputCount gateIndex gate
          (encodeNormalizedGateRowsFrom (gateIndex + 1) gates ++ input)
          output with ⟨afterGate, hgate⟩
      rcases ih afterGate (gateIndex + 1)
          ((.andMark :: generalCircuitGateFormulaList inputCount gateIndex gate).reverse ++
            output) with ⟨finalState, htail⟩
      refine ⟨finalState, ?_⟩
      have hfull := step_comp _ _ (by
        simpa [List.append_assoc] using hgate) htail
      simpa [gateRowsStepsFrom, encodeNormalizedGateRowsFrom,
        generalCircuitGateRowsListFrom, List.reverse_append,
        List.append_assoc] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
