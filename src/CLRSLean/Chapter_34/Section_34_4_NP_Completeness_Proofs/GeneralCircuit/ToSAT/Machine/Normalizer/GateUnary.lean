import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.GateConstant

/-!
# Guarded circuit normalizer: unary gates
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

/-- Exact successful run for a NOT gate whose dependency is below the current
chronological gate index. -/
theorem notGate_phase (state : State) (source slack inputCount : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[2 * (source + slack + 1) + 3 * source + 7]
        (some (cfg (some .gates) state
          (encodeCircuitGate (.not source) ++ input) output rows
          inputCount (source + slack + 1) 0 0 0)) =
        some (cfg (some .gates) finalState input output
          ((encodeNormalizedGateRow (source + slack + 1) (.not source)).reverse ++ rows)
          inputCount (source + slack + 1 + 1) 0 0 0) := by
  have h₁ : transition^[1]
      (some (cfg (some .gates) state
        (encodeCircuitGate (.not source) ++ input) output rows
        inputCount (source + slack + 1) 0 0 0)) =
      some (cfg (some (.rowIndexCopy .not))
        { state with inputBuffer := some .notMark }
        (encNat source ++ input) output (.gateRowMark :: rows)
        inputCount (source + slack + 1) 0 0 0) := by
    change step (cfg (some .gates) state
      (.notMark :: (encNat source ++ input)) output rows
      inputCount (source + slack + 1) 0 0 0) = _
    simpa [rawGateTag] using gates_tag_step state .not
      (encNat source ++ input) output rows inputCount (source + slack + 1) 0 0 0
  rcases rowPrefix_phase { state with inputBuffer := some .notMark } .not
      (source + slack + 1) (encNat source ++ input) output
      (.gateRowMark :: rows) inputCount 0 0 with ⟨s₂, h₂⟩
  rcases boundedOperand_phase s₂ .notGate (by decide) source slack inputCount
      0 0 input output
      (afterRowPrefixRows .not
        (.fieldEnd ::
          (List.replicate (source + slack + 1) .tick ++ .gateRowMark :: rows))) with
    ⟨s₃, h₃⟩
  have h₁₂ := step_comp _ _ h₁ h₂
  have hfull := step_comp _ _ h₁₂ h₃
  refine ⟨s₃, ?_⟩
  have hsteps : 1 + (2 * (source + slack + 1) + 2) + (3 * source + 4) =
      2 * (source + slack + 1) + 3 * source + 7 := by omega
  rw [← hsteps]
  simpa [encodeNormalizedGateRow, encodeNormalizedNat, encodeNormalizedGate,
    normalizedGateTag, afterRowPrefixLabel, afterRowPrefixRows,
    afterRowPrefixGateCount, afterBoundLabel, afterBoundRows,
    afterBoundGateCount, operandRows, operandOutputIndex, withBound,
    List.reverse_append, List.append_assoc, List.reverse_replicate] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
