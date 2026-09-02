import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Cleanup

/-!
# Guarded circuit normalizer: bounded operands and input gates
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

private theorem afterOperandLabel_eq_compare {ret : Return}
    (hret : ret ≠ .outputGate) :
    afterOperandLabel ret = .compareOperand ret := by
  cases ret <;> simp_all [afterOperandLabel]

/-- Parse a gate operand, prove it strictly below its selected unary bound,
restore that bound, and execute the finite continuation. -/
theorem boundedOperand_phase (state : State) (ret : Return)
    (hret : ret ≠ .outputGate) (count extra inputCount gateCount outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[3 * count + 4]
        (some (cfg (some (.parseOperand ret)) state (encNat count ++ input)
          output rows
          (withBound ret (count + extra + 1) inputCount gateCount).1
          (withBound ret (count + extra + 1) inputCount gateCount).2
          0 0 outputIndex)) =
        some (cfg (some (afterBoundLabel ret)) finalState input output
          (afterBoundRows ret (operandRows ret count rows))
          (withBound ret (count + extra + 1) inputCount gateCount).1
          (afterBoundGateCount ret
            (withBound ret (count + extra + 1) inputCount gateCount).2)
          0 0 (operandOutputIndex ret count outputIndex)) := by
  rcases operand_phase state ret count 0 input output rows
      (withBound ret (count + extra + 1) inputCount gateCount).1
      (withBound ret (count + extra + 1) inputCount gateCount).2
      0 outputIndex with ⟨s₁, h₁⟩
  have h₁' : transition^[count + 1]
      (some (cfg (some (.parseOperand ret)) state (encNat count ++ input)
        output rows
        (withBound ret (count + extra + 1) inputCount gateCount).1
        (withBound ret (count + extra + 1) inputCount gateCount).2
        0 0 outputIndex)) =
      some (cfg (some (.compareOperand ret)) s₁ input output
        (operandRows ret count rows)
        (withBound ret (count + extra + 1) inputCount gateCount).1
        (withBound ret (count + extra + 1) inputCount gateCount).2
        count 0 (operandOutputIndex ret count outputIndex)) := by
    simpa [afterOperandLabel_eq_compare hret] using h₁
  rcases compareOperand_phase s₁ ret count extra inputCount gateCount 0
      (operandOutputIndex ret count outputIndex) input output
      (operandRows ret count rows) with ⟨s₂, h₂⟩
  have h₂' : transition^[count + 1]
      (some (cfg (some (.compareOperand ret)) s₁ input output
        (operandRows ret count rows)
        (withBound ret (count + extra + 1) inputCount gateCount).1
        (withBound ret (count + extra + 1) inputCount gateCount).2
        count 0 (operandOutputIndex ret count outputIndex))) =
      some (cfg (some (.restoreBound ret)) s₂ input output
        (operandRows ret count rows)
        (withBound ret extra inputCount gateCount).1
        (withBound ret extra inputCount gateCount).2
        0 (count + 1) (operandOutputIndex ret count outputIndex)) := by
    simpa using h₂
  rcases restoreBound_phase s₂ ret (count + 1) extra inputCount gateCount 0
      (operandOutputIndex ret count outputIndex) input output
      (operandRows ret count rows) with ⟨s₃, h₃⟩
  have h₃' : transition^[count + 1]
      (some (cfg (some (.restoreBound ret)) s₂ input output
        (operandRows ret count rows)
        (withBound ret extra inputCount gateCount).1
        (withBound ret extra inputCount gateCount).2
        0 (count + 1) (operandOutputIndex ret count outputIndex))) =
      some (cfg (some (.restoreBound ret)) s₃ input output
        (operandRows ret count rows)
        (withBound ret (count + extra + 1) inputCount gateCount).1
        (withBound ret (count + extra + 1) inputCount gateCount).2
        0 0 (operandOutputIndex ret count outputIndex)) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₃
  have h₄ : transition^[1]
      (some (cfg (some (.restoreBound ret)) s₃ input output
        (operandRows ret count rows)
        (withBound ret (count + extra + 1) inputCount gateCount).1
        (withBound ret (count + extra + 1) inputCount gateCount).2
        0 0 (operandOutputIndex ret count outputIndex))) =
      some (cfg (some (afterBoundLabel ret))
        { s₃ with counterPresent := false }
        input output (afterBoundRows ret (operandRows ret count rows))
        (withBound ret (count + extra + 1) inputCount gateCount).1
        (afterBoundGateCount ret
          (withBound ret (count + extra + 1) inputCount gateCount).2)
        0 0 (operandOutputIndex ret count outputIndex)) := by
    change step (cfg (some (.restoreBound ret)) s₃ input output
      (operandRows ret count rows)
      (withBound ret (count + extra + 1) inputCount gateCount).1
      (withBound ret (count + extra + 1) inputCount gateCount).2
      0 0 (operandOutputIndex ret count outputIndex)) = _
    exact restore_bound_done_step s₃ ret input output
      (operandRows ret count rows)
      (withBound ret (count + extra + 1) inputCount gateCount).1
      (withBound ret (count + extra + 1) inputCount gateCount).2
      0 (operandOutputIndex ret count outputIndex)
  have h₁₂ := step_comp _ _ h₁' h₂'
  have h₁₃ := step_comp _ _ h₁₂ h₃'
  have hfull := step_comp _ _ h₁₃ h₄
  refine ⟨{ s₃ with counterPresent := false }, ?_⟩
  have hsteps : count + 1 + (count + 1) + (count + 1) + 1 =
      3 * count + 4 := by omega
  rw [← hsteps]
  exact hfull

/-- Exact successful run for an input gate whose source is in range. -/
theorem inputGate_phase (state : State) (inputIndex slack gateIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[2 * gateIndex + 3 * inputIndex + 7]
        (some (cfg (some .gates) state
          (encodeCircuitGate (.input inputIndex) ++ input) output rows
          (inputIndex + slack + 1) gateIndex 0 0 0)) =
        some (cfg (some .gates) finalState input output
          ((encodeNormalizedGateRow gateIndex (.input inputIndex)).reverse ++ rows)
          (inputIndex + slack + 1) (gateIndex + 1) 0 0 0) := by
  have h₁ : transition^[1]
      (some (cfg (some .gates) state
        (encodeCircuitGate (.input inputIndex) ++ input) output rows
        (inputIndex + slack + 1) gateIndex 0 0 0)) =
      some (cfg (some (.rowIndexCopy .input))
        { state with inputBuffer := some .inputMark }
        (encNat inputIndex ++ input) output (.gateRowMark :: rows)
        (inputIndex + slack + 1) gateIndex 0 0 0) := by
    change step (cfg (some .gates) state
      (.inputMark :: (encNat inputIndex ++ input)) output rows
      (inputIndex + slack + 1) gateIndex 0 0 0) = _
    simpa [rawGateTag] using gates_tag_step state .input
      (encNat inputIndex ++ input) output rows (inputIndex + slack + 1)
      gateIndex 0 0 0
  rcases rowPrefix_phase { state with inputBuffer := some .inputMark } .input
      gateIndex (encNat inputIndex ++ input) output (.gateRowMark :: rows)
      (inputIndex + slack + 1) 0 0 with ⟨s₂, h₂⟩
  rcases boundedOperand_phase s₂ .inputGate (by decide) inputIndex slack 0
      gateIndex 0 input output
      (afterRowPrefixRows .input
        (.fieldEnd :: (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
    ⟨s₃, h₃⟩
  have h₁₂ := step_comp _ _ h₁ h₂
  have hfull := step_comp _ _ h₁₂ h₃
  refine ⟨s₃, ?_⟩
  have hsteps : 1 + (2 * gateIndex + 2) + (3 * inputIndex + 4) =
      2 * gateIndex + 3 * inputIndex + 7 := by omega
  rw [← hsteps]
  simpa [encodeNormalizedGateRow, encodeNormalizedNat, encodeNormalizedGate,
    normalizedGateTag,
    afterRowPrefixLabel, afterRowPrefixRows, afterRowPrefixGateCount,
    afterBoundLabel, afterBoundRows, afterBoundGateCount, operandRows,
    operandOutputIndex, withBound, List.reverse_append, List.append_assoc,
    List.reverse_replicate] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
