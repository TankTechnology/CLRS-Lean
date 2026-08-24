import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.GateUnary

/-!
# Guarded circuit normalizer: binary gates
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

def binaryKind : Bool → GateKind
  | false => .or
  | true => .and

def binaryGate (isAnd : Bool) (left right : Nat) : CircuitGate :=
  if isAnd then .and left right else .or left right

def binaryLeftReturn : Bool → Return
  | false => .orLeft
  | true => .andLeft

def binaryRightReturn : Bool → Return
  | false => .orRight
  | true => .andRight

private theorem binaryGate_phase (state : State) (isAnd : Bool)
    (left right gateIndex inputCount : Nat)
    (hleft : left < gateIndex) (hright : right < gateIndex)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[2 * gateIndex + 3 * left + 3 * right + 11]
        (some (cfg (some .gates) state
          (encodeCircuitGate (binaryGate isAnd left right) ++ input) output rows
          inputCount gateIndex 0 0 0)) =
        some (cfg (some .gates) finalState input output
          ((encodeNormalizedGateRow gateIndex
            (binaryGate isAnd left right)).reverse ++ rows)
          inputCount (gateIndex + 1) 0 0 0) := by
  obtain ⟨leftSlack, hleftEq⟩ := Nat.exists_eq_add_of_lt hleft
  obtain ⟨rightSlack, hrightEq⟩ := Nat.exists_eq_add_of_lt hright
  have h₁ : transition^[1]
      (some (cfg (some .gates) state
        (encodeCircuitGate (binaryGate isAnd left right) ++ input) output rows
        inputCount gateIndex 0 0 0)) =
      some (cfg (some (.rowIndexCopy (binaryKind isAnd)))
        { state with inputBuffer := some (rawGateTag (binaryKind isAnd)) }
        (encNat left ++ encNat right ++ input) output (.gateRowMark :: rows)
        inputCount gateIndex 0 0 0) := by
    change step (cfg (some .gates) state
      (encodeCircuitGate (binaryGate isAnd left right) ++ input) output rows
      inputCount gateIndex 0 0 0) = _
    have htag := gates_tag_step state (binaryKind isAnd)
      (encNat left ++ encNat right ++ input) output rows inputCount gateIndex 0 0 0
    cases isAnd <;>
      simpa [binaryGate, binaryKind, rawGateTag, encodeCircuitGate,
        List.append_assoc] using htag
  rcases rowPrefix_phase
      { state with inputBuffer := some (rawGateTag (binaryKind isAnd)) }
      (binaryKind isAnd) gateIndex (encNat left ++ encNat right ++ input)
      output (.gateRowMark :: rows) inputCount 0 0 with ⟨s₂, h₂⟩
  have h₂' : transition^[2 * gateIndex + 2]
      (some (cfg (some (.rowIndexCopy (binaryKind isAnd)))
        { state with inputBuffer := some (rawGateTag (binaryKind isAnd)) }
        (encNat left ++ encNat right ++ input) output (.gateRowMark :: rows)
        inputCount gateIndex 0 0 0)) =
      some (cfg (some (.parseOperand (binaryLeftReturn isAnd))) s₂
        (encNat left ++ encNat right ++ input) output
        (afterRowPrefixRows (binaryKind isAnd)
          (.fieldEnd :: (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
        inputCount gateIndex 0 0 0) := by
    cases isAnd <;>
      simpa [binaryKind, binaryLeftReturn, rawGateTag, afterRowPrefixLabel,
        afterRowPrefixGateCount] using h₂
  rcases boundedOperand_phase s₂ (binaryLeftReturn isAnd) (by
      cases isAnd <;> decide) left leftSlack inputCount 0 0
      (encNat right ++ input) output
      (afterRowPrefixRows (binaryKind isAnd)
        (.fieldEnd :: (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
    ⟨s₃, h₃⟩
  have h₃' : transition^[3 * left + 4]
      (some (cfg (some (.parseOperand (binaryLeftReturn isAnd))) s₂
        (encNat left ++ encNat right ++ input) output
        (afterRowPrefixRows (binaryKind isAnd)
          (.fieldEnd :: (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
        inputCount gateIndex 0 0 0)) =
      some (cfg (some (.parseOperand (binaryRightReturn isAnd))) s₃
        (encNat right ++ input) output
        (afterBoundRows (binaryLeftReturn isAnd)
          (operandRows (binaryLeftReturn isAnd) left
            (afterRowPrefixRows (binaryKind isAnd)
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))))
        inputCount gateIndex 0 0 0) := by
    cases isAnd <;>
      simpa [binaryLeftReturn, binaryRightReturn, afterBoundLabel,
        afterBoundRows, afterBoundGateCount, operandOutputIndex, withBound,
        hleftEq] using h₃
  rcases boundedOperand_phase s₃ (binaryRightReturn isAnd) (by
      cases isAnd <;> decide) right rightSlack inputCount 0 0 input output
      (afterBoundRows (binaryLeftReturn isAnd)
        (operandRows (binaryLeftReturn isAnd) left
          (afterRowPrefixRows (binaryKind isAnd)
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows))))) with
    ⟨s₄, h₄⟩
  have h₄' : transition^[3 * right + 4]
      (some (cfg (some (.parseOperand (binaryRightReturn isAnd))) s₃
        (encNat right ++ input) output
        (afterBoundRows (binaryLeftReturn isAnd)
          (operandRows (binaryLeftReturn isAnd) left
            (afterRowPrefixRows (binaryKind isAnd)
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))))
        inputCount gateIndex 0 0 0)) =
      some (cfg (some .gates) s₄ input output
        (afterBoundRows (binaryRightReturn isAnd)
          (operandRows (binaryRightReturn isAnd) right
            (afterBoundRows (binaryLeftReturn isAnd)
              (operandRows (binaryLeftReturn isAnd) left
                (afterRowPrefixRows (binaryKind isAnd)
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++
                      .gateRowMark :: rows)))))))
        inputCount (gateIndex + 1) 0 0 0) := by
    cases isAnd <;>
      simpa [binaryRightReturn, afterBoundLabel, afterBoundRows,
        afterBoundGateCount, operandOutputIndex, withBound, hrightEq] using h₄
  have h₁₂ := step_comp _ _ h₁ h₂'
  have h₁₃ := step_comp _ _ h₁₂ h₃'
  have hfull := step_comp _ _ h₁₃ h₄'
  refine ⟨s₄, ?_⟩
  have hsteps : 1 + (2 * gateIndex + 2) + (3 * left + 4) +
      (3 * right + 4) = 2 * gateIndex + 3 * left + 3 * right + 11 := by
    omega
  rw [← hsteps]
  cases isAnd <;>
    simpa [binaryGate, binaryKind, binaryLeftReturn, binaryRightReturn,
      encodeNormalizedGateRow, encodeNormalizedNat, encodeNormalizedGate,
      normalizedGateTag, afterRowPrefixLabel, afterRowPrefixRows,
      afterRowPrefixGateCount, afterBoundLabel, afterBoundRows,
      afterBoundGateCount, operandRows, operandOutputIndex, withBound,
      List.reverse_append, List.append_assoc, List.reverse_replicate] using hfull

/-- Exact successful run for an AND gate. -/
theorem andGate_phase (state : State) (left right gateIndex inputCount : Nat)
    (hleft : left < gateIndex) (hright : right < gateIndex)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[2 * gateIndex + 3 * left + 3 * right + 11]
        (some (cfg (some .gates) state
          (encodeCircuitGate (.and left right) ++ input) output rows
          inputCount gateIndex 0 0 0)) =
        some (cfg (some .gates) finalState input output
          ((encodeNormalizedGateRow gateIndex (.and left right)).reverse ++ rows)
          inputCount (gateIndex + 1) 0 0 0) := by
  simpa [binaryGate] using
    binaryGate_phase state true left right gateIndex inputCount hleft hright
      input output rows

/-- Exact successful run for an OR gate. -/
theorem orGate_phase (state : State) (left right gateIndex inputCount : Nat)
    (hleft : left < gateIndex) (hright : right < gateIndex)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[2 * gateIndex + 3 * left + 3 * right + 11]
        (some (cfg (some .gates) state
          (encodeCircuitGate (.or left right) ++ input) output rows
          inputCount gateIndex 0 0 0)) =
        some (cfg (some .gates) finalState input output
          ((encodeNormalizedGateRow gateIndex (.or left right)).reverse ++ rows)
          inputCount (gateIndex + 1) 0 0 0) := by
  simpa [binaryGate] using
    binaryGate_phase state false left right gateIndex inputCount hleft hright
      input output rows

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
