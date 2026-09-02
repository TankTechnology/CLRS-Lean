import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Run
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding.Length

/-! # General-circuit formula emitter: structural runtime bounds -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- A gate expression costs at most four scans of the permanent input-count
prefix plus its own normalized body. -/
theorem gateExprSteps_le (inputCount : Nat) (gate : CircuitGate) :
    gateExprSteps inputCount gate ≤
      4 * inputCount + (encodeNormalizedGate gate).length + 4 := by
  cases gate with
  | input inputIndex =>
      simp [gateExprSteps, inputGateSteps, encodeNormalizedGate,
        encodeNormalizedNat]
      omega
  | const value =>
      cases value <;>
        simp [gateExprSteps, constantGateSteps, encodeNormalizedGate]
  | not source =>
      simp [gateExprSteps, notGateSteps, encodeNormalizedGate,
        encodeNormalizedNat]
      omega
  | and left right =>
      simp [gateExprSteps, binaryGateSteps, encodeNormalizedGate,
        encodeNormalizedNat]
      omega
  | or left right =>
      simp [gateExprSteps, binaryGateSteps, encodeNormalizedGate,
        encodeNormalizedNat]
      omega

/-- One indexed row has a linear overhead in the permanent input count; all
other work is charged directly to symbols present in that row. -/
theorem gateRowSteps_le (inputCount gateIndex : Nat) (gate : CircuitGate) :
    gateRowSteps inputCount gateIndex gate ≤
      (6 * inputCount + 6) +
        (encodeNormalizedGateRow gateIndex gate).length := by
  have hgate := gateExprSteps_le inputCount gate
  simp [gateRowSteps, encodeNormalizedGateRow] at ⊢
  omega

/-- Summing the row bound charges at most one input-count scan budget per
gate, in addition to the symbols of the indexed row stream itself. -/
theorem gateRowsStepsFrom_le (inputCount gateIndex : Nat)
    (gates : List CircuitGate) :
    gateRowsStepsFrom inputCount gateIndex gates ≤
      gates.length * (6 * inputCount + 6) +
        (encodeNormalizedGateRowsFrom gateIndex gates).length := by
  induction gates generalizing gateIndex with
  | nil => simp [gateRowsStepsFrom, encodeNormalizedGateRowsFrom]
  | cons gate gates ih =>
      have hrow := gateRowSteps_le inputCount gateIndex gate
      have htail := ih (gateIndex + 1)
      calc
        gateRowsStepsFrom inputCount gateIndex (gate :: gates) =
            gateRowSteps inputCount gateIndex gate +
              gateRowsStepsFrom inputCount (gateIndex + 1) gates := rfl
        _ ≤ ((6 * inputCount + 6) +
              (encodeNormalizedGateRow gateIndex gate).length) +
            (gates.length * (6 * inputCount + 6) +
              (encodeNormalizedGateRowsFrom (gateIndex + 1) gates).length) :=
          Nat.add_le_add hrow htail
        _ = (gate :: gates).length * (6 * inputCount + 6) +
            (encodeNormalizedGateRowsFrom gateIndex (gate :: gates)).length := by
          simp only [List.length_cons, encodeNormalizedGateRowsFrom,
            List.length_append]
          ring

/-- Exact size decomposition of a canonical guarded work record. -/
theorem encodeNormalizedCircuit_length_eq (c : Circuit) :
    (encodeNormalizedCircuit c).length =
      c.inputCount + c.output + c.gates.length + 7 +
        (encodeNormalizedGateRowsFrom 0 c.gates).length := by
  simp [encodeNormalizedCircuit]
  omega

theorem inputCount_le_normalizedLength (c : Circuit) :
    c.inputCount ≤ (encodeNormalizedCircuit c).length := by
  rw [encodeNormalizedCircuit_length_eq]
  omega

theorem gateCount_le_normalizedLength (c : Circuit) :
    c.gates.length ≤ (encodeNormalizedCircuit c).length := by
  rw [encodeNormalizedCircuit_length_eq]
  omega

theorem outputIndex_le_normalizedLength (c : Circuit) :
    c.output ≤ (encodeNormalizedCircuit c).length := by
  rw [encodeNormalizedCircuit_length_eq]
  omega

theorem rowStreamLength_le_normalizedLength (c : Circuit) :
    (encodeNormalizedGateRowsFrom 0 c.gates).length ≤
      (encodeNormalizedCircuit c).length := by
  rw [encodeNormalizedCircuit_length_eq]
  omega

/-- The direct reverse emitter has a single quadratic envelope in the length
of its canonical guarded input record. -/
theorem reverseSuccessfulSteps_le (c : Circuit) :
    reverseSuccessfulSteps c ≤
      16 * ((encodeNormalizedCircuit c).length + 1) ^ 2 := by
  let n := (encodeNormalizedCircuit c).length
  have hi : c.inputCount ≤ n := inputCount_le_normalizedLength c
  have ho : c.output ≤ n := outputIndex_le_normalizedLength c
  have hg : c.gates.length ≤ n := gateCount_le_normalizedLength c
  have hr : (encodeNormalizedGateRowsFrom 0 c.gates).length ≤ n :=
    rowStreamLength_le_normalizedLength c
  have hrows := gateRowsStepsFrom_le c.inputCount 0 c.gates
  have hfactor : 6 * c.inputCount + 6 ≤ 6 * n + 6 := by omega
  have hproduct :
      c.gates.length * (6 * c.inputCount + 6) ≤ n * (6 * n + 6) :=
    Nat.mul_le_mul hg hfactor
  have hrows' : gateRowsStepsFrom c.inputCount 0 c.gates ≤
      n * (6 * n + 6) + n := by omega
  have hheader : headerSteps c ≤ 9 * (n + 1) := by
    simp [headerSteps]
    omega
  simp only [reverseSuccessfulSteps]
  nlinarith [sq_nonneg (n : Int)]

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
