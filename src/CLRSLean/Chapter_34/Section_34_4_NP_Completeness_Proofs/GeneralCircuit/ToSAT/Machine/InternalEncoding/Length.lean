import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding.RoundTrip

/-!
# Guarded circuit work-record length bounds

Chronological gate indices are unary, so the internal record can be quadratic
even though each individual gate body preserves the raw encoding length.
-/

namespace CLRS.Chapter34

@[simp] theorem encodeNormalizedNat_length (n : Nat) :
    (encodeNormalizedNat n).length = n + 1 := by
  simp [encodeNormalizedNat]

/-- Changing finite tags does not change a gate body's encoded length. -/
theorem encodeNormalizedGate_length_eq (gate : CircuitGate) :
    (encodeNormalizedGate gate).length = (encodeCircuitGate gate).length := by
  cases gate with
  | input inputIndex => simp [encodeNormalizedGate, encodeCircuitGate, encNat]
  | const value => cases value <;> simp [encodeNormalizedGate, encodeCircuitGate]
  | not source => simp [encodeNormalizedGate, encodeCircuitGate, encNat]
  | and left right => simp [encodeNormalizedGate, encodeCircuitGate, encNat]; omega
  | or left right => simp [encodeNormalizedGate, encodeCircuitGate, encNat]; omega

/-- One indexed row consists of its unary index, the unchanged gate body, and
three structural symbols. -/
theorem encodeNormalizedGateRow_length (gateIndex : Nat)
    (gate : CircuitGate) :
    (encodeNormalizedGateRow gateIndex gate).length =
      gateIndex + (encodeCircuitGate gate).length + 3 := by
  simp [encodeNormalizedGateRow, encodeNormalizedGate_length_eq]
  omega

private theorem encodeNormalizedGateRowsFrom_length_le
    (gateIndex : Nat) (gates : List CircuitGate) :
    (encodeNormalizedGateRowsFrom gateIndex gates).length ≤
      (gates.flatMap encodeCircuitGate).length +
        gates.length * (gateIndex + gates.length + 3) := by
  induction gates generalizing gateIndex with
  | nil => simp [encodeNormalizedGateRowsFrom]
  | cons gate gates ih =>
      have htail := ih (gateIndex + 1)
      simp only [encodeNormalizedGateRowsFrom, List.length_append,
        encodeNormalizedGateRow_length, List.flatMap_cons,
        List.length_cons] at htail ⊢
      nlinarith

private theorem gates_length_le_flatMap_encodeCircuitGate
    (gates : List CircuitGate) :
    gates.length ≤ (gates.flatMap encodeCircuitGate).length := by
  induction gates with
  | nil => simp
  | cons gate gates ih =>
      have hgate : 1 ≤ (encodeCircuitGate gate).length := by
        cases gate with
        | input inputIndex => simp [encodeCircuitGate]
        | const value => cases value <;> simp [encodeCircuitGate]
        | not source => simp [encodeCircuitGate]
        | and left right => simp [encodeCircuitGate]
        | or left right => simp [encodeCircuitGate]
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega

/-- The indexed internal record is at most quadratic in the raw canonical
circuit encoding. -/
theorem encodeNormalizedCircuit_length_le (c : Circuit) :
    (encodeNormalizedCircuit c).length ≤
      8 * ((encodeCircuit c).length + 1) ^ 2 := by
  let rawGateLength := (c.gates.flatMap encodeCircuitGate).length
  let rawLength := (encodeCircuit c).length
  have hrows := encodeNormalizedGateRowsFrom_length_le 0 c.gates
  have hgates : c.gates.length ≤ rawGateLength :=
    gates_length_le_flatMap_encodeCircuitGate c.gates
  have hraw : rawLength = c.inputCount + rawGateLength + c.output + 3 := by
    simp [rawLength, encodeCircuit, rawGateLength, encNat]
    omega
  have hgatesRaw : c.gates.length ≤ rawLength := by omega
  have hrecord :
      (encodeNormalizedCircuit c).length =
        c.inputCount + c.output + c.gates.length + 7 +
          (encodeNormalizedGateRowsFrom 0 c.gates).length := by
    simp [encodeNormalizedCircuit]
    omega
  rw [hrecord]
  nlinarith

/-- Guarded normalization has one quadratic bound on malformed, ill-formed,
and valid raw inputs. -/
theorem normalizeGeneralCircuit_length_le (input : List CircuitSym) :
    (normalizeGeneralCircuit input).length ≤
      8 * (input.length + 1) ^ 2 := by
  cases hdecode : decodeCircuit input with
  | none =>
      have hbase : 1 ≤ input.length + 1 := by omega
      have hsquare : 1 ≤ (input.length + 1) ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul hbase hbase
      have hpositive : 1 ≤ 8 * (input.length + 1) ^ 2 := by nlinarith
      simpa [normalizeGeneralCircuit, hdecode] using hpositive
  | some c =>
      by_cases hwellFormed : c.WellFormed
      · have hcanonical := encodeCircuit_of_decodeCircuit_eq_some hdecode
        have hbound := encodeNormalizedCircuit_length_le c
        simpa [normalizeGeneralCircuit, hdecode, hwellFormed, hcanonical] using hbound
      · have hbase : 1 ≤ input.length + 1 := by omega
        have hsquare : 1 ≤ (input.length + 1) ^ 2 := by
          simpa [pow_two] using Nat.mul_le_mul hbase hbase
        have hpositive : 1 ≤ 8 * (input.length + 1) ^ 2 := by nlinarith
        simpa [normalizeGeneralCircuit, hdecode, hwellFormed] using hpositive

end CLRS.Chapter34
