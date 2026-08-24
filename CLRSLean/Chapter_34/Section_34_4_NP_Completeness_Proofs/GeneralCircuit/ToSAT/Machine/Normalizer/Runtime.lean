import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Run

/-!
# Guarded circuit normalizer: successful runtime bounds

The exact successful cost is first bounded by a small cubic envelope.  The
public layer later weakens every route to one deliberately generous sextic
polynomial, shared with malformed and ill-formed inputs.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

/-- A gate's nominal normalization cost is linear in its current chronological
index and raw unary body length. -/
theorem gateSteps_le_encoding (gateIndex : Nat) (gate : CircuitGate) :
    gateSteps gateIndex gate ≤
      10 * (gateIndex + (encodeCircuitGate gate).length + 1) := by
  cases gate with
  | input inputIndex =>
      simp [gateSteps, encodeCircuitGate, encNat]
      omega
  | const value =>
      cases value <;> simp [gateSteps, encodeCircuitGate] <;> omega
  | not source =>
      simp [gateSteps, encodeCircuitGate, encNat]
      omega
  | and left right =>
      simp [gateSteps, encodeCircuitGate, encNat]
      omega
  | or left right =>
      simp [gateSteps, encodeCircuitGate, encNat]
      omega

/-- The nominal cost of a complete gate family is quadratic in its raw symbol
length and initial chronological index. -/
theorem gateFamilyStepsFrom_le_encoding (gateIndex : Nat)
    (gates : List CircuitGate) :
    gateFamilyStepsFrom gateIndex gates ≤
      20 * (gates.length + 1) *
        (gateIndex + (gates.flatMap encodeCircuitGate).length +
          gates.length + 1) := by
  induction gates generalizing gateIndex with
  | nil => simp [gateFamilyStepsFrom]
  | cons gate gates ih =>
      have hhead := gateSteps_le_encoding gateIndex gate
      have htail := ih (gateIndex + 1)
      simp only [gateFamilyStepsFrom, List.length_cons, List.flatMap_cons,
        List.length_append]
      nlinarith

/-- Every encoded gate contributes at least its finite tag. -/
theorem gates_length_le_flat_encoding (gates : List CircuitGate) :
    gates.length ≤ (gates.flatMap encodeCircuitGate).length := by
  induction gates with
  | nil => simp
  | cons gate gates ih =>
      have hgate : 1 ≤ (encodeCircuitGate gate).length := by
        cases gate with
        | input i => simp [encodeCircuitGate]
        | const value => cases value <;> simp [encodeCircuitGate]
        | not source => simp [encodeCircuitGate]
        | and left right => simp [encodeCircuitGate]
        | or left right => simp [encodeCircuitGate]
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega

/-- Public step envelope.  Its large coefficient intentionally leaves ample
room for all parser cleanup routes proved in `RejectBounds`. -/
def stepBound (inputLength : Nat) : Nat :=
  1048576 * (inputLength + 1) ^ 6 + 1048576

/-- The exact canonical successful run is dominated by the public envelope. -/
theorem successfulSteps_le (c : Circuit) :
    successfulSteps c ≤ stepBound (encodeCircuit c).length := by
  let n := (encodeCircuit c).length
  let gateSymbols := (c.gates.flatMap encodeCircuitGate).length
  change successfulSteps c ≤ stepBound n
  have hgateRun := gateFamilyStepsFrom_le_encoding 0 c.gates
  have hgates := gates_length_le_flat_encoding c.gates
  have hrecord := encodeNormalizedCircuit_length_le c
  have hparts : n = c.inputCount + gateSymbols + c.output + 3 := by
    simp [n, gateSymbols, encodeCircuit, encNat]
    omega
  have hrows : (encodeNormalizedGateRowsFrom 0 c.gates).length ≤
      8 * (n + 1) ^ 2 := by
    have hheader :
        (encodeNormalizedGateRowsFrom 0 c.gates).length ≤
          (encodeNormalizedCircuit c).length := by
      simp [encodeNormalizedCircuit]
      omega
    exact hheader.trans (by simpa [n] using hrecord)
  have hpow : (n + 1) ^ 2 ≤ (n + 1) ^ 6 :=
    pow_le_pow_right₀ (show 1 ≤ n + 1 by omega) (by omega)
  simp only [successfulSteps, validFinishSteps, stepBound]
  simp only [Nat.zero_add] at hgateRun
  nlinarith

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
