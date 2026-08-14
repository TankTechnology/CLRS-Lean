import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.MalformedRun

/-!
# Concrete verifier: polynomial runtime estimates
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

/-- A valid gate costs at most a fixed linear function of the input-bit and
already-computed gate counts. -/
theorem gateSteps_le (gate : CircuitGate) (inputCount gateCount : Nat)
    (hvalid : gate.ValidAt inputCount gateCount) :
    gateSteps gateCount gate ≤ 10 * (inputCount + gateCount + 1) := by
  cases gate with
  | input i =>
      simp [CircuitGate.ValidAt] at hvalid
      simp [gateSteps]
      omega
  | const value =>
      simp [gateSteps]
      omega
  | not source =>
      simp [CircuitGate.ValidAt] at hvalid
      simp [gateSteps]
      omega
  | and left right =>
      simp [CircuitGate.ValidAt] at hvalid
      simp [gateSteps]
      omega
  | or left right =>
      simp [CircuitGate.ValidAt] at hvalid
      simp [gateSteps]
      omega

/-- Even without semantic validity, a gate phase's syntactic cost is linear
in its unary encoding and the current value count.  This is used only as a
numeric envelope for malformed streams; invalid gates reject before executing
the nominal successful phase. -/
theorem gateSteps_le_encoding (gate : CircuitGate) (gateCount : Nat) :
    gateSteps gateCount gate ≤
      10 * (gateCount + (encodeCircuitGate gate).length + 1) := by
  cases gate with
  | input i =>
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

/-- The nominal cost attached to any encoded gate list is quadratic in the
list's symbol length and its initial value count, with no validity premise. -/
theorem gateListSteps_le_encoding (gates : List CircuitGate)
    (initialCount : Nat) :
    gateListSteps initialCount gates ≤
      20 * (gates.length + 1) *
        (initialCount + (gates.flatMap encodeCircuitGate).length +
          gates.length + 1) := by
  induction gates generalizing initialCount with
  | nil => simp [gateListSteps]
  | cons gate gates ih =>
      have hhead := gateSteps_le_encoding gate initialCount
      have htail := ih (initialCount + 1)
      simp only [gateListSteps, List.length_cons, List.flatMap_cons,
        List.length_append]
      nlinarith

/-- Summing the linear gate estimate over an ordered valid gate segment gives
a quadratic bound. -/
theorem gateListSteps_le (gates : List CircuitGate)
    (inputCount initialCount : Nat)
    (hvalid : ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputCount (initialCount + i)) :
    gateListSteps initialCount gates ≤
      10 * gates.length * (inputCount + initialCount + gates.length + 1) := by
  induction gates generalizing initialCount with
  | nil => simp [gateListSteps]
  | cons gate gates ih =>
      have hgate : gate.ValidAt inputCount initialCount := by
        simpa using hvalid 0 (by simp)
      have htail : ∀ i (hi : i < gates.length),
          (gates.get ⟨i, hi⟩).ValidAt inputCount (initialCount + 1 + i) := by
        intro i hi
        have hnext := hvalid (i + 1) (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
      have hhead := gateSteps_le gate inputCount initialCount hgate
      have hrest := ih (initialCount + 1) htail
      simp only [gateListSteps, List.length_cons]
      nlinarith

/-- A successful designated-output phase is linear in the certificate and
value-array lengths. -/
theorem outputSteps_le (inputBits : List Bool) (values : Array Bool)
    (outputIndex : Nat) (houtput : outputIndex < values.size) :
    outputSteps inputBits values outputIndex ≤
      10 * (inputBits.length + values.size + 1) := by
  simp [outputSteps, cleanupSteps]
  omega

/-- Every encoded gate contributes at least its tag symbol. -/
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

theorem gates_length_le_encodeCircuit (c : Circuit) :
    c.gates.length ≤ (encodeCircuit c).length := by
  have h := gates_length_le_flat_encoding c.gates
  simp only [encodeCircuit, List.length_append, List.length_cons]
  omega

/-- The exact successful path fits a uniform quadratic in the complete
pair-encoded input length. -/
theorem successfulSteps_le (certificate : List CircuitSym) (c : Circuit)
    (hwf : c.WellFormed)
    (hlength : certificate.length = c.inputCount) :
    successfulSteps certificate c ≤
      50 * ((pairEncoding certificate (encodeCircuit c)).length + 1) ^ 2 := by
  let pairLength := (pairEncoding certificate (encodeCircuit c)).length
  have hpair : pairLength = certificate.length + (encodeCircuit c).length + 1 := by
    simp [pairLength, pairEncoding]
    omega
  have hgates : c.gates.length ≤ (encodeCircuit c).length :=
    gates_length_le_encodeCircuit c
  have hgateRun := gateListSteps_le c.gates certificate.length 0 (by
    intro i hi
    simpa [hlength] using hwf.2 i hi)
  have houtput := outputSteps_le (assignmentBits certificate)
    (c.evalValues (assignmentInputs certificate)) c.output (by
      simpa [Circuit.evalValues_size] using hwf.1)
  simp only [successfulSteps]
  simp only [assignmentBits_length, Circuit.evalValues_size] at houtput
  rw [hlength]
  nlinarith

/-- The concrete verifier already computes the exact public Boolean on every
input.  The final polynomial wrapper strengthens this unbounded witness. -/
noncomputable def generalCircuitVerifierComputable :
    TM2Computable
      (fun pr : List CircuitSym × List CircuitSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => generalCircuitVerifier pr.1 pr.2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  outputsFun := fun ⟨certificate, input⟩ => by
    have hnonempty : Nonempty (TM2Outputs machine (pairEncoding certificate input)
        (some (boolEncoding (generalCircuitVerifier certificate input)))) := by
      rcases verifier_run certificate input with ⟨steps, hrun⟩
      refine ⟨⟨steps, ?_⟩⟩
      change (flip Option.bind step)^[steps]
        (some (initList machine (pairEncoding certificate input))) =
        some (haltList machine [generalCircuitVerifier certificate input])
      exact hrun
    simpa using Classical.choice hnonempty

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
