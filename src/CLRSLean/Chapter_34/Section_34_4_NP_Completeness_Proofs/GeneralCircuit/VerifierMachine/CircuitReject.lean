import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CircuitRun
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.RejectPhases

/-!
# Concrete verifier: rejection of invalid gates
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition

private abbrev transition := flip Option.bind step

/-- Every canonically encoded gate that violates its input/predecessor bound
reaches the common rejecting halt. -/
theorem gate_reject_of_not_valid (state : State) (gate : CircuitGate)
    (inputBits : List Bool) (values : Array Bool)
    (rest : List (Option CircuitSym))
    (hinvalid : ¬ gate.ValidAt inputBits.length values.size) :
    Rejects (cfg (some .gates) state
      (List.map some (encodeCircuitGate gate) ++ rest)
      [] inputBits values.toList.reverse [] values.size 0 0) := by
  cases gate with
  | input i =>
      have htag := gates_input_step state (List.map some (encNat i) ++ rest)
        [] inputBits values.toList.reverse [] values.size 0 0
      apply Rejects.before_step (by simpa [encodeCircuitGate] using htag)
      rcases parse_nat_phase
          { state with inputBuffer := some (some .inputMark) }
          .inputGate i 0 rest [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterParse, hparse⟩
      apply Rejects.before_steps (i + 1) (by simpa [parsedLabel] using hparse)
      exact certificate_lookup_reject afterParse inputBits i rest
        values.toList.reverse [] values.size 0 (by
          simp [CircuitGate.ValidAt] at hinvalid
          omega)
  | const value =>
      simp [CircuitGate.ValidAt] at hinvalid
  | not source =>
      have htag := gates_not_step state (List.map some (encNat source) ++ rest)
        [] inputBits values.toList.reverse [] values.size 0 0
      apply Rejects.before_step (by simpa [encodeCircuitGate] using htag)
      rcases parse_nat_phase
          { state with inputBuffer := some (some .notMark) }
          .notGate source 0 rest [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterParse, hparse⟩
      apply Rejects.before_steps (source + 1) (by simpa [parsedLabel] using hparse)
      exact gate_lookup_reject afterParse .notGate values.size source rest
        inputBits values.toList.reverse [] 0 (by
          simp [CircuitGate.ValidAt] at hinvalid
          omega)
  | and left right =>
      let rightInput := List.map some (encNat right) ++ rest
      have htag := gates_and_step state
        (List.map some (encNat left) ++ rightInput)
        [] inputBits values.toList.reverse [] values.size 0 0
      apply Rejects.before_step (by
        simpa [encodeCircuitGate, rightInput, List.map_append, List.append_assoc]
          using htag)
      rcases parse_nat_phase
          { state with inputBuffer := some (some .andMark) }
          .andLeft left 0 rightInput [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterLeftParse, hleftParse⟩
      apply Rejects.before_steps (left + 1)
        (by simpa [parsedLabel] using hleftParse)
      by_cases hleft : left < values.size
      · rcases reverse_split_getD values.toList left hleft with
          ⟨front, older, hsplit, hlength, holder⟩
        have hcount : front.length + older.length + 1 = values.size := by
          simpa using hlength
        rcases gate_lookup_and_left_phase afterLeftParse front older
            (values.toList.getD left false) rightInput [] inputBits with
          ⟨afterLeftLookup, hlookup⟩
        change transition^[2 * older.length + 2 * front.length + 6] _ = _ at hlookup
        have hlookup' : transition^[2 * values.size + 4]
            (some (cfg (some (.gateSubtract .andLeft)) afterLeftParse rightInput
              [] inputBits values.toList.reverse [] values.size left 0)) =
            some (cfg (some (.parseNat
                (.andRight (values.toList.getD left false))))
              afterLeftLookup rightInput [] inputBits values.toList.reverse []
              values.size 0 0) := by
          have hcost : 2 * values.size + 4 =
              2 * older.length + 2 * front.length + 6 := by omega
          rw [hcost, hsplit, ← hcount]
          simpa only [holder] using hlookup
        apply Rejects.before_steps (2 * values.size + 4) hlookup'
        rcases parse_nat_phase afterLeftLookup
            (.andRight (values.toList.getD left false)) right 0 rest [] inputBits
            values.toList.reverse [] values.size 0 with
          ⟨afterRightParse, hrightParse⟩
        apply Rejects.before_steps (right + 1)
          (by simpa only [parsedLabel, rightInput, Nat.zero_add] using hrightParse)
        have hright : values.size ≤ right := by
          simp [CircuitGate.ValidAt, hleft] at hinvalid
          omega
        exact gate_lookup_reject afterRightParse
          (.andRight (values.toList.getD left false)) values.size right rest
          inputBits values.toList.reverse [] 0 hright
      · exact gate_lookup_reject afterLeftParse .andLeft values.size left rightInput
          inputBits values.toList.reverse [] 0 (by omega)
  | or left right =>
      let rightInput := List.map some (encNat right) ++ rest
      have htag := gates_or_step state
        (List.map some (encNat left) ++ rightInput)
        [] inputBits values.toList.reverse [] values.size 0 0
      apply Rejects.before_step (by
        simpa [encodeCircuitGate, rightInput, List.map_append, List.append_assoc]
          using htag)
      rcases parse_nat_phase
          { state with inputBuffer := some (some .orMark) }
          .orLeft left 0 rightInput [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterLeftParse, hleftParse⟩
      apply Rejects.before_steps (left + 1)
        (by simpa [parsedLabel] using hleftParse)
      by_cases hleft : left < values.size
      · rcases reverse_split_getD values.toList left hleft with
          ⟨front, older, hsplit, hlength, holder⟩
        have hcount : front.length + older.length + 1 = values.size := by
          simpa using hlength
        rcases gate_lookup_or_left_phase afterLeftParse front older
            (values.toList.getD left false) rightInput [] inputBits with
          ⟨afterLeftLookup, hlookup⟩
        change transition^[2 * older.length + 2 * front.length + 6] _ = _ at hlookup
        have hlookup' : transition^[2 * values.size + 4]
            (some (cfg (some (.gateSubtract .orLeft)) afterLeftParse rightInput
              [] inputBits values.toList.reverse [] values.size left 0)) =
            some (cfg (some (.parseNat
                (.orRight (values.toList.getD left false))))
              afterLeftLookup rightInput [] inputBits values.toList.reverse []
              values.size 0 0) := by
          have hcost : 2 * values.size + 4 =
              2 * older.length + 2 * front.length + 6 := by omega
          rw [hcost, hsplit, ← hcount]
          simpa only [holder] using hlookup
        apply Rejects.before_steps (2 * values.size + 4) hlookup'
        rcases parse_nat_phase afterLeftLookup
            (.orRight (values.toList.getD left false)) right 0 rest [] inputBits
            values.toList.reverse [] values.size 0 with
          ⟨afterRightParse, hrightParse⟩
        apply Rejects.before_steps (right + 1)
          (by simpa only [parsedLabel, rightInput, Nat.zero_add] using hrightParse)
        have hright : values.size ≤ right := by
          simp [CircuitGate.ValidAt, hleft] at hinvalid
          omega
        exact gate_lookup_reject afterRightParse
          (.orRight (values.toList.getD left false)) values.size right rest
          inputBits values.toList.reverse [] 0 hright
      · exact gate_lookup_reject afterLeftParse .orLeft values.size left rightInput
          inputBits values.toList.reverse [] 0 (by omega)

/-- An ordered gate stream rejects at its first invalid gate. -/
theorem gate_list_reject_of_not_valid (state : State) (gates : List CircuitGate)
    (inputBits : List Bool) (values : Array Bool)
    (rest : List (Option CircuitSym))
    (hinvalid : ¬ ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputBits.length (values.size + i)) :
    Rejects (cfg (some .gates) state
      (List.map some (gates.flatMap encodeCircuitGate) ++ rest)
      [] inputBits values.toList.reverse [] values.size 0 0) := by
  induction gates generalizing state values with
  | nil => simp at hinvalid
  | cons gate gates ih =>
      by_cases hgate : gate.ValidAt inputBits.length values.size
      · let nextValues :=
          values.push (gate.evalWith (fun i => inputBits.getD i false) values)
        have htailInvalid : ¬ ∀ i (hi : i < gates.length),
            (gates.get ⟨i, hi⟩).ValidAt inputBits.length (nextValues.size + i) := by
          intro htail
          apply hinvalid
          intro i hi
          cases i with
          | zero => simpa using hgate
          | succ i =>
              have hi' : i < gates.length := by simpa using hi
              have hnext := htail i hi'
              simpa [nextValues, Array.size_push, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm] using hnext
        let tailInput := List.map some (gates.flatMap encodeCircuitGate) ++ rest
        rcases gate_phase state gate inputBits values tailInput hgate with
          ⟨afterGate, hrun⟩
        have hreject := ih afterGate nextValues htailInvalid
        apply Rejects.before_steps (gateSteps values.size gate)
        · simpa [tailInput, List.map_append, List.append_assoc] using hrun
        · simpa [tailInput, nextValues, Array.size_push] using hreject
      · simpa [List.map_append, List.append_assoc] using
          gate_reject_of_not_valid state gate inputBits values
            (List.map some (gates.flatMap encodeCircuitGate) ++ rest) hgate

/-- A canonical output marker rejects when its designated gate does not exist. -/
theorem output_reject_of_not_valid (state : State) (inputBits : List Bool)
    (values : Array Bool) (outputIndex : Nat)
    (hinvalid : values.size ≤ outputIndex) :
    Rejects (cfg (some .gates) state
      (List.map some (.outputMark :: encNat outputIndex))
      [] inputBits values.toList.reverse [] values.size 0 0) := by
  have htag := gates_output_step state (List.map some (encNat outputIndex))
    [] inputBits values.toList.reverse [] values.size 0 0
  apply Rejects.before_step (by simpa using htag)
  rcases parse_nat_phase
      { state with inputBuffer := some (some .outputMark) }
      .outputGate outputIndex 0 [] [] inputBits values.toList.reverse [] values.size 0 with
    ⟨afterParse, hparse⟩
  apply Rejects.before_steps (outputIndex + 1)
    (by simpa only [parsedLabel, Nat.zero_add, List.append_nil] using hparse)
  let afterTrailing : State := { afterParse with inputBuffer := none }
  have htrailing := check_trailing_empty_step afterParse [] inputBits
    values.toList.reverse [] values.size outputIndex 0
  apply Rejects.before_step (by simpa [afterTrailing] using htrailing)
  exact gate_lookup_reject afterTrailing .outputGate values.size outputIndex []
    inputBits values.toList.reverse [] 0 hinvalid

/-- Once the header has been accepted, a canonical circuit body rejects if
the circuit is not well formed. -/
theorem circuit_body_reject_of_not_wellFormed (state : State)
    (c : Circuit) (inputBits : List Bool)
    (hbitsLength : inputBits.length = c.inputCount)
    (hinvalid : ¬ c.WellFormed) :
    Rejects (cfg (some .gates) state
      (List.map some (c.gates.flatMap encodeCircuitGate) ++
        List.map some (.outputMark :: encNat c.output))
      [] inputBits [] [] 0 0 0) := by
  let outputInput := List.map some (.outputMark :: encNat c.output)
  by_cases hgates : ∀ i (hi : i < c.gates.length),
      (c.gates.get ⟨i, hi⟩).ValidAt inputBits.length
        ((#[] : Array Bool).size + i)
  · rcases gate_list_phase state c.gates inputBits #[] outputInput hgates with
      ⟨afterGates, hrun⟩
    let finalValues := evalGateList inputBits #[] c.gates
    have hsize : finalValues.size = c.gates.length := by
      simp [finalValues]
    have houtput : finalValues.size ≤ c.output := by
      rw [hsize]
      by_contra hout
      apply hinvalid
      refine ⟨by omega, ?_⟩
      intro i hi
      have hgate := hgates i hi
      simpa [hbitsLength] using hgate
    apply Rejects.before_steps (gateListSteps 0 c.gates)
    · simpa [outputInput, finalValues] using hrun
    · simpa [outputInput, finalValues, hsize] using
        output_reject_of_not_valid afterGates inputBits finalValues
          c.output houtput
  · exact gate_list_reject_of_not_valid state c.gates inputBits #[] outputInput
      hgates

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
