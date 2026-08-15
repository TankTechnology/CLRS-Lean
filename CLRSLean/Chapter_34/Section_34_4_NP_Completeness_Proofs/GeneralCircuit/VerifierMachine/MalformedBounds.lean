import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.RejectBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Runtime

/-!
# Concrete verifier: malformed-route bounds

This module lifts the exact invalid-gate and malformed-encoding runs to
explicit quantitative budgets.  Local route bounds remain intentionally
generous; the public runtime layer later weakens them to one polynomial in the
complete pair-encoded input length.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- Generous linear budget for rejection while decoding one canonical gate. -/
def gateRejectBound (gate : CircuitGate) (inputBits : List Bool)
    (values : Array Bool) (rest : List (Option CircuitSym)) : Nat :=
  2 * (encodeCircuitGate gate).length + 4 * values.size +
    2 * inputBits.length + rest.length + 20

/-- Every canonical gate violating an input/predecessor bound rejects within
the local gate budget. -/
theorem gate_rejectsIn_of_not_valid (state : State) (gate : CircuitGate)
    (inputBits : List Bool) (values : Array Bool)
    (rest : List (Option CircuitSym))
    (hinvalid : ¬ gate.ValidAt inputBits.length values.size) :
    RejectsIn (cfg (some .gates) state
      (List.map some (encodeCircuitGate gate) ++ rest)
      [] inputBits values.toList.reverse [] values.size 0 0)
      (gateRejectBound gate inputBits values rest) := by
  cases gate with
  | input i =>
      have hi : inputBits.length ≤ i := by
        simpa [CircuitGate.ValidAt] using hinvalid
      have htag := gates_input_step state (List.map some (encNat i) ++ rest)
        [] inputBits values.toList.reverse [] values.size 0 0
      rcases parse_nat_phase
          { state with inputBuffer := some (some .inputMark) }
          .inputGate i 0 rest [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterParse, hparse⟩
      have hlookup := certificate_lookup_rejectsIn afterParse inputBits i rest
        values.toList.reverse [] values.size 0 hi
      have hparsed := RejectsIn.before_steps (i + 1)
        (by simpa [parsedLabel] using hparse) hlookup
      have hfull := RejectsIn.before_step
        (by simpa [encodeCircuitGate] using htag) hparsed
      exact RejectsIn.mono hfull (by
        simp [gateRejectBound, certificateLookupRejectBound, encodeCircuitGate, encNat]
        omega)
  | const value =>
      simp [CircuitGate.ValidAt] at hinvalid
  | not source =>
      have htag := gates_not_step state (List.map some (encNat source) ++ rest)
        [] inputBits values.toList.reverse [] values.size 0 0
      rcases parse_nat_phase
          { state with inputBuffer := some (some .notMark) }
          .notGate source 0 rest [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterParse, hparse⟩
      have hlookup := gate_lookup_rejectsIn afterParse .notGate values.size source rest
        inputBits values.toList.reverse [] 0 (by
          simp [CircuitGate.ValidAt] at hinvalid
          omega)
      have hparsed := RejectsIn.before_steps (source + 1)
        (by simpa [parsedLabel] using hparse) hlookup
      have hfull := RejectsIn.before_step
        (by simpa [encodeCircuitGate] using htag) hparsed
      exact RejectsIn.mono hfull (by
        simp [gateRejectBound, gateLookupRejectBound, encodeCircuitGate, encNat]
        omega)
  | and left right =>
      let rightInput := List.map some (encNat right) ++ rest
      have htag := gates_and_step state
        (List.map some (encNat left) ++ rightInput)
        [] inputBits values.toList.reverse [] values.size 0 0
      rcases parse_nat_phase
          { state with inputBuffer := some (some .andMark) }
          .andLeft left 0 rightInput [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterLeftParse, hleftParse⟩
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
        rcases parse_nat_phase afterLeftLookup
            (.andRight (values.toList.getD left false)) right 0 rest [] inputBits
            values.toList.reverse [] values.size 0 with
          ⟨afterRightParse, hrightParse⟩
        have hright : values.size ≤ right := by
          simp [CircuitGate.ValidAt, hleft] at hinvalid
          omega
        have hreject := gate_lookup_rejectsIn afterRightParse
          (.andRight (values.toList.getD left false)) values.size right rest
          inputBits values.toList.reverse [] 0 hright
        have hrightFull := RejectsIn.before_steps (right + 1)
          (by simpa only [parsedLabel, rightInput, Nat.zero_add] using hrightParse) hreject
        have hlookupFull := RejectsIn.before_steps (2 * values.size + 4)
          hlookup' hrightFull
        have hleftFull := RejectsIn.before_steps (left + 1)
          (by simpa [parsedLabel] using hleftParse) hlookupFull
        have hfull := RejectsIn.before_step
          (by simpa [encodeCircuitGate, rightInput, List.map_append,
              List.append_assoc] using htag) hleftFull
        have hfull' : RejectsIn (cfg (some .gates) state
            (List.map some (encodeCircuitGate (.and left right)) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)
            (gateLookupRejectBound values.size right rest inputBits
                values.toList.reverse [] 0 + (right + 1) +
              (2 * values.size + 4) + (left + 1) + 1) := by
          simpa [encodeCircuitGate, rightInput, List.map_append,
            List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (by
          simp [gateRejectBound, gateLookupRejectBound, encodeCircuitGate, encNat]
          omega)
      ·
        have hreject := gate_lookup_rejectsIn afterLeftParse .andLeft values.size left
          rightInput inputBits values.toList.reverse [] 0 (by omega)
        have hleftFull := RejectsIn.before_steps (left + 1)
          (by simpa [parsedLabel] using hleftParse) hreject
        have hfull := RejectsIn.before_step
          (by simpa [encodeCircuitGate, rightInput, List.map_append,
              List.append_assoc] using htag) hleftFull
        have hfull' : RejectsIn (cfg (some .gates) state
            (List.map some (encodeCircuitGate (.and left right)) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)
            (gateLookupRejectBound values.size left rightInput inputBits
              values.toList.reverse [] 0 + (left + 1) + 1) := by
          simpa [encodeCircuitGate, rightInput, List.map_append,
            List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (by
          simp [gateRejectBound, gateLookupRejectBound, rightInput,
            encodeCircuitGate, encNat]
          omega)
  | or left right =>
      let rightInput := List.map some (encNat right) ++ rest
      have htag := gates_or_step state
        (List.map some (encNat left) ++ rightInput)
        [] inputBits values.toList.reverse [] values.size 0 0
      rcases parse_nat_phase
          { state with inputBuffer := some (some .orMark) }
          .orLeft left 0 rightInput [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterLeftParse, hleftParse⟩
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
        rcases parse_nat_phase afterLeftLookup
            (.orRight (values.toList.getD left false)) right 0 rest [] inputBits
            values.toList.reverse [] values.size 0 with
          ⟨afterRightParse, hrightParse⟩
        have hright : values.size ≤ right := by
          simp [CircuitGate.ValidAt, hleft] at hinvalid
          omega
        have hreject := gate_lookup_rejectsIn afterRightParse
          (.orRight (values.toList.getD left false)) values.size right rest
          inputBits values.toList.reverse [] 0 hright
        have hrightFull := RejectsIn.before_steps (right + 1)
          (by simpa only [parsedLabel, rightInput, Nat.zero_add] using hrightParse) hreject
        have hlookupFull := RejectsIn.before_steps (2 * values.size + 4)
          hlookup' hrightFull
        have hleftFull := RejectsIn.before_steps (left + 1)
          (by simpa [parsedLabel] using hleftParse) hlookupFull
        have hfull := RejectsIn.before_step
          (by simpa [encodeCircuitGate, rightInput, List.map_append,
              List.append_assoc] using htag) hleftFull
        have hfull' : RejectsIn (cfg (some .gates) state
            (List.map some (encodeCircuitGate (.or left right)) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)
            (gateLookupRejectBound values.size right rest inputBits
                values.toList.reverse [] 0 + (right + 1) +
              (2 * values.size + 4) + (left + 1) + 1) := by
          simpa [encodeCircuitGate, rightInput, List.map_append,
            List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (by
          simp [gateRejectBound, gateLookupRejectBound, encodeCircuitGate, encNat]
          omega)
      ·
        have hreject := gate_lookup_rejectsIn afterLeftParse .orLeft values.size left
          rightInput inputBits values.toList.reverse [] 0 (by omega)
        have hleftFull := RejectsIn.before_steps (left + 1)
          (by simpa [parsedLabel] using hleftParse) hreject
        have hfull := RejectsIn.before_step
          (by simpa [encodeCircuitGate, rightInput, List.map_append,
              List.append_assoc] using htag) hleftFull
        have hfull' : RejectsIn (cfg (some .gates) state
            (List.map some (encodeCircuitGate (.or left right)) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)
            (gateLookupRejectBound values.size left rightInput inputBits
              values.toList.reverse [] 0 + (left + 1) + 1) := by
          simpa [encodeCircuitGate, rightInput, List.map_append,
            List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (by
          simp [gateRejectBound, gateLookupRejectBound, rightInput,
            encodeCircuitGate, encNat]
          omega)

/-- Budget for rejection at the first invalid gate of a canonical stream. -/
def gateListRejectBound (gates : List CircuitGate) (inputBits : List Bool)
    (values : Array Bool) (rest : List (Option CircuitSym)) : Nat :=
  gateListSteps values.size gates +
    2 * (gates.flatMap encodeCircuitGate).length +
    4 * (values.size + gates.length) + 2 * inputBits.length + rest.length + 20

/-- An ordered gate stream rejects at its first invalid gate within the stream
budget. -/
theorem gate_list_rejectsIn_of_not_valid (state : State) (gates : List CircuitGate)
    (inputBits : List Bool) (values : Array Bool)
    (rest : List (Option CircuitSym))
    (hinvalid : ¬ ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputBits.length (values.size + i)) :
    RejectsIn (cfg (some .gates) state
      (List.map some (gates.flatMap encodeCircuitGate) ++ rest)
      [] inputBits values.toList.reverse [] values.size 0 0)
      (gateListRejectBound gates inputBits values rest) := by
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
        have htail : RejectsIn
            (cfg (some .gates) afterGate tailInput [] inputBits
              nextValues.toList.reverse [] nextValues.size 0 0)
            (gateListRejectBound gates inputBits nextValues rest) := by
          simpa [tailInput, nextValues, Array.size_push] using hreject
        have hfull := RejectsIn.before_steps (gateSteps values.size gate)
          (by
            simpa [tailInput, nextValues, List.map_append, List.append_assoc,
              Array.toList_push, List.reverse_append] using hrun) htail
        have hfull' : RejectsIn
            (cfg (some .gates) state
              (List.map some ((gate :: gates).flatMap encodeCircuitGate) ++ rest)
              [] inputBits values.toList.reverse [] values.size 0 0)
            (gateListRejectBound gates inputBits nextValues rest +
              gateSteps values.size gate) := by
          simpa [List.map_append, List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (by
          simp [gateListRejectBound, gateListSteps, nextValues]
          omega)
      ·
        have hreject := gate_rejectsIn_of_not_valid state gate inputBits values
          (List.map some (gates.flatMap encodeCircuitGate) ++ rest) hgate
        have hreject' : RejectsIn
            (cfg (some .gates) state
              (List.map some ((gate :: gates).flatMap encodeCircuitGate) ++ rest)
              [] inputBits values.toList.reverse [] values.size 0 0)
            (gateRejectBound gate inputBits values
              (List.map some (gates.flatMap encodeCircuitGate) ++ rest)) := by
          simpa [List.map_append, List.append_assoc] using hreject
        exact RejectsIn.mono hreject' (by
          simp [gateListRejectBound, gateRejectBound, gateListSteps]
          omega)

/-- Budget for rejecting a canonical output marker outside the value array. -/
def outputRejectBound (inputBits : List Bool) (values : Array Bool)
    (outputIndex : Nat) : Nat :=
  2 * outputIndex + inputBits.length + 2 * values.size + 14

/-- A canonical output marker outside the computed gate array rejects within
the output budget. -/
theorem output_rejectsIn_of_not_valid (state : State) (inputBits : List Bool)
    (values : Array Bool) (outputIndex : Nat)
    (hinvalid : values.size ≤ outputIndex) :
    RejectsIn (cfg (some .gates) state
      (List.map some (.outputMark :: encNat outputIndex))
      [] inputBits values.toList.reverse [] values.size 0 0)
      (outputRejectBound inputBits values outputIndex) := by
  have htag := gates_output_step state (List.map some (encNat outputIndex))
    [] inputBits values.toList.reverse [] values.size 0 0
  rcases parse_nat_phase
      { state with inputBuffer := some (some .outputMark) }
      .outputGate outputIndex 0 [] [] inputBits values.toList.reverse [] values.size 0 with
    ⟨afterParse, hparse⟩
  let afterTrailing : State := { afterParse with inputBuffer := none }
  have htrailing := check_trailing_empty_step afterParse [] inputBits
    values.toList.reverse [] values.size outputIndex 0
  have hreject := gate_lookup_rejectsIn afterTrailing .outputGate values.size outputIndex []
    inputBits values.toList.reverse [] 0 hinvalid
  have hchecked := RejectsIn.before_step
    (by simpa [afterTrailing] using htrailing) hreject
  have hparsed := RejectsIn.before_steps (outputIndex + 1)
    (by simpa only [parsedLabel, Nat.zero_add, List.append_nil] using hparse) hchecked
  have hfull := RejectsIn.before_step (by simpa using htag) hparsed
  exact RejectsIn.mono hfull (by
    simp [outputRejectBound, gateLookupRejectBound]
    omega)

/-- Local budget for rejecting a canonical but non-well-formed circuit body. -/
def circuitBodyRejectBound (c : Circuit) (inputBits : List Bool) : Nat :=
  gateListSteps 0 c.gates +
    2 * (c.gates.flatMap encodeCircuitGate).length +
    4 * c.gates.length + 2 * inputBits.length + 2 * c.output + 22

/-- After an accepted header, every non-well-formed canonical circuit body
rejects within the local body budget. -/
theorem circuit_body_rejectsIn_of_not_wellFormed (state : State)
    (c : Circuit) (inputBits : List Bool)
    (hbitsLength : inputBits.length = c.inputCount)
    (hinvalid : ¬ c.WellFormed) :
    RejectsIn (cfg (some .gates) state
      (List.map some (c.gates.flatMap encodeCircuitGate) ++
        List.map some (.outputMark :: encNat c.output))
      [] inputBits [] [] 0 0 0)
      (circuitBodyRejectBound c inputBits) := by
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
    have hreject := output_rejectsIn_of_not_valid afterGates inputBits finalValues
      c.output houtput
    have hreject' : RejectsIn
        (cfg (some .gates) afterGates outputInput [] inputBits
          finalValues.toList.reverse [] finalValues.size 0 0)
        (outputRejectBound inputBits finalValues c.output) := by
      simpa [outputInput, finalValues, hsize] using hreject
    have hfull := RejectsIn.before_steps (gateListSteps 0 c.gates)
      (by simpa [outputInput, finalValues] using hrun) hreject'
    exact RejectsIn.mono hfull (by
      simp [circuitBodyRejectBound, outputRejectBound, hsize]
      omega)
  ·
    have hreject := gate_list_rejectsIn_of_not_valid state c.gates inputBits #[]
      outputInput hgates
    have hreject' : RejectsIn
        (cfg (some .gates) state
          (List.map some (c.gates.flatMap encodeCircuitGate) ++
            List.map some (.outputMark :: encNat c.output))
          [] inputBits [] [] 0 0 0)
        (gateListRejectBound c.gates inputBits #[] outputInput) := by
      simpa [outputInput] using hreject
    exact RejectsIn.mono hreject' (by
      simp [gateListRejectBound, circuitBodyRejectBound, outputInput,
        encodeCircuitGate, encNat]
      omega)

/-- Budget for a single non-output tag whose structural gate decoder fails. -/
def gateDecodeRejectBound (symbol : CircuitSym) (symbols : List CircuitSym)
    (inputBits : List Bool) (values : Array Bool) : Nat :=
  2 * (symbol :: symbols).length + 2 * inputBits.length +
    4 * values.size + 24

/-- A non-output gate tag whose decoder fails rejects within the local
malformed-gate budget. -/
theorem gate_decode_rejectsIn (state : State) (symbol : CircuitSym)
    (symbols : List CircuitSym) (inputBits : List Bool) (values : Array Bool)
    (houtput : symbol ≠ .outputMark)
    (hdecode : decodeCircuitGate (symbol :: symbols) = none) :
    RejectsIn (cfg (some .gates) state (List.map some (symbol :: symbols))
      [] inputBits values.toList.reverse [] values.size 0 0)
      (gateDecodeRejectBound symbol symbols inputBits values) := by
  cases symbol with
  | inputMark =>
      have hnat : decNat symbols = none := by
        simp [decodeCircuitGate] at hdecode
        exact Option.eq_none_iff_forall_ne_some.mpr (by
          rintro ⟨n, rest⟩ hsome
          exact hdecode n rest hsome)
      have htag := gates_input_step state (List.map some symbols)
        [] inputBits values.toList.reverse [] values.size 0 0
      have hreject := parse_nat_rejectsIn_of_decNat_none
        { state with inputBuffer := some (some .inputMark) }
        .inputGate symbols inputBits values.toList.reverse [] values.size 0 0 hnat
      have hfull := RejectsIn.before_step (by simpa using htag) hreject
      exact RejectsIn.mono hfull (by
        simp [gateDecodeRejectBound, parseNatMalformedBound]
        omega)
  | constFalseMark => simp [decodeCircuitGate] at hdecode
  | constTrueMark => simp [decodeCircuitGate] at hdecode
  | notMark =>
      have hnat : decNat symbols = none := by
        simp [decodeCircuitGate] at hdecode
        exact Option.eq_none_iff_forall_ne_some.mpr (by
          rintro ⟨n, rest⟩ hsome
          exact hdecode n rest hsome)
      have htag := gates_not_step state (List.map some symbols)
        [] inputBits values.toList.reverse [] values.size 0 0
      have hreject := parse_nat_rejectsIn_of_decNat_none
        { state with inputBuffer := some (some .notMark) }
        .notGate symbols inputBits values.toList.reverse [] values.size 0 0 hnat
      have hfull := RejectsIn.before_step (by simpa using htag) hreject
      exact RejectsIn.mono hfull (by
        simp [gateDecodeRejectBound, parseNatMalformedBound]
        omega)
  | andMark =>
      cases hleft : decNat symbols with
      | none =>
          have htag := gates_and_step state (List.map some symbols)
            [] inputBits values.toList.reverse [] values.size 0 0
          have hreject := parse_nat_rejectsIn_of_decNat_none
            { state with inputBuffer := some (some .andMark) }
            .andLeft symbols inputBits values.toList.reverse [] values.size 0 0 hleft
          have hfull := RejectsIn.before_step (by simpa using htag) hreject
          exact RejectsIn.mono hfull (by
            simp [gateDecodeRejectBound, parseNatMalformedBound]
            omega)
      | some decoded =>
          rcases decoded with ⟨left, middle⟩
          have hright : decNat middle = none := by
            simp [decodeCircuitGate, hleft] at hdecode
            exact Option.eq_none_iff_forall_ne_some.mpr (by
              rintro ⟨n, rest⟩ hsome
              exact hdecode n rest hsome)
          have hsymbols := eq_encNat_append_of_decNat_eq_some hleft
          rw [hsymbols]
          have htag := gates_and_step state
            (List.map some (encNat left) ++ List.map some middle)
            [] inputBits values.toList.reverse [] values.size 0 0
          rcases parse_nat_phase
              { state with inputBuffer := some (some .andMark) }
              .andLeft left 0 (List.map some middle) [] inputBits
              values.toList.reverse [] values.size 0 with
            ⟨afterLeftParse, hparse⟩
          by_cases hvalid : left < values.size
          · rcases reverse_split_getD values.toList left hvalid with
              ⟨front, older, hsplit, hlength, holder⟩
            have hcount : front.length + older.length + 1 = values.size := by
              simpa using hlength
            rcases gate_lookup_and_left_phase afterLeftParse front older
                (values.toList.getD left false) (List.map some middle) [] inputBits with
              ⟨afterLookup, hlookup⟩
            change transition^[2 * older.length + 2 * front.length + 6] _ = _ at hlookup
            have hlookup' : transition^[2 * values.size + 4]
                (some (cfg (some (.gateSubtract .andLeft)) afterLeftParse
                  (List.map some middle) [] inputBits values.toList.reverse []
                  values.size left 0)) =
                some (cfg (some (.parseNat
                    (.andRight (values.toList.getD left false))))
                  afterLookup (List.map some middle) [] inputBits
                  values.toList.reverse [] values.size 0 0) := by
              have hcost : 2 * values.size + 4 =
                  2 * older.length + 2 * front.length + 6 := by omega
              rw [hcost, hsplit, ← hcount]
              simpa only [holder] using hlookup
            have hreject := parse_nat_rejectsIn_of_decNat_none afterLookup
              (.andRight (values.toList.getD left false)) middle inputBits
              values.toList.reverse [] values.size 0 0 hright
            have hlookupFull := RejectsIn.before_steps (2 * values.size + 4)
              hlookup' hreject
            have hparseFull := RejectsIn.before_steps (left + 1)
              (by simpa only [parsedLabel, Nat.zero_add] using hparse) hlookupFull
            have hfull := RejectsIn.before_step
              (by simpa [List.map_append, List.append_assoc] using htag) hparseFull
            have hfull' : RejectsIn
                (cfg (some .gates) state
                  (List.map some
                    (.andMark :: (encNat left ++ middle)))
                  [] inputBits values.toList.reverse [] values.size 0 0)
                (parseNatMalformedBound middle inputBits values.toList.reverse []
                    values.size 0 0 +
                  (2 * values.size + 4) + (left + 1) + 1) := by
              simpa [List.map_append, List.append_assoc] using hfull
            exact RejectsIn.mono hfull' (by
              simp [gateDecodeRejectBound, parseNatMalformedBound, encNat]
              omega)
          ·
            have hreject := gate_lookup_rejectsIn afterLeftParse .andLeft
              values.size left (List.map some middle) inputBits
              values.toList.reverse [] 0 (by omega)
            have hparseFull := RejectsIn.before_steps (left + 1)
              (by simpa only [parsedLabel, Nat.zero_add] using hparse) hreject
            have hfull := RejectsIn.before_step
              (by simpa [List.map_append, List.append_assoc] using htag) hparseFull
            have hfull' : RejectsIn
                (cfg (some .gates) state
                  (List.map some (.andMark :: (encNat left ++ middle)))
                  [] inputBits values.toList.reverse [] values.size 0 0)
                (gateLookupRejectBound values.size left (List.map some middle)
                    inputBits values.toList.reverse [] 0 +
                  (left + 1) + 1) := by
              simpa [List.map_append, List.append_assoc] using hfull
            exact RejectsIn.mono hfull' (by
              simp [gateDecodeRejectBound, gateLookupRejectBound, encNat]
              omega)
  | orMark =>
      cases hleft : decNat symbols with
      | none =>
          have htag := gates_or_step state (List.map some symbols)
            [] inputBits values.toList.reverse [] values.size 0 0
          have hreject := parse_nat_rejectsIn_of_decNat_none
            { state with inputBuffer := some (some .orMark) }
            .orLeft symbols inputBits values.toList.reverse [] values.size 0 0 hleft
          have hfull := RejectsIn.before_step (by simpa using htag) hreject
          exact RejectsIn.mono hfull (by
            simp [gateDecodeRejectBound, parseNatMalformedBound]
            omega)
      | some decoded =>
          rcases decoded with ⟨left, middle⟩
          have hright : decNat middle = none := by
            simp [decodeCircuitGate, hleft] at hdecode
            exact Option.eq_none_iff_forall_ne_some.mpr (by
              rintro ⟨n, rest⟩ hsome
              exact hdecode n rest hsome)
          have hsymbols := eq_encNat_append_of_decNat_eq_some hleft
          rw [hsymbols]
          have htag := gates_or_step state
            (List.map some (encNat left) ++ List.map some middle)
            [] inputBits values.toList.reverse [] values.size 0 0
          rcases parse_nat_phase
              { state with inputBuffer := some (some .orMark) }
              .orLeft left 0 (List.map some middle) [] inputBits
              values.toList.reverse [] values.size 0 with
            ⟨afterLeftParse, hparse⟩
          by_cases hvalid : left < values.size
          · rcases reverse_split_getD values.toList left hvalid with
              ⟨front, older, hsplit, hlength, holder⟩
            have hcount : front.length + older.length + 1 = values.size := by
              simpa using hlength
            rcases gate_lookup_or_left_phase afterLeftParse front older
                (values.toList.getD left false) (List.map some middle) [] inputBits with
              ⟨afterLookup, hlookup⟩
            change transition^[2 * older.length + 2 * front.length + 6] _ = _ at hlookup
            have hlookup' : transition^[2 * values.size + 4]
                (some (cfg (some (.gateSubtract .orLeft)) afterLeftParse
                  (List.map some middle) [] inputBits values.toList.reverse []
                  values.size left 0)) =
                some (cfg (some (.parseNat
                    (.orRight (values.toList.getD left false))))
                  afterLookup (List.map some middle) [] inputBits
                  values.toList.reverse [] values.size 0 0) := by
              have hcost : 2 * values.size + 4 =
                  2 * older.length + 2 * front.length + 6 := by omega
              rw [hcost, hsplit, ← hcount]
              simpa only [holder] using hlookup
            have hreject := parse_nat_rejectsIn_of_decNat_none afterLookup
              (.orRight (values.toList.getD left false)) middle inputBits
              values.toList.reverse [] values.size 0 0 hright
            have hlookupFull := RejectsIn.before_steps (2 * values.size + 4)
              hlookup' hreject
            have hparseFull := RejectsIn.before_steps (left + 1)
              (by simpa only [parsedLabel, Nat.zero_add] using hparse) hlookupFull
            have hfull := RejectsIn.before_step
              (by simpa [List.map_append, List.append_assoc] using htag) hparseFull
            have hfull' : RejectsIn
                (cfg (some .gates) state
                  (List.map some (.orMark :: (encNat left ++ middle)))
                  [] inputBits values.toList.reverse [] values.size 0 0)
                (parseNatMalformedBound middle inputBits values.toList.reverse []
                    values.size 0 0 +
                  (2 * values.size + 4) + (left + 1) + 1) := by
              simpa [List.map_append, List.append_assoc] using hfull
            exact RejectsIn.mono hfull' (by
              simp [gateDecodeRejectBound, parseNatMalformedBound, encNat]
              omega)
          ·
            have hreject := gate_lookup_rejectsIn afterLeftParse .orLeft
              values.size left (List.map some middle) inputBits
              values.toList.reverse [] 0 (by omega)
            have hparseFull := RejectsIn.before_steps (left + 1)
              (by simpa only [parsedLabel, Nat.zero_add] using hparse) hreject
            have hfull := RejectsIn.before_step
              (by simpa [List.map_append, List.append_assoc] using htag) hparseFull
            have hfull' : RejectsIn
                (cfg (some .gates) state
                  (List.map some (.orMark :: (encNat left ++ middle)))
                  [] inputBits values.toList.reverse [] values.size 0 0)
                (gateLookupRejectBound values.size left (List.map some middle)
                    inputBits values.toList.reverse [] 0 +
                  (left + 1) + 1) := by
              simpa [List.map_append, List.append_assoc] using hfull
            exact RejectsIn.mono hfull' (by
              simp [gateDecodeRejectBound, gateLookupRejectBound, encNat]
              omega)
  | outputMark => exact False.elim (houtput rfl)
  | argMark =>
      have hreject := rejectsIn_after_cleanup_step _ _ (List.map some symbols)
        inputBits values.toList.reverse [] values.size 0 0
        (gates_bad_marker_reject_step state .argMark (Or.inl rfl)
          (List.map some symbols) [] inputBits values.toList.reverse [] values.size 0 0)
      exact RejectsIn.mono hreject (by
        simp [gateDecodeRejectBound, cleanupSteps]
        omega)
  | endMark =>
      have hreject := rejectsIn_after_cleanup_step _ _ (List.map some symbols)
        inputBits values.toList.reverse [] values.size 0 0
        (gates_bad_marker_reject_step state .endMark (Or.inr rfl)
          (List.map some symbols) [] inputBits values.toList.reverse [] values.size 0 0)
      exact RejectsIn.mono hreject (by
        simp [gateDecodeRejectBound, cleanupSteps]
        omega)

/-- Quadratic envelope for a structurally malformed remaining gate stream.
The fuel decrease pays for one successful gate phase while the symbol and
value terms remain monotone along recursive decoding. -/
def gateStreamRejectBound (fuel : Nat) (symbols : List CircuitSym)
    (inputBits : List Bool) (values : Array Bool) : Nat :=
  100 * (fuel + symbols.length + inputBits.length + values.size + 1) ^ 2

private theorem quadratic_pays_linear (small large cost : Nat)
    (hgap : small + 1 ≤ large) (hcost : cost ≤ 10 * large) :
    100 * small ^ 2 + cost ≤ 100 * large ^ 2 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hgap
  nlinarith

/-- If structural gate-stream decoding fails for genuine structural reasons
(rather than artificial fuel exhaustion), the concrete machine rejects within
the uniform quadratic stream budget. -/
theorem gate_stream_rejectsIn_of_decode_none (state : State) (fuel : Nat)
    (symbols : List CircuitSym) (inputBits : List Bool) (values : Array Bool)
    (hfuel : symbols.length ≤ fuel)
    (hdecode : decodeCircuitGates fuel symbols = none) :
    RejectsIn (cfg (some .gates) state (List.map some symbols)
      [] inputBits values.toList.reverse [] values.size 0 0)
      (gateStreamRejectBound fuel symbols inputBits values) := by
  induction fuel generalizing state symbols values with
  | zero =>
      have hempty : symbols = [] := by
        cases symbols <;> simp_all
      subst symbols
      have hreject := rejectsIn_after_cleanup_step _ _ [] inputBits
        values.toList.reverse [] values.size 0 0
        (gates_eof_reject_step state [] inputBits values.toList.reverse []
          values.size 0 0)
      exact RejectsIn.mono hreject (by
        simp [gateStreamRejectBound, cleanupSteps]
        nlinarith)
  | succ fuel ih =>
      cases symbols with
      | nil =>
          have hreject := rejectsIn_after_cleanup_step _ _ [] inputBits
            values.toList.reverse [] values.size 0 0
            (gates_eof_reject_step state [] inputBits values.toList.reverse []
              values.size 0 0)
          exact RejectsIn.mono hreject (by
            simp [gateStreamRejectBound, cleanupSteps]
            nlinarith)
      | cons symbol symbols =>
          by_cases hout : symbol = .outputMark
          · subst symbol
            have hnat : decNat symbols = none := by
              simp [decodeCircuitGates] at hdecode
              exact Option.eq_none_iff_forall_ne_some.mpr (by
                rintro ⟨n, rest⟩ hsome
                exact hdecode n rest hsome)
            have htag := gates_output_step state (List.map some symbols)
              [] inputBits values.toList.reverse [] values.size 0 0
            have hreject := parse_nat_rejectsIn_of_decNat_none
              { state with inputBuffer := some (some .outputMark) }
              .outputGate symbols inputBits values.toList.reverse []
              values.size 0 0 hnat
            have hfull := RejectsIn.before_step (by simpa using htag) hreject
            exact RejectsIn.mono hfull (by
              simp [gateStreamRejectBound, parseNatMalformedBound]
              nlinarith)
          · cases hgate : decodeCircuitGate (symbol :: symbols) with
            | none =>
                have hreject := gate_decode_rejectsIn state symbol symbols
                  inputBits values hout hgate
                exact RejectsIn.mono hreject (by
                  simp [gateStreamRejectBound, gateDecodeRejectBound]
                  nlinarith)
            | some decoded =>
                rcases decoded with ⟨gate, rest⟩
                have hrestDecode : decodeCircuitGates fuel rest = none := by
                  cases symbol <;> simp_all [decodeCircuitGates]
                  all_goals
                    exact Option.eq_none_iff_forall_ne_some.mpr (by
                      rintro ⟨gates, output, trailing⟩ hsome
                      exact hdecode gates output trailing hsome)
                have hsymbols :=
                  eq_encodeCircuitGate_append_of_decodeCircuitGate_eq_some hgate
                have hgateLength : 1 ≤ (encodeCircuitGate gate).length := by
                  cases gate with
                  | input i => simp [encodeCircuitGate]
                  | const value => cases value <;> simp [encodeCircuitGate]
                  | not source => simp [encodeCircuitGate]
                  | and left right => simp [encodeCircuitGate]
                  | or left right => simp [encodeCircuitGate]
                have hrestFuel : rest.length ≤ fuel := by
                  have hlength := congrArg List.length hsymbols
                  simp only [List.length_cons, List.length_append] at hlength hfuel
                  omega
                have hrestLength : rest.length ≤ symbols.length := by
                  have hlength := congrArg List.length hsymbols
                  simp only [List.length_cons, List.length_append] at hlength
                  omega
                rw [hsymbols]
                by_cases hvalid : gate.ValidAt inputBits.length values.size
                · let nextValues := values.push
                    (gate.evalWith (fun i => inputBits.getD i false) values)
                  rcases gate_phase state gate inputBits values (List.map some rest)
                      hvalid with ⟨afterGate, hrun⟩
                  have htail := ih afterGate rest nextValues hrestFuel hrestDecode
                  have htail' : RejectsIn
                      (cfg (some .gates) afterGate (List.map some rest)
                        [] inputBits nextValues.toList.reverse [] nextValues.size 0 0)
                      (gateStreamRejectBound fuel rest inputBits nextValues) := by
                    simpa [nextValues, List.getD_eq_getElem?_getD,
                      Array.toList_push, List.reverse_append] using htail
                  have hfull := RejectsIn.before_steps (gateSteps values.size gate)
                    (by simpa [List.map_append, nextValues,
                      Array.toList_push, List.reverse_append] using hrun) htail'
                  have hfull' : RejectsIn
                      (cfg (some .gates) state
                        (List.map some (encodeCircuitGate gate ++ rest))
                        [] inputBits values.toList.reverse [] values.size 0 0)
                      (gateStreamRejectBound fuel rest inputBits nextValues +
                        gateSteps values.size gate) := by
                    simpa [List.map_append] using hfull
                  have hgateCost := gateSteps_le gate inputBits.length values.size hvalid
                  exact RejectsIn.mono hfull' (by
                    simp only [gateStreamRejectBound, nextValues, Array.size_push]
                    apply quadratic_pays_linear
                    · simp only [List.length_append]
                      omega
                    · exact hgateCost.trans (by
                        apply Nat.mul_le_mul_left
                        omega))
                ·
                  have hreject := gate_rejectsIn_of_not_valid state gate inputBits values
                    (List.map some rest) hvalid
                  have hreject' : RejectsIn
                      (cfg (some .gates) state
                        (List.map some (encodeCircuitGate gate ++ rest))
                        [] inputBits values.toList.reverse [] values.size 0 0)
                      (gateRejectBound gate inputBits values (List.map some rest)) := by
                    simpa [List.map_append] using hreject
                  exact RejectsIn.mono hreject' (by
                    simp [gateStreamRejectBound, gateRejectBound]
                    nlinarith)

/-- Route budget for a decoded gate stream that leaves trailing symbols after
its output index. -/
def gateStreamTrailingRejectBound (gates : List CircuitGate)
    (outputIndex : Nat) (trailing : List CircuitSym)
    (inputBits : List Bool) (values : Array Bool) : Nat :=
  gateListSteps values.size gates +
    2 * (gates.flatMap encodeCircuitGate).length +
    2 * trailing.length + 2 * inputBits.length +
    4 * (values.size + gates.length) + 2 * outputIndex + 30

/-- A successfully decoded stream with unconsumed trailing symbols rejects
within an explicit route budget, whether rejection occurs at an earlier
invalid gate or at the trailing-symbol check itself. -/
theorem gate_stream_rejectsIn_of_trailing (state : State) (fuel : Nat)
    (symbols : List CircuitSym) (inputBits : List Bool) (values : Array Bool)
    (gates : List CircuitGate) (outputIndex : Nat) (trailing : List CircuitSym)
    (hdecode : decodeCircuitGates fuel symbols =
      some (gates, outputIndex, trailing))
    (htrailing : trailing ≠ []) :
    RejectsIn (cfg (some .gates) state (List.map some symbols)
      [] inputBits values.toList.reverse [] values.size 0 0)
      (gateStreamTrailingRejectBound gates outputIndex trailing inputBits values) := by
  have hsymbols :=
    eq_encodeCircuitGates_append_of_decodeCircuitGates_eq_some hdecode
  rw [hsymbols]
  let outputInput :=
    List.map some (.outputMark :: encNat outputIndex ++ trailing)
  have hinputMap :
      List.map some
          (gates.flatMap encodeCircuitGate ++
            .outputMark :: encNat outputIndex ++ trailing) =
        List.map some (gates.flatMap encodeCircuitGate) ++ outputInput := by
    simp [outputInput, List.map_append, List.append_assoc]
  rw [hinputMap]
  by_cases hgates : ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputBits.length (values.size + i)
  · rcases gate_list_phase state gates inputBits values outputInput hgates with
      ⟨afterGates, hrun⟩
    let finalValues := evalGateList inputBits values gates
    have hrun' : transition^[gateListSteps values.size gates]
        (some (cfg (some .gates) state
          (List.map some (gates.flatMap encodeCircuitGate) ++ outputInput)
          [] inputBits values.toList.reverse [] values.size 0 0)) =
        some (cfg (some .gates) afterGates outputInput [] inputBits
          finalValues.toList.reverse [] finalValues.size 0 0) := by
      simpa [finalValues] using hrun
    have htag := gates_output_step afterGates
      (List.map some (encNat outputIndex ++ trailing)) [] inputBits
      finalValues.toList.reverse [] finalValues.size 0 0
    rcases parse_nat_phase
        { afterGates with inputBuffer := some (some .outputMark) }
        .outputGate outputIndex 0 (List.map some trailing) [] inputBits
        finalValues.toList.reverse [] finalValues.size 0 with
      ⟨afterParse, hparse⟩
    have hparse' : transition^[outputIndex + 1]
        (some (cfg (some (.parseNat .outputGate))
          { afterGates with inputBuffer := some (some .outputMark) }
          (List.map some (encNat outputIndex) ++ List.map some trailing)
          [] inputBits finalValues.toList.reverse [] finalValues.size 0 0)) =
        some (cfg (some .checkTrailing) afterParse (List.map some trailing)
          [] inputBits finalValues.toList.reverse [] finalValues.size outputIndex 0) := by
      simpa only [parsedLabel, Nat.zero_add] using hparse
    cases trailing with
    | nil => contradiction
    | cons head tail =>
        have hreject := rejectsIn_after_cleanup_step _ _ (List.map some tail)
          inputBits finalValues.toList.reverse [] finalValues.size outputIndex 0
          (by
            simpa using check_trailing_nonempty_step afterParse (some head)
              (List.map some tail) [] inputBits finalValues.toList.reverse []
              finalValues.size outputIndex 0)
        have hparsed := RejectsIn.before_steps (outputIndex + 1) hparse' hreject
        have htagged := RejectsIn.before_step (by
          simpa only [outputInput, List.map_cons, List.map_append,
            List.cons_append] using htag) hparsed
        have htagged' : RejectsIn
            (cfg (some .gates) afterGates outputInput [] inputBits
              finalValues.toList.reverse [] finalValues.size 0 0)
            (cleanupSteps (List.map some tail) inputBits finalValues.toList.reverse []
                finalValues.size outputIndex 0 + 1 + (outputIndex + 1) + 1) := by
          simpa [outputInput, List.map_append, List.append_assoc] using htagged
        have hfull := RejectsIn.before_steps (gateListSteps values.size gates)
          hrun' htagged'
        exact RejectsIn.mono hfull (by
          simp [gateStreamTrailingRejectBound, cleanupSteps, finalValues]
          omega)
  ·
    have hreject := gate_list_rejectsIn_of_not_valid state gates inputBits values
      outputInput hgates
    have hreject' : RejectsIn
        (cfg (some .gates) state
          (List.map some (gates.flatMap encodeCircuitGate) ++ outputInput)
          [] inputBits values.toList.reverse [] values.size 0 0)
        (gateListRejectBound gates inputBits values outputInput) := by
      simpa using hreject
    exact RejectsIn.mono hreject' (by
      simp [gateStreamTrailingRejectBound, gateListRejectBound, outputInput,
        encodeCircuitGate, encNat]
      omega)

/-- The trailing-stream route budget is itself quadratic in the serialized
stream and the live certificate/value lengths. -/
theorem gateStreamTrailingRejectBound_le (fuel : Nat)
    (symbols : List CircuitSym) (inputBits : List Bool) (values : Array Bool)
    (gates : List CircuitGate) (outputIndex : Nat) (trailing : List CircuitSym)
    (hdecode : decodeCircuitGates fuel symbols =
      some (gates, outputIndex, trailing)) :
    gateStreamTrailingRejectBound gates outputIndex trailing inputBits values ≤
      100 * (symbols.length + inputBits.length + values.size + 1) ^ 2 := by
  have hsymbols :=
    eq_encodeCircuitGates_append_of_decodeCircuitGates_eq_some hdecode
  have hlength := congrArg List.length hsymbols
  simp only [List.length_append, List.length_cons, encNat,
    List.length_replicate, List.length_nil] at hlength
  have hgates := gates_length_le_flat_encoding gates
  have hsteps := gateListSteps_le_encoding gates values.size
  simp only [gateStreamTrailingRejectBound]
  nlinarith

/-- Internal quadratic envelope established by the route arithmetic. -/
def verifierQuadraticBound (inputLength : Nat) : Nat :=
  10000 * (inputLength + 1) ^ 2

/-- Public deliberately generous quartic step budget for the complete
two-input verifier. -/
def verifierStepBound (inputLength : Nat) : Nat :=
  10000 * (inputLength + 1) ^ 4

theorem verifierQuadraticBound_le (inputLength : Nat) :
    verifierQuadraticBound inputLength ≤ verifierStepBound inputLength := by
  have hone : 1 ≤ (inputLength + 1) ^ 2 := by
    simpa using Nat.pow_le_pow_left (show 1 ≤ inputLength + 1 by omega) 2
  have hsquare : (inputLength + 1) ^ 2 ≤
      (inputLength + 1) ^ 2 * (inputLength + 1) ^ 2 := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left ((inputLength + 1) ^ 2) hone
  simp only [verifierQuadraticBound, verifierStepBound]
  apply Nat.mul_le_mul_left
  calc
    (inputLength + 1) ^ 2 ≤
        (inputLength + 1) ^ 2 * (inputLength + 1) ^ 2 := hsquare
    _ = (inputLength + 1) ^ 4 := by ring

/-- Every input rejected by the total circuit decoder reaches the canonical
false halt within the verifier's uniform input-length budget. -/
theorem malformed_circuit_rejectsIn (certificate input : List CircuitSym)
    (hdecode : decodeCircuit input = none) :
    RejectsIn (initList machine (pairEncoding certificate input))
      (verifierStepBound (pairEncoding certificate input).length) := by
  rcases certificate_header_phase certificate input with
    ⟨afterHeader, hheaderValid, hheaderRun⟩
  cases hnat : decNat input with
  | none =>
      have hreject := input_count_rejectsIn_of_decNat_none afterHeader input
        (assignmentBits certificate) [] [] certificate.length 0 0 hnat
      have hfull := RejectsIn.before_steps (2 * (certificate.length + 1))
        hheaderRun hreject
      exact RejectsIn.mono hfull (le_trans (by
        simp [inputCountMalformedBound, verifierQuadraticBound, pairEncoding]
        nlinarith) (verifierQuadraticBound_le _))
  | some decodedNat =>
      rcases decodedNat with ⟨inputCount, rest⟩
      have hinput := eq_encNat_append_of_decNat_eq_some hnat
      have hinputLength := congrArg List.length hinput
      simp only [List.length_append, encNat, List.length_replicate,
        List.length_cons, List.length_nil] at hinputLength
      rw [hinput]
      by_cases hlength : certificate.length = inputCount
      · by_cases hlegal : certificate.all isAssignmentSymbol = true
        · have hstateValid : afterHeader.validAssignment = true := by
            rw [hheaderValid, hlegal]
          rcases input_count_phase afterHeader inputCount (List.map some rest)
              (assignmentBits certificate) [] [] 0 0 hstateValid with
            ⟨afterCount, hcount⟩
          have hcount' : transition^[inputCount + 1]
              (some (cfg (some .inputCount) afterHeader
                (List.map some (encNat inputCount ++ rest)) []
                (assignmentBits certificate) [] [] certificate.length 0 0)) =
              some (cfg (some .gates) afterCount (List.map some rest) []
                (assignmentBits certificate) [] [] 0 0 0) := by
            simpa [List.map_append, hlength] using hcount
          cases hgates : decodeCircuitGates rest.length rest with
          | none =>
              have hreject := gate_stream_rejectsIn_of_decode_none afterCount
                rest.length rest (assignmentBits certificate) #[] (by omega) hgates
              have hcountFull := RejectsIn.before_steps (inputCount + 1)
                hcount' hreject
              have hfull := RejectsIn.before_steps (2 * (certificate.length + 1))
                (by simpa [hinput] using hheaderRun) hcountFull
              exact RejectsIn.mono hfull (le_trans (by
                simp [gateStreamRejectBound, verifierQuadraticBound, pairEncoding,
                  assignmentBits_length, encNat]
                nlinarith) (verifierQuadraticBound_le _))
          | some decodedGates =>
              rcases decodedGates with ⟨gates, outputIndex, trailing⟩
              have htrailing : trailing ≠ [] := by
                intro hempty
                subst trailing
                simp [decodeCircuit, hnat, hgates] at hdecode
              have hreject := gate_stream_rejectsIn_of_trailing afterCount
                rest.length rest (assignmentBits certificate) #[] gates
                outputIndex trailing hgates htrailing
              have hrejectBound := gateStreamTrailingRejectBound_le rest.length
                rest (assignmentBits certificate) #[] gates outputIndex trailing hgates
              have hreject' := RejectsIn.mono hreject hrejectBound
              have hcountFull := RejectsIn.before_steps (inputCount + 1)
                hcount' hreject'
              have hfull := RejectsIn.before_steps (2 * (certificate.length + 1))
                (by simpa [hinput] using hheaderRun) hcountFull
              exact RejectsIn.mono hfull (le_trans (by
                simp [verifierQuadraticBound, pairEncoding, assignmentBits_length,
                  encNat]
                nlinarith) (verifierQuadraticBound_le _))
        ·
          have hfalse : certificate.all isAssignmentSymbol = false := by
            cases hvalue : certificate.all isAssignmentSymbol <;> simp_all
          have hreject := input_count_rejectsIn afterHeader inputCount
            certificate.length (List.map some rest) (assignmentBits certificate)
            [] [] 0 0 (Or.inr (by rw [hheaderValid]; exact hfalse))
          have hreject' : RejectsIn
              (cfg (some .inputCount) afterHeader
                (List.map some (encNat inputCount ++ rest)) []
                (assignmentBits certificate) [] [] certificate.length 0 0)
              (inputCountRejectBound inputCount certificate.length
                (List.map some rest) (assignmentBits certificate) [] [] 0 0) := by
            simpa [List.map_append] using hreject
          have hfull := RejectsIn.before_steps (2 * (certificate.length + 1))
            (by simpa [hinput] using hheaderRun) hreject'
          exact RejectsIn.mono hfull (le_trans (by
            simp [inputCountRejectBound, verifierQuadraticBound, pairEncoding,
              assignmentBits_length, encNat]
            nlinarith) (verifierQuadraticBound_le _))
      ·
        have hreject := input_count_rejectsIn afterHeader inputCount
          certificate.length (List.map some rest) (assignmentBits certificate)
          [] [] 0 0 (Or.inl hlength)
        have hreject' : RejectsIn
            (cfg (some .inputCount) afterHeader
              (List.map some (encNat inputCount ++ rest)) []
              (assignmentBits certificate) [] [] certificate.length 0 0)
            (inputCountRejectBound inputCount certificate.length
              (List.map some rest) (assignmentBits certificate) [] [] 0 0) := by
          simpa [List.map_append] using hreject
        have hfull := RejectsIn.before_steps (2 * (certificate.length + 1))
          (by simpa [hinput] using hheaderRun) hreject'
        exact RejectsIn.mono hfull (le_trans (by
          simp [inputCountRejectBound, verifierQuadraticBound, pairEncoding,
            assignmentBits_length, encNat]
          nlinarith) (verifierQuadraticBound_le _))

/-- The canonical-circuit rejection budget is quadratic in the circuit
encoding and the live input-bit vector, without assuming well-formedness. -/
theorem circuitBodyRejectBound_le (c : Circuit) (inputBits : List Bool) :
    circuitBodyRejectBound c inputBits ≤
      1000 * ((encodeCircuit c).length + inputBits.length + 1) ^ 2 := by
  have hgates := gates_length_le_flat_encoding c.gates
  have hsteps := gateListSteps_le_encoding c.gates 0
  have hproduct :
      (c.gates.length + 1) *
          ((c.gates.flatMap encodeCircuitGate).length + c.gates.length + 1) ≤
        ((c.gates.flatMap encodeCircuitGate).length + 1) *
          (2 * ((c.gates.flatMap encodeCircuitGate).length + 1)) := by
    apply Nat.mul_le_mul <;> omega
  have hsteps' : gateListSteps 0 c.gates ≤
      40 * ((c.gates.flatMap encodeCircuitGate).length + 1) ^ 2 := by
    calc
      gateListSteps 0 c.gates ≤
          20 * (c.gates.length + 1) *
            ((c.gates.flatMap encodeCircuitGate).length + c.gates.length + 1) := by
              simpa using hsteps
      _ ≤ 20 * (((c.gates.flatMap encodeCircuitGate).length + 1) *
            (2 * ((c.gates.flatMap encodeCircuitGate).length + 1))) := by
              simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 20 hproduct
      _ = 40 * ((c.gates.flatMap encodeCircuitGate).length + 1) ^ 2 := by ring
  let total := (encodeCircuit c).length + inputBits.length + 1
  have htotal : 1 ≤ total := by
    simp [total]
  have hgateMeasure :
      (c.gates.flatMap encodeCircuitGate).length + 1 ≤ total := by
    simp [total, encodeCircuit, encNat]
    omega
  have hstepsTotal : gateListSteps 0 c.gates ≤ 40 * total ^ 2 := by
    exact hsteps'.trans (Nat.mul_le_mul_left 40
      (Nat.pow_le_pow_left hgateMeasure 2))
  have hencodedGates :
      (c.gates.flatMap encodeCircuitGate).length ≤ total := by omega
  have hgatesTotal : c.gates.length ≤ total := hgates.trans hencodedGates
  have hinputTotal : inputBits.length ≤ total := by
    simp [total]
    omega
  have houtputTotal : c.output ≤ total := by
    simp [total, encodeCircuit, encNat]
    omega
  have hlinear :
      2 * (c.gates.flatMap encodeCircuitGate).length +
          4 * c.gates.length + 2 * inputBits.length + 2 * c.output + 22 ≤
        100 * total := by
    nlinarith
  simp only [circuitBodyRejectBound]
  rw [show (encodeCircuit c).length + inputBits.length + 1 = total by rfl]
  nlinarith

/-- Every canonical circuit failing a static certificate/circuit check reaches
the canonical false halt within the same public verifier budget. -/
theorem canonical_rejectsIn (certificate : List CircuitSym) (c : Circuit)
    (hbad : ¬ c.WellFormed ∨
      certificate.length ≠ c.inputCount ∨
      certificate.all isAssignmentSymbol = false) :
    RejectsIn
      (initList machine (pairEncoding certificate (encodeCircuit c)))
      (verifierStepBound
        (pairEncoding certificate (encodeCircuit c)).length) := by
  rcases certificate_header_phase certificate (encodeCircuit c) with
    ⟨afterHeader, hheaderValid, hheaderRun⟩
  let gateInput :=
    List.map some (c.gates.flatMap encodeCircuitGate) ++
      List.map some (.outputMark :: encNat c.output)
  have hencoded : List.map some (encodeCircuit c) =
      List.map some (encNat c.inputCount) ++ gateInput := by
    simp [encodeCircuit, gateInput, List.map_append, List.append_assoc]
  have hinputCount : c.inputCount ≤ (encodeCircuit c).length := by
    simp [encodeCircuit, encNat]
  have hgateInputLength : gateInput.length ≤ (encodeCircuit c).length := by
    simp [gateInput, encodeCircuit, encNat]
    omega
  by_cases hlength : certificate.length = c.inputCount
  · by_cases hlegal : certificate.all isAssignmentSymbol = true
    · have hstateValid : afterHeader.validAssignment = true := by
        rw [hheaderValid, hlegal]
      rcases input_count_phase afterHeader c.inputCount gateInput
          (assignmentBits certificate) [] [] 0 0 hstateValid with
        ⟨afterCount, hcount⟩
      have hnwf : ¬ c.WellFormed := by
        rcases hbad with hnwf | hrest
        · exact hnwf
        · rcases hrest with hne | hfalse
          · exact False.elim (hne hlength)
          · rw [hlegal] at hfalse
            contradiction
      have hreject := circuit_body_rejectsIn_of_not_wellFormed afterCount c
        (assignmentBits certificate) (by simp [hlength]) hnwf
      have hbodyBound := circuitBodyRejectBound_le c (assignmentBits certificate)
      have hreject' := RejectsIn.mono hreject hbodyBound
      have hreject'' : RejectsIn
          (cfg (some .gates) afterCount gateInput []
            (assignmentBits certificate) [] [] 0 0 0)
          (1000 * ((encodeCircuit c).length +
            (assignmentBits certificate).length + 1) ^ 2) := by
        simpa [gateInput] using hreject'
      have hcountFull := RejectsIn.before_steps (c.inputCount + 1)
        hcount hreject''
      have hcountFull' : RejectsIn
          (cfg (some .inputCount) afterHeader (List.map some (encodeCircuit c))
            [] (assignmentBits certificate) [] [] certificate.length 0 0)
          (1000 * ((encodeCircuit c).length +
              (assignmentBits certificate).length + 1) ^ 2 +
            (c.inputCount + 1)) := by
        simpa [hencoded, hlength] using hcountFull
      have hfull := RejectsIn.before_steps (2 * (certificate.length + 1))
        hheaderRun hcountFull'
      exact RejectsIn.mono hfull (le_trans (by
        simp [verifierQuadraticBound, pairEncoding, assignmentBits_length]
        nlinarith) (verifierQuadraticBound_le _))
    ·
      have hfalse : certificate.all isAssignmentSymbol = false := by
        cases hvalue : certificate.all isAssignmentSymbol <;> simp_all
      have hreject := input_count_rejectsIn afterHeader c.inputCount
        certificate.length gateInput (assignmentBits certificate) [] [] 0 0
        (Or.inr (by rw [hheaderValid]; exact hfalse))
      have hreject' : RejectsIn
          (cfg (some .inputCount) afterHeader (List.map some (encodeCircuit c))
            [] (assignmentBits certificate) [] [] certificate.length 0 0)
          (inputCountRejectBound c.inputCount certificate.length gateInput
            (assignmentBits certificate) [] [] 0 0) := by
        simpa [hencoded] using hreject
      have hfull := RejectsIn.before_steps (2 * (certificate.length + 1))
        hheaderRun hreject'
      exact RejectsIn.mono hfull (le_trans (by
        simp [inputCountRejectBound, verifierQuadraticBound, pairEncoding,
          assignmentBits_length]
        nlinarith [hinputCount, hgateInputLength]) (verifierQuadraticBound_le _))
  ·
    have hreject := input_count_rejectsIn afterHeader c.inputCount
      certificate.length gateInput (assignmentBits certificate) [] [] 0 0
      (Or.inl hlength)
    have hreject' : RejectsIn
        (cfg (some .inputCount) afterHeader (List.map some (encodeCircuit c))
          [] (assignmentBits certificate) [] [] certificate.length 0 0)
        (inputCountRejectBound c.inputCount certificate.length gateInput
          (assignmentBits certificate) [] [] 0 0) := by
      simpa [hencoded] using hreject
    have hfull := RejectsIn.before_steps (2 * (certificate.length + 1))
      hheaderRun hreject'
    exact RejectsIn.mono hfull (le_trans (by
      simp [inputCountRejectBound, verifierQuadraticBound, pairEncoding,
        assignmentBits_length]
      nlinarith [hinputCount, hgateInputLength]) (verifierQuadraticBound_le _))

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
