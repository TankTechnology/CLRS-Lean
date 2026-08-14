import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CanonicalRun

/-!
# Concrete verifier: malformed serialized circuits
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- A non-output gate tag whose gate decoder fails is rejected by the machine. -/
theorem gate_decode_reject (state : State) (symbol : CircuitSym)
    (symbols : List CircuitSym) (inputBits : List Bool) (values : Array Bool)
    (houtput : symbol ≠ .outputMark)
    (hdecode : decodeCircuitGate (symbol :: symbols) = none) :
    Rejects (cfg (some .gates) state (List.map some (symbol :: symbols))
      [] inputBits values.toList.reverse [] values.size 0 0) := by
  cases symbol with
  | inputMark =>
      have hnat : decNat symbols = none := by
        simp [decodeCircuitGate] at hdecode
        exact Option.eq_none_iff_forall_ne_some.mpr (by
          rintro ⟨n, rest⟩ hsome
          exact hdecode n rest hsome)
      have htag := gates_input_step state (List.map some symbols)
        [] inputBits values.toList.reverse [] values.size 0 0
      apply Rejects.before_step (by simpa using htag)
      exact parse_nat_reject_of_decNat_none
        { state with inputBuffer := some (some .inputMark) }
        .inputGate symbols inputBits values.toList.reverse [] values.size 0 0 hnat
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
      apply Rejects.before_step (by simpa using htag)
      exact parse_nat_reject_of_decNat_none
        { state with inputBuffer := some (some .notMark) }
        .notGate symbols inputBits values.toList.reverse [] values.size 0 0 hnat
  | andMark =>
      cases hleft : decNat symbols with
      | none =>
          have htag := gates_and_step state (List.map some symbols)
            [] inputBits values.toList.reverse [] values.size 0 0
          apply Rejects.before_step (by simpa using htag)
          exact parse_nat_reject_of_decNat_none
            { state with inputBuffer := some (some .andMark) }
            .andLeft symbols inputBits values.toList.reverse [] values.size 0 0 hleft
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
          apply Rejects.before_step (by
            simpa [List.map_append, List.append_assoc] using htag)
          rcases parse_nat_phase
              { state with inputBuffer := some (some .andMark) }
              .andLeft left 0 (List.map some middle) [] inputBits
              values.toList.reverse [] values.size 0 with
            ⟨afterLeftParse, hparse⟩
          apply Rejects.before_steps (left + 1)
            (by simpa only [parsedLabel, Nat.zero_add] using hparse)
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
            apply Rejects.before_steps (2 * values.size + 4) hlookup'
            exact parse_nat_reject_of_decNat_none afterLookup
              (.andRight (values.toList.getD left false)) middle inputBits
              values.toList.reverse [] values.size 0 0 hright
          · exact gate_lookup_reject afterLeftParse .andLeft values.size left
              (List.map some middle) inputBits values.toList.reverse [] 0 (by omega)
  | orMark =>
      cases hleft : decNat symbols with
      | none =>
          have htag := gates_or_step state (List.map some symbols)
            [] inputBits values.toList.reverse [] values.size 0 0
          apply Rejects.before_step (by simpa using htag)
          exact parse_nat_reject_of_decNat_none
            { state with inputBuffer := some (some .orMark) }
            .orLeft symbols inputBits values.toList.reverse [] values.size 0 0 hleft
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
          apply Rejects.before_step (by
            simpa [List.map_append, List.append_assoc] using htag)
          rcases parse_nat_phase
              { state with inputBuffer := some (some .orMark) }
              .orLeft left 0 (List.map some middle) [] inputBits
              values.toList.reverse [] values.size 0 with
            ⟨afterLeftParse, hparse⟩
          apply Rejects.before_steps (left + 1)
            (by simpa only [parsedLabel, Nat.zero_add] using hparse)
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
            apply Rejects.before_steps (2 * values.size + 4) hlookup'
            exact parse_nat_reject_of_decNat_none afterLookup
              (.orRight (values.toList.getD left false)) middle inputBits
              values.toList.reverse [] values.size 0 0 hright
          · exact gate_lookup_reject afterLeftParse .orLeft values.size left
              (List.map some middle) inputBits values.toList.reverse [] 0 (by omega)
  | outputMark => exact False.elim (houtput rfl)
  | argMark =>
      exact rejects_after_cleanup_step _ _ (List.map some symbols) inputBits
        values.toList.reverse [] values.size 0 0
        (gates_bad_marker_reject_step state .argMark (Or.inl rfl)
          (List.map some symbols) [] inputBits values.toList.reverse [] values.size 0 0)
  | endMark =>
      exact rejects_after_cleanup_step _ _ (List.map some symbols) inputBits
        values.toList.reverse [] values.size 0 0
        (gates_bad_marker_reject_step state .endMark (Or.inr rfl)
          (List.map some symbols) [] inputBits values.toList.reverse [] values.size 0 0)

/-- A gate stream whose structural decoder fails is rejected.  The fuel
hypothesis is the one used by `decodeCircuit`: at least the remaining symbol
count, so failure cannot be an artificial fuel exhaustion. -/
theorem gate_stream_reject_of_decode_none (state : State) (fuel : Nat)
    (symbols : List CircuitSym) (inputBits : List Bool) (values : Array Bool)
    (hfuel : symbols.length ≤ fuel)
    (hdecode : decodeCircuitGates fuel symbols = none) :
    Rejects (cfg (some .gates) state (List.map some symbols)
      [] inputBits values.toList.reverse [] values.size 0 0) := by
  induction fuel generalizing state symbols values with
  | zero =>
      have hempty : symbols = [] := by
        cases symbols <;> simp_all
      subst symbols
      exact rejects_after_cleanup_step _ _ [] inputBits values.toList.reverse []
        values.size 0 0
        (gates_eof_reject_step state [] inputBits values.toList.reverse []
          values.size 0 0)
  | succ fuel ih =>
      cases symbols with
      | nil =>
          exact rejects_after_cleanup_step _ _ [] inputBits values.toList.reverse []
            values.size 0 0
            (gates_eof_reject_step state [] inputBits values.toList.reverse []
              values.size 0 0)
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
            apply Rejects.before_step (by simpa using htag)
            exact parse_nat_reject_of_decNat_none
              { state with inputBuffer := some (some .outputMark) }
              .outputGate symbols inputBits values.toList.reverse []
              values.size 0 0 hnat
          · cases hgate : decodeCircuitGate (symbol :: symbols) with
            | none =>
                exact gate_decode_reject state symbol symbols inputBits values
                  hout hgate
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
                rw [hsymbols]
                by_cases hvalid : gate.ValidAt inputBits.length values.size
                · let nextValues := values.push
                    (gate.evalWith (fun i => inputBits.getD i false) values)
                  rcases gate_phase state gate inputBits values (List.map some rest)
                      hvalid with ⟨afterGate, hrun⟩
                  apply Rejects.before_steps (gateSteps values.size gate)
                  · simpa [List.map_append] using hrun
                  · simpa [nextValues, List.getD_eq_getElem?_getD,
                      Array.toList_push, List.reverse_append] using
                      ih afterGate rest nextValues hrestFuel hrestDecode
                · simpa [List.map_append] using
                    gate_reject_of_not_valid state gate inputBits values
                      (List.map some rest) hvalid

/-- A structurally decoded gate stream with unconsumed trailing symbols is
rejected at the output boundary (or earlier at its first invalid gate). -/
theorem gate_stream_reject_of_trailing (state : State) (fuel : Nat)
    (symbols : List CircuitSym) (inputBits : List Bool) (values : Array Bool)
    (gates : List CircuitGate) (outputIndex : Nat) (trailing : List CircuitSym)
    (hdecode : decodeCircuitGates fuel symbols =
      some (gates, outputIndex, trailing))
    (htrailing : trailing ≠ []) :
    Rejects (cfg (some .gates) state (List.map some symbols)
      [] inputBits values.toList.reverse [] values.size 0 0) := by
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
    apply Rejects.before_steps (gateListSteps values.size gates)
    · exact hrun'
    · have htag := gates_output_step afterGates
          (List.map some (encNat outputIndex ++ trailing)) [] inputBits
          finalValues.toList.reverse [] finalValues.size 0 0
      apply Rejects.before_step (by
        simpa only [outputInput, List.map_cons, List.map_append,
          List.cons_append] using htag)
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
      apply Rejects.before_steps (outputIndex + 1) hparse'
      cases trailing with
      | nil => contradiction
      | cons head tail =>
          exact rejects_after_cleanup_step _ _ (List.map some tail) inputBits
            finalValues.toList.reverse [] finalValues.size outputIndex 0
            (by
              simpa using check_trailing_nonempty_step afterParse (some head)
                (List.map some tail) [] inputBits finalValues.toList.reverse []
                finalValues.size outputIndex 0)
  · exact gate_list_reject_of_not_valid state gates inputBits values outputInput hgates

/-- Every input rejected by the public circuit decoder reaches `[false]`. -/
theorem malformed_circuit_reject (certificate input : List CircuitSym)
    (hdecode : decodeCircuit input = none) :
    Rejects (initList machine (pairEncoding certificate input)) := by
  rcases certificate_header_phase certificate input with
    ⟨afterHeader, hheaderValid, hheaderRun⟩
  apply Rejects.before_steps (2 * (certificate.length + 1)) hheaderRun
  cases hnat : decNat input with
  | none =>
      exact input_count_reject_of_decNat_none afterHeader input
        (assignmentBits certificate) [] [] certificate.length 0 0 hnat
  | some decodedNat =>
      rcases decodedNat with ⟨inputCount, rest⟩
      have hinput := eq_encNat_append_of_decNat_eq_some hnat
      rw [hinput]
      by_cases hlength : certificate.length = inputCount
      · by_cases hlegal : certificate.all isAssignmentSymbol = true
        · have hstateValid : afterHeader.validAssignment = true := by
            rw [hheaderValid, hlegal]
          rcases input_count_phase afterHeader inputCount (List.map some rest)
              (assignmentBits certificate) [] [] 0 0 hstateValid with
            ⟨afterCount, hcount⟩
          apply Rejects.before_steps (inputCount + 1) (by
            simpa [List.map_append, hlength] using hcount)
          cases hgates : decodeCircuitGates rest.length rest with
          | none =>
              exact gate_stream_reject_of_decode_none afterCount rest.length rest
                (assignmentBits certificate) #[] (by omega) hgates
          | some decodedGates =>
              rcases decodedGates with ⟨gates, outputIndex, trailing⟩
              have htrailing : trailing ≠ [] := by
                intro hempty
                subst trailing
                simp [decodeCircuit, hnat, hgates] at hdecode
              exact gate_stream_reject_of_trailing afterCount rest.length rest
                (assignmentBits certificate) #[] gates outputIndex trailing
                hgates htrailing
        · have hfalse : certificate.all isAssignmentSymbol = false := by
            cases hvalue : certificate.all isAssignmentSymbol <;> simp_all
          simpa [List.map_append] using
            input_count_reject afterHeader inputCount certificate.length
              (List.map some rest) (assignmentBits certificate) [] [] 0 0
              (Or.inr (by rw [hheaderValid]; exact hfalse))
      · simpa [List.map_append] using
          input_count_reject afterHeader inputCount certificate.length
            (List.map some rest) (assignmentBits certificate) [] [] 0 0
            (Or.inl hlength)

/-- The concrete machine computes the correct Boolean on every malformed
circuit input. -/
theorem malformed_run (certificate input : List CircuitSym)
    (hdecode : decodeCircuit input = none) :
    ∃ steps,
      transition^[steps]
        (some (initList machine (pairEncoding certificate input))) =
        some (haltList machine [generalCircuitVerifier certificate input]) := by
  rcases malformed_circuit_reject certificate input hdecode with ⟨steps, hrun⟩
  exact ⟨steps, by simpa [generalCircuitVerifier, hdecode] using hrun⟩

/-- Unbounded exact correctness of the concrete machine on every pair.  The
separate runtime layer upgrades this result to polynomial time. -/
theorem verifier_run (certificate input : List CircuitSym) :
    ∃ steps,
      transition^[steps]
        (some (initList machine (pairEncoding certificate input))) =
        some (haltList machine [generalCircuitVerifier certificate input]) := by
  cases hdecode : decodeCircuit input with
  | none => exact malformed_run certificate input hdecode
  | some c =>
      have hcanonical := encodeCircuit_of_decodeCircuit_eq_some hdecode
      subst input
      exact canonical_run certificate c

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
