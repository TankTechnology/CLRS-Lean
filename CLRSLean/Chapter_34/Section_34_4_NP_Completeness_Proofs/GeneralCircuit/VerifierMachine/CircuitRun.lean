import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CircuitPhases

/-!
# Concrete verifier: circuit header, output, and successful complete run
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- Consume the unary circuit input count while matching it against the
already-counted certificate length. -/
theorem input_count_phase (state : State) (n : Nat)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (index saved : Nat) (hvalid : state.validAssignment = true) :
    ∃ finalState,
      transition^[n + 1]
        (some (cfg (some .inputCount) state
          (List.map some (encNat n) ++ input)
          [] certificate values scratch n index saved)) =
        some (cfg (some .gates) finalState input [] certificate values scratch
          0 index saved) := by
  induction n generalizing state with
  | zero =>
      let finalState : State :=
        { state with inputBuffer := some (some .endMark), counterPresent := false }
      refine ⟨finalState, ?_⟩
      change step (cfg (some .inputCount) state (some .endMark :: input)
        [] certificate values scratch 0 index saved) = _
      exact input_count_end_step state input [] certificate values scratch
        index saved hvalid
  | succ n ih =>
      let nextState : State :=
        { state with inputBuffer := some (some .argMark), counterPresent := true }
      have hnextValid : nextState.validAssignment = true := by
        simpa [nextState] using hvalid
      rcases ih nextState hnextValid with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := input_count_arg_step state
        (List.map some (encNat n) ++ input) [] certificate values scratch n index saved
      have hfull := step_then (n + 1) hfirst hrun
      simpa [nextState, encNat, List.replicate_succ, List.append_assoc] using hfull

/-- Exact cost from the encoded output marker through canonical halt. -/
def outputSteps (inputBits : List Bool) (values : Array Bool)
    (outputIndex : Nat) : Nat :=
  1 + (outputIndex + 1) + 1 + (2 * values.size + 4) +
    cleanupSteps [] inputBits values.toList.reverse [] values.size 0 0

/-- Read a valid designated output, perform the final restoring lookup, clear
all work stacks, and halt with exactly its Boolean value. -/
theorem output_phase (state : State) (inputBits : List Bool)
    (values : Array Bool) (outputIndex : Nat)
    (houtput : outputIndex < values.size) :
    transition^[outputSteps inputBits values outputIndex]
      (some (cfg (some .gates) state
        (List.map some (.outputMark :: encNat outputIndex))
        [] inputBits values.toList.reverse [] values.size 0 0)) =
      some (haltList machine [values.getD outputIndex false]) := by
  rcases reverse_split_getD values.toList outputIndex houtput with
    ⟨front, older, hsplit, hlength, holder⟩
  have hcount : front.length + older.length + 1 = values.size := by
    simpa using hlength
  have htag : transition^[1]
      (some (cfg (some .gates) state
        (List.map some (.outputMark :: encNat outputIndex))
        [] inputBits values.toList.reverse [] values.size 0 0)) =
      some (cfg (some (.parseNat .outputGate))
        { state with inputBuffer := some (some .outputMark) }
        (List.map some (encNat outputIndex))
        [] inputBits values.toList.reverse [] values.size 0 0) := by
    change step (cfg (some .gates) state
      (List.map some (.outputMark :: encNat outputIndex))
      [] inputBits values.toList.reverse [] values.size 0 0) = _
    simpa using gates_output_step state (List.map some (encNat outputIndex))
      [] inputBits values.toList.reverse [] values.size 0 0
  rcases parse_nat_phase
      { state with inputBuffer := some (some .outputMark) }
      .outputGate outputIndex 0 [] [] inputBits values.toList.reverse [] values.size 0 with
    ⟨afterParse, hparse⟩
  have hparse' : transition^[outputIndex + 1]
      (some (cfg (some (.parseNat .outputGate))
        { state with inputBuffer := some (some .outputMark) }
        (List.map some (encNat outputIndex))
        [] inputBits values.toList.reverse [] values.size 0 0)) =
      some (cfg (some .checkTrailing) afterParse [] [] inputBits
        values.toList.reverse [] values.size outputIndex 0) := by
    simpa [parsedLabel] using hparse
  let afterTrailing : State := { afterParse with inputBuffer := none }
  have htrailing : transition^[1]
      (some (cfg (some .checkTrailing) afterParse [] [] inputBits
        values.toList.reverse [] values.size outputIndex 0)) =
      some (cfg (some (.gateSubtract .outputGate)) afterTrailing [] [] inputBits
        values.toList.reverse [] values.size outputIndex 0) := by
    change step (cfg (some .checkTrailing) afterParse [] [] inputBits
      values.toList.reverse [] values.size outputIndex 0) = _
    exact check_trailing_empty_step afterParse [] inputBits values.toList.reverse []
      values.size outputIndex 0
  rcases gate_lookup_output_phase afterTrailing front older
      (values.toList.getD outputIndex false) inputBits with
    ⟨afterLookup, hlookup⟩
  change transition^[2 * older.length + 2 * front.length + 6] _ = _ at hlookup
  have hlookup' : transition^[2 * values.size + 4]
      (some (cfg (some (.gateSubtract .outputGate)) afterTrailing [] [] inputBits
        values.toList.reverse [] values.size outputIndex 0)) =
      some (cfg (some (.clearInput (values.toList.getD outputIndex false)))
        afterLookup [] [] inputBits values.toList.reverse [] values.size 0 0) := by
    have hcost : 2 * values.size + 4 =
        2 * older.length + 2 * front.length + 6 := by omega
    rw [hcost, hsplit, ← hcount]
    simpa only [holder] using hlookup
  have hcleanup := cleanup_phase afterLookup
    (values.toList.getD outputIndex false) [] inputBits values.toList.reverse []
    values.size 0 0
  have h₁ := step_comp 1 (outputIndex + 1) htag hparse'
  have h₂ := step_comp ((outputIndex + 1) + 1) 1 h₁ htrailing
  have h₃ := step_comp (1 + ((outputIndex + 1) + 1))
    (2 * values.size + 4) h₂ hlookup'
  have hfull := step_comp
    ((2 * values.size + 4) + (1 + ((outputIndex + 1) + 1)))
    (cleanupSteps [] inputBits values.toList.reverse [] values.size 0 0)
    h₃ hcleanup
  have hsteps : outputSteps inputBits values outputIndex =
      cleanupSteps [] inputBits values.toList.reverse [] values.size 0 0 +
        ((2 * values.size + 4) + (1 + ((outputIndex + 1) + 1))) := by
    simp [outputSteps]
    omega
  rw [hsteps]
  simpa only [array_toList_getD] using hfull

/-- Boolean stack interpretation of a certificate. -/
def assignmentBits (certificate : List CircuitSym) : List Bool :=
  certificate.map assignmentSymbolValue

@[simp] theorem assignmentBits_length (certificate : List CircuitSym) :
    (assignmentBits certificate).length = certificate.length := by
  simp [assignmentBits]

/-- The stack interpretation has exactly the public certificate lookup
semantics, including the out-of-bounds default. -/
theorem assignmentBits_getD (certificate : List CircuitSym) (i : Nat) :
    (assignmentBits certificate).getD i false = assignmentInputs certificate i := by
  by_cases hi : i < certificate.length
  · have hmap : i < (assignmentBits certificate).length := by simpa using hi
    simp [assignmentBits, assignmentInputs, hi, List.getD_eq_getElem _ _ hmap,
      List.getElem_map]
  · have hmap : (assignmentBits certificate).length ≤ i := by
      simp only [assignmentBits_length]
      omega
    simp [assignmentInputs, hi, List.getD_eq_default _ _ hmap]

/-- The concrete gate-list accumulator is the public circuit evaluator on the
same certificate. -/
theorem evalGateList_assignment (certificate : List CircuitSym)
    (gates : List CircuitGate) :
    evalGateList (assignmentBits certificate) #[] gates =
      gates.foldl
        (fun values gate =>
          values.push (gate.evalWith (assignmentInputs certificate) values)) #[] := by
  unfold evalGateList
  have hinputs : (fun i => (assignmentBits certificate).getD i false) =
      assignmentInputs certificate := by
    funext i
    exact assignmentBits_getD certificate i
  rw [hinputs]

/-- Initial list configurations expose exactly the named verifier stacks. -/
theorem initList_eq_cfg (input : List (Option CircuitSym)) :
    initList machine input =
      cfg (some .scanCertificate) initialState input [] [] [] [] 0 0 0 := by
  apply _root_.Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext stack
    cases stack <;> simp [initList, cfg, machine, stackContents]

/-- Exact step count for the accepting/rejecting Boolean result on a
well-formed, canonically encoded circuit with a legal, correctly-sized
certificate.  The result bit itself may be false. -/
def successfulSteps (certificate : List CircuitSym) (c : Circuit) : Nat :=
  (certificate.length + 1) +
    (certificate.length + 1) +
      (c.inputCount + 1) +
        gateListSteps 0 c.gates +
          outputSteps (assignmentBits certificate)
            (c.evalValues (assignmentInputs certificate)) c.output

/-- End-to-end semantic correctness on every well-formed encoded circuit and
legal certificate of the declared length. -/
theorem successful_run (certificate : List CircuitSym) (c : Circuit)
    (hwf : c.WellFormed)
    (hlength : certificate.length = c.inputCount)
    (hlegal : certificate.all isAssignmentSymbol = true) :
    transition^[successfulSteps certificate c]
      (some (initList machine (pairEncoding certificate (encodeCircuit c)))) =
      some (haltList machine [c.eval (assignmentInputs certificate)]) := by
  let bits := assignmentBits certificate
  have hbitsLength : bits.length = c.inputCount := by
    simp [bits, hlength]
  rcases scan_phase initialState certificate
      (List.map some (encodeCircuit c)) [] [] [] [] 0 0 0 with
    ⟨afterScan, hscanLegal, hscan⟩
  have hscanLegal' : afterScan.validAssignment = true := by
    simpa [initialState, hlegal] using hscanLegal
  have hscan' : transition^[certificate.length + 1]
      (some (initList machine (pairEncoding certificate (encodeCircuit c)))) =
      some (cfg (some .reverseCertificate) afterScan
        (List.map some (encodeCircuit c)) [] [] [] bits.reverse
        certificate.length 0 0) := by
    rw [initList_eq_cfg]
    simpa [pairEncoding, bits, assignmentBits, List.append_assoc] using hscan
  rcases reverse_phase afterScan bits.reverse
      (List.map some (encodeCircuit c)) [] [] [] certificate.length 0 0 with
    ⟨afterReverse, hreverseLegal, hreverse⟩
  have hreverse' : transition^[certificate.length + 1]
      (some (cfg (some .reverseCertificate) afterScan
        (List.map some (encodeCircuit c)) [] [] [] bits.reverse
        certificate.length 0 0)) =
      some (cfg (some .inputCount) afterReverse
        (List.map some (encodeCircuit c)) [] bits [] []
        certificate.length 0 0) := by
    simpa [bits] using hreverse
  let gateInput :=
    List.map some (c.gates.flatMap encodeCircuitGate) ++
      List.map some (.outputMark :: encNat c.output)
  rcases input_count_phase afterReverse c.inputCount gateInput bits [] [] 0 0
      (by rw [hreverseLegal]; exact hscanLegal') with ⟨afterCount, hcount⟩
  have hcount' : transition^[c.inputCount + 1]
      (some (cfg (some .inputCount) afterReverse
        (List.map some (encodeCircuit c)) [] bits [] [] certificate.length 0 0)) =
      some (cfg (some .gates) afterCount gateInput [] bits [] [] 0 0 0) := by
    rw [hlength]
    simpa [encodeCircuit, gateInput, List.map_append, List.append_assoc] using hcount
  have hgatesValid : ∀ i (hi : i < c.gates.length),
      (c.gates.get ⟨i, hi⟩).ValidAt bits.length
        ((#[] : Array Bool).size + i) := by
    intro i hi
    simpa [hbitsLength] using hwf.2 i hi
  let outputInput := List.map some (.outputMark :: encNat c.output)
  rcases gate_list_phase afterCount c.gates bits #[] outputInput hgatesValid with
    ⟨afterGates, hgates⟩
  let finalValues := evalGateList bits #[] c.gates
  have hfinalValues : finalValues = c.evalValues (assignmentInputs certificate) := by
    simpa [finalValues, bits, Circuit.evalValues] using
      evalGateList_assignment certificate c.gates
  have hfinalSize : finalValues.size = c.gates.length := by
    rw [hfinalValues, Circuit.evalValues_size]
  have hgates' : transition^[gateListSteps 0 c.gates]
      (some (cfg (some .gates) afterCount gateInput [] bits [] [] 0 0 0)) =
      some (cfg (some .gates) afterGates outputInput [] bits
        finalValues.toList.reverse [] finalValues.size 0 0) := by
    simpa [gateInput, outputInput, finalValues, hfinalSize] using hgates
  have houtputBound : c.output < finalValues.size := by
    rw [hfinalValues, Circuit.evalValues_size]
    exact hwf.1
  have houtput := output_phase afterGates bits finalValues c.output houtputBound
  have houtput' : transition^[outputSteps bits
      (c.evalValues (assignmentInputs certificate)) c.output]
      (some (cfg (some .gates) afterGates outputInput [] bits
        finalValues.toList.reverse [] finalValues.size 0 0)) =
      some (haltList machine [c.eval (assignmentInputs certificate)]) := by
    rw [← hfinalValues]
    have hresult : finalValues.getD c.output false =
        c.eval (assignmentInputs certificate) := by
      rw [hfinalValues]
      rfl
    simpa only [outputInput, hresult] using houtput
  have h₁ := step_comp (certificate.length + 1) (certificate.length + 1)
    hscan' hreverse'
  have h₂ := step_comp ((certificate.length + 1) + (certificate.length + 1))
    (c.inputCount + 1) h₁ hcount'
  have h₃ := step_comp
    ((c.inputCount + 1) + ((certificate.length + 1) + (certificate.length + 1)))
    (gateListSteps 0 c.gates) h₂ hgates'
  have hfull := step_comp
    ((gateListSteps 0 c.gates) +
      ((c.inputCount + 1) +
        ((certificate.length + 1) + (certificate.length + 1))))
    (outputSteps bits (c.evalValues (assignmentInputs certificate)) c.output)
    h₃ houtput'
  have hsteps : successfulSteps certificate c =
      outputSteps bits (c.evalValues (assignmentInputs certificate)) c.output +
        ((gateListSteps 0 c.gates) +
          ((c.inputCount + 1) +
            ((certificate.length + 1) + (certificate.length + 1)))) := by
    simp [successfulSteps, bits]
    omega
  rw [hsteps]
  exact hfull

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
