import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CircuitReject

/-!
# Concrete verifier: complete behavior on canonical circuit encodings
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- Scan and restore an arbitrary certificate before starting the circuit
header check. -/
theorem certificate_header_phase (certificate : List CircuitSym)
    (circuitInput : List CircuitSym) :
    ∃ finalState,
      finalState.validAssignment = certificate.all isAssignmentSymbol ∧
      transition^[2 * (certificate.length + 1)]
        (some (initList machine (pairEncoding certificate circuitInput))) =
        some (cfg (some .inputCount) finalState (List.map some circuitInput)
          [] (assignmentBits certificate) [] [] certificate.length 0 0) := by
  rcases scan_phase initialState certificate (List.map some circuitInput)
      [] [] [] [] 0 0 0 with ⟨afterScan, hscanValid, hscan⟩
  rcases reverse_phase afterScan (assignmentBits certificate).reverse
      (List.map some circuitInput) [] [] [] certificate.length 0 0 with
    ⟨afterReverse, hreverseValid, hreverse⟩
  have hscan' : transition^[certificate.length + 1]
      (some (initList machine (pairEncoding certificate circuitInput))) =
      some (cfg (some .reverseCertificate) afterScan
        (List.map some circuitInput) [] [] []
        (assignmentBits certificate).reverse certificate.length 0 0) := by
    rw [initList_eq_cfg]
    simpa [pairEncoding, assignmentBits, List.append_assoc] using hscan
  have hreverse' : transition^[certificate.length + 1]
      (some (cfg (some .reverseCertificate) afterScan
        (List.map some circuitInput) [] [] []
        (assignmentBits certificate).reverse certificate.length 0 0)) =
      some (cfg (some .inputCount) afterReverse (List.map some circuitInput)
        [] (assignmentBits certificate) [] [] certificate.length 0 0) := by
    simpa using hreverse
  refine ⟨afterReverse, ?_, ?_⟩
  · rw [hreverseValid, hscanValid]
    simp [initialState]
  · have hfull := step_comp (certificate.length + 1)
      (certificate.length + 1) hscan' hreverse'
    have hsteps : 2 * (certificate.length + 1) =
        (certificate.length + 1) + (certificate.length + 1) := by omega
    rw [hsteps]
    exact hfull

/-- Every canonical circuit whose static checks fail reaches `[false]`. -/
theorem canonical_reject (certificate : List CircuitSym) (c : Circuit)
    (hbad : ¬ c.WellFormed ∨
      certificate.length ≠ c.inputCount ∨
      certificate.all isAssignmentSymbol = false) :
    Rejects (initList machine (pairEncoding certificate (encodeCircuit c))) := by
  rcases certificate_header_phase certificate (encodeCircuit c) with
    ⟨afterHeader, hheaderValid, hheader⟩
  apply Rejects.before_steps (2 * (certificate.length + 1)) hheader
  let gateInput :=
    List.map some (c.gates.flatMap encodeCircuitGate) ++
      List.map some (.outputMark :: encNat c.output)
  have hencoded : List.map some (encodeCircuit c) =
      List.map some (encNat c.inputCount) ++ gateInput := by
    simp [encodeCircuit, gateInput, List.map_append, List.append_assoc]
  rw [hencoded]
  by_cases hlength : certificate.length = c.inputCount
  · by_cases hlegal : certificate.all isAssignmentSymbol = true
    · have hstateValid : afterHeader.validAssignment = true := by
        rw [hheaderValid, hlegal]
      rcases input_count_phase afterHeader c.inputCount gateInput
          (assignmentBits certificate) [] [] 0 0 hstateValid with
        ⟨afterCount, hcount⟩
      apply Rejects.before_steps (c.inputCount + 1) (by
        simpa [hlength] using hcount)
      have hnwf : ¬ c.WellFormed := by
        rcases hbad with hnwf | hrest
        · exact hnwf
        · rcases hrest with hne | hfalse
          · exact False.elim (hne hlength)
          · rw [hlegal] at hfalse
            contradiction
      exact circuit_body_reject_of_not_wellFormed afterCount c
        (assignmentBits certificate) (by simp [hlength]) hnwf
    · have hfalse : certificate.all isAssignmentSymbol = false := by
        cases hvalue : certificate.all isAssignmentSymbol <;> simp_all
      exact input_count_reject afterHeader c.inputCount certificate.length gateInput
        (assignmentBits certificate) [] [] 0 0
        (Or.inr (by rw [hheaderValid]; exact hfalse))
  · exact input_count_reject afterHeader c.inputCount certificate.length gateInput
      (assignmentBits certificate) [] [] 0 0 (Or.inl hlength)

/-- Complete exact result for every legal certificate of the declared length
and every canonical well-formed circuit, including a false evaluation. -/
theorem canonical_wellFormed_run (certificate : List CircuitSym) (c : Circuit)
    (hwf : c.WellFormed)
    (hlength : certificate.length = c.inputCount)
    (hlegal : certificate.all isAssignmentSymbol = true) :
    ∃ steps,
      transition^[steps]
        (some (initList machine (pairEncoding certificate (encodeCircuit c)))) =
        some (haltList machine [generalCircuitVerifier certificate (encodeCircuit c)]) := by
  refine ⟨successfulSteps certificate c, ?_⟩
  simpa [generalCircuitVerifier, decodeCircuit_encodeCircuit, hwf, hlength, hlegal]
    using successful_run certificate c hwf hlength hlegal

/-- Complete result for every certificate and canonical circuit encoding. -/
theorem canonical_run (certificate : List CircuitSym) (c : Circuit) :
    ∃ steps,
      transition^[steps]
        (some (initList machine (pairEncoding certificate (encodeCircuit c)))) =
        some (haltList machine [generalCircuitVerifier certificate (encodeCircuit c)]) := by
  by_cases hwf : c.WellFormed
  · by_cases hlength : certificate.length = c.inputCount
    · by_cases hlegal : certificate.all isAssignmentSymbol = true
      · exact canonical_wellFormed_run certificate c hwf hlength hlegal
      · have hfalse : certificate.all isAssignmentSymbol = false := by
          cases hvalue : certificate.all isAssignmentSymbol <;> simp_all
        rcases canonical_reject certificate c (Or.inr (Or.inr hfalse)) with
          ⟨steps, hrun⟩
        refine ⟨steps, ?_⟩
        simpa [generalCircuitVerifier, decodeCircuit_encodeCircuit, hwf, hlength,
          hfalse] using hrun
    · rcases canonical_reject certificate c (Or.inr (Or.inl hlength)) with
        ⟨steps, hrun⟩
      refine ⟨steps, ?_⟩
      simpa [generalCircuitVerifier, decodeCircuit_encodeCircuit, hwf, hlength]
        using hrun
  · rcases canonical_reject certificate c (Or.inl hwf) with ⟨steps, hrun⟩
    refine ⟨steps, ?_⟩
    simpa [generalCircuitVerifier, decodeCircuit_encodeCircuit, hwf] using hrun

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
