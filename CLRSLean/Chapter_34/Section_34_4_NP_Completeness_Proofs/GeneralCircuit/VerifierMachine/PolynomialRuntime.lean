import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.MalformedBounds

/-!
# Concrete verifier: uniform polynomial runtime

This module joins the bounded successful, canonical-rejection, and malformed
routes into the public `TM2ComputableInPolyTime` witness.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- Canonical static-check rejection is an in-time output of the public
Boolean verifier, not merely a run to an internal rejection configuration. -/
private theorem canonical_reject_outputs_in_time
    (certificate : List CircuitSym) (c : Circuit)
    (hbad : ¬ c.WellFormed ∨
      certificate.length ≠ c.inputCount ∨
      certificate.all isAssignmentSymbol = false) :
    Nonempty (TM2OutputsInTime machine
      (pairEncoding certificate (encodeCircuit c))
      (some (boolEncoding
        (generalCircuitVerifier certificate (encodeCircuit c))))
      (verifierStepBound
        (pairEncoding certificate (encodeCircuit c)).length)) := by
  have hreject := canonical_rejectsIn certificate c hbad
  rcases hbad with hnwf | hrest
  · change Nonempty (EvalsToInTime step
      (initList machine (pairEncoding certificate (encodeCircuit c)))
      (some (haltList machine
        [generalCircuitVerifier certificate (encodeCircuit c)]))
      (verifierStepBound (pairEncoding certificate (encodeCircuit c)).length))
    simpa [RejectsIn, boolEncoding, generalCircuitVerifier,
      decodeCircuit_encodeCircuit, hnwf] using hreject
  · rcases hrest with hlength | hlegal
    · change Nonempty (EvalsToInTime step
        (initList machine (pairEncoding certificate (encodeCircuit c)))
        (some (haltList machine
          [generalCircuitVerifier certificate (encodeCircuit c)]))
        (verifierStepBound (pairEncoding certificate (encodeCircuit c)).length))
      simpa [RejectsIn, boolEncoding, generalCircuitVerifier,
        decodeCircuit_encodeCircuit, hlength] using hreject
    · change Nonempty (EvalsToInTime step
        (initList machine (pairEncoding certificate (encodeCircuit c)))
        (some (haltList machine
          [generalCircuitVerifier certificate (encodeCircuit c)]))
        (verifierStepBound (pairEncoding certificate (encodeCircuit c)).length))
      simpa [RejectsIn, boolEncoding, generalCircuitVerifier,
        decodeCircuit_encodeCircuit, hlegal] using hreject

/-- The concrete verifier returns its exact public Boolean within one uniform
polynomial budget on every pair-encoded certificate/input, including all
malformed and rejecting inputs. -/
theorem verifier_outputs_in_time_nonempty (certificate input : List CircuitSym) :
    Nonempty (TM2OutputsInTime machine (pairEncoding certificate input)
      (some (boolEncoding (generalCircuitVerifier certificate input)))
      (verifierStepBound (pairEncoding certificate input).length)) := by
  cases hdecode : decodeCircuit input with
  | none =>
      have hreject := malformed_circuit_rejectsIn certificate input hdecode
      change Nonempty (EvalsToInTime step
        (initList machine (pairEncoding certificate input))
        (some (haltList machine
          [generalCircuitVerifier certificate input]))
        (verifierStepBound (pairEncoding certificate input).length))
      simpa [RejectsIn, boolEncoding, generalCircuitVerifier, hdecode]
        using hreject
  | some c =>
      have hcanonical := encodeCircuit_of_decodeCircuit_eq_some hdecode
      subst input
      by_cases hwf : c.WellFormed
      · by_cases hlength : certificate.length = c.inputCount
        · by_cases hlegal : certificate.all isAssignmentSymbol = true
          · refine ⟨?_⟩
            change EvalsToInTime step
              (initList machine (pairEncoding certificate (encodeCircuit c)))
              (some (haltList machine
                [generalCircuitVerifier certificate (encodeCircuit c)]))
              (verifierStepBound
                (pairEncoding certificate (encodeCircuit c)).length)
            have hrun := successful_run certificate c hwf hlength hlegal
            have hsteps := successfulSteps_le certificate c hwf hlength
            refine {
              steps := successfulSteps certificate c
              evals_in_steps := ?_
              steps_le_m := ?_ }
            · simpa [generalCircuitVerifier, decodeCircuit_encodeCircuit,
                hwf, hlength, hlegal] using hrun
            · exact hsteps.trans (le_trans (by
                simp [verifierQuadraticBound]) (verifierQuadraticBound_le _))
          ·
            have hfalse : certificate.all isAssignmentSymbol = false := by
              cases hvalue : certificate.all isAssignmentSymbol <;> simp_all
            exact canonical_reject_outputs_in_time certificate c
              (Or.inr (Or.inr hfalse))
        · exact canonical_reject_outputs_in_time certificate c
            (Or.inr (Or.inl hlength))
      · exact canonical_reject_outputs_in_time certificate c (Or.inl hwf)

/-- Chosen bounded run used by Mathlib's structure field.  The propositional
`Nonempty` theorem above is the compositional proof surface; this definition
performs the single classical extraction needed by the bundled machine API. -/
noncomputable def verifier_outputs_in_time (certificate input : List CircuitSym) :
    TM2OutputsInTime machine (pairEncoding certificate input)
      (some (boolEncoding (generalCircuitVerifier certificate input)))
      (verifierStepBound (pairEncoding certificate input).length) :=
  Classical.choice (verifier_outputs_in_time_nonempty certificate input)

/-- Polynomial whose evaluation is exactly `verifierStepBound`. -/
noncomputable def verifierTime : Polynomial Nat :=
  10000 * (Polynomial.X + 1) ^ 4

@[simp] theorem verifierTime_eval (n : Nat) :
    verifierTime.eval n = verifierStepBound n := by
  simp [verifierTime, verifierStepBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- Machine-level polynomial-time computability of the executable
general-circuit certificate verifier. -/
noncomputable def generalCircuitVerifierComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List CircuitSym × List CircuitSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => generalCircuitVerifier pr.1 pr.2) where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := verifierTime
  outputsFun := fun ⟨certificate, input⟩ => by
    simpa using verifier_outputs_in_time certificate input

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
