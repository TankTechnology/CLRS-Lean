import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.MalformedBounds

/-!
# Guarded circuit normalizer: uniform polynomial runtime

This module joins successful canonical inputs, invalid canonical inputs, and
malformed raw inputs under one concrete polynomial bound.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition
open _root_.Turing

/-- The fixed normalizer returns its public guarded result within one uniform
polynomial budget on every raw circuit-symbol stream. -/
theorem allInputsWithinPolynomial (input : List CircuitSym) :
    Nonempty (TM2OutputsInTime machine input
      (some (normalizeGeneralCircuit input)) (stepBound input.length)) := by
  cases hdecode : decodeCircuit input with
  | none =>
      have hreject := malformed_rejectsIn input hdecode
      change Nonempty (EvalsToInTime step (initList machine input)
        (some (haltList machine (normalizeGeneralCircuit input)))
        (stepBound input.length))
      simpa [RejectsIn, normalizeGeneralCircuit, hdecode] using hreject
  | some c =>
      have hcanonical := encodeCircuit_of_decodeCircuit_eq_some hdecode
      subst input
      by_cases hwellFormed : c.WellFormed
      · refine ⟨{
          steps := successfulSteps c
          evals_in_steps := ?_
          steps_le_m := successfulSteps_le c }⟩
        change (flip Option.bind step)^[successfulSteps c]
          (some (initList machine (encodeCircuit c))) =
            some (haltList machine
              (normalizeGeneralCircuit (encodeCircuit c)))
        simpa [normalizeGeneralCircuit, decodeCircuit_encodeCircuit,
          hwellFormed] using canonical_run_exact c hwellFormed
      · have hreject := canonical_invalid_rejectsIn c hwellFormed
        have hbounded := RejectsIn.mono hreject (canonicalRejectBound_le c)
        change Nonempty (EvalsToInTime step (initList machine (encodeCircuit c))
          (some (haltList machine
            (normalizeGeneralCircuit (encodeCircuit c))))
          (stepBound (encodeCircuit c).length))
        simpa [RejectsIn, normalizeGeneralCircuit, decodeCircuit_encodeCircuit,
          hwellFormed] using hbounded

/-- Polynomial whose evaluation is definitionally the public step budget. -/
noncomputable def runtimePolynomial : Polynomial Nat :=
  1048576 * (Polynomial.X + 1) ^ 6 + 1048576

@[simp] theorem runtimePolynomial_eval (n : Nat) :
    runtimePolynomial.eval n = stepBound n := by
  simp [runtimePolynomial, stepBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- Machine-level polynomial-time computability of guarded circuit
normalization, including malformed and non-well-formed inputs. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id normalizeGeneralCircuit where
  tm := machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := runtimePolynomial
  outputsFun := fun input => by
    simpa using Classical.choice (allInputsWithinPolynomial input)

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
