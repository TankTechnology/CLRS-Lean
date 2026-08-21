import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConstraintValiditySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeeds

/-!
# Closed coordinates of the final transition outputs

Each local transition circuit ends in one final AND gate.  Its output is
therefore the last wire in a fixed-cost transition block.  This module gives
the subtraction-free polynomial offset and specializes the family coordinate
formula to verifier instances.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Last-wire offset of one local transition circuit. -/
def transitionCircuitOutputOffsetPolynomial
    (tm : _root_.Turing.FinTM2) : Polynomial Nat :=
  2 + dispatchGatePolynomial tm +
    Polynomial.C (Fintype.card tm.K * maxPushesPerStep tm + 2) +
    (Polynomial.C 6 * cfgBitPolynomial tm + 1)

/-- The transition output offset is exactly one less than the full local
transition cost at every positive workspace height. -/
theorem transitionCircuitOutputOffsetPolynomial_eval_add_one
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (hwork : 0 < workHeight tm H) :
    (transitionCircuitOutputOffsetPolynomial tm).eval H + 1 =
      transitionCircuitGateCost tm H := by
  rw [← transitionCircuitGatePolynomial_eval tm H hwork]
  simp [transitionCircuitOutputOffsetPolynomial,
    transitionCircuitGatePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul]

/-- Input-length polynomial for the output offset of one verifier transition. -/
def verifierTransitionOutputOffsetPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  (transitionCircuitOutputOffsetPolynomial W.machine.tm).comp
    (verifierHeight W)

@[simp] theorem verifierTransitionOutputOffsetPolynomial_eval_add_one
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierTransitionOutputOffsetPolynomial W).eval n + 1 =
      transitionCircuitGateCost W.machine.tm
        ((verifierHeight W).eval n) := by
  rw [verifierTransitionOutputOffsetPolynomial, Polynomial.eval_comp,
    transitionCircuitOutputOffsetPolynomial_eval_add_one]
  exact Nat.add_pos_left (verifierHeight_eval_pos W n)
    (maxPushesPerStep W.machine.tm)

/-- Closed coordinate of every semantic verifier-transition output. -/
theorem verifierTransitions_output_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (step : Fin ((verifierHorizon W).eval input.length)) :
    (verifierTransitions W input).outputs step =
      (verifierTransitionStartPolynomial W).eval input.length +
        step.val * transitionCircuitGateCost W.machine.tm
          ((verifierHeight W).eval input.length) +
        (verifierTransitionOutputOffsetPolynomial W).eval input.length := by
  have hfamily := transitionCircuitFamily_output_add_one_eq W.machine.tm
    ((verifierHeight W).eval input.length)
    (verifierValidity W input).builder (verifierRows W input).rows
    (fun row =>
      ((verifierRows W input).rowValid row).mono
        ((verifierPool W input).extension.trans
          (verifierValidity W input).extension)) step
  change (verifierTransitions W input).outputs step + 1 = _ at hfamily
  rw [← verifierTransitionStartPolynomial_eval_eq_validity_length W
    input.length] at hfamily
  have hoff := verifierTransitionOutputOffsetPolynomial_eval_add_one W
    input.length
  rw [← hoff] at hfamily
  have hcancel :
      (verifierTransitions W input).outputs step + 1 =
        ((verifierTransitionStartPolynomial W).eval input.length +
            step.val * transitionCircuitGateCost W.machine.tm
              ((verifierHeight W).eval input.length) +
            (verifierTransitionOutputOffsetPolynomial W).eval input.length) +
          1 := by
    simpa only [Nat.add_assoc, Nat.add_mul] using hfamily
  exact Nat.add_right_cancel hcancel

end CLRS.Chapter34.Turing.CookLevin
