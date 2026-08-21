import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConstraintTransitionOutputs
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryProgression

/-!
# Raw-input source for final transition constraint wires

The transition outputs form a second exact polynomial affine progression,
starting at the completed-validity endpoint.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First final-conjunction transition source wire. -/
def verifierTransitionOutputBasePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierTransitionStartPolynomial W +
    verifierTransitionOutputOffsetPolynomial W

/-- Forward delimiter-bearing transition source blocks. -/
def verifierTransitionOutputSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryProgressionFrameStream
    (verifierTransitionOutputBasePolynomial W)
    (verifierTransitionCostPolynomial W)
    (verifierHorizon W) input

/-- The affine source is exactly the semantic transition-output list. -/
theorem verifierTransitionOutputSource_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionOutputSource W input =
      encodeAffineConjunctionSources
        (List.ofFn (verifierTransitions W input).outputs) := by
  unfold verifierTransitionOutputSource
    exactPolynomialAffineUnaryProgressionFrameStream
    affineUnaryProgressionFrameStream affineUnaryProgressionValues
    exactPolynomialAffineUnaryProgression
  rw [affineUnaryProgressionValuesFrom_eq_ofFn]
  simp only [verifierTransitionOutputBasePolynomial,
    Polynomial.eval_add, verifierTransitionCostPolynomial_eval]
  unfold encodeAffineConjunctionSources encodeUnaryFrame
  congr 1
  apply List.ofFn_inj.mpr
  funext step
  rw [verifierTransitions_output_eq]
  ring

/-- A fixed polynomial-time TM2 emits every transition output source from the
original verifier word. -/
noncomputable def verifierTransitionOutputSource_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionOutputSource W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (verifierTransitionOutputBasePolynomial W)
      (verifierTransitionCostPolynomial W)
      (verifierHorizon W)

end CLRS.Chapter34.Turing.CookLevin
