import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmFrames

/-!
# Arithmetic layout of the verifier-input final disjunction

The input arms are followed by one false-seeded OR fold.  This module gives
its start and every source wire without referring to the recursive circuit
builder.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Pure arithmetic start of the final input-arm disjunction. -/
def verifierInputFinalOrStart
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  (verifierInputArmsStartPolynomial W).eval input.length +
    verifierInputArmPrefixCost W input.length
      (W.certificateBound.eval input.length + 1)

/-- Pure output wire of the conjunction for one candidate length. -/
def verifierInputArmOutputWire
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) : Nat :=
  (verifierInputArmsStartPolynomial W).eval input.length +
    verifierInputArmPrefixCost W input.length arm.val +
      arm.val + input.length + 2

/-- Pure ordered source family of the final input-arm disjunction. -/
def verifierInputFinalOrWires
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List Nat :=
  List.ofFn fun arm :
      Fin (W.certificateBound.eval input.length + 1) =>
    verifierInputArmOutputWire W input arm

/-- The semantic recursive arm builder ends at the pure final-OR start. -/
theorem verifierInputBoundaryScript_finalOrStart_eq_arithmetic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundaryScript W input).finalOrStart =
      verifierInputFinalOrStart W input := by
  unfold verifierInputFinalOrStart
  unfold verifierInputBoundaryScript compileVerifierInputShapeScript
  dsimp only
  rw [VerifierInput.InputArmsResult.gate_delta]
  rw [verifierInputArmsStartPolynomial_eval_eq_separatorBuilder]
  rfl

/-- The semantic final-OR source list is exactly the arithmetic conjunction
output family. -/
theorem verifierInputBoundaryScript_finalOrWires_eq_arithmetic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundaryScript W input).finalOrWires =
      verifierInputFinalOrWires W input := by
  unfold verifierInputBoundaryScript compileVerifierInputShapeScript
  dsimp only
  unfold verifierInputFinalOrWires
  apply List.ofFn_inj.mpr
  funext arm
  rw [VerifierInput.buildInputArms_wires_eq]
  · unfold verifierInputArmOutputWire verifierInputArmPrefixCost
    rw [verifierInputArmsStartPolynomial_eval_eq_separatorBuilder]
  · exact verifierInputArm_fits W input arm

end CLRS.Chapter34.Turing.CookLevin
