import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFinalOrLayout

/-!
# Builder-free verifier-input boundary script

All three phases of the input boundary are assembled here from arithmetic
data generated from the raw word: separator sources, candidate conjunction
frames, and the final disjunction.  The resulting record is proved equal to
the original proof-carrying semantic script.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Complete verifier-input runtime script with no circuit-builder field. -/
def verifierInputBoundaryArithmeticScript
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineVerifierInputShapeScript :=
  { separatorSources := verifierInputSeparatorCompiledSources W input
    armFrames := List.ofFn fun arm :
        Fin (W.certificateBound.eval input.length + 1) =>
      some (verifierInputArmArithmeticFrame W input arm)
    finalOrStart := verifierInputFinalOrStart W input
    finalOrWires := verifierInputFinalOrWires W input }

/-- The builder-free script is literally the canonical semantic script. -/
theorem verifierInputBoundaryArithmeticScript_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputBoundaryArithmeticScript W input =
      verifierInputBoundaryScript W input := by
  have hseparator :
      (verifierInputBoundaryScript W input).separatorSources =
        verifierInputSeparatorCompiledSources W input := by
    unfold verifierInputBoundaryScript compileVerifierInputShapeScript
    dsimp only
    exact (verifierInputSeparatorCompiledSources_eq W input).symm
  have harms := verifierInputBoundaryScript_armFrames_eq_arithmetic W input
  have hstart :=
    verifierInputBoundaryScript_finalOrStart_eq_arithmetic W input
  have hwires :=
    verifierInputBoundaryScript_finalOrWires_eq_arithmetic W input
  unfold verifierInputBoundaryArithmeticScript
  cases hscript : verifierInputBoundaryScript W input with
  | mk separatorSources armFrames finalOrStart finalOrWires =>
      simp only [hscript] at hseparator harms hstart hwires ⊢
      subst separatorSources
      subst armFrames
      subst finalOrStart
      subst finalOrWires
      rfl

/-- Consequently the arithmetic script produces the exact semantic
input-boundary gate bytes. -/
theorem verifierInputBoundaryArithmeticScript_gateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineVerifierInputShapeScriptGateStream
        (verifierInputBoundaryArithmeticScript W input) =
      verifierInputBoundaryGateStream W input := by
  rw [verifierInputBoundaryArithmeticScript_eq]
  exact verifierInputBoundaryScript_gateStream_eq W input

end CLRS.Chapter34.Turing.CookLevin
