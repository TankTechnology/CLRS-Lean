import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowMark

/-!
# Marked widened-fallback descriptors from the raw verifier word

This is the concrete source boundary needed by descriptor-local stack-route
passes: the already verified raw-input affine source is followed by the fixed
seven-field row marker.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Every runtime widened-fallback progression descriptor, now with an outer
row marker suitable for descriptor-local streaming rewrites. -/
noncomputable def verifierTransitionWidenedFallbackMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  markAffineUnaryTripleProgressionRows
    (verifierTransitionWidenedFallbackDescriptorFrames W input)

/-- Exact marked descriptor semantics over every transition-row seed. -/
theorem verifierTransitionWidenedFallbackMarkedDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionWidenedFallbackMarkedDescriptorFrames W input =
      encodeAffineUnaryTripleProgressionMarkedFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionWidenedFallbackProgressions W.machine.tm)) := by
  unfold verifierTransitionWidenedFallbackMarkedDescriptorFrames
  rw [verifierTransitionWidenedFallbackDescriptorFrames_eq]
  exact markAffineUnaryTripleProgressionRows_encode _

/-- One fixed polynomial-time TM2 emits the marked descriptor family directly
from the original verifier input. -/
noncomputable def
    verifierTransitionWidenedFallbackMarkedDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionWidenedFallbackMarkedDescriptorFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionWidenedFallbackDescriptorFrames_computableInPolyTime W)
      markAffineUnaryTripleProgressionRows_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionWidenedFallbackMarkedDescriptorFrames] using run }

end CLRS.Chapter34.Turing.CookLevin
