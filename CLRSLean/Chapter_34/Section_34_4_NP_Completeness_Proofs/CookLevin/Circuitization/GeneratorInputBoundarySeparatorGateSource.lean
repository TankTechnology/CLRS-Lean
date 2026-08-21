import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundarySeparatorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NotFamilyRuntime

/-!
# Concrete separator-NOT gate source for the verifier input boundary

This module closes the gap between the raw-input arithmetic source and the
literal serialized circuit gates consumed by the input-boundary phase.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Literal circuit-byte stream of the input-stack separator NOT gates. -/
def verifierInputSeparatorGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List CircuitSym :=
  affineNotFamilyGateStream (verifierInputSeparatorSources W input)

/-- The arithmetic stream is exactly the separator phase of the canonical
semantic input-boundary script. -/
theorem verifierInputSeparatorGateStream_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputSeparatorGateStream W input =
      affineNotFamilyGateStream
        (verifierInputBoundaryScript W input).separatorSources := by
  unfold verifierInputSeparatorGateStream
  rfl

/-- End-to-end fixed polynomial-time TM2 from the raw verifier word to every
serialized separator NOT gate. -/
noncomputable def verifierInputSeparatorGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputSeparatorGateStream W) := by
  letI : Fintype Γ := W.alphabetFintype
  let source : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineNotFamilySources
      (verifierInputSeparatorSources W) := by
    let raw := verifierInputSeparatorInputTarget_computableInPolyTime W
    exact
      { tm := raw.tm
        inputAlphabet := raw.inputAlphabet
        outputAlphabet := raw.outputAlphabet
        time := raw.time
        outputsFun := fun input => by
          have run := raw.outputsFun input
          rw [verifierInputSeparatorInputTarget_eq_canonical W input] at run
          simpa only [id_eq] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      affineNotFamilyGateStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def, id_eq,
          verifierInputSeparatorGateStream] using run }

end CLRS.Chapter34.Turing.CookLevin
