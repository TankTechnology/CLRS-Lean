import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundarySeparatorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmOptionalSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFinalOrGateSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialAffineUnaryProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputShapeRuntime

/-!
# Complete concrete verifier-input boundary source

All runtime operands are compiled from the original verifier word, assembled
into the exact `AffineInputShapeScript` encoding, and executed by the existing
continuous fixed controller.  The resulting theorem is the end-to-end
polynomial-time source for the complete input-boundary circuit bytes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The explicit phase boundary following the separator NOT operands. -/
def verifierInputBoundarySeparatorTerminator
    {Γ : Type} (_input : List Γ) : List UnaryFrameSym :=
  [.frameEnd]

/-- A fixed polynomial-time source for the one-symbol phase boundary.  It is
obtained from a one-element zero progression and the verified delimiter map,
so the input is consumed by an ordinary total TM2. -/
noncomputable def
    verifierInputBoundarySeparatorTerminator_computableInPolyTime
    {Γ : Type} [Fintype Γ] :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@verifierInputBoundarySeparatorTerminator Γ) := by
  let zeroFrame :=
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (Γ := Γ) (Polynomial.C 0) (Polynomial.C 0) (Polynomial.C 1)
  let delimitedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch zeroFrame
      (unaryFrameDelimiterMap_computableInPolyTime [.frameEnd] (by simp))
  let delimited := Classical.choice delimitedExists
  exact
    { tm := delimited.tm
      inputAlphabet := delimited.inputAlphabet
      outputAlphabet := delimited.outputAlphabet
      time := delimited.time
      outputsFun := fun input => by
        have run := delimited.outputsFun input
        simpa [Function.comp_def,
          verifierInputBoundarySeparatorTerminator,
          exactPolynomialAffineUnaryProgressionFrameStream,
          exactPolynomialAffineUnaryProgression,
          affineUnaryProgressionFrameStream,
          affineUnaryProgressionValues,
          affineUnaryProgressionValuesFrom,
          encodeUnaryFrame, encodeUnaryFrameBlock,
          rewriteUnaryFrameDelimiters,
          rewriteUnaryFrameDelimitersFrom,
          unaryFrameDelimiterStep] using run }

/-- Builder-free complete input accepted by the continuous input-shape
controller. -/
def verifierInputBoundaryInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierInputSeparatorInputTarget W input ++
    verifierInputBoundarySeparatorTerminator input ++
    verifierInputArmOptionalInputTarget W input ++
    verifierInputFinalOrFrameInput W input

/-- The assembled byte stream is exactly the canonical semantic script
encoding, not merely an extensionally equivalent list of phases. -/
theorem verifierInputBoundaryInputTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputBoundaryInputTarget W input =
      encodeAffineVerifierInputShapeScript
        (verifierInputBoundaryScript W input) := by
  unfold verifierInputBoundaryInputTarget
    verifierInputBoundarySeparatorTerminator
    encodeAffineVerifierInputShapeScript
    encodeAffineInputShapeScript
    affineInputShapeFinalOrFrames
  rw [verifierInputSeparatorInputTarget_eq_canonical]
  rw [verifierInputArmOptionalInputTarget_eq]
  unfold verifierInputArmOptionalFrames
  rw [verifierInputFinalOrFrameInput_eq_canonical]
  rw [← verifierInputBoundaryScript_armFrames_eq_arithmetic]
  rw [← verifierInputBoundaryScript_finalOrStart_eq_arithmetic]
  rw [← verifierInputBoundaryScript_finalOrWires_eq_arithmetic]
  rfl

/-- One fixed polynomial-time TM2 emits the complete continuous-controller
input directly from the original verifier word. -/
noncomputable def verifierInputBoundaryInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputBoundaryInputTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let separator := verifierInputSeparatorInputTarget_computableInPolyTime W
  let terminator :=
    verifierInputBoundarySeparatorTerminator_computableInPolyTime (Γ := Γ)
  let separatorBlock :=
    unaryFrameSameInputConcat_computableInPolyTime separator terminator
  let arms := verifierInputArmOptionalInputTarget_computableInPolyTime W
  let throughArms :=
    unaryFrameSameInputConcat_computableInPolyTime separatorBlock arms
  let finalOr := verifierInputFinalOrFrameInput_computableInPolyTime W
  let complete :=
    unaryFrameSameInputConcat_computableInPolyTime throughArms finalOr
  exact
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := fun input => by
        have run := complete.outputsFun input
        simpa [verifierInputBoundaryInputTarget,
          List.append_assoc] using run }

/-- End-to-end Cook--Levin input-boundary closure: a fixed polynomial-time
TM2 maps the original verifier word to the exact canonical circuit gate
serialization of all three input-boundary phases. -/
noncomputable def verifierInputBoundaryGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputBoundaryGateStream W) := by
  letI : Fintype Γ := W.alphabetFintype
  let raw := verifierInputBoundaryInputTarget_computableInPolyTime W
  let source : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineInputShapeScript
      (verifierInputBoundaryScript W) :=
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        rw [verifierInputBoundaryInputTarget_eq_canonical W input] at run
        simpa only [id_eq, encodeAffineVerifierInputShapeScript] using run }
  let executedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      affineInputShapeGateStream_computableInPolyTime
  let executed := Classical.choice executedExists
  exact
    { tm := executed.tm
      inputAlphabet := executed.inputAlphabet
      outputAlphabet := executed.outputAlphabet
      time := executed.time
      outputsFun := fun input => by
        have run := executed.outputsFun input
        simp only [Function.comp_def, id_eq] at run
        have hsemantic := verifierInputBoundaryScript_gateStream_eq W input
        change affineInputShapeGateStream
            (verifierInputBoundaryScript W input) =
          verifierInputBoundaryGateStream W input at hsemantic
        rw [hsemantic] at run
        simpa only [id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin
