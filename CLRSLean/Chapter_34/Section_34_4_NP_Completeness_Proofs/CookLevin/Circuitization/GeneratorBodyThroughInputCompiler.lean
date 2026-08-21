import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBodyTransitionPrefixCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInitialBoundaryAlignment
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryCompleteSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBody
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# Raw-input compiler through the verifier input boundary

This module joins the already verified validity, transition, initial-boundary,
and input-boundary sources.  The result is one fixed polynomial-time source
for the exact prefix of the continuous verifier-body script through the input
shape phase.  Only the accepting boundary, final conjunction, and output wire
remain after this prefix.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A constant one-symbol unary stream, used for controller phase markers. -/
def constantUnarySingleton {Γ : Type} (symbol : UnaryFrameSym)
    (_input : List Γ) : List UnaryFrameSym :=
  [symbol]

/-- Every fixed unary phase marker has a concrete polynomial-time source. -/
noncomputable def constantUnarySingleton_computableInPolyTime
    {Γ : Type} [Fintype Γ] (symbol : UnaryFrameSym) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (constantUnarySingleton (Γ := Γ) symbol) := by
  let zeroFrame :=
    exactPolynomialAffineUnaryProgressionFrameStream_computableInPolyTime
      (Γ := Γ) (Polynomial.C 0) (Polynomial.C 0) (Polynomial.C 1)
  let delimitedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch zeroFrame
      (unaryFrameDelimiterMap_computableInPolyTime [symbol] (by simp))
  let delimited := Classical.choice delimitedExists
  exact
    { tm := delimited.tm
      inputAlphabet := delimited.inputAlphabet
      outputAlphabet := delimited.outputAlphabet
      time := delimited.time
      outputsFun := fun input => by
        have run := delimited.outputsFun input
        simpa [Function.comp_def, constantUnarySingleton,
          exactPolynomialAffineUnaryProgressionFrameStream,
          exactPolynomialAffineUnaryProgression,
          affineUnaryProgressionFrameStream,
          affineUnaryProgressionValues,
          affineUnaryProgressionValuesFrom,
          encodeUnaryFrame, encodeUnaryFrameBlock,
          rewriteUnaryFrameDelimiters,
          rewriteUnaryFrameDelimitersFrom,
          unaryFrameDelimiterStep] using run }

/-- Literal unary body-script prefix through completion of the verifier input
shape.  Parentheses record the same append tree used by the concrete source. -/
def verifierBodyThroughInputUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierBodyTransitionPrefixUnaryTarget W input ++
    .separator ::
      (verifierInitialBoundaryInputTarget W input ++
        .separator ::
          (verifierInputBoundaryInputTarget W input ++ [.tick]))

/-- The assembled source is the canonical body encoding through the input
shape phase, byte for byte. -/
theorem verifierBodyThroughInputUnaryTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierBodyThroughInputUnaryTarget W input =
      (((encodeAffineValidityRowFamilyInput
            (verifierValidityRowFramesByLength W input.length) ++
          encodeAffineTransitionFamilyUnary
            (verifierTransitionFamilyScripts W input) ++ [.separator]) ++
        encodeAffineEqFinFrames
          (compileVerifierInitialBoundaryFrames W input)) ++ [.separator]) ++
      encodeAffineInputShapeScript
          (verifierInputBoundaryScript W input) ++ [.tick] := by
  unfold verifierBodyThroughInputUnaryTarget
  rw [verifierBodyTransitionPrefixUnaryTarget_eq_canonical,
    verifierInitialBoundaryInputTarget_eq_canonical,
    verifierInputBoundaryInputTarget_eq_canonical]
  simp only [encodeAffineVerifierInputShapeScript]
  simp [List.append_assoc]

/-- The full canonical unary body script is this compiled prefix followed by
exactly the three still-uncompiled tail fields. -/
theorem encodeAffineVerifierBodyUnary_eq_throughInput_append
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineVerifierBodyUnary (compileVerifierBodyScript W input) =
      verifierBodyThroughInputUnaryTarget W input ++
        encodeAffineVerifierTailAccepting
          (compileVerifierAcceptingBoundaryFrames W input) ++
        encodeAffineConjunctionFrame
          (verifierFinalConjunctionFrame W input) ++
        encodeUnaryFrameBlock (verifierCircuit W input).output := by
  rw [verifierBodyThroughInputUnaryTarget_eq_canonical]
  unfold encodeAffineVerifierBodyUnary compileVerifierBodyScript
    compileVerifierTailScript encodeAffineVerifierTailScript
  rw [← verifierTransitionFamilyScripts_eq_canonical]
  simp [List.append_assoc]

/-- A single fixed polynomial-time TM2 emits the complete unary body prefix
from the original verifier word. -/
noncomputable def
    verifierBodyThroughInputUnaryTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyThroughInputUnaryTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let transitionPrefix :=
    verifierBodyTransitionPrefixUnaryTarget_computableInPolyTime W
  let separator :=
    constantUnarySingleton_computableInPolyTime (Γ := Γ) .separator
  let throughTransition := unaryFrameSameInputConcat_computableInPolyTime
    transitionPrefix separator
  let initial := verifierInitialBoundaryInputTarget_computableInPolyTime W
  let throughInitial := unaryFrameSameInputConcat_computableInPolyTime
    throughTransition initial
  let throughInitialSeparator :=
    unaryFrameSameInputConcat_computableInPolyTime throughInitial separator
  let inputShape := verifierInputBoundaryInputTarget_computableInPolyTime W
  let throughInput := unaryFrameSameInputConcat_computableInPolyTime
    throughInitialSeparator inputShape
  let tick := constantUnarySingleton_computableInPolyTime (Γ := Γ) .tick
  let complete := unaryFrameSameInputConcat_computableInPolyTime
    throughInput tick
  exact
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := fun input => by
        have run := complete.outputsFun input
        simpa [verifierBodyThroughInputUnaryTarget,
          constantUnarySingleton, List.append_assoc] using run }

/-- Common-alphabet version of the verified unary prefix, ready for the
continuous verifier-body controller. -/
def verifierBodyThroughInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineStmtScriptSym :=
  (verifierBodyThroughInputUnaryTarget W input).map .data

/-- The typed complete body script has the generated typed prefix literally
at its front. -/
theorem encodeAffineVerifierBodyScript_eq_throughInput_append
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineVerifierBodyScript (compileVerifierBodyScript W input) =
      verifierBodyThroughInputTarget W input ++
        (encodeAffineVerifierTailAccepting
            (compileVerifierAcceptingBoundaryFrames W input) ++
          encodeAffineConjunctionFrame
            (verifierFinalConjunctionFrame W input) ++
          encodeUnaryFrameBlock (verifierCircuit W input).output).map .data := by
  unfold encodeAffineVerifierBodyScript verifierBodyThroughInputTarget
  rw [encodeAffineVerifierBodyUnary_eq_throughInput_append]
  simp only [List.map_append]
  simp [List.append_assoc]

/-- The common-alphabet body prefix is itself produced by one fixed
polynomial-time TM2. -/
noncomputable def verifierBodyThroughInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyThroughInputTarget W) := by
  let unary :=
    verifierBodyThroughInputUnaryTarget_computableInPolyTime W
  let mappedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch unary
      (listMap_computableInPolyTime AffineStmtScriptSym.data)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (verifierBodyThroughInputUnaryTarget W input).map
        AffineStmtScriptSym.data)
  simpa only [Function.comp_def] using Classical.choice mappedExists

end CLRS.Chapter34.Turing.CookLevin
