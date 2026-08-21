import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConstraintSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBodyThroughAcceptingCompiler

/-!
# Complete raw-input compiler for the final conjunction frame

The frame start is the accepting-boundary endpoint, its sources are the
verified tail-first constraint stream, and one final marker closes the frame.
Joining this field to the previous body compiler leaves only the circuit
output-wire block.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Complete unary runtime input for the final verifier conjunction. -/
def verifierFinalConjunctionInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierAcceptingBoundaryEndFrame W input ++
    verifierConstraintOutputReversedSource W input ++ [.frameEnd]

/-- The generated target is exactly the semantic conjunction-frame encoding. -/
theorem verifierFinalConjunctionInputTarget_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierFinalConjunctionInputTarget W input =
      encodeAffineConjunctionFrame
        (verifierFinalConjunctionFrame W input) := by
  unfold verifierFinalConjunctionInputTarget
    verifierFinalConjunctionFrame encodeAffineConjunctionFrame
  rw [verifierAcceptingBoundaryEndFrame_eq,
    verifierAcceptingBoundary_gates_length_eq_end,
    verifierConstraintOutputReversedSource_eq]
  simp [encodeUnaryFrame, List.append_assoc]

/-- One fixed polynomial-time TM2 emits the complete final-conjunction field. -/
noncomputable def verifierFinalConjunctionInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierFinalConjunctionInputTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let start := verifierAcceptingBoundaryEndFrame_computableInPolyTime W
  let wires := verifierConstraintOutputReversedSource_computableInPolyTime W
  let prefix := unaryFrameSameInputConcat_computableInPolyTime start wires
  let boundary := constantUnarySingleton_computableInPolyTime
    (Γ := Γ) .frameEnd
  let complete := unaryFrameSameInputConcat_computableInPolyTime
    prefix boundary
  simpa [verifierFinalConjunctionInputTarget,
    constantUnarySingleton, List.append_assoc] using complete

/-- Complete unary verifier body through the final conjunction field. -/
def verifierBodyThroughConjunctionUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierBodyThroughAcceptingUnaryTarget W input ++
    verifierFinalConjunctionInputTarget W input

/-- After this compiler only the circuit output-wire block remains. -/
theorem encodeAffineVerifierBodyUnary_eq_throughConjunction_append
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineVerifierBodyUnary (compileVerifierBodyScript W input) =
      verifierBodyThroughConjunctionUnaryTarget W input ++
        encodeUnaryFrameBlock (verifierCircuit W input).output := by
  rw [encodeAffineVerifierBodyUnary_eq_throughAccepting_append]
  rw [← verifierFinalConjunctionInputTarget_eq]
  simp [verifierBodyThroughConjunctionUnaryTarget, List.append_assoc]

/-- A fixed polynomial-time TM2 emits the unary body through conjunction. -/
noncomputable def
    verifierBodyThroughConjunctionUnaryTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyThroughConjunctionUnaryTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let prefix :=
    verifierBodyThroughAcceptingUnaryTarget_computableInPolyTime W
  let conjunction :=
    verifierFinalConjunctionInputTarget_computableInPolyTime W
  let complete := unaryFrameSameInputConcat_computableInPolyTime
    prefix conjunction
  simpa [verifierBodyThroughConjunctionUnaryTarget] using complete

/-- Common-alphabet body target through final conjunction. -/
def verifierBodyThroughConjunctionTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineStmtScriptSym :=
  (verifierBodyThroughConjunctionUnaryTarget W input).map .data

/-- The typed body encoding now differs only by its final output-wire field. -/
theorem encodeAffineVerifierBodyScript_eq_throughConjunction_append
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineVerifierBodyScript (compileVerifierBodyScript W input) =
      verifierBodyThroughConjunctionTarget W input ++
        (encodeUnaryFrameBlock (verifierCircuit W input).output).map .data := by
  unfold encodeAffineVerifierBodyScript verifierBodyThroughConjunctionTarget
  rw [encodeAffineVerifierBodyUnary_eq_throughConjunction_append]
  simp only [List.map_append]

/-- The common-alphabet conjunction-complete body is polynomial-time
computable from the original input. -/
noncomputable def verifierBodyThroughConjunctionTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyThroughConjunctionTarget W) := by
  let unary :=
    verifierBodyThroughConjunctionUnaryTarget_computableInPolyTime W
  let mappedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch unary
      (listMap_computableInPolyTime AffineStmtScriptSym.data)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (verifierBodyThroughConjunctionUnaryTarget W input).map
        AffineStmtScriptSym.data)
  simpa only [Function.comp_def] using Classical.choice mappedExists

end CLRS.Chapter34.Turing.CookLevin
