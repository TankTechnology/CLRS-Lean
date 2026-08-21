import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryClosure
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBodyThroughInputCompiler

/-!
# Raw-input verifier-body compiler through the accepting boundary

The accepting operand is a static machine-level branch: an unrepresentable
accepting symbol emits the controller's `none` marker, while a representable
symbol emits the complete canonical equality family.  Joining it to the
existing body prefix leaves only the final conjunction and output wire.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Total raw-input target for the optional accepting operand, including its
leading option tag and trailing separator. -/
def verifierAcceptingOperandUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  if hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁ then
    .frameEnd :: verifierAcceptingBoundaryInputTarget W hmember input ++
      [.separator]
  else
    [.separator]

/-- The total raw-input target is byte-for-byte the optional accepting field
of the semantic verifier-tail script. -/
theorem verifierAcceptingOperandUnaryTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierAcceptingOperandUnaryTarget W input =
      encodeAffineVerifierTailAccepting
        (compileVerifierAcceptingBoundaryFrames W input) := by
  classical
  by_cases hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁
  · rw [compileVerifierAcceptingBoundaryFrames_eq_some_slotFrames
      W hmember input]
    simp [verifierAcceptingOperandUnaryTarget, hmember,
      encodeAffineVerifierTailAccepting,
      verifierAcceptingBoundaryInputTarget_eq_canonical,
      List.append_assoc]
  · rw [compileVerifierAcceptingBoundaryFrames_eq_none W hmember input]
    simp [verifierAcceptingOperandUnaryTarget, hmember,
      encodeAffineVerifierTailAccepting]

/-- A single fixed polynomial-time TM2 emits the total semantic accepting
operand directly from the original verifier word. -/
noncomputable def verifierAcceptingOperandUnaryTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingOperandUnaryTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  by_cases hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁
  · let frameEnd :=
      constantUnarySingleton_computableInPolyTime (Γ := Γ) .frameEnd
    let boundary :=
      verifierAcceptingBoundaryInputTarget_computableInPolyTime W hmember
    let tagged := unaryFrameSameInputConcat_computableInPolyTime
      frameEnd boundary
    let separator :=
      constantUnarySingleton_computableInPolyTime (Γ := Γ) .separator
    let complete := unaryFrameSameInputConcat_computableInPolyTime
      tagged separator
    exact
      { tm := complete.tm
        inputAlphabet := complete.inputAlphabet
        outputAlphabet := complete.outputAlphabet
        time := complete.time
        outputsFun := fun input => by
          have run := complete.outputsFun input
          simpa [verifierAcceptingOperandUnaryTarget, hmember,
            constantUnarySingleton, List.append_assoc] using run }
  · let separator :=
      constantUnarySingleton_computableInPolyTime (Γ := Γ) .separator
    exact
      { tm := separator.tm
        inputAlphabet := separator.inputAlphabet
        outputAlphabet := separator.outputAlphabet
        time := separator.time
        outputsFun := fun input => by
          have run := separator.outputsFun input
          simpa [verifierAcceptingOperandUnaryTarget, hmember,
            constantUnarySingleton] using run }

/-- Complete raw-input unary verifier-body prefix through the optional
accepting boundary. -/
def verifierBodyThroughAcceptingUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierBodyThroughInputUnaryTarget W input ++
    verifierAcceptingOperandUnaryTarget W input

/-- The semantic unary body is the compiled prefix through accepting followed
by exactly the final conjunction and output-wire fields. -/
theorem encodeAffineVerifierBodyUnary_eq_throughAccepting_append
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineVerifierBodyUnary (compileVerifierBodyScript W input) =
      verifierBodyThroughAcceptingUnaryTarget W input ++
        encodeAffineConjunctionFrame
          (verifierFinalConjunctionFrame W input) ++
        encodeUnaryFrameBlock (verifierCircuit W input).output := by
  rw [encodeAffineVerifierBodyUnary_eq_throughInput_append]
  rw [← verifierAcceptingOperandUnaryTarget_eq_canonical]
  simp [verifierBodyThroughAcceptingUnaryTarget, List.append_assoc]

/-- A fixed polynomial-time TM2 emits the unary verifier body through its
accepting-boundary phase. -/
noncomputable def verifierBodyThroughAcceptingUnaryTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyThroughAcceptingUnaryTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let prefixSource :=
    verifierBodyThroughInputUnaryTarget_computableInPolyTime W
  let acceptingSource :=
    verifierAcceptingOperandUnaryTarget_computableInPolyTime W
  let complete := unaryFrameSameInputConcat_computableInPolyTime
    prefixSource acceptingSource
  exact
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := fun input => by
        have run := complete.outputsFun input
        simpa [verifierBodyThroughAcceptingUnaryTarget] using run }

/-- Common-alphabet version of the prefix through accepting, ready for the
continuous body controller. -/
def verifierBodyThroughAcceptingTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineStmtScriptSym :=
  (verifierBodyThroughAcceptingUnaryTarget W input).map .data

/-- The typed body encoding has the generated accepting-complete target as
an exact prefix. -/
theorem encodeAffineVerifierBodyScript_eq_throughAccepting_append
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineVerifierBodyScript (compileVerifierBodyScript W input) =
      verifierBodyThroughAcceptingTarget W input ++
        (encodeAffineConjunctionFrame
            (verifierFinalConjunctionFrame W input) ++
          encodeUnaryFrameBlock (verifierCircuit W input).output).map .data := by
  unfold encodeAffineVerifierBodyScript verifierBodyThroughAcceptingTarget
  rw [encodeAffineVerifierBodyUnary_eq_throughAccepting_append]
  simp only [List.map_append]
  simp [List.append_assoc]

/-- The common-alphabet prefix through accepting is polynomial-time
computable from the original input. -/
noncomputable def verifierBodyThroughAcceptingTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyThroughAcceptingTarget W) := by
  let unary :=
    verifierBodyThroughAcceptingUnaryTarget_computableInPolyTime W
  let mappedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch unary
      (listMap_computableInPolyTime AffineStmtScriptSym.data)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (verifierBodyThroughAcceptingUnaryTarget W input).map
        AffineStmtScriptSym.data)
  simpa only [Function.comp_def] using Classical.choice mappedExists

end CLRS.Chapter34.Turing.CookLevin
