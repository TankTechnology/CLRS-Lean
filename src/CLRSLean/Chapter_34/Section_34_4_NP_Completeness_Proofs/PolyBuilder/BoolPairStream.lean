import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time

/-!
# Reusable same-input Boolean pair streams

Given two fixed polynomial-time Boolean-list transducers over the same input,
this module constructs their standard option-separated `pairEncoding`.  It is
the plumbing needed to feed independent compact computations to the generic
list-equality, addition, and comparison machines.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.BoolPairStream

open CLRS.Chapter34.Turing.PolyBuilder

def leftPart (bits : List Bool) : List (Option Bool) := bits.map some

def rightPart (bits : List Bool) : List (Option Bool) :=
  none :: bits.map some

private def rightSpec : StatefulFlatMapSpec Bool Bool (Option Bool) where
  initial := false
  action started bit :=
    if started then ([some bit], true) else ([none, some bit], true)
  finish started := if started then [] else [none]

private theorem rightStarted (bits : List Bool) :
    rewriteStatefulFlatMapFrom rightSpec true bits = bits.map some := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [rightSpec] using congrArg (some bit :: ·) ih

theorem rightRewrite (bits : List Bool) :
    rewriteStatefulFlatMap rightSpec bits = rightPart bits := by
  cases bits with
  | nil => rfl
  | cons bit bits =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom.eq_def]
      simpa [rightSpec, rightPart] using
        congrArg (fun tail => none :: some bit :: tail) (rightStarted bits)

def encodeOptionBoolPair : Option Bool → UnaryFrameSym × UnaryFrameSym
  | none => (.tick, .tick)
  | some false => (.tick, .separator)
  | some true => (.separator, .tick)

def decodeOptionBoolPair :
    UnaryFrameSym → UnaryFrameSym → Option Bool
  | .tick, .tick => none
  | .tick, .separator => some false
  | .separator, .tick => some true
  | _, _ => none

@[simp] theorem decode_encodeOptionBoolPair (symbol : Option Bool) :
    decodeOptionBoolPair (encodeOptionBoolPair symbol).1
      (encodeOptionBoolPair symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some bit => cases bit <;> rfl

noncomputable def leftPartComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id leftPart :=
  listMap_computableInPolyTime some

noncomputable def rightPartComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id rightPart := by
  have machine := statefulFlatMap_computableInPolyTime rightSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun bits => by
        have output := machine.outputsFun bits
        rw [rightRewrite] at output
        exact output }

/-- Build `pairEncoding (left input) (right input)` from two computations over
the same encoded input. -/
noncomputable def computableInPolyTime
    {α Γ : Type} [Fintype Γ]
    {inputEncoding : α → List Γ}
    {left right : α → List Bool}
    (leftMachine : _root_.Turing.TM2ComputableInPolyTime
      inputEncoding id left)
    (rightMachine : _root_.Turing.TM2ComputableInPolyTime
      inputEncoding id right) :
    _root_.Turing.TM2ComputableInPolyTime inputEncoding
      (fun pair : List Bool × List Bool =>
        CLRS.Chapter34.pairEncoding pair.1 pair.2)
      (fun input => (left input, right input)) := by
  let leftExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      leftMachine leftPartComputableInPolyTime
  let rightExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      rightMachine rightPartComputableInPolyTime
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeOptionBoolPair decodeOptionBoolPair decode_encodeOptionBoolPair
    (Classical.choice leftExists) (Classical.choice rightExists)
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        simpa [CLRS.Chapter34.pairEncoding, leftPart, rightPart,
          Function.comp_def] using
          output }

end CLRS.Chapter34.Turing.PolyBuilder.BoolPairStream
