import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.Canonicality
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.MaskCertificate.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Fixed syntax checks for SUBSET-SUM instances and mask certificates

The instance grammar contains at least the target field.  A mask certificate
contains zero or more raw Boolean symbols.  Both checks are implemented by
the same finite state space and emit one Boolean.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumVerifier.Syntax

open PolyBuilder

inductive Mode
  | instanceStart
  | instanceNeedField
  | instanceBetween
  | fieldEmpty
  | fieldSingleZero
  | fieldPositive
  | maskStart
  | maskBody
  | ended
  | invalid
deriving DecidableEq, Fintype

def nextMode : Mode → SubsetSumSym → Mode
  | .instanceStart, .instanceMark => .instanceNeedField
  | .instanceNeedField, .numberMark => .fieldEmpty
  | .instanceBetween, .numberMark => .fieldEmpty
  | .instanceBetween, .recordEnd => .ended
  | .fieldEmpty, .bit false => .fieldSingleZero
  | .fieldEmpty, .bit true => .fieldPositive
  | .fieldSingleZero, .fieldEnd => .instanceBetween
  | .fieldPositive, .bit _ => .fieldPositive
  | .fieldPositive, .fieldEnd => .instanceBetween
  | .maskStart, .certificateMark => .maskBody
  | .maskBody, .bit _ => .maskBody
  | .maskBody, .recordEnd => .ended
  | _, _ => .invalid

def modeAccepts : Mode → Bool
  | .ended => true
  | _ => false

def spec (initial : Mode) :
    StatefulFlatMapSpec Mode SubsetSumSym Bool where
  initial := initial
  action mode symbol := ([], nextMode mode symbol)
  finish mode := [modeAccepts mode]

def finalMode (mode : Mode) (input : List SubsetSumSym) : Mode :=
  input.foldl nextMode mode

private theorem rewriteFrom_eq (initial mode : Mode)
    (input : List SubsetSumSym) :
    rewriteStatefulFlatMapFrom (spec initial) mode input =
      [modeAccepts (finalMode mode input)] := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [spec, finalMode] using ih (nextMode mode symbol)

def instanceSyntax (input : List SubsetSumSym) : Bool :=
  (rewriteStatefulFlatMap (spec .instanceStart) input).headD false

def maskSyntax (input : List SubsetSumSym) : Bool :=
  (rewriteStatefulFlatMap (spec .maskStart) input).headD false

theorem instanceSyntax_eq (input : List SubsetSumSym) :
    instanceSyntax input =
      modeAccepts (finalMode .instanceStart input) := by
  unfold instanceSyntax rewriteStatefulFlatMap
  rw [rewriteFrom_eq]
  rfl

theorem maskSyntax_eq (input : List SubsetSumSym) :
    maskSyntax input = modeAccepts (finalMode .maskStart input) := by
  unfold maskSyntax rewriteStatefulFlatMap
  rw [rewriteFrom_eq]
  rfl

private theorem rewrite_instance_eq (input : List SubsetSumSym) :
    rewriteStatefulFlatMap (spec .instanceStart) input =
      [instanceSyntax input] := by
  unfold instanceSyntax rewriteStatefulFlatMap
  rw [rewriteFrom_eq]
  rfl

private theorem rewrite_mask_eq (input : List SubsetSumSym) :
    rewriteStatefulFlatMap (spec .maskStart) input = [maskSyntax input] := by
  unfold maskSyntax rewriteStatefulFlatMap
  rw [rewriteFrom_eq]
  rfl

noncomputable def instanceComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      _root_.Turing.TM2Comp.boolEncoding instanceSyntax := by
  have machine := statefulFlatMap_computableInPolyTime (spec .instanceStart)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [rewrite_instance_eq] at output
        exact output }

noncomputable def maskComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      _root_.Turing.TM2Comp.boolEncoding maskSyntax := by
  have machine := statefulFlatMap_computableInPolyTime (spec .maskStart)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [rewrite_mask_eq] at output
        exact output }

end CLRS.Chapter34.Turing.SubsetSumVerifier.Syntax
