import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.TargetField
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputConcat

/-!
# Runtime affine source for SUBSET-SUM slack items

For clause `j`, a slack item has canonical binary payload
`1 · 0^(blockWidth * (variableCount + j))`.  The zero counts therefore form
one runtime affine progression.  This file generates its three unary
parameters from arbitrary raw CNF input with fixed polynomial-time machines.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

inductive SlackProductSourceSym
  | block | variable
deriving DecidableEq, Fintype, Repr

def slackBlockTags (input : List CNFSym) : List SlackProductSourceSym :=
  (reductionBlockWidthTicks input).map fun _ => .block

def slackVariableTags (input : List CNFSym) : List SlackProductSourceSym :=
  (variableBudgetTicks input).map fun _ => .variable

def slackProductSource (input : List CNFSym) : List SlackProductSourceSym :=
  slackBlockTags input ++ slackVariableTags input

def slackProductBody :
    LoopBody (SlackProductSourceSym × SlackProductSourceSym) Unit where
  emit
    | (.block, .variable) => [()]
    | _ => []
  cost _ := 1
  emit_length_le_cost pair := by
    rcases pair with ⟨left, right⟩
    cases left <;> cases right <;> simp

/-- Unary clock of length `blockWidth * variableCount`. -/
def slackBaseProductTicks (input : List CNFSym) : List Unit :=
  nestedLoopOutput slackProductBody (slackProductSource input)

private theorem flatMap_replicate_singleton {α β : Type}
    (count : Nat) (value : α) (output : β) :
    (List.replicate count value).flatMap (fun _ => [output]) =
      List.replicate count output := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private theorem flatMap_replicate_nil {α β : Type}
    (count : Nat) (value : α) :
    (List.replicate count value).flatMap (fun _ => ([] : List β)) = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private theorem flatMap_replicate_eq_flatten {α β : Type}
    (count : Nat) (value : α) (f : α → List β) :
    (List.replicate count value).flatMap f =
      (List.replicate count (f value)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private theorem flatten_replicate_nil {α : Type} (count : Nat) :
    (List.replicate count ([] : List α)).flatten = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private theorem flatten_replicate_singleton {α : Type}
    (count : Nat) (value : α) :
    (List.replicate count [value]).flatten = List.replicate count value := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private theorem flatten_replicate_replicate {α : Type}
    (outer inner : Nat) (value : α) :
    (List.replicate outer (List.replicate inner value)).flatten =
      List.replicate (outer * inner) value := by
  induction outer with
  | zero => simp
  | succ outer ih =>
      rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul,
        Nat.add_comm, List.replicate_add]

theorem slackBaseProductTicks_eq (input : List CNFSym) :
    slackBaseProductTicks input =
      List.replicate
        (reductionBlockWidth (decodeCNF input) *
          reductionVariableCount (decodeCNF input)) () := by
  rw [slackBaseProductTicks, slackProductSource, slackBlockTags,
    slackVariableTags, reductionBlockWidthTicks_eq, variableBudgetTicks_eq]
  simp only [List.map_replicate]
  change
    (List.replicate (reductionBlockWidth (decodeCNF input))
        SlackProductSourceSym.block ++
      List.replicate (reductionVariableCount (decodeCNF input))
        SlackProductSourceSym.variable).flatMap (fun outer =>
      (List.replicate (reductionBlockWidth (decodeCNF input))
          SlackProductSourceSym.block ++
        List.replicate (reductionVariableCount (decodeCNF input))
          SlackProductSourceSym.variable).flatMap (fun inner =>
        slackProductBody.emit (outer, inner))) = _
  let blockWidth := reductionBlockWidth (decodeCNF input)
  let variableCount := reductionVariableCount (decodeCNF input)
  have hblock :
      (List.replicate blockWidth SlackProductSourceSym.block ++
        List.replicate variableCount SlackProductSourceSym.variable).flatMap
          (fun inner => slackProductBody.emit (.block, inner)) =
        List.replicate variableCount () := by
    rw [List.flatMap_append, flatMap_replicate_eq_flatten,
      flatMap_replicate_eq_flatten]
    change (List.replicate blockWidth ([] : List Unit)).flatten ++
      (List.replicate variableCount [()]).flatten = _
    rw [flatten_replicate_nil, flatten_replicate_singleton,
      List.nil_append]
  have hvariable :
      (List.replicate blockWidth SlackProductSourceSym.block ++
        List.replicate variableCount SlackProductSourceSym.variable).flatMap
          (fun inner => slackProductBody.emit (.variable, inner)) = [] := by
    rw [List.flatMap_append]
    simp [slackProductBody, flatMap_replicate_nil]
  rw [List.flatMap_append, flatMap_replicate_eq_flatten,
    flatMap_replicate_eq_flatten, hblock, hvariable,
    flatten_replicate_nil, List.append_nil]
  rw [flatten_replicate_replicate]

noncomputable def slackBlockTags_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackBlockTags := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reductionBlockWidthTicks_computableInPolyTime
      (listMap_computableInPolyTime
        (fun _ : Unit => SlackProductSourceSym.block))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (reductionBlockWidthTicks input).map
      fun _ => SlackProductSourceSym.block)
  simpa only [Function.comp_def] using Classical.choice composed

noncomputable def slackVariableTags_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackVariableTags := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      variableBudgetTicks_computableInPolyTime
      (listMap_computableInPolyTime
        (fun _ : Unit => SlackProductSourceSym.variable))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (variableBudgetTicks input).map
      fun _ => SlackProductSourceSym.variable)
  simpa only [Function.comp_def] using Classical.choice composed

private def encodeSlackProductSourcePair :
    SlackProductSourceSym → UnaryFrameSym × UnaryFrameSym
  | .block => (.tick, .tick)
  | .variable => (.tick, .separator)

private def decodeSlackProductSourcePair :
    UnaryFrameSym → UnaryFrameSym → SlackProductSourceSym
  | .tick, .separator => .variable
  | _, _ => .block

private theorem decode_encodeSlackProductSourcePair
    (symbol : SlackProductSourceSym) :
    decodeSlackProductSourcePair (encodeSlackProductSourcePair symbol).1
      (encodeSlackProductSourcePair symbol).2 = symbol := by
  cases symbol <;> rfl

noncomputable def slackProductSource_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackProductSource :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeSlackProductSourcePair decodeSlackProductSourcePair
    decode_encodeSlackProductSourcePair
    slackBlockTags_computableInPolyTime
    slackVariableTags_computableInPolyTime

noncomputable def slackBaseProductTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackBaseProductTicks := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      slackProductSource_computableInPolyTime
      (nestedLoop_computableInPolyTime slackProductBody)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => nestedLoopOutput slackProductBody (slackProductSource input))
  simpa only [Function.comp_def] using Classical.choice composed

/-- Turn one unary clock into one ordinary delimiter-bearing frame. -/
def unaryClockFrameSpec : StatefulFlatMapSpec Unit Unit UnaryFrameSym where
  initial := ()
  action _ _ := ([.tick], ())
  finish _ := [.separator]

def unaryClockFrame (ticks : List Unit) : List UnaryFrameSym :=
  rewriteStatefulFlatMap unaryClockFrameSpec ticks

private theorem unaryClockFrameFrom_eq (ticks : List Unit) :
    rewriteStatefulFlatMapFrom unaryClockFrameSpec () ticks =
      List.replicate ticks.length .tick ++ [.separator] := by
  induction ticks with
  | nil => rfl
  | cons _ ticks ih =>
      rw [rewriteStatefulFlatMapFrom]
      change .tick :: rewriteStatefulFlatMapFrom unaryClockFrameSpec () ticks =
        List.replicate (ticks.length + 1) .tick ++ [.separator]
      rw [ih]
      simp [List.replicate_succ]

theorem unaryClockFrame_eq (ticks : List Unit) :
    unaryClockFrame ticks = encodeUnaryFrame [ticks.length] := by
  rw [unaryClockFrame, rewriteStatefulFlatMap, unaryClockFrameFrom_eq]
  simp [encodeUnaryFrame, encodeUnaryFrameBlock]

noncomputable def unaryClockFrame_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id unaryClockFrame :=
  statefulFlatMap_computableInPolyTime unaryClockFrameSpec

def slackBaseFrame (input : List CNFSym) : List UnaryFrameSym :=
  unaryClockFrame (slackBaseProductTicks input)

def slackStepFrame (input : List CNFSym) : List UnaryFrameSym :=
  unaryClockFrame (reductionBlockWidthTicks input)

def slackCountFrame (input : List CNFSym) : List UnaryFrameSym :=
  unaryClockFrame (clauseCountTicks input)

def slackProgression (input : List CNFSym) : AffineUnaryProgression where
  base := reductionBlockWidth (decodeCNF input) *
    reductionVariableCount (decodeCNF input)
  step := reductionBlockWidth (decodeCNF input)
  count := (decodeCNF input).length

/-- Exact three-field runtime source for all slack zero counts. -/
def slackProgressionSource (input : List CNFSym) : List UnaryFrameSym :=
  slackBaseFrame input ++ slackStepFrame input ++ slackCountFrame input

theorem slackProgressionSource_eq (input : List CNFSym) :
    slackProgressionSource input =
      encodeAffineUnaryProgression (slackProgression input) := by
  rw [slackProgressionSource, slackBaseFrame, slackStepFrame, slackCountFrame,
    unaryClockFrame_eq, unaryClockFrame_eq, unaryClockFrame_eq,
    slackBaseProductTicks_eq, reductionBlockWidthTicks_eq,
    clauseCountTicks_eq]
  simp [encodeAffineUnaryProgression, slackProgression, encodeUnaryFrame,
    List.append_assoc]

private noncomputable def slackBaseFrame_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackBaseFrame := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      slackBaseProductTicks_computableInPolyTime
      unaryClockFrame_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryClockFrame (slackBaseProductTicks input))
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def slackStepFrame_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackStepFrame := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reductionBlockWidthTicks_computableInPolyTime
      unaryClockFrame_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryClockFrame (reductionBlockWidthTicks input))
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def slackCountFrame_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackCountFrame := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      clauseCountTicks_computableInPolyTime
      unaryClockFrame_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryClockFrame (clauseCountTicks input))
  simpa only [Function.comp_def] using Classical.choice composed

private noncomputable def slackProgressionPrefix_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List CNFSym => slackBaseFrame input ++ slackStepFrame input) :=
  unaryFrameSameInputConcat_computableInPolyTime
    slackBaseFrame_computableInPolyTime slackStepFrame_computableInPolyTime

/-- A fixed polynomial-time TM2 generates the complete runtime affine source
for all clause-indexed slack values. -/
noncomputable def slackProgressionSource_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryProgression slackProgression := by
  let joined := unaryFrameSameInputConcat_computableInPolyTime
    slackProgressionPrefix_computableInPolyTime
    slackCountFrame_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [← slackProgressionSource_eq]
        simpa [slackProgressionSource, List.append_assoc] using output }

end CLRS.Chapter34.Turing.SubsetSumReduction
