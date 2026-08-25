import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.Dimensions
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.VariableBudget
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros

/-!
# Runtime batches for the SUBSET-SUM choice items

The choice-item generator must inspect the complete normalized formula once
for every variable.  This file materializes precisely those batches with the
already verified fixed nested-loop controller.  Each batch also carries the
unary block width and variable budget needed by the later local formatter.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Nine-symbol transport alphabet: exactly the capacity of the reusable
two-`UnaryFrameSym` codec. -/
inductive ChoiceBatchSym
  | outerTick | widthTick | variableTick
  | formula (symbol : CNFSym)
  | batchEnd
deriving DecidableEq, Fintype, Repr

/-- Map every source cell to one fixed batch symbol. -/
def choiceBatchUnitTagSpec (tag : ChoiceBatchSym) :
    StatefulFlatMapSpec Unit Unit ChoiceBatchSym where
  initial := ()
  action _ _ := ([tag], ())
  finish _ := []

def choiceBatchUnitTag (tag : ChoiceBatchSym) (input : List Unit) :
    List ChoiceBatchSym :=
  rewriteStatefulFlatMap (choiceBatchUnitTagSpec tag) input

private theorem choiceBatchUnitTagFrom_eq (tag : ChoiceBatchSym)
    (input : List Unit) :
    rewriteStatefulFlatMapFrom (choiceBatchUnitTagSpec tag) () input =
      input.map fun _ => tag := by
  induction input with
  | nil => rfl
  | cons _ input ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [tag] ++
          rewriteStatefulFlatMapFrom (choiceBatchUnitTagSpec tag) () input =
        tag :: List.map (fun _ => tag) input
      rw [ih]
      rfl

@[simp] theorem choiceBatchUnitTag_eq (tag : ChoiceBatchSym)
    (input : List Unit) :
    choiceBatchUnitTag tag input = input.map fun _ => tag := by
  exact choiceBatchUnitTagFrom_eq tag input

noncomputable def choiceBatchUnitTag_computableInPolyTime
    (tag : ChoiceBatchSym) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (choiceBatchUnitTag tag) :=
  statefulFlatMap_computableInPolyTime (choiceBatchUnitTagSpec tag)

/-- Inject normalized CNF symbols into the batch alphabet. -/
def choiceBatchFormulaTagSpec :
    StatefulFlatMapSpec Unit CNFSym ChoiceBatchSym where
  initial := ()
  action _ symbol := ([.formula symbol], ())
  finish _ := []

def choiceBatchFormulaTag (input : List CNFSym) : List ChoiceBatchSym :=
  rewriteStatefulFlatMap choiceBatchFormulaTagSpec input

private theorem choiceBatchFormulaTagFrom_eq (input : List CNFSym) :
    rewriteStatefulFlatMapFrom choiceBatchFormulaTagSpec () input =
      input.map .formula := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [.formula symbol] ++
          rewriteStatefulFlatMapFrom choiceBatchFormulaTagSpec () input =
        .formula symbol :: List.map .formula input
      rw [ih]
      rfl

@[simp] theorem choiceBatchFormulaTag_eq (input : List CNFSym) :
    choiceBatchFormulaTag input = input.map .formula := by
  exact choiceBatchFormulaTagFrom_eq input

noncomputable def choiceBatchFormulaTag_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id choiceBatchFormulaTag :=
  statefulFlatMap_computableInPolyTime choiceBatchFormulaTagSpec

/-- Ignore the raw word and emit the unique inner-batch sentinel. -/
def choiceBatchEndSpec :
    StatefulFlatMapSpec Unit CNFSym ChoiceBatchSym where
  initial := ()
  action _ _ := ([], ())
  finish _ := [.batchEnd]

def choiceBatchEnd (input : List CNFSym) : List ChoiceBatchSym :=
  rewriteStatefulFlatMap choiceBatchEndSpec input

private theorem choiceBatchEndFrom_eq (input : List CNFSym) :
    rewriteStatefulFlatMapFrom choiceBatchEndSpec () input = [.batchEnd] := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      simpa [rewriteStatefulFlatMapFrom, choiceBatchEndSpec] using ih

@[simp] theorem choiceBatchEnd_eq (input : List CNFSym) :
    choiceBatchEnd input = [.batchEnd] := by
  exact choiceBatchEndFrom_eq input

noncomputable def choiceBatchEnd_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id choiceBatchEnd :=
  statefulFlatMap_computableInPolyTime choiceBatchEndSpec

/-- Inner payload copied once for every variable. -/
def choiceBatchPayload (input : List CNFSym) : List ChoiceBatchSym :=
  choiceBatchUnitTag .widthTick (reductionBlockWidthTicks input) ++
    choiceBatchUnitTag .variableTick (variableBudgetTicks input) ++
    choiceBatchFormulaTag (TMClique.normalizeCNFInput input) ++
    choiceBatchEnd input

/-- Compact nested-loop source.  Only the initial `outerTick` cells select
productive outer rows. -/
def choiceBatchLoopSource (input : List CNFSym) : List ChoiceBatchSym :=
  choiceBatchUnitTag .outerTick (variableBudgetTicks input) ++
    choiceBatchPayload input

/-- Pair-local filter used by the verified nested-loop macro. -/
def choiceBatchLoopBody : LoopBody (ChoiceBatchSym × ChoiceBatchSym)
    ChoiceBatchSym where
  emit pair :=
    match pair.1, pair.2 with
    | .outerTick, .widthTick => [.widthTick]
    | .outerTick, .variableTick => [.variableTick]
    | .outerTick, .formula symbol => [.formula symbol]
    | .outerTick, .batchEnd => [.batchEnd]
    | _, _ => []
  cost _ := 1
  emit_length_le_cost pair := by cases pair.1 <;> cases pair.2 <;> simp

/-- Runtime row family consumed by the local choice-digit controller. -/
def choiceBatches (input : List CNFSym) : List ChoiceBatchSym :=
  nestedLoopOutput choiceBatchLoopBody (choiceBatchLoopSource input)

private theorem choiceBatchLoopRow_outer
    (input : List ChoiceBatchSym) :
    input.flatMap (fun inner => choiceBatchLoopBody.emit
      (.outerTick, inner)) =
      input.filter fun symbol => symbol != .outerTick := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      cases symbol <;>
        simpa [List.flatMap_cons, List.filter_cons, choiceBatchLoopBody]
          using ih

private theorem choiceBatchLoopRow_nonouter
    (outer : ChoiceBatchSym) (houter : outer != .outerTick)
    (input : List ChoiceBatchSym) :
    input.flatMap (fun inner => choiceBatchLoopBody.emit (outer, inner)) =
      [] := by
  cases outer <;> simp_all [choiceBatchLoopBody]

private theorem choiceBatchPayload_no_outer (input : List CNFSym) :
    (choiceBatchPayload input).filter
        (fun symbol => symbol != ChoiceBatchSym.outerTick) =
      choiceBatchPayload input := by
  simp [choiceBatchPayload]

private theorem choiceBatchPayload_ne_outer (input : List CNFSym)
    {symbol : ChoiceBatchSym} (hsymbol : symbol ∈ choiceBatchPayload input) :
    symbol != .outerTick := by
  have hfilter := congrArg (fun values => symbol ∈ values)
    (choiceBatchPayload_no_outer input)
  simpa [hsymbol] using hfilter

private theorem choiceBatchLoopRow_outer_source (count : Nat)
    (input : List CNFSym) :
    (List.replicate count ChoiceBatchSym.outerTick ++
        choiceBatchPayload input).flatMap
        (fun inner => choiceBatchLoopBody.emit (.outerTick, inner)) =
      choiceBatchPayload input := by
  rw [List.flatMap_append, List.flatMap_replicate,
    choiceBatchLoopRow_outer, choiceBatchPayload_no_outer]
  simp [choiceBatchLoopBody]

private theorem choiceBatchLoopRows_nonouter
    (source payload : List ChoiceBatchSym)
    (hne : ∀ symbol ∈ payload, symbol != ChoiceBatchSym.outerTick) :
    payload.flatMap (fun outer => source.flatMap
      (fun inner => choiceBatchLoopBody.emit (outer, inner))) = [] := by
  induction payload with
  | nil => rfl
  | cons outer payload ih =>
      rw [List.flatMap_cons,
        choiceBatchLoopRow_nonouter outer (hne outer (by simp)),
        ih (fun symbol hsymbol => hne symbol (by simp [hsymbol]))]
      simp

/-- Exact row-major meaning of the nested-loop expansion. -/
theorem choiceBatches_eq (input : List CNFSym) :
    choiceBatches input =
      (List.replicate (reductionVariableCount (decodeCNF input))
        (choiceBatchPayload input)).flatten := by
  rw [choiceBatches, nestedLoopOutput, choiceBatchLoopSource,
    choiceBatchUnitTag_eq, variableBudgetTicks_eq, List.map_replicate,
    List.flatMap_append, List.flatMap_replicate,
    choiceBatchLoopRow_outer_source]
  rw [choiceBatchLoopRows_nonouter]
  · simp
  · intro symbol hsymbol
    exact choiceBatchPayload_ne_outer input hsymbol

/-- Two-symbol transport code for the nine batch symbols. -/
def encodeChoiceBatchSymPair :
    ChoiceBatchSym → UnaryFrameSym × UnaryFrameSym
  | .outerTick => (.tick, .tick)
  | .widthTick => (.tick, .separator)
  | .variableTick => (.tick, .frameEnd)
  | .formula .clauseMark => (.separator, .tick)
  | .formula .posMark => (.separator, .separator)
  | .formula .negMark => (.separator, .frameEnd)
  | .formula .varMark => (.frameEnd, .tick)
  | .formula .endMark => (.frameEnd, .separator)
  | .batchEnd => (.frameEnd, .frameEnd)

def decodeChoiceBatchSymPair :
    UnaryFrameSym → UnaryFrameSym → ChoiceBatchSym
  | .tick, .tick => .outerTick
  | .tick, .separator => .widthTick
  | .tick, .frameEnd => .variableTick
  | .separator, .tick => .formula .clauseMark
  | .separator, .separator => .formula .posMark
  | .separator, .frameEnd => .formula .negMark
  | .frameEnd, .tick => .formula .varMark
  | .frameEnd, .separator => .formula .endMark
  | .frameEnd, .frameEnd => .batchEnd

@[simp] theorem decode_encodeChoiceBatchSymPair (symbol : ChoiceBatchSym) :
    decodeChoiceBatchSymPair (encodeChoiceBatchSymPair symbol).1
      (encodeChoiceBatchSymPair symbol).2 = symbol := by
  cases symbol with
  | outerTick | widthTick | variableTick | batchEnd => rfl
  | formula symbol => cases symbol <;> rfl

private noncomputable def choiceOuterTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => choiceBatchUnitTag .outerTick
        (variableBudgetTicks input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      variableBudgetTicks_computableInPolyTime
      (choiceBatchUnitTag_computableInPolyTime .outerTick)
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def choiceWidthTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => choiceBatchUnitTag .widthTick
        (reductionBlockWidthTicks input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reductionBlockWidthTicks_computableInPolyTime
      (choiceBatchUnitTag_computableInPolyTime .widthTick)
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def choiceVariableTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => choiceBatchUnitTag .variableTick
        (variableBudgetTicks input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      variableBudgetTicks_computableInPolyTime
      (choiceBatchUnitTag_computableInPolyTime .variableTick)
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def choiceFormula_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => choiceBatchFormulaTag
        (TMClique.normalizeCNFInput input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      TMClique.normalizeCNFInput_computableInPolyTime
      choiceBatchFormulaTag_computableInPolyTime
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def choiceBatchPayload_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id choiceBatchPayload := by
  let widthVariable := fixedPairSameInputConcat_computableInPolyTime
    encodeChoiceBatchSymPair decodeChoiceBatchSymPair
    decode_encodeChoiceBatchSymPair
    choiceWidthTicks_computableInPolyTime
    choiceVariableTicks_computableInPolyTime
  let throughFormula := fixedPairSameInputConcat_computableInPolyTime
    encodeChoiceBatchSymPair decodeChoiceBatchSymPair
    decode_encodeChoiceBatchSymPair widthVariable
    choiceFormula_computableInPolyTime
  let complete := fixedPairSameInputConcat_computableInPolyTime
    encodeChoiceBatchSymPair decodeChoiceBatchSymPair
    decode_encodeChoiceBatchSymPair throughFormula
    choiceBatchEnd_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      choiceBatchUnitTag ChoiceBatchSym.widthTick
          (reductionBlockWidthTicks input) ++
        choiceBatchUnitTag ChoiceBatchSym.variableTick
          (variableBudgetTicks input) ++
        choiceBatchFormulaTag (TMClique.normalizeCNFInput input) ++
        choiceBatchEnd input)
  simpa only [choiceBatchUnitTag_eq, choiceBatchFormulaTag_eq,
    choiceBatchEnd_eq, List.append_assoc] using complete

private noncomputable def choiceBatchLoopSource_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id choiceBatchLoopSource := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeChoiceBatchSymPair decodeChoiceBatchSymPair
    decode_encodeChoiceBatchSymPair
    choiceOuterTicks_computableInPolyTime
    choiceBatchPayload_computableInPolyTime

/-- A fixed composed polynomial-time TM2 generates all choice batches from
the original raw CNF word. -/
noncomputable def choiceBatches_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id choiceBatches := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      choiceBatchLoopSource_computableInPolyTime
      (nestedLoop_computableInPolyTime choiceBatchLoopBody)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => nestedLoopOutput choiceBatchLoopBody
      (choiceBatchLoopSource input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction
