import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.SmallDigitBlock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# Runtime source for the SUBSET-SUM target block matrix

The target contains one digit-one block for every variable-budget cell and
one digit-four block for every clause.  The source word below places those row
tags before one runtime column-position stream.  A later verified nested loop
can therefore emit the complete rectangular bit matrix without performing
arithmetic on the packed natural number.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

/-- Finite tags consumed by the target block matrix controller. -/
inductive TargetBlockSourceSym
  | variableRow
  | clauseRow
  | column (position : SmallDigitPosition)
deriving DecidableEq, Fintype, Repr

/-- A fixed pair code used only to invoke same-input concatenation closure. -/
def encodeTargetBlockSourceSymPair :
    TargetBlockSourceSym → UnaryFrameSym × UnaryFrameSym
  | .variableRow => (.tick, .tick)
  | .clauseRow => (.tick, .separator)
  | .column .bit0 => (.tick, .frameEnd)
  | .column .bit1 => (.separator, .tick)
  | .column .bit2 => (.separator, .separator)
  | .column .padding => (.separator, .frameEnd)

def decodeTargetBlockSourceSymPair :
    UnaryFrameSym → UnaryFrameSym → TargetBlockSourceSym
  | .tick, .tick => .variableRow
  | .tick, .separator => .clauseRow
  | .tick, .frameEnd => .column .bit0
  | .separator, .tick => .column .bit1
  | .separator, .separator => .column .bit2
  | .separator, .frameEnd => .column .padding
  | .frameEnd, _ => .variableRow

@[simp] theorem decode_encodeTargetBlockSourceSymPair
    (symbol : TargetBlockSourceSym) :
    decodeTargetBlockSourceSymPair
        (encodeTargetBlockSourceSymPair symbol).1
        (encodeTargetBlockSourceSymPair symbol).2 = symbol := by
  cases symbol with
  | variableRow => rfl
  | clauseRow => rfl
  | column position => cases position <;> rfl

def targetVariableRows (input : List CNFSym) :
    List TargetBlockSourceSym :=
  (variableBudgetTicks input).map fun _ => .variableRow

def targetClauseRows (input : List CNFSym) :
    List TargetBlockSourceSym :=
  (clauseCountTicks input).map fun _ => .clauseRow

def targetColumns (input : List CNFSym) : List TargetBlockSourceSym :=
  (smallDigitPositions (reductionBlockWidthTicks input)).map .column

def targetBlockRows (input : List CNFSym) : List TargetBlockSourceSym :=
  targetVariableRows input ++ targetClauseRows input

/-- Row tags followed by the shared runtime bit-column positions. -/
def targetBlockSource (input : List CNFSym) : List TargetBlockSourceSym :=
  targetBlockRows input ++ targetColumns input

noncomputable def targetVariableRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetVariableRows := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      variableBudgetTicks_computableInPolyTime
      (listMap_computableInPolyTime
        (fun _ : Unit => TargetBlockSourceSym.variableRow))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (variableBudgetTicks input).map
      fun _ => TargetBlockSourceSym.variableRow)
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def targetClauseRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetClauseRows := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      clauseCountTicks_computableInPolyTime
      (listMap_computableInPolyTime
        (fun _ : Unit => TargetBlockSourceSym.clauseRow))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (clauseCountTicks input).map
      fun _ => TargetBlockSourceSym.clauseRow)
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def targetColumns_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetColumns := by
  let positionsExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reductionBlockWidthTicks_computableInPolyTime
      smallDigitPositions_computableInPolyTime
  let positions := Classical.choice positionsExists
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch positions
      (listMap_computableInPolyTime TargetBlockSourceSym.column)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (smallDigitPositions
      (reductionBlockWidthTicks input)).map TargetBlockSourceSym.column)
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def targetBlockRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetBlockRows :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeTargetBlockSourceSymPair decodeTargetBlockSourceSymPair
    decode_encodeTargetBlockSourceSymPair
    targetVariableRows_computableInPolyTime
    targetClauseRows_computableInPolyTime

noncomputable def targetBlockSource_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetBlockSource :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeTargetBlockSourceSymPair decodeTargetBlockSourceSymPair
    decode_encodeTargetBlockSourceSymPair
    targetBlockRows_computableInPolyTime
    targetColumns_computableInPolyTime

end CLRS.Chapter34.Turing.SubsetSumReduction
