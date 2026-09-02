import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceBlockSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import Mathlib.Tactic

/-!
# Choice blocks: fixed nested-loop expansion

The nested loop expands each finite choice digit across the shared runtime
position stream.  The unique `bit0` position emits one boundary for an item-end
row.  All control symbols are silent when they occur as outer rows.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

inductive ChoiceBlockSym
  | bit (value : Bool)
  | itemEnd
deriving DecidableEq, Fintype, Repr

def choiceBlockBody :
    LoopBody (ChoiceBlockSourceSym × ChoiceBlockSourceSym) ChoiceBlockSym where
  emit
    | (.rowDigit digit, .column position) =>
        [.bit (smallDigitBit digit.toSmallDigit position)]
    | (.rowEnd, .column .bit0) => [.itemEnd]
    | _ => []
  cost _ := 1
  emit_length_le_cost pair := by
    rcases pair with ⟨outer, inner⟩
    cases outer with
    | rowDigit digit => cases inner <;> simp
    | rowEnd =>
        cases inner with
        | rowDigit digit => simp
        | rowEnd => simp
        | column position => cases position <;> simp
    | column position => cases inner <;> simp

def choiceBlockExpand (positions : List SmallDigitPosition) :
    ChoiceCountSym → List ChoiceBlockSym
  | .digit digit =>
      positions.map fun position =>
        .bit (smallDigitBit (choiceBlockDigitTag digit).toSmallDigit position)
  | .itemEnd => [.itemEnd]

/-- Concrete forward block-and-boundary stream. -/
def choiceBlockStream (truth : Bool) (input : List CNFSym) :
    List ChoiceBlockSym :=
  nestedLoopOutput choiceBlockBody (choiceBlockSource truth input)

private def choiceBlockSourceOf (rows : List ChoiceCountSym)
    (positions : List SmallDigitPosition) : List ChoiceBlockSourceSym :=
  rows.map choiceBlockRowTag ++ positions.map .column

private theorem choiceBlockInner_rowDigit (rows : List ChoiceCountSym)
    (positions : List SmallDigitPosition) (digit : ChoiceBlockDigit) :
    (choiceBlockSourceOf rows positions).flatMap
        (fun inner => choiceBlockBody.emit (.rowDigit digit, inner)) =
      positions.map fun position =>
        .bit (smallDigitBit digit.toSmallDigit position) := by
  rw [choiceBlockSourceOf, List.flatMap_append]
  have hrows : (rows.map choiceBlockRowTag).flatMap
      (fun inner => choiceBlockBody.emit (.rowDigit digit, inner)) = [] := by
    induction rows with
    | nil => rfl
    | cons symbol rows ih =>
        rw [List.map_cons, List.flatMap_cons]
        cases symbol <;> change [] ++ _ = [] <;> simpa using ih
  rw [hrows, List.nil_append]
  induction positions with
  | nil => rfl
  | cons position positions ih =>
      rw [List.map_cons, List.flatMap_cons]
      change [_] ++ _ = _ :: _
      simp only [List.singleton_append, List.cons.injEq, true_and]
      exact ih

private def choiceBlockBoundaryEmit :
    SmallDigitPosition → List ChoiceBlockSym
  | .bit0 => [.itemEnd]
  | _ => []

private theorem choiceBlockBoundaryFrom_noBit0
    (position : SmallDigitPosition) (hposition : position ≠ .bit0)
    (width : List Unit) :
    (rewriteStatefulFlatMapFrom smallDigitPositionSpec position width).flatMap
        choiceBlockBoundaryEmit = [] := by
  induction width generalizing position with
  | nil => rfl
  | cons _ width ih =>
      cases position with
      | bit0 => contradiction
      | bit1 =>
          simpa [rewriteStatefulFlatMapFrom, smallDigitPositionSpec,
            SmallDigitPosition.next, choiceBlockBoundaryEmit] using
            ih .bit2 (by simp)
      | bit2 =>
          simpa [rewriteStatefulFlatMapFrom, smallDigitPositionSpec,
            SmallDigitPosition.next, choiceBlockBoundaryEmit] using
            ih .padding (by simp)
      | padding =>
          simpa [rewriteStatefulFlatMapFrom, smallDigitPositionSpec,
            SmallDigitPosition.next, choiceBlockBoundaryEmit] using
            ih .padding (by simp)

private theorem choiceBlockBoundary_positions (width : List Unit)
    (hwidth : 0 < width.length) :
    (smallDigitPositions width).flatMap choiceBlockBoundaryEmit =
      [.itemEnd] := by
  cases width with
  | nil => simp at hwidth
  | cons _ width =>
      change (rewriteStatefulFlatMapFrom smallDigitPositionSpec .bit0
        (() :: width)).flatMap choiceBlockBoundaryEmit = [.itemEnd]
      rw [rewriteStatefulFlatMapFrom]
      change ChoiceBlockSym.itemEnd ::
          (rewriteStatefulFlatMapFrom smallDigitPositionSpec .bit1 width).flatMap
            choiceBlockBoundaryEmit = [.itemEnd]
      rw [choiceBlockBoundaryFrom_noBit0 .bit1 (by simp)]

private theorem choiceBlockInner_rowEnd (rows : List ChoiceCountSym)
    (width : List Unit) (hwidth : 0 < width.length) :
    (choiceBlockSourceOf rows (smallDigitPositions width)).flatMap
        (fun inner => choiceBlockBody.emit (.rowEnd, inner)) =
      [.itemEnd] := by
  rw [choiceBlockSourceOf, List.flatMap_append]
  have hrows : (rows.map choiceBlockRowTag).flatMap
      (fun inner => choiceBlockBody.emit (.rowEnd, inner)) = [] := by
    induction rows with
    | nil => rfl
    | cons symbol rows ih =>
        rw [List.map_cons, List.flatMap_cons]
        cases symbol <;> change [] ++ _ = [] <;> simpa using ih
  rw [hrows, List.nil_append]
  rw [List.flatMap_map]
  have hemit :
      (fun position =>
        choiceBlockBody.emit (.rowEnd, .column position)) =
        choiceBlockBoundaryEmit := by
    funext position
    cases position <;> rfl
  rw [hemit]
  change (smallDigitPositions width).flatMap choiceBlockBoundaryEmit = _
  exact choiceBlockBoundary_positions width hwidth

private theorem choiceBlockInner_column (rows : List ChoiceCountSym)
    (positions : List SmallDigitPosition)
    (outerPosition : SmallDigitPosition) :
    (choiceBlockSourceOf rows positions).flatMap
        (fun inner => choiceBlockBody.emit (.column outerPosition, inner)) =
      [] := by
  induction (choiceBlockSourceOf rows positions) with
  | nil => rfl
  | cons symbol input ih =>
      rw [List.flatMap_cons]
      cases symbol <;> change [] ++ _ = [] <;> simpa using ih

private theorem choiceBlockOuterRows
    (outerRows innerRows : List ChoiceCountSym)
    (width : List Unit) (hwidth : 0 < width.length) :
    (outerRows.map choiceBlockRowTag).flatMap
        (fun outer =>
          (choiceBlockSourceOf innerRows (smallDigitPositions width)).flatMap
            (fun inner => choiceBlockBody.emit (outer, inner))) =
      outerRows.flatMap (choiceBlockExpand (smallDigitPositions width)) := by
  induction outerRows with
  | nil => rfl
  | cons symbol outerRows ih =>
      rw [List.map_cons, List.flatMap_cons, List.flatMap_cons]
      cases symbol with
      | digit digit =>
          simp only [choiceBlockRowTag, choiceBlockExpand]
          rw [choiceBlockInner_rowDigit, ih]
      | itemEnd =>
          simp only [choiceBlockRowTag, choiceBlockExpand]
          rw [choiceBlockInner_rowEnd _ _ hwidth, ih]

private theorem choiceBlockOuterColumns
    (outerPositions : List SmallDigitPosition)
    (innerRows : List ChoiceCountSym)
    (innerPositions : List SmallDigitPosition) :
    (outerPositions.map ChoiceBlockSourceSym.column).flatMap
        (fun outer =>
          (choiceBlockSourceOf innerRows innerPositions).flatMap
            (fun inner => choiceBlockBody.emit (outer, inner))) = [] := by
  induction outerPositions with
  | nil => rfl
  | cons position positions ih =>
      rw [List.map_cons, List.flatMap_cons,
        choiceBlockInner_column, ih, List.nil_append]

private theorem choiceBlockOutput_eq (rows : List ChoiceCountSym)
    (width : List Unit) (hwidth : 0 < width.length) :
    nestedLoopOutput choiceBlockBody
        (choiceBlockSourceOf rows (smallDigitPositions width)) =
      rows.flatMap (choiceBlockExpand (smallDigitPositions width)) := by
  change (choiceBlockSourceOf rows (smallDigitPositions width)).flatMap
      (fun outer =>
        (choiceBlockSourceOf rows (smallDigitPositions width)).flatMap
          (fun inner => choiceBlockBody.emit (outer, inner))) = _
  rw [show choiceBlockSourceOf rows (smallDigitPositions width) =
      rows.map choiceBlockRowTag ++
        (smallDigitPositions width).map ChoiceBlockSourceSym.column by rfl,
    List.flatMap_append]
  have hrows := choiceBlockOuterRows rows rows width hwidth
  have hcolumns := choiceBlockOuterColumns (smallDigitPositions width) rows
    (smallDigitPositions width)
  simp only [choiceBlockSourceOf] at hrows hcolumns
  rw [hrows, hcolumns, List.append_nil]

/-- The nested loop is exactly pointwise fixed-width digit expansion with one
preserved marker per item. -/
theorem choiceBlockStream_eq (truth : Bool) (input : List CNFSym) :
    choiceBlockStream truth input =
      (choiceDigitStream (decodeCNF input) truth).flatMap
        (choiceBlockExpand
          (smallDigitPositions (reductionBlockWidthTicks input))) := by
  have hwidth : 0 < (reductionBlockWidthTicks input).length := by
    rw [reductionBlockWidthTicks_eq]
    simp [reductionBlockWidth]
  rw [choiceBlockStream, choiceBlockSource, choiceBlockRows,
    choiceBlockColumns]
  exact choiceBlockOutput_eq _ _ hwidth

/-- The complete forward block stream is generated by one fixed polynomial-
time TM2 from arbitrary raw CNF syntax. -/
noncomputable def choiceBlockStream_computableInPolyTime (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (choiceBlockStream truth) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (choiceBlockSource_computableInPolyTime truth)
      (nestedLoop_computableInPolyTime choiceBlockBody)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => nestedLoopOutput choiceBlockBody
      (choiceBlockSource truth input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction
