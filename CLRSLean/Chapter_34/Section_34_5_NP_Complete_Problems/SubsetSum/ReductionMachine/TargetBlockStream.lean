import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.TargetBlockSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import Mathlib.Tactic

/-!
# Fixed nested-loop generation of the SUBSET-SUM target bits

The verified row-major nested loop filters the tagged source down to
`row × column` pairs.  Variable rows select the bit pattern for digit one;
clause rows select digit four.  This file proves that its complete output is
exactly the little-endian packed target word used by the mathematical
reduction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

def targetBlockBody :
    LoopBody (TargetBlockSourceSym × TargetBlockSourceSym) Bool where
  emit
    | (.variableRow, .column position) =>
        [smallDigitBit .one position]
    | (.clauseRow, .column position) =>
        [smallDigitBit .four position]
    | _ => []
  cost _ := 1
  emit_length_le_cost pair := by
    rcases pair with ⟨outer, inner⟩
    cases outer <;> cases inner <;> simp

/-- Direct little-endian target stream emitted by the fixed nested loop. -/
def targetPackedBitsLE (input : List CNFSym) : List Bool :=
  nestedLoopOutput targetBlockBody (targetBlockSource input)

private def targetBlockSourceOf (variableCount clauseCount : Nat)
    (positions : List SmallDigitPosition) : List TargetBlockSourceSym :=
  List.replicate variableCount .variableRow ++
    List.replicate clauseCount .clauseRow ++ positions.map .column

private theorem targetBlockSource_eq_of (input : List CNFSym) :
    targetBlockSource input =
      targetBlockSourceOf
        (reductionVariableCount (decodeCNF input))
        (decodeCNF input).length
        (smallDigitPositions (reductionBlockWidthTicks input)) := by
  rw [targetBlockSource, targetBlockRows, targetVariableRows,
    targetClauseRows, targetColumns, variableBudgetTicks_eq,
    clauseCountTicks_eq]
  simp [targetBlockSourceOf]

private theorem flatMap_replicate_eq_flatten {α β : Type}
    (count : Nat) (symbol : α) (f : α → List β) :
    (List.replicate count symbol).flatMap f =
      (List.replicate count (f symbol)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.flatMap_cons,
        List.flatten_cons, ih]

private theorem flatMap_map_nil {α β γ : Type}
    (input : List α) (f : α → β) (g : β → List γ)
    (h : ∀ value, g (f value) = []) :
    (input.map f).flatMap g = [] := by
  induction input with
  | nil => rfl
  | cons value input ih => simp [h, ih]

private theorem flatten_replicate_nil {α : Type} (count : Nat) :
    (List.replicate count ([] : List α)).flatten = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private theorem targetBlockInner_variable
    (variableCount clauseCount : Nat)
    (positions : List SmallDigitPosition) :
    (targetBlockSourceOf variableCount clauseCount positions).flatMap
        (fun inner => targetBlockBody.emit (.variableRow, inner)) =
      positions.map (smallDigitBit .one) := by
  rw [targetBlockSourceOf, List.flatMap_append, List.flatMap_append,
    flatMap_replicate_eq_flatten, flatMap_replicate_eq_flatten]
  have hvariable : targetBlockBody.emit
      (.variableRow, .variableRow) = [] := rfl
  have hclause : targetBlockBody.emit
      (.variableRow, .clauseRow) = [] := rfl
  rw [hvariable, hclause, flatten_replicate_nil, flatten_replicate_nil]
  simp only [List.nil_append]
  induction positions with
  | nil => rfl
  | cons position positions ih =>
      have hcolumn : targetBlockBody.emit
          (.variableRow, .column position) =
            [smallDigitBit .one position] := rfl
      simp only [List.map_cons, List.flatMap_cons, hcolumn,
        List.singleton_append, ih]

private theorem targetBlockInner_clause
    (variableCount clauseCount : Nat)
    (positions : List SmallDigitPosition) :
    (targetBlockSourceOf variableCount clauseCount positions).flatMap
        (fun inner => targetBlockBody.emit (.clauseRow, inner)) =
      positions.map (smallDigitBit .four) := by
  rw [targetBlockSourceOf, List.flatMap_append, List.flatMap_append,
    flatMap_replicate_eq_flatten, flatMap_replicate_eq_flatten]
  have hvariable : targetBlockBody.emit
      (.clauseRow, .variableRow) = [] := rfl
  have hclause : targetBlockBody.emit
      (.clauseRow, .clauseRow) = [] := rfl
  rw [hvariable, hclause, flatten_replicate_nil, flatten_replicate_nil]
  simp only [List.nil_append]
  induction positions with
  | nil => rfl
  | cons position positions ih =>
      have hcolumn : targetBlockBody.emit
          (.clauseRow, .column position) =
            [smallDigitBit .four position] := rfl
      simp only [List.map_cons, List.flatMap_cons, hcolumn,
        List.singleton_append, ih]

private theorem targetBlockInner_column
    (variableCount clauseCount : Nat)
    (positions : List SmallDigitPosition) (outerPosition : SmallDigitPosition) :
    (targetBlockSourceOf variableCount clauseCount positions).flatMap
        (fun inner => targetBlockBody.emit (.column outerPosition, inner)) =
      [] := by
  rw [targetBlockSourceOf, List.flatMap_append, List.flatMap_append,
    flatMap_replicate_eq_flatten, flatMap_replicate_eq_flatten]
  simp [targetBlockBody]

private theorem targetBlockOutput_eq_repeated
    (variableCount clauseCount : Nat)
    (positions : List SmallDigitPosition) :
    nestedLoopOutput targetBlockBody
        (targetBlockSourceOf variableCount clauseCount positions) =
      (List.replicate variableCount
          (positions.map (smallDigitBit .one))).flatten ++
      (List.replicate clauseCount
          (positions.map (smallDigitBit .four))).flatten := by
  change
    (List.replicate variableCount TargetBlockSourceSym.variableRow ++
      List.replicate clauseCount TargetBlockSourceSym.clauseRow ++
        positions.map TargetBlockSourceSym.column).flatMap
      (fun outer =>
        (targetBlockSourceOf variableCount clauseCount positions).flatMap
          (fun inner => targetBlockBody.emit (outer, inner))) = _
  rw [List.flatMap_append, List.flatMap_append,
    flatMap_replicate_eq_flatten,
    flatMap_replicate_eq_flatten, targetBlockInner_variable,
    targetBlockInner_clause]
  have hcolumns :
      (positions.map TargetBlockSourceSym.column).flatMap
          (fun outer =>
            (targetBlockSourceOf variableCount clauseCount positions).flatMap
              (fun inner => targetBlockBody.emit (outer, inner))) = [] := by
    exact flatMap_map_nil positions TargetBlockSourceSym.column _
      (targetBlockInner_column variableCount clauseCount positions)
  rw [hcolumns, List.append_nil]

private def repeatBlock (count : Nat) (block : List Bool) : List Bool :=
  (List.replicate count block).flatten

@[simp] private theorem repeatBlock_zero (block : List Bool) :
    repeatBlock 0 block = [] := rfl

@[simp] private theorem repeatBlock_succ (count : Nat) (block : List Bool) :
    repeatBlock (count + 1) block = block ++ repeatBlock count block := by
  simp [repeatBlock, List.replicate_succ]

private theorem packedBitsLE_splitTarget
    (blockWidth variableCount clauseCount : Nat) :
    packedBitsLE blockWidth (variableCount + clauseCount)
        (fun column => if column < variableCount then 1 else 4) =
      repeatBlock variableCount (fixedBinaryBlock blockWidth 1) ++
        repeatBlock clauseCount (fixedBinaryBlock blockWidth 4) := by
  induction variableCount with
  | zero =>
      simp only [Nat.zero_add, Nat.not_lt_zero, ↓reduceIte,
        repeatBlock_zero, List.nil_append]
      induction clauseCount with
      | zero => rfl
      | succ clauseCount ih =>
          rw [show clauseCount + 1 = clauseCount + 1 by rfl,
            packedBitsLE_succ, repeatBlock_succ]
          simpa using ih
  | succ variableCount ih =>
      rw [show variableCount + 1 + clauseCount =
          (variableCount + clauseCount) + 1 by omega,
        packedBitsLE_succ, repeatBlock_succ]
      have hshift :
          (fun column => if column + 1 < variableCount + 1 then 1 else 4) =
            (fun column => if column < variableCount then 1 else 4) := by
        funext column
        simp only [Nat.add_lt_add_iff_right]
      simp only [Nat.zero_lt_succ, ↓reduceIte, hshift, ih]
      rw [List.append_assoc]

theorem targetPackedBitsLE_eq (input : List CNFSym) :
    targetPackedBitsLE input =
      packedBitsLE (reductionBlockWidth (decodeCNF input))
        (reductionWidth (decodeCNF input))
        (targetDigit (decodeCNF input)) := by
  have hwidth : 3 ≤ (reductionBlockWidthTicks input).length := by
    rw [reductionBlockWidthTicks_eq]
    simp [reductionBlockWidth]
  rw [targetPackedBitsLE, targetBlockSource_eq_of,
    targetBlockOutput_eq_repeated, smallDigitPositions_map,
    smallDigitPositions_map,
    smallDigitBlock_eq_fixedBinaryBlock .one _ hwidth,
    smallDigitBlock_eq_fixedBinaryBlock .four _ hwidth,
    reductionBlockWidthTicks_eq]
  change _ = packedBitsLE (reductionBlockWidth (decodeCNF input))
    (reductionVariableCount (decodeCNF input) + (decodeCNF input).length)
    (fun column =>
      if column < reductionVariableCount (decodeCNF input) then 1 else 4)
  simp only [List.length_replicate, SmallDigit.value]
  change
    repeatBlock (reductionVariableCount (decodeCNF input))
        (fixedBinaryBlock (reductionBlockWidth (decodeCNF input)) 1) ++
      repeatBlock (decodeCNF input).length
        (fixedBinaryBlock (reductionBlockWidth (decodeCNF input)) 4) = _
  exact (packedBitsLE_splitTarget
    (reductionBlockWidth (decodeCNF input))
    (reductionVariableCount (decodeCNF input))
    (decodeCNF input).length).symm

/-- The complete little-endian target bit matrix is generated by one fixed
polynomial-time TM2 from arbitrary raw CNF syntax. -/
noncomputable def targetPackedBitsLE_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetPackedBitsLE := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      targetBlockSource_computableInPolyTime
      (nestedLoop_computableInPolyTime targetBlockBody)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => nestedLoopOutput targetBlockBody (targetBlockSource input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction
