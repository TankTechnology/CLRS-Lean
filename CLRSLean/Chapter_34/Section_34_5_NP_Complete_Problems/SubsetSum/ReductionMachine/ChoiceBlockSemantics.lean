import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceBlockStream
import Mathlib.Tactic

/-!
# Choice blocks: textbook bit semantics

On the three-CNF branch, the finite digit expansion agrees with the exact
little-endian packed choice-item payload used by the mathematical reduction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open _root_.CLRS.Chapter34.SubsetSumReduction

private def bitBlock (bits : List Bool) : List ChoiceBlockSym :=
  bits.map .bit

private def repeatBlock (count : Nat) (block : List Bool) : List Bool :=
  (List.replicate count block).flatten

@[simp] private theorem repeatBlock_zero (block : List Bool) :
    repeatBlock 0 block = [] := rfl

@[simp] private theorem repeatBlock_succ (count : Nat) (block : List Bool) :
    repeatBlock (count + 1) block = block ++ repeatBlock count block := by
  simp [repeatBlock, List.replicate_succ]

private theorem packedBitsLE_constant (blockWidth count digit : Nat) :
    packedBitsLE blockWidth count (fun _ => digit) =
      repeatBlock count (fixedBinaryBlock blockWidth digit) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [packedBitsLE_succ, repeatBlock_succ]
      exact congrArg (List.append (fixedBinaryBlock blockWidth digit)) ih

private theorem packedBitsLE_oneHot (blockWidth before after : Nat) :
    packedBitsLE blockWidth (before + 1 + after)
        (fun column => if column = before then 1 else 0) =
      repeatBlock before (fixedBinaryBlock blockWidth 0) ++
        fixedBinaryBlock blockWidth 1 ++
          repeatBlock after (fixedBinaryBlock blockWidth 0) := by
  induction before with
  | zero =>
      rw [Nat.zero_add, show 1 + after = after + 1 by omega,
        packedBitsLE_succ]
      have htail : (fun column => if column + 1 = 0 then 1 else 0) =
          (fun _ => 0) := by
        funext column
        simp
      rw [htail, packedBitsLE_constant]
      rfl
  | succ before ih =>
      rw [show before + 1 + 1 + after = (before + 1 + after) + 1 by omega,
        packedBitsLE_succ, repeatBlock_succ]
      have hzero : (if 0 = before + 1 then 1 else 0) = 0 := by simp
      rw [hzero]
      have hshift :
          (fun column => if column + 1 = before + 1 then 1 else 0) =
            (fun column => if column = before then 1 else 0) := by
        funext column
        simp only [Nat.add_right_cancel_iff]
      rw [hshift, ih]
      simp only [List.append_assoc]

private theorem choiceBlockDigitTag_occurrence (count : Nat) :
    (choiceBlockDigitTag (occurrenceSmallDigit count)).toSmallDigit =
      occurrenceSmallDigit count := by
  cases count with
  | zero => rfl
  | succ count =>
      cases count with
      | zero => rfl
      | succ count =>
          cases count with
          | zero => rfl
          | succ count =>
              cases count with
              | zero => rfl
              | succ count => rfl

private theorem choiceBlockExpand_zero (width : List Unit) :
    choiceBlockExpand (smallDigitPositions width) (.digit .zero) =
      bitBlock (smallDigitBlock .zero width) := by
  have h := congrArg (List.map ChoiceBlockSym.bit)
    (smallDigitPositions_map SmallDigit.zero width)
  simpa [choiceBlockExpand, bitBlock, choiceBlockDigitTag,
    ChoiceBlockDigit.toSmallDigit, List.map_map, Function.comp_def] using h

private theorem choiceBlockExpand_one (width : List Unit) :
    choiceBlockExpand (smallDigitPositions width) (.digit .one) =
      bitBlock (smallDigitBlock .one width) := by
  have h := congrArg (List.map ChoiceBlockSym.bit)
    (smallDigitPositions_map SmallDigit.one width)
  simpa [choiceBlockExpand, bitBlock, choiceBlockDigitTag,
    ChoiceBlockDigit.toSmallDigit, List.map_map, Function.comp_def] using h

private theorem choiceBlockExpand_occurrence (count : Nat)
    (width : List Unit) :
    choiceBlockExpand (smallDigitPositions width)
        (.digit (occurrenceSmallDigit count)) =
      bitBlock (smallDigitBlock (occurrenceSmallDigit count) width) := by
  have h := congrArg (List.map ChoiceBlockSym.bit)
    (smallDigitPositions_map (occurrenceSmallDigit count) width)
  simpa [choiceBlockExpand, bitBlock, choiceBlockDigitTag_occurrence,
    List.map_map, Function.comp_def] using h

private theorem flatMap_replicate_eq_flatten {α β : Type}
    (count : Nat) (symbol : α) (f : α → List β) :
    (List.replicate count symbol).flatMap f =
      (List.replicate count (f symbol)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.flatMap_cons,
        List.flatten_cons, ih]

private theorem choiceVariableExpand_eq (formula : CNF) (index : Nat)
    (hindex : index < reductionVariableCount formula)
    (width : List Unit) (hwidth : width.length = reductionBlockWidth formula) :
    (choiceVariableDigits formula index).flatMap
        (choiceBlockExpand (smallDigitPositions width)) =
      bitBlock (choiceVariableBlocksLE formula index) := by
  let after := reductionVariableCount formula - index - 1
  have hcount : reductionVariableCount formula = index + 1 + after := by
    omega
  have hafter : index + 1 + after - index - 1 = after := by
    omega
  have hwidthThree : 3 ≤ width.length := by
    rw [hwidth]
    simp [reductionBlockWidth]
  have hzero := smallDigitBlock_eq_fixedBinaryBlock .zero width hwidthThree
  have hone := smallDigitBlock_eq_fixedBinaryBlock .one width hwidthThree
  rw [choiceVariableDigits, choiceVariableBlocksLE, hcount,
    packedBitsLE_oneHot]
  rw [List.flatMap_append, List.flatMap_cons,
    flatMap_replicate_eq_flatten, flatMap_replicate_eq_flatten,
    choiceBlockExpand_zero, choiceBlockExpand_one]
  simp [bitBlock, repeatBlock, List.map_append, List.map_flatten,
    hzero, hone, hwidth, hafter, SmallDigit.value,
    List.append_assoc]

private theorem choiceClauseExpand_eq {formula : CNF}
    (hthree : IsThreeCNF formula) (index : Nat) (truth : Bool)
    (width : List Unit) (hwidthThree : 3 ≤ width.length) :
    (choiceOccurrenceDigits formula index truth).flatMap
        (choiceBlockExpand (smallDigitPositions width)) =
      bitBlock (packedBitsLE width.length formula.length fun clause =>
        (formula.getD clause []).count (itemLiteral index truth)) := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      have hclauseLength : clause.length ≤ 3 :=
        hthree clause (by simp)
      have hcount : clause.count (itemLiteral index truth) ≤ 3 :=
        List.count_le_length.trans hclauseLength
      have htail : IsThreeCNF formula := by
        intro current hcurrent
        exact hthree current (by simp [hcurrent])
      have ih' := ih htail
      have hblock := smallDigitBlock_eq_fixedBinaryBlock
        (occurrenceSmallDigit (clause.count (itemLiteral index truth)))
        width hwidthThree
      have hvalue := occurrenceSmallDigit_value_of_le_three hcount
      have hshift :
          (fun column =>
            (((clause :: formula).getD (column + 1) []).count
              (itemLiteral index truth))) =
          (fun column =>
            (formula.getD column []).count (itemLiteral index truth)) := by
        funext column
        simp
      simp only [choiceOccurrenceDigits, List.map_cons, List.flatMap_cons]
      rw [
        choiceBlockExpand_occurrence]
      rw [List.length_cons,
        show formula.length + 1 = formula.length + 1 by rfl,
        packedBitsLE_succ, hshift]
      change _ = List.map ChoiceBlockSym.bit
        (fixedBinaryBlock width.length
          (clause.count (itemLiteral index truth)) ++
            packedBitsLE width.length formula.length fun column =>
              (formula.getD column []).count (itemLiteral index truth))
      rw [List.map_append]
      have ihBits :
          (choiceOccurrenceDigits formula index truth).flatMap
              (choiceBlockExpand (smallDigitPositions width)) =
            List.map ChoiceBlockSym.bit
              (packedBitsLE width.length formula.length fun clause =>
                (formula.getD clause []).count
                  (itemLiteral index truth)) := by
        simpa [bitBlock] using ih'
      rw [hblock, hvalue]
      simp only [choiceOccurrenceDigits] at ihBits
      rw [ihBits]
      rfl

private theorem choiceItemExpand_eq {formula : CNF}
    (hthree : IsThreeCNF formula) (index : Nat)
    (hindex : index < reductionVariableCount formula) (truth : Bool)
    (width : List Unit) (hwidth : width.length = reductionBlockWidth formula) :
    (choiceVariableDigits formula index ++
      choiceOccurrenceDigits formula index truth ++
        [ChoiceCountSym.itemEnd]).flatMap
        (choiceBlockExpand (smallDigitPositions width)) =
      bitBlock (choicePackedBitsLE formula index truth) ++ [.itemEnd] := by
  have hwidthThree : 3 ≤ width.length := by
    rw [hwidth]
    simp [reductionBlockWidth]
  rw [List.flatMap_append, List.flatMap_append,
    choiceVariableExpand_eq formula index hindex width hwidth,
    choiceClauseExpand_eq hthree index truth width hwidthThree]
  simp [choiceBlockExpand, choicePackedBitsLE, choiceClauseBlocksLE,
    hwidth, bitBlock,
    List.map_append, List.append_assoc]

/-- All little-endian choice payloads, with one boundary after every item. -/
def choicePackedBlockStream (formula : CNF) (truth : Bool) :
    List ChoiceBlockSym :=
  (List.range (reductionVariableCount formula)).flatMap fun index =>
    bitBlock (choicePackedBitsLE formula index truth) ++ [.itemEnd]

private theorem choiceDigitExpand_eq {formula : CNF}
    (hthree : IsThreeCNF formula) (truth : Bool) (width : List Unit)
    (hwidth : width.length = reductionBlockWidth formula) :
    (choiceDigitStream formula truth).flatMap
        (choiceBlockExpand (smallDigitPositions width)) =
      choicePackedBlockStream formula truth := by
  rw [choiceDigitStream, choicePackedBlockStream, List.flatMap_assoc]
  apply List.flatMap_congr
  intro index hindex
  exact choiceItemExpand_eq hthree index
    (List.mem_range.mp hindex) truth width hwidth

/-- On the source three-CNF language, the generated block stream is exactly
the textbook little-endian packed payload for every choice item. -/
theorem choiceBlockStream_packed_eq {input : List CNFSym}
    (hthree : IsThreeCNF (decodeCNF input)) (truth : Bool) :
    choiceBlockStream truth input =
      choicePackedBlockStream (decodeCNF input) truth := by
  rw [choiceBlockStream_eq]
  apply choiceDigitExpand_eq hthree truth
  rw [reductionBlockWidthTicks_eq]
  simp

end CLRS.Chapter34.Turing.SubsetSumReduction
