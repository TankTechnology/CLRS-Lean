import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.Dimensions
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.BinaryBlocks

/-!
# Fixed-width blocks for the five reduction digits

The CLRS column construction only uses digits zero through four.  A four-state
streaming controller emits their three low bits and then zero padding.  On the
reduction's block width (which is at least three), this is exactly the
`fixedBinaryBlock` semantic representation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

inductive SmallDigit
  | zero | one | two | three | four
deriving DecidableEq, Fintype, Repr

def SmallDigit.value : SmallDigit → Nat
  | .zero => 0
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4

inductive SmallDigitPosition
  | bit0 | bit1 | bit2 | padding
deriving DecidableEq, Fintype, Repr

def smallDigitBit : SmallDigit → SmallDigitPosition → Bool
  | .zero, _ => false
  | .one, .bit0 => true
  | .one, _ => false
  | .two, .bit1 => true
  | .two, _ => false
  | .three, .bit0 | .three, .bit1 => true
  | .three, _ => false
  | .four, .bit2 => true
  | .four, _ => false

@[simp] theorem smallDigitBit_padding (digit : SmallDigit) :
    smallDigitBit digit .padding = false := by
  cases digit <;> rfl

def SmallDigitPosition.next : SmallDigitPosition → SmallDigitPosition
  | .bit0 => .bit1
  | .bit1 => .bit2
  | .bit2 | .padding => .padding

/-- Runtime column positions shared by every small-digit block. -/
def smallDigitPositionSpec :
    StatefulFlatMapSpec SmallDigitPosition Unit SmallDigitPosition where
  initial := .bit0
  action position _ := ([position], position.next)
  finish _ := []

def smallDigitPositions (width : List Unit) : List SmallDigitPosition :=
  rewriteStatefulFlatMap smallDigitPositionSpec width

def smallDigitBlockSpec (digit : SmallDigit) :
    StatefulFlatMapSpec SmallDigitPosition Unit Bool where
  initial := .bit0
  action position _ := ([smallDigitBit digit position], position.next)
  finish _ := []

/-- Concrete block emitted from a unary width stream. -/
def smallDigitBlock (digit : SmallDigit) (width : List Unit) : List Bool :=
  rewriteStatefulFlatMap (smallDigitBlockSpec digit) width

private theorem smallDigitPositions_mapFrom
    (digit : SmallDigit) (position : SmallDigitPosition)
    (width : List Unit) :
    (rewriteStatefulFlatMapFrom smallDigitPositionSpec position width).map
        (smallDigitBit digit) =
      rewriteStatefulFlatMapFrom (smallDigitBlockSpec digit) position width := by
  induction width generalizing position with
  | nil => rfl
  | cons _ width ih =>
      rw [rewriteStatefulFlatMapFrom, rewriteStatefulFlatMapFrom]
      simp only [smallDigitPositionSpec, smallDigitBlockSpec,
        List.map_append, List.map_singleton]
      exact congrArg (List.cons (smallDigitBit digit position))
        (ih position.next)

theorem smallDigitPositions_map (digit : SmallDigit) (width : List Unit) :
    (smallDigitPositions width).map (smallDigitBit digit) =
      smallDigitBlock digit width := by
  simpa [smallDigitPositions, smallDigitBlock, rewriteStatefulFlatMap,
    smallDigitPositionSpec, smallDigitBlockSpec] using
      smallDigitPositions_mapFrom digit .bit0 width

private theorem smallDigitBlockFrom_padding
    (digit : SmallDigit) (width : List Unit) :
    rewriteStatefulFlatMapFrom (smallDigitBlockSpec digit) .padding width =
      List.replicate width.length false := by
  induction width with
  | nil => rfl
  | cons _ width ih =>
      rw [rewriteStatefulFlatMapFrom]
      simp only [smallDigitBlockSpec, smallDigitBit_padding,
        SmallDigitPosition.next] at ih ⊢
      simp [ih, List.replicate_succ]

private theorem smallDigitBlock_three_prefix
    (digit : SmallDigit) (tail : List Unit) :
    smallDigitBlock digit (() :: () :: () :: tail) =
      [smallDigitBit digit .bit0, smallDigitBit digit .bit1,
        smallDigitBit digit .bit2] ++
        List.replicate tail.length false := by
  rw [smallDigitBlock, rewriteStatefulFlatMap]
  have hpadding := smallDigitBlockFrom_padding digit tail
  simp only [smallDigitBlockSpec, SmallDigitPosition.next] at hpadding
  simp only [rewriteStatefulFlatMapFrom, smallDigitBlockSpec,
    SmallDigitPosition.next]
  rw [hpadding]
  rfl

private theorem fixedBinaryBlock_smallDigit
    (digit : SmallDigit) (tailLength : Nat) :
    fixedBinaryBlock (tailLength + 3) digit.value =
      [smallDigitBit digit .bit0, smallDigitBit digit .bit1,
        smallDigitBit digit .bit2] ++
        List.replicate tailLength false := by
  cases digit <;>
    simp [fixedBinaryBlock, Nat.digitsAppend, SmallDigit.value,
      smallDigitBit, List.replicate_succ, Nat.add_comm]

theorem smallDigitBlock_eq_fixedBinaryBlock
    (digit : SmallDigit) (width : List Unit) (hwidth : 3 ≤ width.length) :
    smallDigitBlock digit width =
      fixedBinaryBlock width.length digit.value := by
  cases width with
  | nil => simp at hwidth
  | cons _ width =>
      cases width with
      | nil => simp at hwidth
      | cons _ width =>
          cases width with
          | nil => simp at hwidth
          | cons _ tail =>
              rw [smallDigitBlock_three_prefix]
              change _ = fixedBinaryBlock (tail.length + 3) digit.value
              rw [fixedBinaryBlock_smallDigit]

/-- Every fixed small digit block is produced by a genuine fixed linear-time
TM2 from its unary width stream. -/
noncomputable def smallDigitBlock_computableInPolyTime (digit : SmallDigit) :
    _root_.Turing.TM2ComputableInPolyTime id id (smallDigitBlock digit) :=
  statefulFlatMap_computableInPolyTime (smallDigitBlockSpec digit)

noncomputable def smallDigitPositions_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id smallDigitPositions :=
  statefulFlatMap_computableInPolyTime smallDigitPositionSpec

/-- Constant reduction digit generated directly from arbitrary raw CNF. -/
def canonicalSmallDigitBlock (digit : SmallDigit)
    (input : List CNFSym) : List Bool :=
  smallDigitBlock digit (reductionBlockWidthTicks input)

theorem canonicalSmallDigitBlock_eq (digit : SmallDigit)
    (input : List CNFSym) :
    canonicalSmallDigitBlock digit input =
      fixedBinaryBlock (reductionBlockWidth (decodeCNF input)) digit.value := by
  rw [canonicalSmallDigitBlock, reductionBlockWidthTicks_eq]
  simpa using smallDigitBlock_eq_fixedBinaryBlock digit
    (List.replicate (reductionBlockWidth (decodeCNF input)) ())
    (by simp [reductionBlockWidth])

noncomputable def canonicalSmallDigitBlock_computableInPolyTime
    (digit : SmallDigit) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (canonicalSmallDigitBlock digit) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reductionBlockWidthTicks_computableInPolyTime
      (smallDigitBlock_computableInPolyTime digit)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => smallDigitBlock digit (reductionBlockWidthTicks input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SubsetSumReduction
