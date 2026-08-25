import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ClauseCount
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.NumericBounds

/-!
# Concrete unary dimensions of the SUBSET-SUM reduction

One reusable affine counter emits a fixed number of ticks for every canonical
unary-index cell and clause marker, plus a fixed terminal constant.  Three
instances compute the column width, item count, and binary block width.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Affine counter over canonical CNF symbols. -/
def cnfAffineCountSpec (endCopies clauseCopies finalCopies : Nat) :
    StatefulFlatMapSpec Unit CNFSym Unit where
  initial := ()
  action _ symbol :=
    (List.replicate
      (match symbol with
       | .endMark => endCopies
       | .clauseMark => clauseCopies
       | _ => 0) (), ())
  finish _ := List.replicate finalCopies ()

def cnfAffineCountTicks (endCopies clauseCopies finalCopies : Nat)
    (input : List CNFSym) : List Unit :=
  rewriteStatefulFlatMap
    (cnfAffineCountSpec endCopies clauseCopies finalCopies) input

private theorem cnfAffineCountTicksFrom_eq
    (endCopies clauseCopies finalCopies : Nat) (input : List CNFSym) :
    rewriteStatefulFlatMapFrom
        (cnfAffineCountSpec endCopies clauseCopies finalCopies) () input =
      List.replicate
        (endCopies * input.count .endMark +
          clauseCopies * input.count .clauseMark + finalCopies) () := by
  induction input with
  | nil => simp [rewriteStatefulFlatMapFrom, cnfAffineCountSpec]
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom]
      simp only [cnfAffineCountSpec] at ih
      cases symbol <;>
        simp [cnfAffineCountSpec, ih, Nat.mul_succ] <;> omega

theorem cnfAffineCountTicks_eq
    (endCopies clauseCopies finalCopies : Nat) (input : List CNFSym) :
    cnfAffineCountTicks endCopies clauseCopies finalCopies input =
      List.replicate
        (endCopies * input.count .endMark +
          clauseCopies * input.count .clauseMark + finalCopies) () := by
  simpa [cnfAffineCountTicks, rewriteStatefulFlatMap,
    cnfAffineCountSpec] using
      cnfAffineCountTicksFrom_eq endCopies clauseCopies finalCopies input

noncomputable def cnfAffineCountTicks_computableInPolyTime
    (endCopies clauseCopies finalCopies : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (cnfAffineCountTicks endCopies clauseCopies finalCopies) :=
  statefulFlatMap_computableInPolyTime
    (cnfAffineCountSpec endCopies clauseCopies finalCopies)

/-- Normalize raw syntax before applying the affine counter. -/
def canonicalAffineCountTicks (endCopies clauseCopies finalCopies : Nat)
    (input : List CNFSym) : List Unit :=
  cnfAffineCountTicks endCopies clauseCopies finalCopies
    (TMClique.normalizeCNFInput input)

theorem canonicalAffineCountTicks_eq
    (endCopies clauseCopies finalCopies : Nat) (input : List CNFSym) :
    canonicalAffineCountTicks endCopies clauseCopies finalCopies input =
      List.replicate
        (endCopies * reductionVariableCount (decodeCNF input) +
          clauseCopies * (decodeCNF input).length + finalCopies) () := by
  rw [canonicalAffineCountTicks, cnfAffineCountTicks_eq,
    TMClique.normalizeCNFInput_eq_encCNF_decodeCNF,
    reductionVariableCount, encCNF_count_clauseMark]

noncomputable def canonicalAffineCountTicks_computableInPolyTime
    (endCopies clauseCopies finalCopies : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (canonicalAffineCountTicks endCopies clauseCopies finalCopies) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      TMClique.normalizeCNFInput_computableInPolyTime
      (cnfAffineCountTicks_computableInPolyTime
        endCopies clauseCopies finalCopies)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => cnfAffineCountTicks endCopies clauseCopies finalCopies
      (TMClique.normalizeCNFInput input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Unary total column count `variables + clauses`. -/
def reductionWidthTicks : List CNFSym → List Unit :=
  canonicalAffineCountTicks 1 1 0

/-- Unary number of generated candidate items `2·variables + 3·clauses`. -/
def reductionItemCountTicks : List CNFSym → List Unit :=
  canonicalAffineCountTicks 2 3 0

/-- Unary fixed binary block width `2·variables + 3·clauses + 3`. -/
def reductionBlockWidthTicks : List CNFSym → List Unit :=
  canonicalAffineCountTicks 2 3 3

theorem reductionWidthTicks_eq (input : List CNFSym) :
    reductionWidthTicks input =
      List.replicate (reductionWidth (decodeCNF input)) () := by
  simpa [reductionWidthTicks, reductionWidth] using
    canonicalAffineCountTicks_eq 1 1 0 input

theorem reductionItemCountTicks_eq (input : List CNFSym) :
    reductionItemCountTicks input =
      List.replicate (reductionItemList (decodeCNF input)).length () := by
  rw [reductionItemCountTicks, canonicalAffineCountTicks_eq,
    reductionItemList_length]
  simp

theorem reductionBlockWidthTicks_eq (input : List CNFSym) :
    reductionBlockWidthTicks input =
      List.replicate (reductionBlockWidth (decodeCNF input)) () := by
  rw [reductionBlockWidthTicks, canonicalAffineCountTicks_eq,
    reductionBlockWidth_eq]

noncomputable def reductionWidthTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id reductionWidthTicks :=
  canonicalAffineCountTicks_computableInPolyTime 1 1 0

noncomputable def reductionItemCountTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id reductionItemCountTicks :=
  canonicalAffineCountTicks_computableInPolyTime 2 3 0

noncomputable def reductionBlockWidthTicks_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id reductionBlockWidthTicks :=
  canonicalAffineCountTicks_computableInPolyTime 2 3 3

end CLRS.Chapter34.Turing.SubsetSumReduction
