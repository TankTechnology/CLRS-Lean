import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Language
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowSelection

/-!
# Boolean-mask certificates for SUBSET-SUM

The public textbook certificate remains a duplicate-free list of indices.
For the concrete fixed verifier it is more economical to use one Boolean per
input value.  This file defines that alternative certificate and its selected
value semantics without changing the language.
-/

namespace CLRS.Chapter34

open Turing.PolyBuilder

/-- Canonical Boolean-mask certificate. -/
def encodeSubsetSumMask (mask : List Bool) : List SubsetSumSym :=
  .certificateMark :: mask.map .bit ++ [.recordEnd]

/-- Values selected pointwise by a Boolean mask. -/
def subsetSumMaskValues (mask : List Bool) (values : List Nat) : List Nat :=
  selectListByBool mask values

/-- The arithmetic predicate checked by the concrete verifier. -/
def SubsetSumData.MaskSumsTo (data : SubsetSumData) (mask : List Bool) : Prop :=
  (subsetSumMaskValues mask data.values).sum = data.target

@[simp] theorem encodeSubsetSumMask_length (mask : List Bool) :
    (encodeSubsetSumMask mask).length = mask.length + 2 := by
  simp [encodeSubsetSumMask]

end CLRS.Chapter34
