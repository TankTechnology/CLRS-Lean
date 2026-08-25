import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.MaskCertificate.Basic
import Mathlib.Tactic

/-!
# Finite-set semantics of Boolean selection

This bridge isolates the only mathematical difference between an index-list
certificate and the Boolean-mask certificate used by the concrete machine.
-/

namespace CLRS.Chapter34

open Turing.PolyBuilder

/-- The mask characteristic function of a finite set of valid positions. -/
def subsetMaskOfFinset {values : List Nat}
    (chosen : Finset (Fin values.length)) : List Bool :=
  List.ofFn fun index => decide (index ∈ chosen)

private theorem sum_selectedValues_ofFn (values : List Nat)
    (keep : Fin values.length → Bool) :
    (selectListByBool (List.ofFn keep) values).sum =
      ∑ index : Fin values.length,
        if keep index then values.get index else 0 := by
  induction values with
  | nil => simp [selectListByBool]
  | cons value values ih =>
      rw [List.ofFn_succ]
      change
        (selectListByBool
          (keep 0 :: List.ofFn fun index => keep index.succ)
          (value :: values)).sum =
        ∑ index : Fin (values.length + 1),
          if keep index then (value :: values).get index else 0
      rw [Fin.sum_univ_succ]
      cases hzero : keep 0 <;>
        simp [selectListByBool, ih]

theorem subsetSumMaskOfFinset_sum {values : List Nat}
    (chosen : Finset (Fin values.length)) :
    (subsetSumMaskValues (subsetMaskOfFinset chosen) values).sum =
      ∑ index ∈ chosen, values.get index := by
  rw [subsetSumMaskValues, subsetMaskOfFinset,
    sum_selectedValues_ofFn]
  simp

/-- Extending or truncating a mask with `false` bits does not affect the
pointwise selection once every input position has been covered. -/
theorem selectListByBool_eq_canonicalMask (mask : List Bool)
    (values : List Nat) :
    selectListByBool mask values =
      selectListByBool
        (List.ofFn fun index : Fin values.length =>
          mask.getD index.val false)
        values := by
  induction values generalizing mask with
  | nil => simp [selectListByBool]
  | cons value values ih =>
      cases mask with
      | nil =>
          rw [List.ofFn_succ]
          simp only [List.getD_nil, selectListByBool]
          rw [List.ofFn_const, selectListByBool_replicate_false]
          simp
      | cons flag mask =>
          rw [List.ofFn_succ]
          cases flag <;> simp [selectListByBool, ih]

end CLRS.Chapter34
