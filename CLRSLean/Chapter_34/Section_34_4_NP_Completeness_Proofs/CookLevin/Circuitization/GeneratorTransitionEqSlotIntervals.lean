import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSource
import Mathlib.Tactic

/-!
# Transition equality slot intervals

This module isolates the finite-prefix arithmetic used to enumerate equality
coordinates.  In particular, it proves that the fixed stack blocks form one
contiguous interval, independently of the later slot and circuit semantics.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- An `ofFn` enumeration of consecutive natural numbers is `List.range'`. -/
theorem transitionEqOfFnAdd_eq_range (base count : Nat) :
    (List.ofFn fun index : Fin count => base + index.val) =
      List.range' base count := by
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_ofFn, List.getElem_range']
    omega

/-- The canonical stack offset is the sum of widths at all earlier positions
in the fixed stack equivalence. -/
theorem transitionEq_cfgStackBitOffset_equiv_symm
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (position : Fin (arithmeticStackCount tm)) :
    cfgStackBitOffset tm height
        ((arithmeticStackEquiv tm).symm position) =
      ∑ prior : Fin position.val,
        cfgStackBitWidth tm height
          ((arithmeticStackEquiv tm).symm
            (Fin.castLE position.isLt.le prior)) := by
  letI : Fintype tm.K := tm.kFin
  unfold cfgStackBitOffset arithmeticStackEquiv arithmeticStackCount
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  change (∑ prior : Fin
      (keyEquiv (keyEquiv.symm position)).val,
        cfgStackBitWidth tm height
          (keyEquiv.symm
            (Fin.castLE (keyEquiv (keyEquiv.symm position)).isLt.le
              prior))) = _
  rw [show keyEquiv (keyEquiv.symm position) = position by
    exact keyEquiv.apply_symm_apply position]

private def transitionEqFinWidthAt {count : Nat}
    (width : Fin count → Nat) (index : Nat) : Nat :=
  if h : index < count then width ⟨index, h⟩ else 0

@[simp] private theorem transitionEqFinWidthAt_fin {count : Nat}
    (width : Fin count → Nat) (index : Fin count) :
    transitionEqFinWidthAt width index.val = width index := by
  simp only [transitionEqFinWidthAt, index.isLt, dite_true]

private theorem transitionEqFinPrefixSum_eq_rangeSum {count : Nat}
    (width : Fin count → Nat) (position : Fin count) :
    (∑ prior : Fin position.val,
      width (Fin.castLE position.isLt.le prior)) =
      ((List.range position.val).map
        (transitionEqFinWidthAt width)).sum := by
  rw [← List.sum_ofFn]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    have hindex : index < position.val := by simpa using hleft
    have hglobal : index < count := Nat.lt_trans hindex position.isLt
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    unfold transitionEqFinWidthAt
    simp only [hglobal, dite_true]
    congr

private theorem transitionEqFinTotalSum_eq_rangeSum {count : Nat}
    (width : Fin count → Nat) :
    (∑ position : Fin count, width position) =
      ((List.range count).map (transitionEqFinWidthAt width)).sum := by
  rw [← List.sum_ofFn]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    have hindex : index < count := by simpa using hleft
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    unfold transitionEqFinWidthAt
    simp only [hindex, dite_true]

private theorem transitionEqNatPrefixIntervals_eq_range
    (base count : Nat) (width : Nat → Nat) :
    (List.ofFn fun position : Fin count =>
      List.range'
        (base + ((List.range position.val).map width).sum)
        (width position.val)).flatten =
      List.range' base (((List.range count).map width).sum) := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.ofFn_succ', List.concat_eq_append, List.flatten_concat]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      simpa only [Nat.one_mul] using
        (List.range'_append (s := base)
          (m := ((List.range count).map width).sum)
          (n := width count) (step := 1))

private theorem transitionEqFinPrefixIntervals_eq_range
    (base count : Nat) (width : Fin count → Nat) :
    (List.ofFn fun position : Fin count =>
      List.range'
        (base + ∑ prior : Fin position.val,
          width (Fin.castLE position.isLt.le prior))
        (width position)).flatten =
      List.range' base (∑ position : Fin count, width position) := by
  calc
    _ = (List.ofFn fun position : Fin count =>
          List.range'
            (base + ((List.range position.val).map
              (transitionEqFinWidthAt width)).sum)
            (transitionEqFinWidthAt width position.val)).flatten := by
        apply congrArg List.flatten
        apply List.ofFn_inj.mpr
        funext position
        rw [transitionEqFinPrefixSum_eq_rangeSum]
        simp
    _ = List.range' base
          (((List.range count).map
            (transitionEqFinWidthAt width)).sum) :=
      transitionEqNatPrefixIntervals_eq_range base count
        (transitionEqFinWidthAt width)
    _ = _ := by rw [← transitionEqFinTotalSum_eq_rangeSum]

/-- Fixed stack bit intervals concatenate to one interval, with an arbitrary
outer base suitable for prefixing halted/label/state coordinates. -/
theorem transitionEqStackIntervals_eq_range
    (tm : _root_.Turing.FinTM2) (height base : Nat) :
    (List.ofFn fun position : Fin (arithmeticStackCount tm) =>
      List.range' (base + cfgStackBitOffset tm height
        ((arithmeticStackEquiv tm).symm position))
        (cfgStackBitWidth tm height
          ((arithmeticStackEquiv tm).symm position))).flatten =
      List.range' base
        ((List.ofFn fun position : Fin (arithmeticStackCount tm) =>
          cfgStackBitWidth tm height
            ((arithmeticStackEquiv tm).symm position)).sum) := by
  let width : Fin (arithmeticStackCount tm) → Nat := fun position =>
    cfgStackBitWidth tm height ((arithmeticStackEquiv tm).symm position)
  calc
    _ = (List.ofFn fun position : Fin (arithmeticStackCount tm) =>
          List.range'
            (base + ∑ prior : Fin position.val,
              width (Fin.castLE position.isLt.le prior))
            (width position)).flatten := by
        apply congrArg List.flatten
        apply List.ofFn_inj.mpr
        funext position
        rw [transitionEq_cfgStackBitOffset_equiv_symm]
    _ = List.range' base
          (∑ position : Fin (arithmeticStackCount tm), width position) :=
      transitionEqFinPrefixIntervals_eq_range base
        (arithmeticStackCount tm) width
    _ = _ := by rw [List.sum_ofFn]

end CLRS.Chapter34.Turing.CookLevin
