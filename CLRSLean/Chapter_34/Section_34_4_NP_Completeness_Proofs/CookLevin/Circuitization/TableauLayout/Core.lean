import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Horizon
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau

/-!
# Consecutive whole-tableau row layouts

This module reserves one consecutive external-input interval for every row of
a `T`-step computation.  It contains only layout arithmetic; allocation lives
in the sibling `Allocation` module.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- A horizon of `T` transitions has the initial row plus `T` successors. -/
def tableauRowCount (T : Nat) : Nat := T + 1

/-- Exact external-input arity of a zero-offset tableau layout. -/
def tableauInputCount (tm : _root_.Turing.FinTM2) (H T : Nat) : Nat :=
  tableauRowCount T * cfgBitCount tm H

/-- Row `t` in a consecutive layout beginning at an arbitrary offset. -/
def tableauRowLayoutAt (tm : _root_.Turing.FinTM2) (H base t : Nat) :
    CfgInputLayout tm H :=
  ⟨base + t * cfgBitCount tm H⟩

/-- Row `t` in the canonical zero-offset tableau layout. -/
def tableauRowLayout (tm : _root_.Turing.FinTM2) (H t : Nat) :
    CfgInputLayout tm H :=
  tableauRowLayoutAt tm H 0 t

@[simp] theorem tableauRowLayoutAt_base (tm : _root_.Turing.FinTM2)
    (H base t : Nat) :
    (tableauRowLayoutAt tm H base t).base =
      base + t * cfgBitCount tm H := rfl

/-- Exact endpoint of one offset row interval. -/
@[simp] theorem tableauRowLayoutAt_finish (tm : _root_.Turing.FinTM2)
    (H base t : Nat) :
    (tableauRowLayoutAt tm H base t).finish =
      base + (t + 1) * cfgBitCount tm H := by
  simp [tableauRowLayoutAt, CfgInputLayout.finish, Nat.add_mul,
    Nat.add_assoc]

/-- Exact endpoint of one canonical row interval. -/
@[simp] theorem tableauRowLayout_finish (tm : _root_.Turing.FinTM2)
    (H t : Nat) :
    (tableauRowLayout tm H t).finish =
      (t + 1) * cfgBitCount tm H := by
  simp [tableauRowLayout]

/-- Every selected row lies inside the exact canonical tableau arity. -/
theorem tableauRowLayout_fits (tm : _root_.Turing.FinTM2) (H T : Nat)
    (t : Fin (tableauRowCount T)) :
    (tableauRowLayout tm H t.val).Fits (tableauInputCount tm H T) := by
  unfold CfgInputLayout.Fits tableauInputCount
  rw [tableauRowLayout_finish]
  exact Nat.mul_le_mul_right _ t.isLt

/-- Earlier rows occupy disjoint intervals from later rows, at any offset. -/
theorem tableauRowLayout_disjoint (tm : _root_.Turing.FinTM2)
    (H base : Nat) {t u : Nat} (htu : t < u) :
    (tableauRowLayoutAt tm H base t).Disjoint
      (tableauRowLayoutAt tm H base u) := by
  apply Or.inl
  rw [tableauRowLayoutAt_finish]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ htu) base

/-- Coordinates in two differently indexed rows never share an external-input
position. -/
theorem tableauRowLayout_index_ne (tm : _root_.Turing.FinTM2)
    (H base : Nat) {t u : Nat} (htu : t < u)
    (left right : CfgSlot tm H) :
    (tableauRowLayoutAt tm H base t).index left ≠
      (tableauRowLayoutAt tm H base u).index right :=
  CfgInputLayout.index_ne_of_disjoint
    (tableauRowLayout_disjoint tm H base htu) left right

end

end CLRS.Chapter34.Turing.CookLevin
