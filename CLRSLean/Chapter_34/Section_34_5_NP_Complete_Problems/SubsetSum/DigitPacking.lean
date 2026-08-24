import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Instance

/-!
# Carry-free decimal-column packing

`packColumns base width digits` treats `digits 0` as the least significant
base-`base` column.  The main interface says that bounded columns are recovered
uniquely from the packed natural number, and that packing commutes with finite
sums.
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- Pack the first `width` columns in the given base into a natural number. -/
def packColumns (base : Nat) : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | width + 1, digits =>
      digits 0 + base * packColumns base width (fun column => digits (column + 1))

@[simp] theorem packColumns_zero (base : Nat) (digits : Nat → Nat) :
    packColumns base 0 digits = 0 := rfl

@[simp] theorem packColumns_succ (base width : Nat) (digits : Nat → Nat) :
    packColumns base (width + 1) digits =
      digits 0 + base * packColumns base width
        (fun column => digits (column + 1)) := rfl

/-- Packing depends only on the columns below `width`. -/
theorem packColumns_congr {base width : Nat} {left right : Nat → Nat}
    (heq : ∀ column < width, left column = right column) :
    packColumns base width left = packColumns base width right := by
  induction width generalizing left right with
  | zero => rfl
  | succ width ih =>
      simp only [packColumns_succ]
      congr 1
      · exact heq 0 (by omega)
      · exact congrArg (fun value => base * value)
          (ih (fun column hcolumn => heq (column + 1) (by omega)))

theorem sum_packColumns {α : Type} [DecidableEq α]
    (items : Finset α) (base width : Nat) (digits : α → Nat → Nat) :
    (∑ item ∈ items, packColumns base width (digits item)) =
      packColumns base width
        (fun column => ∑ item ∈ items, digits item column) := by
  induction width generalizing digits with
  | zero => simp
  | succ width ih =>
      simp only [packColumns_succ, Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      exact ih (fun item column => digits item (column + 1))

theorem packColumns_injective_of_lt_base
    {base width : Nat} {left right : Nat → Nat}
    (hbase : 0 < base)
    (hleft : ∀ column < width, left column < base)
    (hright : ∀ column < width, right column < base)
    (heq : packColumns base width left = packColumns base width right) :
    ∀ column < width, left column = right column := by
  induction width generalizing left right with
  | zero => simp
  | succ width ih =>
      have hleft0 : left 0 < base := hleft 0 (by omega)
      have hright0 : right 0 < base := hright 0 (by omega)
      have hmod := congrArg (fun value => value % base) heq
      simp [packColumns] at hmod
      rw [Nat.mod_eq_of_lt hleft0, Nat.mod_eq_of_lt hright0] at hmod
      have htail :
          packColumns base width (fun column => left (column + 1)) =
            packColumns base width (fun column => right (column + 1)) := by
        simp only [packColumns_succ] at heq
        rw [← hmod] at heq
        exact Nat.mul_left_cancel hbase (Nat.add_left_cancel heq)
      have ih' := ih
        (left := fun column => left (column + 1))
        (right := fun column => right (column + 1))
        (fun column hcolumn => hleft (column + 1) (by omega))
        (fun column hcolumn => hright (column + 1) (by omega))
        htail
      intro column hcolumn
      cases column with
      | zero => exact hmod
      | succ column => exact ih' column (by omega)

end CLRS.Chapter34.SubsetSumReduction
