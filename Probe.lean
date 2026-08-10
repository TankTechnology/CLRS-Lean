import Mathlib.Data.List.Basic
import Mathlib.Tactic

variable {α : Type} [DecidableEq α]
variable (s : Finset α) (x : α)

#check Finset.card_union_of_disjoint
#check Finset.disjoint_left
#check Finset.sum_insert
#check Finset.sum_erase_add
#check Finset.sum_eq_sum_erase
#check Finset.sum_add_distrib
#check Finset.sum_congr
#check Finset.card_insert_of_notMem
#check Finset.card_insert
#check Finset.mem_insert_self
#check Finset.mem_of_mem_erase
#check Finset.insert_erase
#check Finset.erase_insert
#check Finset.erase_subset_erase
#check Finset.filter_erase
#check Finset.filter_union
#check Finset.mem_erase
#check Finset.sum_erase
#check Finset.card_eq_zero
#check Finset.eq_empty_iff_forall_not_mem
#check Finset.sum_eq_zero
#check Finset.sum_sub_distrib

-- insert/erase: insert x (s.erase x) = insert x s
example (hx : x ∈ s) : insert x (s.erase x) = s := by
  exact Finset.insert_erase hx

-- (s.erase x).filter P = s.filter (fun b => b ≠ x ∧ P b)
example (P : α → Prop) [DecidablePred P] :
    (s.erase x).filter P = s.filter (fun b => b ≠ x ∧ P b) := by
  ext b
  by_cases hbx : b = x
  · subst b
    simp
  · simp [hbx]

-- card split
example (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    (s.filter (fun b => P b ∧ Q b)).card + (s.filter (fun b => ¬ P b ∧ Q b)).card =
      (s.filter Q).card := by
  have hdisj : Disjoint (s.filter (fun b => P b ∧ Q b)) (s.filter (fun b => ¬ P b ∧ Q b)) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    simp at hb1 hb2
    exact hb1.1 hb2.1
  have hunion : (s.filter (fun b => P b ∧ Q b)) ∪ (s.filter (fun b => ¬ P b ∧ Q b)) =
      s.filter Q := by
    ext b
    simp
    by_cases h : P b
    · simp [h]
    · simp [h]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

-- sum split: ∑ over insert x (s.erase x)
example (f : α → ℕ) (hx : x ∈ s) :
    (∑ a in s.erase x, f a) + f x = ∑ a in s, f a := by
  rw [← Finset.sum_insert (by simp : x ∉ s.erase x)]
  -- now RHS is ∑ in insert x (s.erase x) = ∑ in s
  rw [Finset.insert_erase hx]

-- card_insert for the excluded-element split
example (P : α → Prop) [DecidablePred P] (hx : x ∈ s) :
    (s.filter P).card = ((s.erase x).filter P).card + (if P x then 1 else 0) := by
  by_cases hP : P x
  · have hxfilter : x ∈ s.filter P := by
      simp [hP, hx]
    have hsplit : s.filter P = insert x ((s.erase x).filter P) := by
      ext b
      by_cases hbx : b = x
      · subst b
        simp [hP, hx]
      · simp [hbx]
    rw [hsplit]
    rw [Finset.card_insert_of_notMem]
    · simp [hP]
    · exact by
        intro hb
        rw [Finset.mem_filter] at hb
        simp at hb
        exact hb.1 rfl
  · have hsplit : s.filter P = (s.erase x).filter P := by
      ext b
      by_cases hbx : b = x
      · subst b
        simp [hP]
      · simp [hbx]
    rw [hsplit]
    simp [hP]
