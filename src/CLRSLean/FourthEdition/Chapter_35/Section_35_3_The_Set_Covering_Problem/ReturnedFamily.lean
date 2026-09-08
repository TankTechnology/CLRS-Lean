import CLRSLean.FourthEdition.Chapter_35.Section_35_3_The_Set_Covering_Problem

/-!
# Approximation bounds for the returned set family

The returned family and the pick count follow the same greedy choices. Every
returned set intersects the initially uncovered universe, so an earlier pick
cannot occur again after its elements have been removed. Thus the family
cardinality equals the pick count, including the empty universe.
-/
namespace CLRS.SetCover
open Finset
variable {α : Type} [DecidableEq α]

theorem greedySetCover_mem_inter_nonempty (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) {S : Finset α}
    (hS : S ∈ greedySetCover F U hcov) : (S ∩ U).Nonempty := by
  classical
  induction U using (measure (fun U : Finset α => U.card)).wf.induction with
  | h U ih =>
    by_cases hU : U = ∅
    · subst U
      rw [greedySetCover.eq_1] at hS
      simp at hS
    · let hF := cover_nonempty F hcov (Finset.nonempty_iff_ne_empty.mpr hU)
      let T := pickSet F U hF
      rw [greedySetCover.eq_1,dif_neg hU] at hS
      rcases mem_insert.mp hS with heq | hmem
      · subst S
        exact pickSet_covers_nonempty F hcov (Finset.nonempty_iff_ne_empty.mpr hU)
      · obtain ⟨x,hx⟩ := ih (U \ T)
          (pickSet_sdiff_card_lt F hcov (Finset.nonempty_iff_ne_empty.mpr hU))
          (cover_sub F hcov sdiff_subset) hmem
        exact ⟨x,mem_inter.mpr ⟨(mem_inter.mp hx).1,(mem_sdiff.mp (mem_inter.mp hx).2).1⟩⟩

/-- No greedy pick is repeated: the actual returned cardinality equals the pick count. -/
theorem greedySetCover_card_eq_cost (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) :
    ((greedySetCover F U hcov).card : ℚ) = greedyCost F U hcov := by
  classical
  induction U using (measure (fun U : Finset α => U.card)).wf.induction with
  | h U ih =>
    by_cases hU : U = ∅
    · subst U
      rw [greedySetCover.eq_1,greedyCost.eq_1]
      simp
    · let hF := cover_nonempty F hcov (Finset.nonempty_iff_ne_empty.mpr hU)
      let T := pickSet F U hF
      let hsub := cover_sub F hcov (sdiff_subset (s:=U) (t:=T))
      have hnot : T ∉ greedySetCover F (U \ T) hsub := by
        intro hmem
        obtain ⟨x,hx⟩ := greedySetCover_mem_inter_nonempty F hsub hmem
        exact (mem_sdiff.mp (mem_inter.mp hx).2).2 (mem_inter.mp hx).1
      have hi := ih (U \ T)
        (pickSet_sdiff_card_lt F hcov (Finset.nonempty_iff_ne_empty.mpr hU)) hsub
      rw [greedySetCover.eq_1,greedyCost.eq_1,dif_neg hU,dif_neg hU]
      rw [card_insert_of_notMem hnot,Nat.cast_add,Nat.cast_one,hi]
      ring

/-- The harmonic approximation bound applies directly to the returned family. -/
theorem greedySetCover_card_approx (X : Finset α) (F : Finset (Finset α))
    (hcov : ∀ x ∈ X, ∃ S ∈ F, x ∈ S)
    (d : Nat) (hd : ∀ S ∈ F, S.card ≤ d)
    (C : Finset (Finset α)) (hCsub : C ⊆ F) (hCcov : Covers X C) :
    ((greedySetCover F X hcov).card : ℚ) ≤ harmonic d * (C.card : ℚ) := by
  rw [greedySetCover_card_eq_cost]
  exact greedySetCover_approx X F hcov d hd C hCsub hCcov

/-- The logarithmic approximation bound also applies to the returned family. -/
theorem greedySetCover_card_ln_approx (X : Finset α) (F : Finset (Finset α))
    (hcov : ∀ x ∈ X, ∃ S ∈ F, x ∈ S)
    (C : Finset (Finset α)) (hCsub : C ⊆ F) (hCcov : Covers X C) :
    ((greedySetCover F X hcov).card : ℚ) ≤
      (C.card : ℚ) * (((⌈Real.log (X.card : ℝ)⌉ : ℤ).toNat + 1 : Nat) : ℚ) := by
  rw [greedySetCover_card_eq_cost]
  exact greedySetCover_ln_approx X F hcov C hCsub hCcov

end CLRS.SetCover
