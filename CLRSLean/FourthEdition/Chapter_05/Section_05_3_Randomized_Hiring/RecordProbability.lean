import CLRSLean.FourthEdition.Chapter_05.Section_05_3_Randomized_Hiring.RecordIndicators
import CLRSLean.FourthEdition.Chapter_05.Section_05_4_Probabilistic_Analysis.OnlineHiring

/-!
# Prefix-record probability under a uniform permutation

This file reuses the position-transposition lemmas from the on-line hiring
development.  A value-reversing involution turns the executable model's
left-to-right maxima into the existing score model's left-to-right minima.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability
open OnlineHiring

/-- The number of permutations whose minimum among the first `m` positions is
at `p` does not depend on `p`. -/
lemma card_isMinInFirst_eq {n m : Nat} (hm : m <= n) (p q : Fin m) :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun sigma => isMinInFirst hm sigma p)).card =
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun sigma => isMinInFirst hm sigma q)).card := by
  classical
  by_cases hpq : p = q
  · subst q
    rfl
  · apply Finset.card_bij
      (fun sigma _ => swapValues (liftFirst hm p) (liftFirst hm q) sigma)
    · intro sigma hsigma
      rw [Finset.mem_filter] at hsigma ⊢
      exact ⟨Finset.mem_univ _, isMinInFirst_swap hm hpq sigma hsigma.2⟩
    · intro sigma1 _ sigma2 _ heq
      have h := congrArg
        (swapValues (liftFirst hm p) (liftFirst hm q)) heq
      simpa [swapValues_involutive] using h
    · intro sigma hsigma
      rw [Finset.mem_filter] at hsigma
      refine ⟨swapValues (liftFirst hm p) (liftFirst hm q) sigma, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [swapValues_comm] using
          isMinInFirst_swap hm (Ne.symm hpq) sigma hsigma.2
      · simp [swapValues_involutive]

/-- The minimum-position event sets partition the full permutation space. -/
lemma sum_card_isMinInFirst {n m : Nat} (hm : m <= n) (hmpos : 0 < m) :
    (∑ p : Fin m,
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun sigma => isMinInFirst hm sigma p)).card) =
      Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  calc
    (∑ p : Fin m,
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun sigma => isMinInFirst hm sigma p)).card) =
        ∑ p : Fin m, ∑ sigma : Equiv.Perm (Fin n),
          if isMinInFirst hm sigma p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.card_filter]
    _ = ∑ sigma : Equiv.Perm (Fin n), ∑ p : Fin m,
          if isMinInFirst hm sigma p then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _sigma : Equiv.Perm (Fin n), 1 := by
      apply Finset.sum_congr rfl
      intro sigma _
      rcases isMinInFirst_exists hm hmpos sigma with ⟨p0, hp0⟩
      have hiff (p : Fin m) : isMinInFirst hm sigma p ↔ p = p0 := by
        constructor
        · intro hp
          exact isMinInFirst_unique hm sigma hp hp0
        · rintro rfl
          exact hp0
      simp_rw [hiff]
      simp
    _ = Fintype.card (Equiv.Perm (Fin n)) := by simp

/-- Every one of the first `m` positions is equally likely to contain their
minimum, hence has probability `1/m`. -/
theorem isMinInFirst_probability {n m : Nat} (hm : m <= n) (hmpos : 0 < m)
    (p : Fin m) :
    fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
      indicator (isMinInFirst hm sigma p)) = 1 / (m : Real) := by
  classical
  have hnum :
      (∑ sigma : Equiv.Perm (Fin n), indicator (isMinInFirst hm sigma p)) =
        (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun sigma => isMinInFirst hm sigma p)).card : Real) :=
    sum_indicator_eq_card (fun sigma : Equiv.Perm (Fin n) =>
      isMinInFirst hm sigma p)
  rw [fintypeExpect, hnum]
  let count : Nat :=
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun sigma => isMinInFirst hm sigma p)).card
  have huniform :
      (∑ q : Fin m,
        (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun sigma => isMinInFirst hm sigma q)).card : Real)) =
        (m : Real) * (count : Real) := by
    calc
      _ = ∑ _q : Fin m, (count : Real) := by
        apply Finset.sum_congr rfl
        intro q _
        exact_mod_cast card_isMinInFirst_eq hm q p
      _ = (m : Real) * (count : Real) := by simp
  have htotal :
      (∑ q : Fin m,
        (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun sigma => isMinInFirst hm sigma q)).card : Real)) =
        (Fintype.card (Equiv.Perm (Fin n)) : Real) := by
    exact_mod_cast sum_card_isMinInFirst hm hmpos
  have heq : (m : Real) * (count : Real) =
      (Fintype.card (Equiv.Perm (Fin n)) : Real) := by
    rw [← huniform]
    exact htotal
  have hmne : (m : Real) ≠ 0 := by positivity
  have hcardne : (Fintype.card (Equiv.Perm (Fin n)) : Real) ≠ 0 := by
    rw [Fintype.card_perm]
    positivity
  change (count : Real) / (Fintype.card (Equiv.Perm (Fin n)) : Real) =
    1 / (m : Real)
  field_simp [hmne, hcardne]
  nlinarith

/-- Being the best score seen at position `i` is the same as being the minimum
of the first `i+1` positions. -/
theorem isRecordAt_iff_isMinInFirst {n : Nat} (sigma : Equiv.Perm (Fin n))
    (i : Fin n) :
    isRecordAt sigma i ↔
      isMinInFirst (Nat.succ_le_iff.mpr i.isLt) sigma
        ⟨i.val, Nat.lt_succ_self i.val⟩ := by
  let hm : i.val + 1 <= n := Nat.succ_le_iff.mpr i.isLt
  let last : Fin (i.val + 1) := ⟨i.val, Nat.lt_succ_self i.val⟩
  change isRecordAt sigma i ↔ isMinInFirst hm sigma last
  constructor
  · intro hrecord t
    by_cases hti : t.val = i.val
    · have hlift : liftFirst hm t = i := by
        apply Fin.ext
        exact hti
      rw [hlift, show liftFirst hm last = i by
        apply Fin.ext
        rfl]
    · have htlt : t.val < i.val := by omega
      have hstrict := hrecord (liftFirst hm t) (by simpa [liftFirst] using htlt)
      exact le_of_lt (by simpa [liftFirst] using hstrict)
  · intro hmin j hji
    have hjfirst : j.val < i.val + 1 := by omega
    have hjne : j ≠ liftFirst hm last := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [liftFirst, last] at hval
      omega
    have hstrict := isMinInFirst_lt hm sigma last hmin j hjfirst hjne
    simpa [liftFirst, last] using hstrict

/-- Under a uniform permutation, position `i` is a score-record (a new
minimum) with probability `1/(i+1)`. -/
theorem scoreRecord_probability {n : Nat} (i : Fin n) :
    fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
      indicator (isRecordAt sigma i)) = 1 / ((i.val + 1 : Nat) : Real) := by
  let hm : i.val + 1 <= n := Nat.succ_le_iff.mpr i.isLt
  let last : Fin (i.val + 1) := ⟨i.val, Nat.lt_succ_self i.val⟩
  calc
    fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
        indicator (isRecordAt sigma i)) =
        fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
          indicator (isMinInFirst hm sigma last)) := by
      apply congrArg fintypeExpect
      funext sigma
      unfold indicator
      exact if_congr (by simpa [hm, last] using isRecordAt_iff_isMinInFirst sigma i) rfl rfl
    _ = 1 / ((i.val + 1 : Nat) : Real) :=
      isMinInFirst_probability hm (Nat.succ_pos _) last

/-- Reverse every sampled rank.  This is an involutive equivalence of the
uniform permutation sample space. -/
def reverseRanksEquiv (n : Nat) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun sigma := sigma.trans Fin.revPerm
  invFun sigma := sigma.trans Fin.revPerm
  left_inv sigma := by
    ext i
    simp [Fin.revPerm_apply, Fin.rev_rev]
  right_inv sigma := by
    ext i
    simp [Fin.revPerm_apply, Fin.rev_rev]

/-- Reversing the rank order turns an executable left-to-right maximum into
the on-line hiring model's left-to-right minimum. -/
theorem permutationPrefixRecordAt_iff_scoreRecord {n : Nat}
    (sigma : Equiv.Perm (Fin n)) (i : Fin n) :
    permutationPrefixRecordAt sigma i ↔
      isRecordAt (reverseRanksEquiv n sigma) i := by
  rw [permutationPrefixRecordAt_iff]
  unfold isRecordAt
  constructor
  · intro h j hji
    change (Fin.revPerm (sigma i)).val < (Fin.revPerm (sigma j)).val
    exact (Fin.rev_lt_rev (i := sigma i) (j := sigma j)).2 (h j hji)
  · intro h j hji
    have hrev := h j hji
    change (Fin.revPerm (sigma i)).val < (Fin.revPerm (sigma j)).val at hrev
    exact (Fin.rev_lt_rev (i := sigma i) (j := sigma j)).1 hrev

/-- **Uniform prefix-record probability.**  Position `i` is a new maximum in
the executable hiring rank order with probability `1/(i+1)`. -/
theorem prefixRecord_probability {n : Nat} (i : Fin n) :
    fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
      indicator (permutationPrefixRecordAt sigma i)) =
      1 / ((i.val + 1 : Nat) : Real) := by
  calc
    fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
        indicator (permutationPrefixRecordAt sigma i)) =
        fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
          indicator (isRecordAt (reverseRanksEquiv n sigma) i)) := by
      apply congrArg fintypeExpect
      funext sigma
      unfold indicator
      exact if_congr (permutationPrefixRecordAt_iff_scoreRecord sigma i) rfl rfl
    _ = fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
          indicator (isRecordAt sigma i)) :=
      fintypeExpect_equiv (reverseRanksEquiv n)
        (fun sigma : Equiv.Perm (Fin n) => indicator (isRecordAt sigma i))
    _ = 1 / ((i.val + 1 : Nat) : Real) := scoreRecord_probability i

end Chapter05
end CLRS
