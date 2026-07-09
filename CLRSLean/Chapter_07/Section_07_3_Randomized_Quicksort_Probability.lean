import Mathlib

open Finset
open Classical

/-!
# Random Permutation Symmetry Lemma

Core: for a uniform random permutation of `Fin n`, each element of a subset
has equal probability 1/|S| of appearing first.  Proved via the transposition
bijection `π ↦ swap(a,b) * π`.
-/

namespace CLRS
namespace Chapter07

variable {n : ℕ}

/-- "Position" of element x in permutation π = π.symm x (the index mapping to x). -/
def pos (π : Equiv.Perm (Fin n)) (x : Fin n) : Fin n := π.symm x

/-- `IsFirstIn S x π` means x has minimal position among S in π. -/
def IsFirstIn (S : Finset (Fin n)) (x : Fin n) (π : Equiv.Perm (Fin n)) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, pos π x ≤ pos π y

/-! ## The swap bijection -/

lemma pos_swap_comp {a b : Fin n} (π : Equiv.Perm (Fin n)) (x : Fin n) :
    pos ((Equiv.swap a b) * π) x = pos π ((Equiv.swap a b) x) := by
  dsimp [pos]
  change ((Equiv.swap a b) * π)⁻¹ x = π⁻¹ ((Equiv.swap a b) x)
  rw [mul_inv_rev]
  rw [Equiv.swap_inv]
  rfl

/-- Composing with swap a b on the LEFT is a bijection on Perm(Fin n). -/
lemma swapComp_bijective {a b : Fin n} :
    Function.Bijective (fun (π : Equiv.Perm (Fin n)) => (Equiv.swap a b) * π) := by
  constructor
  · intro π₁ π₂ h
    apply_fun (fun φ => (Equiv.swap a b).symm * φ) at h
    simpa [mul_assoc] using h
  · intro π
    refine ⟨(Equiv.swap a b).symm * π, ?_⟩
    simp

/-- If a is first in S under π, then b is first under swap a b ∘ π. -/
lemma IsFirstIn_swap {S : Finset (Fin n)} {a b : Fin n} (hne : a ≠ b)
    (π : Equiv.Perm (Fin n)) (ha : IsFirstIn S a π) (hbS : b ∈ S) :
    IsFirstIn S b ((Equiv.swap a b) * π) := by
  rcases ha with ⟨haS, ha_min⟩
  let σ := Equiv.swap a b
  have hσa : σ a = b := by simp [σ]
  have hσb : σ b = a := by simp [σ]
  refine ⟨hbS, ?_⟩
  intro y hyS
  rw [pos_swap_comp π b, pos_swap_comp π y, hσb]
  -- Need: pos π a ≤ pos π (σ y)
  -- Since σ y ∈ S (σ permutes S), ha_min applies
  have hσy_S : σ y ∈ S := by
    -- σ swaps a and b, both in S, fixes others
    by_cases hya : y = a
    · subst y; simpa [σ]
    · by_cases hyb : y = b
      · subst y; simpa [σ]
      · have : σ y = y := Equiv.swap_apply_of_ne_of_ne hya hyb
        rw [this]; exact hyS
  exact ha_min (σ y) hσy_S

/-! ## Equal cardinality via bijection -/

/-- The sets of permutations where a is first vs where b is first have equal cardinality. -/
lemma card_firstSet_eq {S : Finset (Fin n)} {a b : Fin n}
    (haS : a ∈ S) (hbS : b ∈ S) (hne : a ≠ b) :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (IsFirstIn S a)).card =
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (IsFirstIn S b)).card := by
  let σ := Equiv.swap a b
  -- The map f(π) = σ * π is a bijection that maps firstSet S a to firstSet S b
  apply Finset.card_bij (fun π _ => σ * π) ?_ ?_ ?_
  · -- f maps firstSet a into firstSet b
    intro π hπ
    rw [Finset.mem_filter] at hπ
    rcases hπ with ⟨hπu, ha⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact IsFirstIn_swap hne π ha hbS
  · -- f is injective (follows from bijectivity)
    intro π₁ _ π₂ _ h
    exact (swapComp_bijective (a:=a) (b:=b)).1 h
  · -- f is surjective onto firstSet b
    intro π hπ
    rw [Finset.mem_filter] at hπ
    rcases hπ with ⟨hπu, hb⟩
    -- preimage: σ * π (since σ⁻¹ = σ, left-multiplying by σ maps back)
    have h_pre : IsFirstIn S a (σ * π) := by
      -- Apply IsFirstIn_swap with a↔b swapped
      have h := IsFirstIn_swap (Ne.symm hne) π hb haS
      simpa [σ, Equiv.swap_comm] using h
    refine ⟨σ * π, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_pre⟩, ?_⟩
    simp [σ]

/-! ## Partition: each permutation has exactly one first element -/

/-- For a nonempty S, each permutation has a unique first element in S. -/
lemma existsUnique_firstInSet (S : Finset (Fin n)) (hSne : S.Nonempty) (π : Equiv.Perm (Fin n)) :
    ∃! s, s ∈ S ∧ IsFirstIn S s π := by
  -- The set {pos π s | s ∈ S} is a nonempty finite set of Fin n, so it has a minimum
  -- The s that maps to that minimum is unique (since π.symm is injective)
  let positions : Finset (Fin n) := S.image (pos π)
  have hpos_ne : positions.Nonempty := by
    rcases hSne with ⟨s, hs⟩
    exact ⟨pos π s, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
  let p := positions.min' hpos_ne
  have hp_mem : p ∈ positions := Finset.min'_mem _ hpos_ne
  rcases Finset.mem_image.mp hp_mem with ⟨s, hsS, hsp⟩
  have h_first : IsFirstIn S s π := by
    refine ⟨hsS, ?_⟩
    intro y hyS
    have hy_pos : pos π y ∈ positions := Finset.mem_image.mpr ⟨y, hyS, rfl⟩
    have hp_le : p ≤ pos π y := Finset.min'_le _ _ hy_pos
    rw [← hsp] at hp_le
    exact hp_le
  refine ⟨s, ⟨hsS, h_first⟩, ?_⟩
  intro s' ⟨hs'S, hs'_first⟩
  have hpos_le : pos π s' ≤ pos π s := hs'_first.2 s hsS
  have hpos_ge : pos π s ≤ pos π s' := h_first.2 s' hs'S
  have hpos_eq : pos π s' = pos π s := le_antisymm hpos_le hpos_ge
  apply π.symm.injective
  exact hpos_eq

/-! ## Main symmetry theorem -/

/-- **Symmetry Lemma.**  For a nonempty set S ⊆ Fin n and s ∈ S, under a uniform
random permutation, P(s is first in S) = 1 / |S|.

Proof: All elements of S have equal probability by `card_firstSet_eq`.
Since the sum over t in S of P(t first) = 1 (each π has exactly one
first element), we get |S| × P(s first) = 1, hence P = 1 / |S|. -/
theorem isFirst_prob (S : Finset (Fin n)) (hSne : S.Nonempty) (s : Fin n) (hsS : s ∈ S) :
    ((Finset.filter (IsFirstIn S s) Finset.univ).card : ℝ) / (Nat.factorial n : ℝ) =
    1 / (S.card : ℝ) := by
  -- Let A_t = {π | IsFirstIn S t π}
  -- Step 1: All A_t have equal cardinality
  have h_eq_card : ∀ t ∈ S, ((Finset.filter (IsFirstIn S t) Finset.univ).card : ℝ) =
      ((Finset.filter (IsFirstIn S s) Finset.univ).card : ℝ) := by
    intro t htS
    by_cases hts : t = s
    · subst t; rfl
    · have hcard := card_firstSet_eq htS hsS hts
      -- This gives Nat equality; cast to ℝ
      exact_mod_cast hcard
  -- Step 2: The sets A_t for t ∈ S are pairwise disjoint
  have h_disjoint : ∀ t₁ t₂, t₁ ∈ S → t₂ ∈ S → t₁ ≠ t₂ →
      Disjoint (Finset.filter (IsFirstIn S t₁) Finset.univ)
               (Finset.filter (IsFirstIn S t₂) Finset.univ) := by
    intro t₁ t₂ ht₁ ht₂ hne
    apply Finset.disjoint_filter.2
    intro π _ h₁ h₂
    -- If π is in both filters, then both t₁ and t₂ are first in S for π
    -- This contradicts uniqueness from existsUnique_firstInSet
    rcases existsUnique_firstInSet S hSne π with ⟨t, ⟨htS, ht_first⟩, hunique⟩
    have heq : t₁ = t₂ := by
      have h1 := hunique t₁ ⟨ht₁, h₁⟩
      have h2 := hunique t₂ ⟨ht₂, h₂⟩
      exact h1.trans h2.symm
    exact hne heq
  -- Step 3: The sets cover Finset.univ
  have h_cover : (Finset.biUnion S (fun t => Finset.filter (IsFirstIn S t) Finset.univ)) =
      Finset.univ := by
    apply Finset.Subset.antisymm
    · exact Finset.subset_univ _
    · intro π hπ
      have hπu : π ∈ Finset.univ := Finset.mem_univ _
      rcases existsUnique_firstInSet S hSne π with ⟨t, ⟨htS, ht_first⟩, _⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨t, htS, Finset.mem_filter.mpr ⟨hπu, ht_first⟩⟩
  -- Step 4: Sum of cardinalities = |univ| = n!
  have h_total_nat : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    simp [Fintype.card_perm]
  have h_pairwise : (S : Set (Fin n)).PairwiseDisjoint
      (fun t => Finset.filter (IsFirstIn S t) Finset.univ) := by
    intro t₁ ht₁ t₂ ht₂ hne
    exact h_disjoint t₁ t₂ ht₁ ht₂ hne
  have h_sum_card : (∑ t ∈ S, (Finset.filter (IsFirstIn S t) Finset.univ).card) =
      Nat.factorial n := by
    calc
      (∑ t ∈ S, (Finset.filter (IsFirstIn S t) Finset.univ).card)
          = (Finset.biUnion S (fun t => Finset.filter (IsFirstIn S t) Finset.univ)).card := by
        rw [Finset.card_biUnion (h := h_pairwise)]
      _ = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by rw [h_cover]
      _ = Nat.factorial n := h_total_nat
  -- Step 5: Since all |A_t| are equal, S.card * |A_s| = n!
  -- Hence |A_s| / n! = 1 / S.card
  have h_total_real : (∑ t ∈ S, ((Finset.filter (IsFirstIn S t) Finset.univ).card : ℝ)) =
      (Nat.factorial n : ℝ) := by exact_mod_cast h_sum_card
  have h_all_eq : (∑ t ∈ S, ((Finset.filter (IsFirstIn S t) Finset.univ).card : ℝ)) =
      (S.card : ℝ) * ((Finset.filter (IsFirstIn S s) Finset.univ).card : ℝ) := by
    calc
      (∑ t ∈ S, ((Finset.filter (IsFirstIn S t) Finset.univ).card : ℝ))
          = (∑ t ∈ S, ((Finset.filter (IsFirstIn S s) Finset.univ).card : ℝ)) :=
        Finset.sum_congr rfl (fun t ht => by rw [h_eq_card t ht])
      _ = (S.card : ℝ) * ((Finset.filter (IsFirstIn S s) Finset.univ).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  rw [h_all_eq] at h_total_real
  have hS_card_ne_zero : (S.card : ℝ) ≠ 0 := by
    have hpos : 0 < S.card := Finset.card_pos.mpr hSne
    positivity
  have h_nfac_ne_zero : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hS_card_ne_zero, h_nfac_ne_zero]
  linarith

/-! ## Application to quicksort comparison probability -/

/-- Convert i..j (all < n) to Finset (Fin n) via an embedding. -/
def rangeFin (n i j : ℕ) (_hij : i ≤ j) (hjn : j < n) : Finset (Fin n) :=
  ((Finset.Icc i j).attach).map
    ⟨fun ⟨k, hk⟩ =>
        ⟨k, lt_of_le_of_lt (Finset.mem_Icc.mp hk).2 hjn⟩,
     fun ⟨a, ha⟩ ⟨b, hb⟩ h => by
        apply Subtype.ext
        simpa using congrArg Fin.val h⟩

/-- ranks i,j are compared iff first of i,...,j is i or j. -/
def comparedInQuicksort (n i j : ℕ) (hij : i < j) (hjn : j < n) (π : Equiv.Perm (Fin n)) : Prop :=
  have hi : i < n := lt_trans hij hjn
  let si : Fin n := ⟨i, hi⟩
  let sj : Fin n := ⟨j, hjn⟩
  let S := rangeFin n i j (Nat.le_of_lt hij) hjn
  IsFirstIn S si π ∨ IsFirstIn S sj π

/-- |rangeFin n i j| = j-i+1. -/
lemma card_rangeFin (n i j : ℕ) (_hij : i ≤ j) (hjn : j < n) :
    (rangeFin n i j _hij hjn).card = j - i + 1 := by
  unfold rangeFin
  rw [Finset.card_map]
  simp
  omega

/-- **CLRS Theorem 7.3.** P(compared) = 2/(j-i+1). -/
theorem compared_prob (n i j : ℕ) (hij : i < j) (hjn : j < n) :
    ((Finset.filter (comparedInQuicksort n i j hij hjn) Finset.univ).card : ℝ) /
      (Nat.factorial n : ℝ) = (2 : ℝ) / ((j - i + 1 : ℕ) : ℝ) := by
  have hi : i < n := lt_trans hij hjn
  have h_le : i ≤ j := Nat.le_of_lt hij
  let si : Fin n := ⟨i, hi⟩
  let sj : Fin n := ⟨j, hjn⟩
  let S := rangeFin n i j h_le hjn
  have hcard_S : S.card = j - i + 1 := card_rangeFin n i j h_le hjn
  have hS_si : si ∈ S := by
    dsimp [S, rangeFin]
    have hi_mem : i ∈ Finset.Icc i j := Finset.mem_Icc.mpr ⟨le_refl i, h_le⟩
    refine Finset.mem_map.mpr ⟨⟨i, hi_mem⟩, Finset.mem_attach _ _, ?_⟩
    ext; rfl
  have hS_sj : sj ∈ S := by
    dsimp [S, rangeFin]
    have hj_mem : j ∈ Finset.Icc i j := Finset.mem_Icc.mpr ⟨h_le, le_refl j⟩
    refine Finset.mem_map.mpr ⟨⟨j, hj_mem⟩, Finset.mem_attach _ _, ?_⟩
    ext; rfl
  have hSne : S.Nonempty := ⟨si, hS_si⟩
  have hne : si ≠ sj := by
    intro h
    have hval : i = j := Fin.ext_iff.mp h
    omega
  have h_disjoint : Disjoint
      (Finset.filter (IsFirstIn S si) Finset.univ)
      (Finset.filter (IsFirstIn S sj) Finset.univ) := by
    apply Finset.disjoint_filter.2
    intro π _ hsi hsj
    rcases hsi with ⟨_, hsi_min⟩; rcases hsj with ⟨_, hsj_min⟩
    have hle1 : pos π si ≤ pos π sj := hsi_min sj hS_sj
    have hle2 : pos π sj ≤ pos π si := hsj_min si hS_si
    have heq : pos π si = pos π sj := le_antisymm hle1 hle2
    apply hne; apply π.symm.injective; exact heq
  have h_si_prob : ((Finset.filter (IsFirstIn S si) Finset.univ).card : ℝ) /
      (Nat.factorial n : ℝ) = 1 / (S.card : ℝ) :=
    isFirst_prob S hSne si hS_si
  have h_sj_prob : ((Finset.filter (IsFirstIn S sj) Finset.univ).card : ℝ) /
      (Nat.factorial n : ℝ) = 1 / (S.card : ℝ) :=
    isFirst_prob S hSne sj hS_sj
  have h_union : (Finset.filter (comparedInQuicksort n i j hij hjn) Finset.univ) =
      (Finset.filter (IsFirstIn S si) Finset.univ) ∪
      (Finset.filter (IsFirstIn S sj) Finset.univ) := by
    ext π; constructor
    · intro h; rcases Finset.mem_filter.mp h with ⟨hu, hc⟩
      unfold comparedInQuicksort at hc
      rcases hc with (h | h)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, h⟩)
    · intro h; rcases Finset.mem_union.mp h with (h' | h')
      · rcases Finset.mem_filter.mp h' with ⟨hu, h⟩
        refine Finset.mem_filter.mpr ⟨hu, ?_⟩
        unfold comparedInQuicksort
        exact Or.inl h
      · rcases Finset.mem_filter.mp h' with ⟨hu, h⟩
        refine Finset.mem_filter.mpr ⟨hu, ?_⟩
        unfold comparedInQuicksort
        exact Or.inr h
  rw [h_union, Finset.card_union_of_disjoint h_disjoint, Nat.cast_add]
  have h_nfac_ne_zero : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have h_card_ne_zero : (S.card : ℝ) ≠ 0 := by
    have hpos : 0 < S.card := Finset.card_pos.mpr hSne
    positivity
  -- Goal: (|A_si| + |A_sj|) / n! = 2 / (j-i+1)
  -- From h_si_prob: |A_si|/n! = 1/S.card
  -- From h_sj_prob: |A_sj|/n! = 1/S.card
  -- Add them: (|A_si| + |A_sj|)/n! = 2/S.card = 2/(j-i+1)
  have h_sum : ((Finset.filter (IsFirstIn S si) Finset.univ).card : ℝ) +
      ((Finset.filter (IsFirstIn S sj) Finset.univ).card : ℝ) =
      (2 : ℝ) * (Nat.factorial n : ℝ) / (S.card : ℝ) := by
    field_simp [h_nfac_ne_zero, h_card_ne_zero] at h_si_prob h_sj_prob ⊢
    linarith [h_si_prob, h_sj_prob]
  calc
    (((Finset.filter (IsFirstIn S si) Finset.univ).card : ℝ) +
      ((Finset.filter (IsFirstIn S sj) Finset.univ).card : ℝ)) / (Nat.factorial n : ℝ)
        = ((2 : ℝ) * (Nat.factorial n : ℝ) / (S.card : ℝ)) / (Nat.factorial n : ℝ) := by rw [h_sum]
    _ = (2 : ℝ) / (S.card : ℝ) := by
      field_simp [h_nfac_ne_zero]
    _ = (2 : ℝ) / ((j - i + 1 : ℕ) : ℝ) := by rw [hcard_S]

end Chapter07
end CLRS
