import Mathlib

/-!
# CLRS Section 21.1 - Disjoint-Set Operations

Abstract specification of disjoint sets as a partition of `Fin n`.
-/

namespace CLRS
namespace Chapter21

/-- A collection of disjoint sets that partition `Fin n`. -/
structure DisjointSets (n : Nat) where
  sets : Finset (Finset (Fin n))
  pairwise_disjoint : (sets : Set (Finset (Fin n))).PairwiseDisjoint id
  covers_univ : ∀ i : Fin n, ∃ s ∈ sets, i ∈ s

namespace DisjointSets

variable {n : Nat}

theorem unique_set_containing (ds : DisjointSets n) (i : Fin n) :
    ∃! s, s ∈ ds.sets ∧ i ∈ s := by
  obtain ⟨s, hs, hi⟩ := ds.covers_univ i
  refine ⟨s, ⟨hs, hi⟩, ?_⟩
  intro t ⟨ht, hi_t⟩
  by_cases h_eq : s = t
  · exact h_eq.symm
  · have hdisj := ds.pairwise_disjoint hs ht h_eq
    have hmem : i ∈ s ∩ t := Finset.mem_inter.mpr ⟨hi, hi_t⟩
    have h_empty : s ∩ t = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
    rw [h_empty] at hmem
    simp at hmem

noncomputable def findSet (ds : DisjointSets n) (i : Fin n) : Finset (Fin n) :=
  Classical.choose (ds.unique_set_containing i)

theorem findSet_mem_sets (ds : DisjointSets n) (i : Fin n) : findSet ds i ∈ ds.sets :=
  ((Classical.choose_spec (ds.unique_set_containing i)).1).1

theorem findSet_mem (ds : DisjointSets n) (i : Fin n) : i ∈ findSet ds i :=
  ((Classical.choose_spec (ds.unique_set_containing i)).1).2

theorem findSet_unique (ds : DisjointSets n) (i : Fin n) (s : Finset (Fin n))
    (hs : s ∈ ds.sets) (hi : i ∈ s) : findSet ds i = s :=
  ((ds.unique_set_containing i).unique
    (Classical.choose_spec (ds.unique_set_containing i)).1 ⟨hs, hi⟩)

theorem same_set_iff_findSet_eq (ds : DisjointSets n) (i j : Fin n) :
    (∃ s ∈ ds.sets, i ∈ s ∧ j ∈ s) ↔ findSet ds i = findSet ds j := by
  constructor
  · intro ⟨s, hs, hi, hj⟩
    have hi_unique := ds.findSet_unique i s hs hi
    have hj_unique := ds.findSet_unique j s hs hj
    rw [hi_unique, hj_unique]
  · intro h
    refine ⟨findSet ds i, findSet_mem_sets ds i, findSet_mem ds i, ?_⟩
    rw [h]
    exact findSet_mem ds j

def makeSet (ds : DisjointSets n) (i : Fin n) : DisjointSets n where
  sets := { {i} } ∪ (ds.sets.image (λ s => s.erase i))
  pairwise_disjoint := by
    rintro u hu v hv hne
    have hu' : u = {i} ∨ ∃ s, s ∈ ds.sets ∧ s.erase i = u := by
      simpa [Finset.mem_union, Finset.mem_image] using hu
    have hv' : v = {i} ∨ ∃ s, s ∈ ds.sets ∧ s.erase i = v := by
      simpa [Finset.mem_union, Finset.mem_image] using hv
    rcases hu' with (rfl | ⟨s₁, hs₁, rfl⟩)
    · rcases hv' with (rfl | ⟨s₂, hs₂, rfl⟩)
      · exact (hne rfl).elim
      · exact Finset.disjoint_left.2 (λ x hx_sing hx_erase =>
          (Finset.mem_erase.1 hx_erase).1 (by simpa using hx_sing))
    · rcases hv' with (rfl | ⟨s₂, hs₂, rfl⟩)
      · exact Finset.disjoint_left.2 (λ x hx_erase hx_sing =>
          (Finset.mem_erase.1 hx_erase).1 (by simpa using hx_sing))
      · by_cases hs_eq : s₁ = s₂
        · subst hs_eq; exfalso; exact hne rfl
        · have hdisj := ds.pairwise_disjoint hs₁ hs₂ hs_eq
          exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
            (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hdisj)
  covers_univ := by
    intro j
    by_cases hj_i : j = i
    · subst j; exact ⟨{i}, Finset.mem_union_left _ (by simp), by simp⟩
    · obtain ⟨s, hs, hj_s⟩ := ds.covers_univ j
      have hj_erase : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hj_i, hj_s⟩
      exact ⟨s.erase i,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩), hj_erase⟩

noncomputable def union (ds : DisjointSets n) (i j : Fin n) : DisjointSets n :=
  let si := findSet ds i
  let sj := findSet ds j
  if h_eq : si = sj then ds else
  { sets := { si ∪ sj } ∪ ((ds.sets.erase si).erase sj)
    pairwise_disjoint := by
      have hsi : si ∈ ds.sets := findSet_mem_sets ds i
      have hsj : sj ∈ ds.sets := findSet_mem_sets ds j
      intro u hu v hv hne
      rcases Finset.mem_union.1 hu with (hu_union | hu_erased)
      · have hu_eq : u = si ∪ sj := Finset.mem_singleton.1 hu_union; subst hu_eq
        rcases Finset.mem_union.1 hv with (hv_union | hv_erased)
        · exact (hne (Finset.mem_singleton.1 hv_union).symm).elim
        · rcases Finset.mem_erase.1 hv_erased with ⟨hv_ne_sj, hv_erased_si⟩
          rcases Finset.mem_erase.1 hv_erased_si with ⟨hv_ne_si, hv_mem⟩
          have hdisj_si : Disjoint si v := ds.pairwise_disjoint hsi hv_mem (Ne.symm hv_ne_si)
          have hdisj_sj : Disjoint sj v := ds.pairwise_disjoint hsj hv_mem (Ne.symm hv_ne_sj)
          exact Finset.disjoint_union_left.mpr ⟨hdisj_si, hdisj_sj⟩
      · rcases Finset.mem_erase.1 hu_erased with ⟨hu_ne_sj, hu_erased_si⟩
        rcases Finset.mem_erase.1 hu_erased_si with ⟨hu_ne_si, hu_mem⟩
        rcases Finset.mem_union.1 hv with (hv_union | hv_erased)
        · have hv_eq : v = si ∪ sj := Finset.mem_singleton.1 hv_union; subst hv_eq
          have hdisj_si : Disjoint u si := ds.pairwise_disjoint hu_mem hsi hu_ne_si
          have hdisj_sj : Disjoint u sj := ds.pairwise_disjoint hu_mem hsj hu_ne_sj
          exact Finset.disjoint_union_right.mpr ⟨hdisj_si, hdisj_sj⟩
        · rcases Finset.mem_erase.1 hv_erased with ⟨hv_ne_sj, hv_erased_si⟩
          rcases Finset.mem_erase.1 hv_erased_si with ⟨hv_ne_si, hv_mem⟩
          exact ds.pairwise_disjoint hu_mem hv_mem hne
    covers_univ := by
      intro k
      have hcov := ds.covers_univ k
      rcases hcov with ⟨s, hs, hk⟩
      by_cases hs_si : s = si
      · subst s
        exact ⟨si ∪ sj, Finset.mem_union_left _ (by simp), Finset.mem_union_left _ hk⟩
      · by_cases hs_sj : s = sj
        · subst s
          exact ⟨si ∪ sj, Finset.mem_union_left _ (by simp), Finset.mem_union_right _ hk⟩
        · have h_erased : s ∈ (ds.sets.erase si).erase sj :=
            Finset.mem_erase.mpr ⟨hs_sj, Finset.mem_erase.mpr ⟨hs_si, hs⟩⟩
          exact ⟨s, Finset.mem_union_right _ h_erased, hk⟩
  }

theorem union_merges (ds : DisjointSets n) (i j : Fin n) :
    ∃ s ∈ (union ds i j).sets, i ∈ s ∧ j ∈ s := by
  by_cases h_eq : findSet ds i = findSet ds j
  · have h_union_eq : union ds i j = ds := by
      unfold union
      simp [h_eq]
    rw [h_union_eq]
    exact ⟨findSet ds i, findSet_mem_sets ds i, findSet_mem ds i,
      by rw [h_eq]; exact findSet_mem ds j⟩
  · have h_union_sets : (union ds i j).sets =
      ({(findSet ds i) ∪ (findSet ds j)} : Finset (Finset (Fin n))) ∪
      ((ds.sets.erase (findSet ds i)).erase (findSet ds j)) := by
      unfold union
      simp [h_eq]
    rw [h_union_sets]
    refine ⟨(findSet ds i) ∪ (findSet ds j), Finset.mem_union_left _ (by simp),
      Finset.mem_union_left _ (findSet_mem ds i),
      Finset.mem_union_right _ (findSet_mem ds j)⟩

theorem partition_invariant (ds : DisjointSets n) :
    (ds.sets : Set (Finset (Fin n))).PairwiseDisjoint id ∧
    ∀ i : Fin n, ∃ s ∈ ds.sets, i ∈ s :=
  ⟨ds.pairwise_disjoint, ds.covers_univ⟩

theorem makeSet_preserves_partition (ds : DisjointSets n) (i : Fin n) :
    ((ds.makeSet i).sets : Set (Finset (Fin n))).PairwiseDisjoint id ∧
    ∀ j : Fin n, ∃ s ∈ (ds.makeSet i).sets, j ∈ s :=
  partition_invariant (ds.makeSet i)

theorem union_preserves_partition (ds : DisjointSets n) (i j : Fin n) :
    ((ds.union i j).sets : Set (Finset (Fin n))).PairwiseDisjoint id ∧
    ∀ k : Fin n, ∃ s ∈ (ds.union i j).sets, k ∈ s :=
  partition_invariant (ds.union i j)

end DisjointSets

end Chapter21
end CLRS
