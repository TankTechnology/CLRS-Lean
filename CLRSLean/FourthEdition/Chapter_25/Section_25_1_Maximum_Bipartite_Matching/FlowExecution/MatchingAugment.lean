import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S2_Alternating_Paths

/-!
# Concrete matching augmentation

The textbook augmentation proof is refined here to return the matching built
by its insert/swap execution.  The attached counter is accumulated by that
same recursion: one unit for a final insertion and two units for each
erase/insert swap.
-/

namespace CLRS

open Finset Classical

namespace Matchings

open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}

/-- Insert a single augmenting edge into a matching. -/
noncomputable def insertAugmentingEdge (M : Matching V G) {l r : V}
    (hE : (l, r) ∈ G.E) (_hM : (l, r) ∉ M.edges)
    (hl : M.IsUnmatchedLeft l) (hr : M.IsUnmatchedRight r) : Matching V G :=
  { edges := insert (l, r) M.edges
    h_subset := Finset.insert_subset hE M.h_subset
    h_unique_left := by
      intro l₂ r₁ r₂ h₁ h₂
      simp only [Finset.mem_insert, Prod.mk.injEq] at h₁ h₂
      rcases h₁ with ⟨e1a, e1b⟩ | h₁ <;>
        rcases h₂ with ⟨e2a, e2b⟩ | h₂
      · exact e1b.trans e2b.symm
      · exact (hl r₂ (e1a ▸ h₂)).elim
      · exact (hl r₁ (e2a ▸ h₁)).elim
      · exact M.h_unique_left l₂ r₁ r₂ h₁ h₂
    h_unique_right := by
      intro l₁ l₂ r₃ h₁ h₂
      simp only [Finset.mem_insert, Prod.mk.injEq] at h₁ h₂
      rcases h₁ with ⟨e1a, e1b⟩ | h₁ <;>
        rcases h₂ with ⟨e2a, e2b⟩ | h₂
      · exact e1a.trans e2a.symm
      · exact (hr l₂ (e1b ▸ h₂)).elim
      · exact (hr l₁ (e2b ▸ h₁)).elim
      · exact M.h_unique_right l₁ l₂ r₃ h₁ h₂ }

theorem insertAugmentingEdge_size (M : Matching V G) {l r : V}
    (hE : (l, r) ∈ G.E) (hM : (l, r) ∉ M.edges)
    (hl : M.IsUnmatchedLeft l) (hr : M.IsUnmatchedRight r) :
    (insertAugmentingEdge M hE hM hl hr).size = M.size + 1 := by
  show (insert (l, r) M.edges).card = M.size + 1
  rw [Finset.card_insert_of_notMem hM]
  rfl

/-- Replace the matched edge `(l',r)` by the nonmatching edge `(l,r)`. -/
noncomputable def swapAugmentingEdge (M : Matching V G) {l r l' : V}
    (hE : (l, r) ∈ G.E) (_hM : (l, r) ∉ M.edges)
    (hM' : (l', r) ∈ M.edges) (hl : M.IsUnmatchedLeft l)
    (_hne : l ≠ l') : Matching V G :=
  { edges := insert (l, r) (M.edges.erase (l', r))
    h_subset := Finset.insert_subset hE
      ((Finset.erase_subset _ _).trans M.h_subset)
    h_unique_left := by
      intro l₂ r₁ r₂ h₁ h₂
      simp only [Finset.mem_insert, Finset.mem_erase, Prod.mk.injEq] at h₁ h₂
      rcases h₁ with ⟨e1a, e1b⟩ | ⟨-, h₁⟩ <;>
        rcases h₂ with ⟨e2a, e2b⟩ | ⟨-, h₂⟩
      · exact e1b.trans e2b.symm
      · exact (hl r₂ (e1a ▸ h₂)).elim
      · exact (hl r₁ (e2a ▸ h₁)).elim
      · exact M.h_unique_left l₂ r₁ r₂ h₁ h₂
    h_unique_right := by
      intro l₁ l₂ r₃ h₁ h₂
      simp only [Finset.mem_insert, Finset.mem_erase, Prod.mk.injEq] at h₁ h₂
      rcases h₁ with ⟨e1a, e1b⟩ | ⟨hne₁, h₁⟩ <;>
        rcases h₂ with ⟨e2a, e2b⟩ | ⟨hne₂, h₂⟩
      · exact e1a.trans e2a.symm
      · exact (hne₂
          (Prod.ext (M.h_unique_right l₂ l' r (e1b ▸ h₂) hM') e1b)).elim
      · exact (hne₁
          (Prod.ext (M.h_unique_right l₁ l' r (e2b ▸ h₁) hM') e2b)).elim
      · exact M.h_unique_right l₁ l₂ r₃ h₁ h₂ }

theorem swapAugmentingEdge_size (M : Matching V G) {l r l' : V}
    (hE : (l, r) ∈ G.E) (hM : (l, r) ∉ M.edges)
    (hM' : (l', r) ∈ M.edges) (hl : M.IsUnmatchedLeft l)
    (hne : l ≠ l') :
    (swapAugmentingEdge M hE hM hM' hl hne).size = M.size := by
  show (insert (l, r) (M.edges.erase (l', r))).card = M.size
  have hnotin : (l, r) ∉ M.edges.erase (l', r) := fun h =>
    hM (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hnotin, Finset.card_erase_of_mem hM',
    Nat.sub_add_cancel (Finset.card_pos.mpr ⟨(l', r), hM'⟩)]
  rfl

/-- The left endpoint removed by a swap is unmatched afterwards. -/
theorem swapAugmentingEdge_unmatched (M : Matching V G) {l r l' : V}
    (hE : (l, r) ∈ G.E) (hM : (l, r) ∉ M.edges)
    (hM' : (l', r) ∈ M.edges) (hl : M.IsUnmatchedLeft l)
    (hne : l ≠ l') :
    (swapAugmentingEdge M hE hM hM' hl hne).IsUnmatchedLeft l' := by
  intro r₂ h
  simp only [swapAugmentingEdge, Finset.mem_insert, Finset.mem_erase,
    Prod.mk.injEq] at h
  rcases h with ⟨e1, -⟩ | ⟨hne2, hmem⟩
  · exact hne e1.symm
  · exact hne2
      (Prod.ext rfl (M.h_unique_left l' r r₂ hM' hmem).symm)

theorem mem_swapAugmentingEdge_iff (M : Matching V G) {l r l' : V}
    (hE : (l, r) ∈ G.E) (hM : (l, r) ∉ M.edges)
    (hM' : (l', r) ∈ M.edges) (hl : M.IsUnmatchedLeft l)
    (hne : l ≠ l') (e : V × V) :
    e ∈ (swapAugmentingEdge M hE hM hM' hl hne).edges ↔
      e = (l, r) ∨ (e ∈ M.edges ∧ e ≠ (l', r)) := by
  simp only [swapAugmentingEdge, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h2, h1⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h2, h1⟩

/-- Result of the concrete alternating-path update.  Its correctness and
linear work bound travel with the returned execution. -/
structure MatchingAugmentRun (G : BipartiteGraph V) (M : Matching V G)
    (p : List V) where
  matching : Matching V G
  work : Nat
  size_eq : matching.size = M.size + 1
  work_le : work ≤ p.length

/-- The concrete first swap of a nontrivial augmenting path, packaged with
the proof that its remaining suffix is augmenting for the new matching. -/
structure AugmentingSwapStep (G : BipartiteGraph V) (M : Matching V G)
    (rest : List V) where
  matching : Matching V G
  size_eq : matching.size = M.size
  tail_isAugmenting : IsAugmentingPath G matching rest

/-- Execute the first erase/insert swap of a path with at least four
vertices. -/
noncomputable def augmentingSwapStep {M : Matching V G} {l r l' : V}
    {rest : List V} (hp : IsAugmentingPath G M (l :: r :: l' :: rest)) :
    AugmentingSwapStep G M (l' :: rest) := by
  have hnePath : l :: r :: l' :: rest ≠ [] := by simp
  have hnd := hp.nodup
  rw [List.nodup_cons] at hnd
  obtain ⟨hlNotin, hnd⟩ := hnd
  rw [List.nodup_cons] at hnd
  obtain ⟨hrNotin, hnd⟩ := hnd
  have hfw := hp.forward (l, r) List.mem_cons_self
  have hbw := hp.backward (l', r) List.mem_cons_self
  have hlu : M.IsUnmatchedLeft l := hp.head_unmatched hnePath
  have hll : l ≠ l' := fun h =>
    hlNotin (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
  let M₁ := swapAugmentingEdge M hfw.1 hfw.2 hbw hlu hll
  have hM₁size : M₁.size = M.size := by
    exact swapAugmentingEdge_size M hfw.1 hfw.2 hbw hlu hll
  have hM₁un : M₁.IsUnmatchedLeft l' := by
    exact swapAugmentingEdge_unmatched M hfw.1 hfw.2 hbw hlu hll
  have hM₁mem (e : V × V) : e ∈ M₁.edges ↔
      e = (l, r) ∨ (e ∈ M.edges ∧ e ≠ (l', r)) := by
    exact mem_swapAugmentingEdge_iff M hfw.1 hfw.2 hbw hlu hll e
  have hlast : (l :: r :: l' :: rest).getLast hnePath =
      (l' :: rest).getLast (by simp) := by
    simp [List.getLast_cons]
  refine
    { matching := M₁
      size_eq := hM₁size
      tail_isAugmenting := ?_ }
  refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have heven := hp.length_even
    have hge := hp.length_ge
    simp only [List.length_cons] at heven hge ⊢
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩
  · have heven := hp.length_even
    have hge := hp.length_ge
    simp only [List.length_cons] at heven hge ⊢
    obtain ⟨k, hk⟩ := heven
    omega
  · intro _
    exact (G.hE_subset _ (M.h_subset hbw)).1
  · intro _ r₂ h
    exact hM₁un r₂ h
  · intro _
    have h := hp.getLast_mem_R hnePath
    rwa [hlast] at h
  · intro _ l₂ h
    rw [hM₁mem] at h
    rcases h with h | ⟨hmem, -⟩
    · obtain ⟨-, heq⟩ := Prod.mk.inj h
      have hrmem : r ∈ l' :: rest := by
        have hlastMem := List.getLast_mem (l := l' :: rest) (by simp)
        rwa [heq] at hlastMem
      exact absurd hrmem hrNotin
    · exact hp.getLast_unmatched hnePath l₂ (hlast ▸ hmem)
  · intro e he
    have hf := hp.forward e (List.mem_cons_of_mem _ he)
    refine ⟨hf.1, fun hmem => ?_⟩
    rw [hM₁mem] at hmem
    rcases hmem with h | ⟨hmem, -⟩
    · obtain ⟨e1, -⟩ := Prod.mk.inj h
      have hm := fst_mem_of_mem_altEdges_left he
      rw [e1] at hm
      exact hlNotin (List.mem_cons_of_mem _ hm)
    · exact hf.2 hmem
  · intro e he
    have hb := hp.backward e (List.mem_cons_of_mem _ he)
    have hne : e ≠ (l', r) := by
      intro hcontra
      have hm := snd_mem_of_mem_altEdges_right he
      rw [hcontra] at hm
      exact hrNotin hm
    exact (hM₁mem e).mpr (Or.inr ⟨hb, hne⟩)

/-- Execute all swaps and the final insertion along an augmenting path. -/
noncomputable def augmentMatchingAlong (M : Matching V G) (p : List V)
    (hp : IsAugmentingPath G M p) : MatchingAugmentRun G M p :=
  match p with
  | [] => by
      exfalso
      simpa using hp.length_ge
  | [_] => by
      exfalso
      simpa using hp.length_ge
  | [l, r] => by
      have hfw := hp.forward (l, r) List.mem_cons_self
      have hne : l :: [r] ≠ [] := by simp
      let M' := insertAugmentingEdge M hfw.1 hfw.2
        (hp.head_unmatched hne) (hp.getLast_unmatched hne)
      exact
        { matching := M'
          work := 1
          size_eq := by
            exact insertAugmentingEdge_size M hfw.1 hfw.2
              (hp.head_unmatched hne) (hp.getLast_unmatched hne)
          work_le := by simp }
  | l :: r :: l' :: rest => by
      let step := augmentingSwapStep hp
      let tail := augmentMatchingAlong step.matching (l' :: rest)
        step.tail_isAugmenting
      exact
        { matching := tail.matching
          work := 2 + tail.work
          size_eq := by
            calc
              tail.matching.size = step.matching.size + 1 := tail.size_eq
              _ = M.size + 1 := by rw [step.size_eq]
          work_le := by
            have htail := tail.work_le
            simp only [List.length_cons] at htail ⊢
            omega }
termination_by p.length

/-- Concrete augmentation increases the matching size by exactly one. -/
theorem augmentMatchingAlong_size (M : Matching V G) (p : List V)
    (hp : IsAugmentingPath G M p) :
    (augmentMatchingAlong M p hp).matching.size = M.size + 1 :=
  (augmentMatchingAlong M p hp).size_eq

/-- The attached update work is at most the path's number of vertices. -/
theorem augmentMatchingAlong_work_le (M : Matching V G) (p : List V)
    (hp : IsAugmentingPath G M p) :
    (augmentMatchingAlong M p hp).work ≤ p.length :=
  (augmentMatchingAlong M p hp).work_le

/-- A simple augmenting path update uses at most one unit per graph vertex. -/
theorem augmentMatchingAlong_work_le_vertexCard (M : Matching V G)
    (p : List V) (hp : IsAugmentingPath G M p) :
    (augmentMatchingAlong M p hp).work ≤ Fintype.card V := by
  exact (augmentMatchingAlong_work_le M p hp).trans
    (List.Nodup.length_le_card hp.nodup)


end Matchings
end CLRS
