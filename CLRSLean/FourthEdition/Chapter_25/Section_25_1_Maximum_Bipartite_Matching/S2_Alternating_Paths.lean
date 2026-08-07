import CLRSLean.Chapter_26.Section_26_3_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S1_Matching_API

/-!
# S2. Alternating paths and augmentation

Alternating-path infrastructure: the `altEdges` decomposition of a vertex
list into forward and backward edges, the `IsAugmentingPath` structure, and
the forward direction of Berge's lemma — an augmenting path yields a matching
that is larger by one.

Main results:

- `IsAugmentingPath`: alternating vertex-simple paths with unmatched endpoints
- `exists_augment_single` and the swap step: single-edge building blocks
- `exists_augment`: augmentation theorem (CLRS §25.1, Berge, forward
  direction)
- `not_isMaximum_of_isAugmentingPath`: an augmenting path certifies
  non-maximality
-/
namespace CLRS

open Finset Classical

namespace Matchings
open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}

/-- The alternating edges of a vertex list, in canonical `(L, R)` orientation.
`(altEdges p).1` is the list of *forward* edges `(p₀,p₁), (p₂,p₃), …` and
`(altEdges p).2` is the list of *backward* edges `(p₂,p₁), (p₄,p₃), …`. -/
def altEdges : List V → List (V × V) × List (V × V)
  | [] => ([], [])
  | [_] => ([], [])
  | l :: r :: rest =>
      let recRes := altEdges rest
      ((l, r) :: recRes.1,
       match rest with
       | [] => recRes.2
       | l' :: _ => (l', r) :: recRes.2)

/-- The first component of a forward edge occurs in the path. -/
lemma fst_mem_of_mem_altEdges_left {p : List V} {e : V × V}
    (h : e ∈ (altEdges p).1) : e.1 ∈ p := by
  induction p using altEdges.induct with
  | case1 => simp [altEdges] at h
  | case2 => simp [altEdges] at h
  | case3 l r rest ih =>
    simp only [altEdges, List.mem_cons] at h
    rcases h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))

/-- The second component of a forward edge occurs in the path. -/
lemma snd_mem_of_mem_altEdges_left {p : List V} {e : V × V}
    (h : e ∈ (altEdges p).1) : e.2 ∈ p := by
  induction p using altEdges.induct with
  | case1 => simp [altEdges] at h
  | case2 => simp [altEdges] at h
  | case3 l r rest ih =>
    simp only [altEdges, List.mem_cons] at h
    rcases h with h | h
    · exact h ▸ List.mem_cons_of_mem _ (List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))

/-- The first component of a backward edge occurs in the path. -/
lemma fst_mem_of_mem_altEdges_right {p : List V} {e : V × V}
    (h : e ∈ (altEdges p).2) : e.1 ∈ p := by
  induction p using altEdges.induct with
  | case1 => simp [altEdges] at h
  | case2 => simp [altEdges] at h
  | case3 l r rest ih =>
    cases rest with
    | nil => simp [altEdges] at h
    | cons l' u =>
      simp only [altEdges, List.mem_cons] at h
      rcases h with h | h
      · exact h ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))

/-- The second component of a backward edge occurs in the path. -/
lemma snd_mem_of_mem_altEdges_right {p : List V} {e : V × V}
    (h : e ∈ (altEdges p).2) : e.2 ∈ p := by
  induction p using altEdges.induct with
  | case1 => simp [altEdges] at h
  | case2 => simp [altEdges] at h
  | case3 l r rest ih =>
    cases rest with
    | nil => simp [altEdges] at h
    | cons l' u =>
      simp only [altEdges, List.mem_cons] at h
      rcases h with h | h
      · exact h ▸ List.mem_cons_of_mem _ (List.mem_cons_self)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))

/-- An **augmenting path** for a matching `M` in a bipartite graph `G`
(CLRS §25.1): an even-length, vertex-simple list `p = [l₀, r₀, l₁, r₁, …]`
whose forward edges `(lᵢ, rᵢ)` are non-matching graph edges, whose backward
edges `(lᵢ₊₁, rᵢ)` are matching edges, and whose two endpoints are unmatched
in `M`. -/
structure IsAugmentingPath (G : BipartiteGraph V) (M : Matching V G)
    (p : List V) : Prop where
  /-- No vertex repeats along the path. -/
  nodup : p.Nodup
  /-- The path has even length. -/
  length_even : Even p.length
  /-- The path has at least two vertices. -/
  length_ge : 2 ≤ p.length
  /-- The path starts on the left. -/
  head_mem_L : ∀ h : p ≠ [], p.head h ∈ G.L
  /-- The path's start vertex is unmatched. -/
  head_unmatched : ∀ h : p ≠ [], ∀ r, (p.head h, r) ∉ M.edges
  /-- The path ends on the right. -/
  getLast_mem_R : ∀ h : p ≠ [], p.getLast h ∈ G.R
  /-- The path's end vertex is unmatched. -/
  getLast_unmatched : ∀ h : p ≠ [], ∀ l, (l, p.getLast h) ∉ M.edges
  /-- Forward edges are non-matching graph edges. -/
  forward : ∀ e ∈ (altEdges p).1, e ∈ G.E ∧ e ∉ M.edges
  /-- Backward edges are matching edges. -/
  backward : ∀ e ∈ (altEdges p).2, e ∈ M.edges

/-- Single-edge augmenting step: if `(l, r)` is a non-matching graph edge
whose endpoints are both unmatched, inserting it into `M` gives a matching
that is larger by one. -/
lemma exists_augment_single {M : Matching V G} {l r : V}
    (hE : (l, r) ∈ G.E) (hM : (l, r) ∉ M.edges)
    (hl : M.IsUnmatchedLeft l) (hr : M.IsUnmatchedRight r) :
    ∃ M' : Matching V G, M'.size = M.size + 1 := by
  refine ⟨{ edges := insert (l, r) M.edges
            h_subset := Finset.insert_subset hE M.h_subset
            h_unique_left := ?_
            h_unique_right := ?_ }, ?_⟩
  · intro l₂ r₁ r₂ h₁ h₂
    simp only [Finset.mem_insert, Prod.mk.injEq] at h₁ h₂
    rcases h₁ with ⟨e1a, e1b⟩ | h₁ <;> rcases h₂ with ⟨e2a, e2b⟩ | h₂
    · exact e1b.trans e2b.symm
    · exact (hl r₂ (e1a ▸ h₂)).elim
    · exact (hl r₁ (e2a ▸ h₁)).elim
    · exact M.h_unique_left l₂ r₁ r₂ h₁ h₂
  · intro l₁ l₂ r₃ h₁ h₂
    simp only [Finset.mem_insert, Prod.mk.injEq] at h₁ h₂
    rcases h₁ with ⟨e1a, e1b⟩ | h₁ <;> rcases h₂ with ⟨e2a, e2b⟩ | h₂
    · exact e1a.trans e2a.symm
    · exact (hr l₂ (e1b ▸ h₂)).elim
    · exact (hr l₁ (e2b ▸ h₁)).elim
    · exact M.h_unique_right l₁ l₂ r₃ h₁ h₂
  · show (insert (l, r) M.edges).card = M.size + 1
    rw [Finset.card_insert_of_notMem hM]
    rfl

/-- Swap step: if `(l, r)` is a non-matching graph edge, `(l', r)` is a
matching edge, and `l` is unmatched on the left, then replacing `(l', r)` by
`(l, r)` gives a matching of the same size in which `l'` is unmatched. -/
lemma exists_swap {M : Matching V G} {l r l' : V}
    (hE : (l, r) ∈ G.E) (hM : (l, r) ∉ M.edges) (hM' : (l', r) ∈ M.edges)
    (hl : M.IsUnmatchedLeft l) (hne : l ≠ l') :
    ∃ M₁ : Matching V G, M₁.size = M.size ∧ M₁.IsUnmatchedLeft l' ∧
      ∀ e, e ∈ M₁.edges ↔ e = (l, r) ∨ (e ∈ M.edges ∧ e ≠ (l', r)) := by
  refine ⟨{ edges := insert (l, r) (M.edges.erase (l', r))
            h_subset := Finset.insert_subset hE
              ((Finset.erase_subset _ _).trans M.h_subset)
            h_unique_left := ?_
            h_unique_right := ?_ }, ?_, ?_, ?_⟩
  · intro l₂ r₁ r₂ h₁ h₂
    simp only [Finset.mem_insert, Finset.mem_erase, Prod.mk.injEq] at h₁ h₂
    rcases h₁ with ⟨e1a, e1b⟩ | ⟨-, h₁⟩ <;> rcases h₂ with ⟨e2a, e2b⟩ | ⟨-, h₂⟩
    · exact e1b.trans e2b.symm
    · exact (hl r₂ (e1a ▸ h₂)).elim
    · exact (hl r₁ (e2a ▸ h₁)).elim
    · exact M.h_unique_left l₂ r₁ r₂ h₁ h₂
  · intro l₁ l₂ r₃ h₁ h₂
    simp only [Finset.mem_insert, Finset.mem_erase, Prod.mk.injEq] at h₁ h₂
    rcases h₁ with ⟨e1a, e1b⟩ | ⟨hne₁, h₁⟩ <;> rcases h₂ with ⟨e2a, e2b⟩ | ⟨hne₂, h₂⟩
    · exact e1a.trans e2a.symm
    · exact (hne₂ (Prod.ext (M.h_unique_right l₂ l' r (e1b ▸ h₂) hM') e1b)).elim
    · exact (hne₁ (Prod.ext (M.h_unique_right l₁ l' r (e2b ▸ h₁) hM') e2b)).elim
    · exact M.h_unique_right l₁ l₂ r₃ h₁ h₂
  · show (insert (l, r) (M.edges.erase (l', r))).card = M.size
    have hnotin : (l, r) ∉ M.edges.erase (l', r) := fun h =>
      hM (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem hnotin, Finset.card_erase_of_mem hM',
      Nat.sub_add_cancel (Finset.card_pos.mpr ⟨(l', r), hM'⟩)]
    rfl
  · intro r₂ h
    simp only [Finset.mem_insert, Finset.mem_erase, Prod.mk.injEq] at h
    rcases h with ⟨e1, -⟩ | ⟨hne2, hmem⟩
    · exact hne e1.symm
    · exact hne2 (Prod.ext rfl (M.h_unique_left l' r r₂ hM' hmem).symm)
  · intro e
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h2, h1⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h2, h1⟩

/-- **Augmentation theorem** (CLRS §25.1, Berge's lemma, forward direction):
a matching that admits an augmenting path can be enlarged by one edge. -/
theorem exists_augment {M : Matching V G} {p : List V}
    (hp : IsAugmentingPath G M p) : ∃ M' : Matching V G, M'.size = M.size + 1 := by
  suffices aux : ∀ (n : ℕ) (M : Matching V G) (p : List V), p.length ≤ n →
      IsAugmentingPath G M p → ∃ M' : Matching V G, M'.size = M.size + 1 from
    aux p.length M p le_rfl hp
  intro n
  induction n with
  | zero =>
    intro M p hlen hp
    have h2 := hp.length_ge
    omega
  | succ n ih =>
    intro M p hlen hp
    cases p with
    | nil =>
      have h2 := hp.length_ge
      simp at h2
    | cons l t =>
      cases t with
      | nil =>
        have h2 := hp.length_ge
        simp at h2
      | cons r rest =>
        cases rest with
        | nil =>
          have hfw := hp.forward (l, r) List.mem_cons_self
          exact exists_augment_single hfw.1 hfw.2
            (hp.head_unmatched (by simp)) (hp.getLast_unmatched (by simp))
        | cons l' rest' =>
          have hne_p : l :: r :: l' :: rest' ≠ [] := by simp
          have hnd := hp.nodup
          rw [List.nodup_cons] at hnd
          obtain ⟨hl_notin, hnd⟩ := hnd
          rw [List.nodup_cons] at hnd
          obtain ⟨hr_notin, hnd⟩ := hnd
          have hfw := hp.forward (l, r) List.mem_cons_self
          have hbw := hp.backward (l', r) List.mem_cons_self
          have hhu : ∀ r₂, (l, r₂) ∉ M.edges := hp.head_unmatched hne_p
          have hll : l ≠ l' := fun h =>
            hl_notin (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
          obtain ⟨M₁, hM₁size, hM₁un, hM₁mem⟩ := exists_swap hfw.1 hfw.2 hbw hhu hll
          -- The tail `l' :: rest'` is augmenting for `M₁`.
          have hgl : (l :: r :: l' :: rest').getLast hne_p =
              (l' :: rest').getLast (by simp) := by
            simp [List.getLast_cons]
          have htail : IsAugmentingPath G M₁ (l' :: rest') := by
            refine ⟨hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · have h2 := hp.length_even
              have h4 := hp.length_ge
              simp only [List.length_cons] at h2 h4 ⊢
              obtain ⟨k, hk⟩ := h2
              exact ⟨k - 1, by omega⟩
            · have h2 := hp.length_even
              have h4 := hp.length_ge
              simp only [List.length_cons] at h2 h4 ⊢
              obtain ⟨k, hk⟩ := h2
              omega
            · intro _
              exact (G.hE_subset _ (M.h_subset hbw)).1
            · intro _ r₂ h
              exact hM₁un r₂ h
            · intro _
              have := hp.getLast_mem_R hne_p
              rwa [hgl] at this
            · intro _ l₂ h
              rw [hM₁mem] at h
              rcases h with h | ⟨hmem, -⟩
              · obtain ⟨-, e2⟩ := Prod.mk.inj h
                have hrmem : r ∈ l' :: rest' := by
                  have hglmem := List.getLast_mem (l := l' :: rest') (by simp)
                  rwa [e2] at hglmem
                exact absurd hrmem hr_notin
              · exact hp.getLast_unmatched hne_p l₂ (hgl ▸ hmem)
            · intro e he
              have hf := hp.forward e (List.mem_cons_of_mem _ he)
              refine ⟨hf.1, fun hmem => ?_⟩
              rw [hM₁mem] at hmem
              rcases hmem with h | ⟨hmem, -⟩
              · obtain ⟨e1, -⟩ := Prod.mk.inj h
                have hm2 := fst_mem_of_mem_altEdges_left he
                rw [e1] at hm2
                exact hl_notin (List.mem_cons_of_mem _ hm2)
              · exact hf.2 hmem
            · intro e he
              have hb := hp.backward e (List.mem_cons_of_mem _ he)
              have hne : e ≠ (l', r) := by
                intro hcontra
                have hm2 := snd_mem_of_mem_altEdges_right he
                rw [hcontra] at hm2
                exact hr_notin hm2
              exact (hM₁mem e).mpr (Or.inr ⟨hb, hne⟩)
          obtain ⟨M₂, hM₂⟩ := ih M₁ (l' :: rest') (by
            have := hp.length_ge
            simp only [List.length_cons] at hlen this ⊢
            omega) htail
          exact ⟨M₂, by omega⟩

/-- An augmenting path certifies that a matching is not maximum. -/
lemma not_isMaximum_of_isAugmentingPath {M : Matching V G} {p : List V}
    (hp : IsAugmentingPath G M p) : ¬ M.IsMaximum := by
  intro hmax
  obtain ⟨M', hM'⟩ := exists_augment hp
  have := hmax M'
  omega

end Matchings

end CLRS
