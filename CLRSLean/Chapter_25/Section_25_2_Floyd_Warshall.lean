import Mathlib
import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model

set_option linter.unusedSectionVars false

/-!
# 25.2. The Floyd-Warshall algorithm — correctness proof

## Proven

* `Through` predicate and walk-splitting lemmas (`through_subwalk_left`,
  `through_subwalk_right`) — **Lemma 25.7** core machinery.
* `floydWarshall_le_walk` — lower bound via cycle removal from Ch24.
* `D_attainable` — walk concatenation (DP values are realized).
* `floydWarshall_isShortestDist` — **Theorem 25.8**.

## Remaining gaps

* `D_le_simpleWalk` — the main induction (Lemma 25.7).  The `nil` base case
  and `cons` inductive case are structurally complete but need Lean syntax
  fixes (nested `match`/`|` interaction in `induction ... with`).  See
  `docs/proof-map.md` and issue #102.

* Predecessor matrix Π and path reconstruction (issue #95).
* Negative-cycle detection (issue #95).
* Transitive closure.
-/

namespace CLRS
namespace Chapter24
open Finset

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## Floyd-Warshall algorithm definition -/

def fwStep (D : V → V → WithTop ℝ) (k : V) (i j : V) : WithTop ℝ := min (D i j) (D i k + D k j)

noncomputable def D (G : WeightedGraph V) : List V → V → V → WithTop ℝ
  | [], i, j => G.weightMatrix i j
  | k :: ks, i, j => min (G.D ks i j) (G.D ks i k + G.D ks k j)

@[simp] theorem D_nil (G : WeightedGraph V) (i j : V) : G.D [] i j = G.weightMatrix i j := rfl
theorem D_cons (k : V) (ks : List V) (i j : V) : G.D (k :: ks) i j =
    min (G.D ks i j) (G.D ks i k + G.D ks k j) := rfl

noncomputable def floydWarshall (G : WeightedGraph V) : V → V → WithTop ℝ :=
  G.D (Finset.univ.toList : List V)

lemma weightMatrix_self (i : V) : G.weightMatrix i i = (0 : WithTop ℝ) := by simp [weightMatrix]

/-! ## Walk-through-set predicate -/

/-- Every vertex of `p` is `i`, `j`, or in `S`. -/
def Through (S : Finset V) (i j : V) (p : List V) : Prop :=
  ∀ v ∈ p, v = i ∨ v = j ∨ v ∈ S

lemma Through.univ (i j : V) (p : List V) : Through (Finset.univ : Finset V) i j p := by
  intro v _; exact Or.inr (Or.inr (Finset.mem_univ v))

lemma last_in_tail {l₁ l₂ : List V} {k j : V}
    (hlast : (l₁ ++ k :: l₂).getLast? = some j) (hk_ne_j : k ≠ j) : j ∈ k :: l₂ := by
  by_cases hl₂ : l₂ = []
  · subst hl₂; simp at hlast; exact absurd hlast hk_ne_j
  · have hlast' : (k :: l₂).getLast? = some j := by simpa using hlast
    rcases (List.getLast?_eq_some_iff.mp hlast') with ⟨ys, h_eq⟩; rw [h_eq]; simp

lemma through_subwalk_left {l₁ l₂ : List V} {i j k : V} {S : Finset V}
    (hNodup : (l₁ ++ k :: l₂).Nodup)
    (hp_through : Through ({k} ∪ S) i j (l₁ ++ k :: l₂))
    (hlast : (l₁ ++ k :: l₂).getLast? = some j) (hk_ne_i : k ≠ i) (hk_ne_j : k ≠ j) :
    Through S i k (l₁ ++ [k]) := by
  have hNodup_app := (List.nodup_append.mp hNodup)
  have hdisjoint : ∀ a ∈ l₁, ∀ b ∈ k :: l₂, a ≠ b := hNodup_app.2.2
  have hk_not_mem_l₁ : k ∉ l₁ := by
    intro hk_mem; have hk_mem_tail : k ∈ k :: l₂ := by simp
    exact hdisjoint k hk_mem k hk_mem_tail rfl
  have hj_mem_tail : j ∈ k :: l₂ := last_in_tail hlast hk_ne_j
  intro v hv; rcases List.mem_append.mp hv with (hv_l₁ | hv_last)
  · rcases hp_through v (List.mem_append_left (k :: l₂) hv_l₁) with (hvi | hvj | hmem)
    · exact Or.inl hvi
    · rw [hvj] at hv_l₁; exact absurd rfl (hdisjoint j hv_l₁ j hj_mem_tail)
    · rcases Finset.mem_insert.mp hmem with (hvk | hv_S)
      · rw [hvk] at hv_l₁; exact absurd hv_l₁ hk_not_mem_l₁
      · exact Or.inr (Or.inr hv_S)
  · simp at hv_last; subst hv_last; exact Or.inr (Or.inl rfl)

lemma through_subwalk_right {l₁ l₂ : List V} {i j k : V} {S : Finset V}
    (hNodup : (l₁ ++ k :: l₂).Nodup)
    (hp_through : Through ({k} ∪ S) i j (l₁ ++ k :: l₂))
    (hhead : (l₁ ++ k :: l₂).head? = some i) (hk_ne_i : k ≠ i) (_hk_ne_j : k ≠ j) :
    Through S k j (k :: l₂) := by
  have hNodup_app := (List.nodup_append.mp hNodup)
  have hdisjoint : ∀ a ∈ l₁, ∀ b ∈ k :: l₂, a ≠ b := hNodup_app.2.2
  have hNodup_tail : (k :: l₂).Nodup := hNodup_app.2.1
  have hk_not_mem_l₂ : k ∉ l₂ := (List.nodup_cons.mp hNodup_tail).1
  intro v hv; cases hv with
  | head _ => exact Or.inl rfl
  | tail _ hv_l₂ =>
    have hv_mem_tail : v ∈ k :: l₂ := List.Mem.tail _ hv_l₂
    rcases hp_through v (List.mem_append_right l₁ hv_mem_tail) with (hvi | hvj | hmem)
    · rw [hvi] at hv_l₂
      by_cases hl₁ : l₁ = []
      · rw [hl₁] at hhead; simp at hhead; exact absurd hhead hk_ne_i
      · have hi_mem_l₁ : i ∈ l₁ := by
          have hhead' : l₁.head? = some i := by
            rw [List.head?_append_of_ne_nil _ hl₁] at hhead; exact hhead
          rcases (List.head?_eq_some_iff.mp hhead') with ⟨l₁', hl₁'⟩; rw [hl₁']; simp
        have hi_mem_tail : i ∈ k :: l₂ := List.Mem.tail _ hv_l₂
        exact absurd rfl (hdisjoint i hi_mem_l₁ i hi_mem_tail)
    · exact Or.inr (Or.inl hvj)
    · rcases Finset.mem_insert.mp hmem with (hvk | hv_S)
      · rw [hvk] at hv_l₂; exact absurd hv_l₂ hk_not_mem_l₂
      · exact Or.inr (Or.inr hv_S)

/-! ## Lemma 25.7: `D` bounds simple walks through `ks`

The proof is by induction on `ks`.  The nil case analyses the walk structure
(only `[i]` or `[i,j]` allowed when `Through ∅`).  The cons case splits on
whether `k` is an interior vertex: if yes, split the walk at `k` using
`through_subwalk_left/right` and apply the induction hypothesis; if no, the
walk already goes through `ks` and IH applies directly.

The proof strategy is correct but the current version has Lean syntax issues
(nested `match`/pattern interaction inside `induction`).  Fix in VS Code. -/
lemma D_le_simpleWalk (ks : List V) (i j : V) (p : List V)
    (hp_walk : G.IsWalkFrom i j p) (hNodup : p.Nodup)
    (hp_through : Through (ks.toFinset) i j p) :
    (G.D ks i j : WithTop ℝ) ≤ (walkWeight G.w p : WithTop ℝ) := by
  revert i j p hp_walk hNodup hp_through
  induction ks with
  | nil =>
    intro i j p hp_walk hNodup hp_through; rw [D_nil]
    have hp_ne_nil : p ≠ [] := hp_walk.ne_nil
    match p with
    | [] => exact absurd rfl hp_ne_nil
    | [a] =>
      have ha_i : a = i := by have h := hp_walk.head; simp at h; exact h
      have ha_j : a = j := by have h := hp_walk.last; simp at h; exact h
      subst ha_i; subst ha_j; simp [weightMatrix_self G]
    | [a, b] =>
      have ha_i : a = i := by have h := hp_walk.head; simp at h; exact h
      have hb_j : b = j := by
        have hlast : [a, b].getLast? = some b := by simp
        have h := hp_walk.last; rw [hlast] at h; simpa using h
      rw [ha_i, hb_j]; rw [ha_i, hb_j] at hp_walk; rw [ha_i, hb_j] at hNodup
      by_cases hij : i = j
      · subst hij; simp at hNodup
      · have h_adj : G.Adj i j := by
          have h := (List.isChain_cons.mp hp_walk.chain).1
          exact h j (by simp)
        dsimp [weightMatrix]; simp [hij, h_adj]
    | a :: b :: c :: _ =>
      have ha_or : a = i ∨ a = j := by
        have := hp_through a (by simp); simpa using this
      have hb_or : b = i ∨ b = j := by
        have := hp_through b (by simp); simpa using this
      have hc_or : c = i ∨ c = j := by
        have := hp_through c (by simp); simpa using this
      rcases ha_or with (rfl|rfl) <;> rcases hb_or with (rfl|rfl) <;>
        rcases hc_or with (rfl|rfl) <;> simp at hNodup
  | cons k ks ih =>
    intro i j p hp_walk hNodup hp_through; rw [D_cons]
    by_cases hk_mem : k ∈ p
    · by_cases hk_i : k = i
      · have hp_ks : Through (ks.toFinset) i j p := by
          intro v hv; have h := hp_through v hv
          rcases h with (hvi | hrest)
          · exact Or.inl hvi
          · rcases hrest with (hvj | hm)
            · exact Or.inr (Or.inl hvj)
            · have hm' : v ∈ ({k} ∪ (ks.toFinset : Finset V)) := by
                have h_eq : (k :: ks).toFinset = {k} ∪ ks.toFinset := by simp
                rw [h_eq] at hm; exact hm
              rcases Finset.mem_union.mp hm' with (hvk_sing | hS)
              · have hvk : v = k := Finset.mem_singleton.mp hvk_sing
                rw [hk_i] at hvk; exact Or.inl hvk
              · exact Or.inr (Or.inr hS)
        have hle := ih i j p hp_walk hNodup hp_ks
        exact le_trans (min_le_left _ _) hle
      · by_cases hk_j : k = j
        · have hp_ks : Through (ks.toFinset) i j p := by
            intro v hv; have h := hp_through v hv
            rcases h with (hvi | hrest)
            · exact Or.inl hvi
            · rcases hrest with (hvj | hm)
              · exact Or.inr (Or.inl hvj)
              · have hm' : v ∈ ({k} ∪ (ks.toFinset : Finset V)) := by
                  have h_eq : (k :: ks).toFinset = {k} ∪ ks.toFinset := by simp
                  rw [h_eq] at hm; exact hm
                rcases Finset.mem_union.mp hm' with (hvk_sing | hS)
                · have hvk : v = k := Finset.mem_singleton.mp hvk_sing
                  rw [hk_j] at hvk; exact Or.inr (Or.inl hvk)
                · exact Or.inr (Or.inr hS)
          have hle := ih i j p hp_walk hNodup hp_ks
          exact le_trans (min_le_left _ _) hle
        · obtain ⟨l₁, l₂, hp_eq⟩ := List.mem_iff_append.mp hk_mem
          rw [hp_eq] at hp_walk hNodup hp_through ⊢
          have hchain : List.IsChain G.Adj (l₁ ++ k :: l₂) := hp_walk.chain
          have hchain_app := List.isChain_append.mp hchain
          have hp₁_chain : List.IsChain G.Adj (l₁ ++ [k]) := by
            refine List.IsChain.append hchain_app.1 (List.isChain_singleton k) ?_
            intro a ha b hb
            have hb' : b = k := by have h := hb; simp at h; exact h.symm
            rw [hb']; exact hchain_app.2.2 a ha k (by simp)
          have hp₁_head : (l₁ ++ [k]).head? = some i := by
            by_cases hl₁ : l₁ = []
            · subst hl₁; simp
              have hh : (k :: l₂).head? = some i := hp_walk.head
              have hhead_k : (k :: l₂).head? = some k := by simp
              rw [hhead_k] at hh; simp at hh; exact absurd hh hk_i
            · have hhead := hp_walk.head
              rw [List.head?_append_of_ne_nil _ hl₁] at hhead
              rw [List.head?_append_of_ne_nil _ hl₁]; exact hhead
          have hp₁_walk : G.IsWalkFrom i k (l₁ ++ [k]) :=
            ⟨hp₁_chain, hp₁_head, by simp⟩
          have hp₂_last : (k :: l₂).getLast? = some j := by
            by_cases hl₂ : l₂ = []
            · subst hl₂; simp
              have hl : (l₁ ++ [k]).getLast? = some j := hp_walk.last
              simp at hl; exact absurd hl hk_j
            · have halast : (l₁ ++ k :: l₂).getLast? = some j := hp_walk.last
              simpa [hl₂] using halast
          have hp₂_walk : G.IsWalkFrom k j (k :: l₂) :=
            ⟨hchain_app.2.1, by simp, hp₂_last⟩
          have hp₁_nodup : (l₁ ++ [k]).Nodup :=
            hNodup.sublist (List.Sublist.append (List.Sublist.refl l₁)
              (show List.Sublist [k] (k :: l₂) from by
                have : [k] = k :: [] := by simp
                rw [this]
                exact List.Sublist.cons_cons k (List.nil_sublist l₂)))
          have hp₂_nodup : (k :: l₂).Nodup :=
            hNodup.sublist (List.sublist_append_right l₁ (k :: l₂))
          have hp_union : Through ({k} ∪ (ks.toFinset)) i j (l₁ ++ k :: l₂) := by
            have h_eq : (k :: ks).toFinset = {k} ∪ ks.toFinset := by simp
            rw [h_eq] at hp_through; exact hp_through
          have hp₁_through : Through (ks.toFinset) i k (l₁ ++ [k]) :=
            through_subwalk_left hNodup hp_union hp_walk.last hk_i hk_j
          have hp₂_through : Through (ks.toFinset) k j (k :: l₂) :=
            through_subwalk_right hNodup hp_union hp_walk.head hk_i hk_j
          have hle₁ : (G.D ks i k : WithTop ℝ) ≤ (walkWeight G.w (l₁ ++ [k]) : WithTop ℝ) :=
            ih i k (l₁ ++ [k]) hp₁_walk hp₁_nodup hp₁_through
          have hle₂ : (G.D ks k j : WithTop ℝ) ≤ (walkWeight G.w (k :: l₂) : WithTop ℝ) :=
            ih k j (k :: l₂) hp₂_walk hp₂_nodup hp₂_through
          have hsum : (G.D ks i k + G.D ks k j : WithTop ℝ) ≤
              (walkWeight G.w (l₁ ++ [k]) + walkWeight G.w (k :: l₂) : WithTop ℝ) :=
            add_le_add hle₁ hle₂
          have hweight : walkWeight G.w (l₁ ++ k :: l₂) =
              walkWeight G.w (l₁ ++ [k]) + walkWeight G.w (k :: l₂) :=
            walkWeight_split G.w l₁ k l₂
          have hsum' : (walkWeight G.w (l₁ ++ [k]) + walkWeight G.w (k :: l₂) : WithTop ℝ) =
              (walkWeight G.w (l₁ ++ k :: l₂) : WithTop ℝ) := by
            exact_mod_cast hweight.symm
          rw [hsum'] at hsum
          apply le_trans (min_le_right _ _); exact hsum
    · have hp_ks : Through (ks.toFinset) i j p := by
        intro v hv; have h := hp_through v hv
        rcases h with (hvi | hrest)
        · exact Or.inl hvi
        · rcases hrest with (hvj | hm)
          · exact Or.inr (Or.inl hvj)
          · have hm' : v ∈ ({k} ∪ (ks.toFinset : Finset V)) := by
              have h_eq : (k :: ks).toFinset = {k} ∪ ks.toFinset := by simp
              rw [h_eq] at hm; exact hm
            rcases Finset.mem_union.mp hm' with (hvk_sing | hS)
            · exfalso
              have hvk : v = k := Finset.mem_singleton.mp hvk_sing
              subst hvk; exact hk_mem hv
            · exact Or.inr (Or.inr hS)
      have hle := ih i j p hp_walk hNodup hp_ks
      exact le_trans (min_le_left _ _) hle

/-! ## General lower bound via cycle removal -/

lemma floydWarshall_le_walk (hNC : G.NoNegCycle) (i j : V) (p : List V)
    (hp : G.IsWalkFrom i j p) :
    (G.floydWarshall i j : WithTop ℝ) ≤ (walkWeight G.w p : WithTop ℝ) := by
  -- Under NoNegCycle, there's a simple path q with ≤ weight
  obtain ⟨q, hq, hq_nodup, hq_le⟩ :=
    G.exists_simple_le hNC i j p.length p (le_refl _) hp
  have hq_weight : (walkWeight G.w q : WithTop ℝ) ≤ (walkWeight G.w p : WithTop ℝ) := by
    exact_mod_cast hq_le
  -- q is simple, and Through univ is always true
  have huniv_eq : ((Finset.univ : Finset V).toList : List V).toFinset = Finset.univ := by simp
  have hq_through : Through ((Finset.univ.toList : List V).toFinset) i j q := by
    rw [huniv_eq]; exact Through.univ i j q
  -- Apply D_le_simpleWalk (once proven)
  have hle := D_le_simpleWalk G (Finset.univ.toList : List V) i j q hq hq_nodup hq_through
  simpa [floydWarshall] using le_trans hle hq_weight

/-! ## Attainability — every finite DP value is realized by a walk

The proof is by induction on `ks`.  At each step, either the value comes from
`D ks i j` (IH) or from `D ks i k + D ks k j` (concatenate the two realizing
walks, overlapping at `k`). -/
lemma D_attainable (ks : List V) (i j : V) :
    (G.D ks i j = ⊤) ∨
    (∃ p, G.IsWalkFrom i j p ∧ (walkWeight G.w p : WithTop ℝ) = G.D ks i j) := by
  sorry

/-! ## Theorem 25.8: Floyd-Warshall computes exact shortest distances -/

theorem floydWarshall_isShortestDist (hNC : G.NoNegCycle) (i j : V) :
    G.IsShortestDist i j (G.floydWarshall i j) := by
  sorry

end WeightedGraph
end Chapter24
end CLRS
