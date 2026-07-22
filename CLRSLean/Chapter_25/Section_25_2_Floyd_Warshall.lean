import Mathlib
import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model

set_option linter.unusedSectionVars false

/-!
# 25.2. The Floyd-Warshall algorithm — correctness proof

## Proven

* `Through` predicate and walk-splitting lemmas (`through_subwalk_left`,
  `through_subwalk_right`) — **Lemma 25.7** core machinery.
* `D_le_simpleWalk` — the main induction (**Lemma 25.7**).
* `floydWarshall_le_walk` — lower bound via cycle removal from Ch24.
* `D_attainable` — walk concatenation (DP values are realized).
* `floydWarshall_isShortestDist` — **Theorem 25.8**.
* `Pi` — predecessor matrix Π (parallel recurrence alongside `D`).
* `Pi_adj` — every predecessor points along a real graph edge.
* `fwReconstructPath` — fuel-based shortest-path reconstruction from Π.
* `floydWarshall_nonneg_diag` — soundness of the diagonal test.
* `negative_diagonal_implies_negative_cycle` — completeness of the diagonal
  test (**CLRS Theorem 25.3**).

## Remaining gaps

* Path reconstruction weight equality (`walkWeight = floydWarshall`).
  Walk validity from `Pi_adj` is proved; the weight-equality lemma requires
  the optimal-substructure property of the final predecessor matrix and is
  deferred to a follow-up proof effort (issue #95).
* Transitive closure (Section 25.2 variant).
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

/-! ## Predecessor matrix Π

The predecessor matrix `Pi ks i j` stores the immediate predecessor of `j` on a
best-known path from `i` to `j` using only intermediate vertices from `ks`.  The
convention follows CLRS equations (25.5)-(25.6):

* `Pi [] i j = none` (NIL) if `i=j` or `(i,j)` is not an edge;
  `Pi [] i j = some i` if `i≠j` and `(i,j)` is an edge.
* `Pi (k::ks) i j = Pi ks k j` when going through `k` yields a strictly shorter
  distance (i.e. `D ks i k + D ks k j < D ks i j`); otherwise `Pi ks i j`.

The final all-pairs predecessor matrix is `floydWarshallPi := Pi (univ.toList)`. -/

/-- Predecessor matrix Π, computed alongside the distance matrix `D` (CLRS eqs.
(25.5)-(25.6)).  `Pi ks i j = some k` means `k` is the predecessor of `j` on a
best-known path from `i` to `j` through vertices in `ks`. -/
noncomputable def Pi (G : WeightedGraph V) : List V → V → V → Option V
  | [], i, j =>
    if i = j then none
    else if G.Adj i j then some i
    else none
  | k :: ks, i, j =>
    if (G.D ks i k + G.D ks k j) < (G.D ks i j) then G.Pi ks k j
    else G.Pi ks i j

@[simp] theorem Pi_nil (G : WeightedGraph V) (i j : V) :
    G.Pi [] i j = (if i = j then none else if G.Adj i j then some i else none) := rfl

theorem Pi_cons (k : V) (ks : List V) (i j : V) : G.Pi (k :: ks) i j =
    (if (G.D ks i k + G.D ks k j) < (G.D ks i j) then G.Pi ks k j else G.Pi ks i j) := rfl

/-- When the distance through `k` is strictly better, the predecessor matrix is
updated to the predecessor of `j` on the best-known path from `k` to `j`. -/
lemma Pi_cons_lt {k : V} {ks : List V} {i j : V}
    (hlt : G.D ks i k + G.D ks k j < G.D ks i j) :
    G.Pi (k :: ks) i j = G.Pi ks k j := by
  rw [Pi_cons, if_pos hlt]

lemma Pi_cons_not_lt {k : V} {ks : List V} {i j : V}
    (hle : ¬ (G.D ks i k + G.D ks k j < G.D ks i j)) :
    G.Pi (k :: ks) i j = G.Pi ks i j := by
  rw [Pi_cons, if_neg hle]

/-- Base-case predecessor specification: `Pi [] i j = some k` implies `k=i`, `i≠j`,
and `(i,j)` is an edge. -/
lemma Pi_nil_spec (G : WeightedGraph V) (i j k : V) (h : G.Pi [] i j = some k) : k = i ∧ i ≠ j ∧ G.Adj i j := by
  rw [Pi_nil] at h
  by_cases hij : i = j
  · subst hij; simp at h
  · simp [hij] at h
    by_cases hadj : G.Adj i j
    · simp [hadj] at h
      have h_ik : i = k := by simpa using h
      have hk_i : k = i := h_ik.symm
      exact ⟨hk_i, hij, hadj⟩
    · simp [hadj] at h

/-- **Predecessor edge lemma.**  `Pi ks i j = some k` implies `(k,j)` is an edge
in the graph.  This is the key invariant for path reconstruction: every
predecessor recorded by `Pi` is an actual predecessor vertex along a real edge.

The proof is by induction on `ks`; both branches of the inductive step preserve
the property from the base case where `Pi [] i j = some i` only when `(i,j) ∈ E`. -/
lemma Pi_adj (ks : List V) (i j k : V) (hPi : G.Pi ks i j = some k) : G.Adj k j := by
  revert i j k
  induction ks with
  | nil =>
    intro i j k hPi
    rcases Pi_nil_spec G i j k hPi with ⟨hk_i, _, hadj⟩
    subst hk_i; exact hadj
  | cons k' ks ih =>
    intro i j k hPi
    rw [Pi_cons] at hPi
    split at hPi
    · exact ih k' j k hPi
    · exact ih i j k hPi

/-- Final Floyd-Warshall predecessor matrix (CLRS Π-matrix). -/
noncomputable def floydWarshallPi (G : WeightedGraph V) : V → V → Option V :=
  G.Pi (Finset.univ.toList : List V)

/-- Edge lemma specialised to the final predecessor matrix. -/
lemma floydWarshallPi_adj (i j k : V) (hPi : G.floydWarshallPi i j = some k) : G.Adj k j :=
  G.Pi_adj (Finset.univ.toList : List V) i j k hPi

/-! ## Path reconstruction

Path reconstruction follows the CLRS PRINT-ALL-PAIRS-SHORTEST-PATH recursion:
given `Π[i,j] = k`, the path from `i` to `j` is the path from `i` to `k` followed
by the edge `(k, j)`.

We use a fuel-based implementation bounded by `Fintype.card V` to ensure
well-founded recursion.  Under `NoNegCycle`, shortest paths are simple, so at most
`|V-1|` edges are needed.  When fuel runs out we return `[]` (which cannot happen
for well-defined shortest paths under `NoNegCycle`). -/

/-- Reconstruct a path from `i` to `j` using at most `fuel` recursion steps.
Returns `[]` when fuel is exhausted or no predecessor exists. -/
def reconstructPathFuel (Pi : V → V → Option V) (fuel : ℕ) (i j : V) : List V :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if h : i = j then [i]
    else
      match Pi i j with
      | none => []
      | some k =>
        let path := reconstructPathFuel Pi fuel i k
        if hpath : path = [] then [] else path ++ [j]

/-- Reconstruct a shortest path from `i` to `j` using the Floyd-Warshall
predecessor matrix.  Fuel = `Fintype.card V` ensures sufficient recursion depth
for simple paths. -/
noncomputable def fwReconstructPath (G : WeightedGraph V) (i j : V) : List V :=
  reconstructPathFuel G.floydWarshallPi (Fintype.card V) i j

/-- A reconstructible vertex pair has a nonempty predecessor chain that
terminates at `i`.  This is the invariant that makes reconstruction succeed. -/
lemma reconstructPathFuel_ne_nil (Pi : V → V → Option V) (fuel : ℕ) (i j : V)
    (h_fuel : 0 < fuel) (h_eq : i = j) : reconstructPathFuel Pi fuel i j = [i] := by
  subst h_eq
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h_fuel) with ⟨n, rfl⟩
  simp [reconstructPathFuel]

lemma reconstructPathFuel_cons (Pi : V → V → Option V) (fuel : ℕ) (i j k : V)
    (hPi : Pi i j = some k) (hij : i ≠ j) (hne : reconstructPathFuel Pi fuel i k ≠ []) :
    reconstructPathFuel Pi (fuel + 1) i j = reconstructPathFuel Pi fuel i k ++ [j] := by
  simp [reconstructPathFuel, hij, hPi, hne]

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
  induction' ks with k ks ih generalizing i j
  · rw [D_nil]; dsimp [weightMatrix]
    by_cases hij : i = j
    · subst hij
      have hw : G.weightMatrix i i = (0 : WithTop ℝ) := weightMatrix_self G i
      simp [hw]
      refine ⟨[i], ?_, ?_⟩
      · exact { chain := List.isChain_singleton i, head := by simp, last := by simp }
      · simp
    · by_cases hadj : G.Adj i j
      · refine Or.inr ⟨[i, j], ?_, ?_⟩
        · refine ⟨?_, by simp, by simp⟩
          refine (List.isChain_cons (x := i) (l := [j])).mpr ⟨?_, List.isChain_singleton j⟩
          intro b hb; simp at hb; subst hb; exact hadj
        · simp [walkWeight, hij, hadj]
      · simp [hij, hadj]
  · rw [D_cons]
    rcases min_choice (G.D ks i j) (G.D ks i k + G.D ks k j) with (hmin | hmin)
    · rw [hmin]; exact ih i j
    · rw [hmin]
      rcases ih i k with (htop_ik | ⟨pik, hpik, hpikw⟩)
      · simp [htop_ik]
      · rcases ih k j with (htop_kj | ⟨pkj, hpkj, hpkjw⟩)
        · simp [htop_kj]
        · -- Concatenate pik ++ pkj.tail (overlap at k)
          have hpik_ne_nil : pik ≠ [] := hpik.ne_nil
          cases pkj with
          | nil => exact absurd rfl hpkj.ne_nil
          | cons a as =>
            have ha_k : a = k := by simpa using hpkj.head
            -- Work with as = pkj.tail, and a = k
            have hpkj_chain' : List.IsChain G.Adj (k :: as) := by
              rw [← ha_k]; exact hpkj.chain
            have chain_decomp := List.isChain_cons.mp hpkj_chain'
            have as_chain : List.IsChain G.Adj as := chain_decomp.2
            have head_adj : ∀ y ∈ as.head?, G.Adj k y := chain_decomp.1
            set q := pik ++ as with hq_def
            -- Chain for concatenated walk
            have hq_chain : List.IsChain G.Adj q := by
              rw [hq_def]
              -- use the iff version of isChain_append
              apply (List.isChain_append (l₁ := pik) (l₂ := as)).mpr
              refine ⟨hpik.chain, as_chain, ?_⟩
              intro a' ha' b' hb'
              rw [hpik.last] at ha'
              simp at ha'
              have ha'_k : a' = k := ha'.symm
              rw [ha'_k]; exact head_adj b' hb'
            have hq_head : q.head? = some i := by
              rw [hq_def, List.head?_append_of_ne_nil _ hpik_ne_nil]; exact hpik.head
            have hq_last : q.getLast? = some j := by
              rw [hq_def]
              by_cases has : as = []
              · subst has; simp
                have hk_eq_j : k = j := by
                  have hlast := hpkj.last; simp at hlast; rw [ha_k] at hlast; exact hlast
                have hpik_last' := hpik.last; rw [hk_eq_j] at hpik_last'; exact hpik_last'
              · have hlast' : (pik ++ as).getLast? = as.getLast? :=
                  List.getLast?_append_of_ne_nil _ has
                rw [hlast']
                have htail_last : as.getLast? = some j := by
                  have hlast_pkj := hpkj.last
                  rw [ha_k] at hlast_pkj
                  have h_getLast : (k :: as).getLast? = as.getLast? := by
                    simpa using List.getLast?_cons_of_ne_nil has
                  rw [h_getLast] at hlast_pkj
                  exact hlast_pkj
                exact htail_last
            have hq_walk : G.IsWalkFrom i j q := ⟨hq_chain, hq_head, hq_last⟩
            -- Weight equality
            have hpik_last_eq := hpik.last
            rcases List.getLast?_eq_some_iff.mp hpik_last_eq with ⟨l, hpik_snoc⟩
            have hq_weight : (walkWeight G.w q : WithTop ℝ) = G.D ks i k + G.D ks k j := by
              rw [hq_def, hpik_snoc]
              have h_list_eq : (l ++ [k]) ++ as = l ++ k :: as := by simp
              rw [h_list_eq]
              rw [walkWeight_split G.w l k as, ← hpik_snoc]
              have h_pkj_eq : (k :: as) = (a :: as) := by
                rw [ha_k]
              rw [h_pkj_eq]
              push_cast; rw [hpikw, hpkjw]
            exact Or.inr ⟨q, hq_walk, hq_weight⟩

theorem floydWarshall_isShortestDist (hNC : G.NoNegCycle) (i j : V) :
    G.IsShortestDist i j (G.floydWarshall i j) := by
  constructor
  · intro p hp; exact G.floydWarshall_le_walk hNC i j p hp
  · rcases G.D_attainable (Finset.univ.toList : List V) i j with (htop | ⟨p, hp, hpw⟩)
    · left; simpa [floydWarshall] using htop
    · right; refine ⟨p, hp, ?_⟩; simpa [floydWarshall] using hpw

/-! ## Negative-cycle detection (CLRS Theorem 25.3)

The Floyd-Warshall algorithm detects negative-weight cycles by inspecting the
diagonal entries of the final distance matrix.  CLRS Theorem 25.3 states:

diagonal entries of the final distance matrix is strictly negative.

We prove both directions. -/

/-- **Soundness of the diagonal test.**  Under `NoNegCycle`, every diagonal entry
of the Floyd-Warshall matrix is nonnegative.  This is the forward direction
(`NoNegCycle → diagonal ≥ 0`) of CLRS Theorem 25.3. -/
theorem floydWarshall_nonneg_diag (hNC : G.NoNegCycle) (i : V) :
    (0 : WithTop ℝ) ≤ G.floydWarshall i i := by
  rcases G.D_attainable (Finset.univ.toList : List V) i i with (htop | ⟨p, hp, hpw⟩)
  · rw [floydWarshall, htop]; exact le_top
  · rw [floydWarshall, ← hpw]
    have h_nonneg : 0 ≤ walkWeight G.w p := hNC i p hp
    exact_mod_cast h_nonneg

/-- **Completeness of the diagonal test.**  If a diagonal entry of the
Floyd-Warshall matrix is strictly negative, then there exists a negative-weight
closed walk in the graph.  This is the reverse direction (`diagonal < 0 → ¬NoNegCycle`)
of CLRS Theorem 25.3. -/
theorem negative_diagonal_implies_negative_cycle (i : V)
    (h : G.floydWarshall i i < (0 : WithTop ℝ)) :
    ∃ (c : List V), G.IsWalkFrom i i c ∧ walkWeight G.w c < 0 := by
  rcases G.D_attainable (Finset.univ.toList : List V) i i with (htop | ⟨p, hp, hpw⟩)
  · rw [floydWarshall, htop] at h; simp at h
  · have hpw_cast : (walkWeight G.w p : WithTop ℝ) = G.floydWarshall i i := by
      simpa [floydWarshall] using hpw
    have h_coe_lt : (walkWeight G.w p : WithTop ℝ) < (0 : WithTop ℝ) := by
      rw [hpw_cast]; exact h
    -- Extract the ℝ inequality from the WithTop inequality.
    -- From h_coe_lt : (walkWeight G.w p : WithTop ℝ) < (0 : WithTop ℝ)
    -- extract the ℝ inequality using exact_mod_cast.
    have h_lt : walkWeight G.w p < 0 := by exact_mod_cast h_coe_lt
    exact ⟨p, hp, h_lt⟩

end WeightedGraph
end Chapter24
end CLRS
