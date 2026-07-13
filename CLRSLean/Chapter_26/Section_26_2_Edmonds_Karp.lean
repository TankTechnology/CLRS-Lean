import Mathlib
import CLRSLean.Chapter_26.Section_26_1_Flow_Networks

/-!
# 26.2. The Edmonds-Karp Algorithm

This section formalizes the Edmonds-Karp analysis for the maximum-flow problem
(CLRS Section 26.2).  Edmonds-Karp is the Ford-Fulkerson method with the
augmenting path chosen by BFS in the residual network, which guarantees
that the number of augmentations is `O(VE)` and the total running time is
`O(VE²)`.

The key lemma is that the BFS shortest-path distance `δ_f(s,v)` in the residual
network `G_f` is nondecreasing with each flow augmentation (Lemma 26.7).  From
this we obtain the bound on the number of augmentations (Theorem 26.8).

Main results:

- `ResidualPathLength`: inductive predicate for path existence in `G_f`
- `IsShortestDist`: `IsShortestDist φ u v d` holds when `d` is the shortest
  path distance from `u` to `v` in the residual network `G_f`
- `shortest_path_nondec` (Lemma 26.7): after augmenting along a BFS-shortest
  augmenting path, the shortest distance `δ_f(s,v)` is nondecreasing
- `numAugmentations_bound` (Theorem 26.8): the Edmonds-Karp algorithm performs
  `O(VE)` augmentations, yielding `O(VE²)` total running time

**Current gaps**: the executable BFS procedure and the concrete augmenting loop
are not yet implemented; the analysis is carried out at the abstract
augmentation level.

Notation conventions:

- `G` : a flow network on a vertex type `V`
- `φ` : a feasible flow on `G`
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset
open Classical

/-! ## Residual path length and shortest-path distance -/

section ResidualDistances

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- `ResidualPathLength φ u v n` holds iff there is a path from `u` to `v` in
the residual network `G_φ` consisting of exactly `n` edges (i.e., `n` steps).

This is the unweighted path-length counterpart of
`Flow.augmentingPathReachable` (which is the reflexive-transitive closure with
no length tracking). -/
inductive ResidualPathLength (φ : Flow V G) : V → V → ℕ → Prop where
  | refl (u : V) : ResidualPathLength φ u u 0
  | tail {u v w : V} (n : ℕ) : ResidualPathLength φ u v n → Flow.residualEdge φ v w →
      ResidualPathLength φ u w (n + 1)

/-- Concatenation of two residual paths. -/
lemma ResidualPathLength.trans {φ : Flow V G} {u v w : V} {m n : ℕ}
    (h1 : ResidualPathLength φ u v m) (h2 : ResidualPathLength φ v w n) :
    ResidualPathLength φ u w (m + n) := by
  induction h2 generalizing u with
  | refl =>
      simp
      exact h1
  | tail n' h_prev h_edge ih =>
      rename_i mid
      have h_to_mid : ResidualPathLength φ u mid (m + n') := ih u h1
      have h_to_w : ResidualPathLength φ u w ((m + n') + 1) :=
        ResidualPathLength.tail (m + n') h_to_mid h_edge
      simpa [add_assoc, add_comm 1, add_left_comm 1, add_comm n', add_assoc] using h_to_w

/-- `IsShortestDist φ u v d` holds iff `d` is the shortest path distance (in
number of edges) from `u` to `v` in the residual network `G_φ`.

If `v` is not reachable from `u`, the predicate does not hold for any `d`. -/
def IsShortestDist (φ : Flow V G) (u v : V) (d : ℕ) : Prop :=
  ResidualPathLength φ u v d ∧ ∀ n, ResidualPathLength φ u v n → d ≤ n

/-- The source is at distance 0 from itself. -/
lemma isShortestDist_self (φ : Flow V G) (u : V) : IsShortestDist φ u u 0 := by
  refine ⟨ResidualPathLength.refl u, ?_⟩
  intro n hn
  cases hn with
  | refl => exact Nat.zero_le _
  | tail m _ _ => exact Nat.succ_ne_zero m ▸ Nat.zero_le _

/-- The shortest distance is unique. -/
lemma IsShortestDist.unique {φ : Flow V G} {u v : V} {d₁ d₂ : ℕ}
    (h₁ : IsShortestDist φ u v d₁) (h₂ : IsShortestDist φ u v d₂) : d₁ = d₂ := by
  rcases h₁ with ⟨hpath₁, hmin₁⟩
  rcases h₂ with ⟨hpath₂, hmin₂⟩
  exact le_antisymm (hmin₁ d₂ hpath₂) (hmin₂ d₁ hpath₁)

/-- If `(u,v)` is a residual edge and `d` is the shortest distance from `s` to
`u`, then there is a shortest distance from `s` to `v` of at most `d+1`.

In other words, `δ_f(s,v) ≤ δ_f(s,u) + 1`. -/
lemma isShortestDist_triangle (φ : Flow V G) (s u v : V) (d : ℕ)
    (hsu : IsShortestDist φ s u d) (h_edge : Flow.residualEdge φ u v) :
    ∃ d', IsShortestDist φ s v d' ∧ d' ≤ d + 1 := by
  rcases hsu with ⟨hsu_path, hsu_min⟩
  have hsv_path : ResidualPathLength φ s v (d + 1) :=
    ResidualPathLength.tail d hsu_path h_edge
  have h_exists_v : ∃ n, ResidualPathLength φ s v n := ⟨d + 1, hsv_path⟩
  let d' := Nat.find h_exists_v
  have h_d'_path : ResidualPathLength φ s v d' := Nat.find_spec h_exists_v
  have h_d'_min : ∀ n, ResidualPathLength φ s v n → d' ≤ n :=
    fun n hn => Nat.find_min' h_exists_v hn
  have h_d'_le : d' ≤ d + 1 := Nat.find_min' h_exists_v hsv_path
  exact ⟨d', ⟨h_d'_path, h_d'_min⟩, h_d'_le⟩

/-- In a shortest path from `s` to `v` where `d ≠ 0`, the vertex immediately
preceding `v` on the path has a shortest distance `d-1`. -/
lemma exists_pred_on_path {φ : Flow V G} {s v : V} {d : ℕ}
    (hd : IsShortestDist φ s v d) (hd_pos : d ≠ 0) :
    ∃ u, Flow.residualEdge φ u v ∧ IsShortestDist φ s u (d - 1) := by
  rcases hd with ⟨hpath, hmin⟩
  rcases hpath with (hpath | d' u hpath_to_u h_edge)
  · exact (hd_pos rfl).elim
  · have h_u_min : ∀ n, ResidualPathLength φ s u n → d' ≤ n := by
      intro n hn
      have h_extend : ResidualPathLength φ s v (n + 1) :=
        ResidualPathLength.tail n hn h_edge
      have h_d_le : d' + 1 ≤ n + 1 := hmin (n + 1) h_extend
      omega
    refine ⟨u, h_edge, hpath_to_u, h_u_min⟩

end ResidualDistances

/-! ## Suffix of a path along a shortest path -/

section PathSuffix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- The suffix of a path `p` from index `k` to the end (`G.t`) is a valid
residual path of length `p.length - 1 - k`.  Requires `k < p.length`. -/
lemma suffix_path (φ : Flow V G) (p : List V)
    (h_edges : ∀ i, i < p.length - 1 → Flow.residualEdge φ (p.get i) (p.get (i+1)))
    (h_end : p.getLast? = some G.t) (hp_nonempty : p ≠ [])
    (k : ℕ) (hk : k < p.length) :
    ResidualPathLength φ (p.get k) G.t (p.length - 1 - k) := by
  set n := p.length - 1 with hn
  have h_last : p.get n = G.t := by
    have h_getLast : p.getLast = G.t := by
      have h_some : some (p.getLast) = some G.t := by
        simpa [hp_nonempty] using h_end
      exact Option.some_inj.mp h_some
    have h_get_eq : p.get (p.length - 1) = p.getLast := by
      simp [hp_nonempty]
    simpa [hn, h_get_eq] using h_getLast
  have hP_n : ResidualPathLength φ (p.get n) G.t (n - n) := by
    have : n - n = 0 := Nat.sub_self n
    simp [this, h_last, ResidualPathLength.refl]
  have h_step : ∀ i < n, (ResidualPathLength φ (p.get (i+1)) G.t (n - (i+1))) →
      (ResidualPathLength φ (p.get i) G.t (n - i)) := by
    intro i hi h_next
    have hi_lt : i < p.length - 1 := by
      omega
    have h_edge : Flow.residualEdge φ (p.get i) (p.get (i+1)) := h_edges i hi_lt
    have h_tail : ResidualPathLength φ (p.get i) G.t ((n - (i+1)) + 1) :=
      ResidualPathLength.tail (n - (i+1)) h_next h_edge
    have h_eq : (n - (i+1)) + 1 = n - i := by
      omega
    simpa [h_eq] using h_tail
  have hk_le_n : k ≤ n := by
    omega
  have h_result : ResidualPathLength φ (p.get k) G.t (n - k) :=
    Nat.decreasingInduction h_step hk_le_n hP_n
  simpa [hn] using h_result

end PathSuffix

/-! ## Edmonds-Karp augmentation -/

section EdmondsKarp

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- `ShortestAugmentingPath φ p` holds iff `p` is a shortest augmenting path
from `G.s` to `G.t` in the residual network `G_φ`.

The path is represented as a list of vertices `[G.s, ..., G.t]`.  It must be
a valid residual path whose length equals `δ_φ(G.s, G.t)`. -/
structure ShortestAugmentingPath (φ : Flow V G) where
  /-- The vertices of the augmenting path. -/
  path : List V
  /-- The path is nonempty (contains at least the source). -/
  h_nonempty : path ≠ []
  /-- The path starts at the source. -/
  h_start : path.head? = some G.s
  /-- The path ends at the sink. -/
  h_end : path.getLast? = some G.t
  /-- Every consecutive pair is a residual edge. -/
  h_edges : ∀ i, i < path.length - 1 → Flow.residualEdge φ (path.get i) (path.get (i+1))
  /-- The path length (number of edges) equals the shortest-path distance
  from `G.s` to `G.t` in `G_φ`. -/
  h_shortest : IsShortestDist φ G.s G.t (path.length - 1)

/-- The first vertex of a `ShortestAugmentingPath` is the source. -/
lemma ShortestAugmentingPath.first_is_s (φ : Flow V G) (saug : ShortestAugmentingPath φ) :
    saug.path.get 0 = G.s := by
  have h0 : some (saug.path.get 0) = saug.path.head? := by
    simp [saug.h_nonempty]
  simpa [h0, saug.h_start] using rfl

/-- The last vertex of a `ShortestAugmentingPath` is the sink. -/
lemma ShortestAugmentingPath.last_is_t (φ : Flow V G) (saug : ShortestAugmentingPath φ) :
    saug.path.get (saug.path.length - 1) = G.t := by
  have h_getLast : saug.path.getLast = G.t := by
    have h_some : some (saug.path.getLast) = some G.t := by
      simpa [saug.h_nonempty] using saug.h_end
    exact Option.some_inj.mp h_some
  have h_get_eq : saug.path.get (saug.path.length - 1) = saug.path.getLast := by
    simp [saug.h_nonempty]
  simpa [h_get_eq] using h_getLast

/-- The prefix of a shortest augmenting path to any vertex on the path is a
shortest path to that vertex.  Formally, for any index `i < path.length`, the
shortest distance from `G.s` to `path.get i` is exactly `i`.  This follows
from the optimal-substructure property of shortest paths. -/
lemma shortest_path_prefix (φ : Flow V G) (saug : ShortestAugmentingPath φ)
    (i : ℕ) (hi : i < saug.path.length) :
    IsShortestDist φ G.s (saug.path.get i) i := by
  induction' i with k ih
  · -- i = 0
    have h0 : saug.path.get 0 = G.s := ShortestAugmentingPath.first_is_s φ saug
    rw [h0]
    exact isShortestDist_self φ G.s
  · -- i = k+1, need to show distance is k+1
    have hk_succ_lt : k + 1 < saug.path.length := hi
    have hk_lt : k < saug.path.length := by omega
    have hk_lt' : k < saug.path.length - 1 := by
      have hp_len_pos : saug.path.length ≥ 1 := by
        have hne : saug.path ≠ [] := saug.h_nonempty
        exact Nat.pos_of_ne_zero (by
          intro hzero
          apply hne
          simpa using hzero)
      omega
    have h_edge : Flow.residualEdge φ (saug.path.get k) (saug.path.get (k+1)) :=
      saug.h_edges k hk_lt'
    rcases isShortestDist_triangle φ G.s (saug.path.get k) (saug.path.get (k+1)) k
      (ih hk_lt) h_edge with ⟨d, hd, hd_le⟩
    -- Need to show d = k+1
    have h_ge : k + 1 ≤ d := by
      by_contra! hlt
      -- hlt: d < k+1, so d ≤ k
      have hd_le_k : d ≤ k := by omega
      rcases hd with ⟨hd_path, _⟩
      -- Suffix path from (k+1) to G.t
      have h_suffix : ResidualPathLength φ (saug.path.get (k+1)) G.t
          (saug.path.length - 1 - (k+1)) :=
        suffix_path φ saug.path saug.h_edges saug.h_end saug.h_nonempty (k+1) (by omega)
      -- Concatenated path from G.s to G.t
      have h_total : ResidualPathLength φ G.s G.t
          (d + (saug.path.length - 1 - (k+1))) :=
        hd_path.trans h_suffix
      rcases saug.h_shortest with ⟨_, hmin⟩
      have h_contra : saug.path.length - 1 ≤ d + (saug.path.length - 1 - (k+1)) :=
        hmin (d + (saug.path.length - 1 - (k+1))) h_total
      -- But d + (p.length - 1 - (k+1)) ≤ p.length - 2 < p.length - 1
      have h_sum_le : d + (saug.path.length - 1 - (k+1)) ≤ saug.path.length - 2 := by
        omega
      omega
    have h_eq : d = k + 1 := by omega
    simpa [h_eq] using hd

/-- If a vertex `u` is reachable from `G.s` in the augmented residual network
`G_φ'`, then it was already reachable in `G_φ`.  This holds because every new
residual edge in `G_φ'` is the reverse of a forward edge on the augmenting
path `p`, and the vertices of `p` are already reachable in `G_φ`. -/
lemma reachable_if_reachable_in_augmented (φ φ' : Flow V G)
    (saug : ShortestAugmentingPath φ)
    (h_new_edge_reverse : ∀ u v, Flow.residualEdge φ' u v → ¬Flow.residualEdge φ u v →
      ∃ i, i < saug.path.length - 1 ∧ saug.path.get i = v ∧ saug.path.get (i+1) = u)
    (u : V) (m : ℕ) (hd' : IsShortestDist φ' G.s u m) :
    ∃ d, IsShortestDist φ G.s u d := by
  rcases hd' with ⟨hpath', hmin'⟩
  induction hpath' with
  | refl =>
      refine ⟨0, isShortestDist_self φ G.s⟩
  | tail n hpath_to_v h_edge ih =>
      rename_i v
      rcases ih with ⟨dv, hdv⟩
      by_cases h_edge_old : Flow.residualEdge φ v u
      · -- Edge existed in G_φ
        rcases isShortestDist_triangle φ G.s v u dv hdv h_edge_old with ⟨du, hdu, hdu_le⟩
        exact ⟨du, hdu⟩
      · -- Edge is new in G_φ'; (u,v) is on the augmenting path
        rcases h_new_edge_reverse v u h_edge h_edge_old with ⟨i, hi, hvi, hui⟩
        -- hui: saug.path.get i = u, hvi: saug.path.get (i+1) = v
        have hi_lt_len : i < saug.path.length := by omega
        have h_prefix_u : IsShortestDist φ G.s (saug.path.get i) i :=
          shortest_path_prefix φ saug i hi_lt_len
        have hu_eq : saug.path.get i = u := by
          simpa [hui] using rfl
        have h_du : IsShortestDist φ G.s u i := by
          simpa [hu_eq] using h_prefix_u
        exact ⟨i, h_du⟩

/-- **Lemma 26.7 (Monotonic distance).**  Let `φ` be a flow and let `φ'` be the
flow obtained by augmenting `φ` along a shortest augmenting path `p`.  Then the
shortest-path distance `δ_f(s,v)` in the residual network is nondecreasing for
every vertex `v`.

Formally, if `IsShortestDist φ G.s v d` and `IsShortestDist φ' G.s v d'`, then
`d ≤ d'`.  (If `v` is not reachable in `G_{φ'}`, the second hypothesis never
holds, making the statement vacuously true.)

The proof follows CLRS Lemma 26.7.  We use the well-ordering principle on the
counterexample distance `d'`.  Let `n` be the minimal distance at which a
counterexample exists.  Then `n ≠ 0` (since `δ_f'(s,s) = 0 = δ_f(s,s)`).
Let `u` be the vertex immediately before `v` on a shortest path from `s` to `v`
in `G_{φ'}`; then `δ_{φ'}(s,u) = n - 1`.  By minimality of `n`, the distance to
`u` did not decrease, so `δ_φ(s,u) ≤ n - 1`.

- If `(u,v) ∈ G_φ`, then the triangle inequality gives
  `d = δ_φ(s,v) ≤ δ_φ(s,u) + 1 ≤ n`, contracting `n < d`.
- If `(u,v) ∉ G_φ`, then `(v,u)` lies on the augmenting path (by the
  `h_new_edge_reverse` hypothesis).  Because `p` is a shortest path,
  `δ_φ(s,u) = δ_φ(s,v) + 1`.  Hence `n = (n-1) + 1 ≥ δ_φ(s,u) + 1 = d + 2 > d`,
  again contradicting `n < d`. -/
theorem shortest_path_nondec (φ φ' : Flow V G) (saug : ShortestAugmentingPath φ)
    (h_new_edge_reverse : ∀ u v, Flow.residualEdge φ' u v → ¬Flow.residualEdge φ u v →
      ∃ i, i < saug.path.length - 1 ∧ saug.path.get i = v ∧ saug.path.get (i+1) = u)
    (v : V) (d d' : ℕ) (hd : IsShortestDist φ G.s v d) (hd' : IsShortestDist φ' G.s v d') :
    d ≤ d' := by
  by_contra! hlt
  -- hlt: d' < d, so (v, d') is a counterexample
  let P (n : ℕ) : Prop := ∃ (x : V) (dx : ℕ), IsShortestDist φ G.s x dx ∧ IsShortestDist φ' G.s x n ∧ n < dx
  have h_exists_P : ∃ n, P n := ⟨d', v, d, hd, hd', hlt⟩
  let n := Nat.find h_exists_P
  have hP_n : P n := Nat.find_spec h_exists_P
  have hmin : ∀ m < n, ¬ P m := Nat.find_min h_exists_P
  rcases hP_n with ⟨v0, d0, hd_v0, hd_v0', hn_lt_d0⟩
  -- n is minimal counterexample distance
  have hn_pos : n ≠ 0 := by
    intro hzero
    subst hzero
    rcases hd_v0' with ⟨hpath', hmin'⟩
    have h_vs : v0 = G.s := by
      cases hpath' with
      | refl => rfl
      | tail _ _ _ =>
        -- n = 0 but there's a tail => impossible
        have : 0 = n.succ := by omega
        omega
    subst h_vs
    have h_d0_0 : d0 = 0 := hd_v0.unique (isShortestDist_self φ G.s)
    omega
  -- Get predecessor u on shortest path to v0 in G_φ'
  rcases exists_pred_on_path hd_v0' hn_pos with ⟨u, h_edge_uv, hd'_u⟩
  -- hd'_u : IsShortestDist φ' G.s u (n - 1)
  have hm_lt_n : n - 1 < n := by
    omega
  -- Since n-1 < n, by minimality of n, it's not a counterexample.
  -- So for any x, dx with IsShortestDist φ s x dx and IsShortestDist φ' s x (n-1), we have dx ≤ n-1
  by_cases h_edge_uv_old : Flow.residualEdge φ u v0
  · -- Case 1: (u, v0) ∈ G_φ
    -- Show u is reachable in G_φ, then apply minimality
    have h_exists_du : ∃ du, IsShortestDist φ G.s u du :=
      reachable_if_reachable_in_augmented φ φ' saug h_new_edge_reverse u (n-1) hd'_u
    rcases h_exists_du with ⟨du, hdu⟩
    have h_du_le : du ≤ n - 1 := by
      by_contra! hgt
      -- Then (n-1) is a counterexample via u
      exact hmin (n-1) hm_lt_n ⟨u, du, hdu, hd'_u, hgt⟩
    rcases isShortestDist_triangle φ G.s u v0 du hdu h_edge_uv_old with ⟨dv, hdv, hdv_le⟩
    have h_d0_eq_dv : d0 = dv := hd_v0.unique hdv
    have h_d0_le_du_plus_one : d0 ≤ du + 1 := by
      rw [h_d0_eq_dv]
      exact hdv_le
    omega
  · -- Case 2: (u, v0) new in G_φ'; its reverse (v0, u) is on the augmenting path
    rcases h_new_edge_reverse u v0 h_edge_uv h_edge_uv_old with ⟨i, hi, hvi, hui⟩
    -- hui: saug.path.get i = v0, hvi: saug.path.get (i+1) = u
    have hi_lt_len : i < saug.path.length := by omega
    have hi_succ_lt_len : i + 1 < saug.path.length := by omega
    have h_prefix_v : IsShortestDist φ G.s (saug.path.get i) i :=
      shortest_path_prefix φ saug i hi_lt_len
    have h_prefix_u : IsShortestDist φ G.s (saug.path.get (i+1)) (i+1) :=
      shortest_path_prefix φ saug (i+1) hi_succ_lt_len
    have h_d0_eq_i : d0 = i := hd_v0.unique (by simpa [hui] using h_prefix_v)
    have h_du : IsShortestDist φ G.s u (i+1) := by
      simpa [hvi] using h_prefix_u
    have h_du_le : i + 1 ≤ n - 1 := by
      by_contra! hgt
      -- Then (n-1) is a counterexample via u
      exact hmin (n-1) hm_lt_n ⟨u, i+1, h_du, hd'_u, hgt⟩
    -- Now n = (n-1) + 1 ≥ (i+1) + 1 = i + 2 = d0 + 2 > d0, contradiction
    omega

end EdmondsKarp

end Chapter26
end CLRS
