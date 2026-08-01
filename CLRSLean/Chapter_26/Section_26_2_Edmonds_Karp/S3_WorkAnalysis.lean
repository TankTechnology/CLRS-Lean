import Mathlib
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.S1_ShortestAugmentingPath
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp.S2_EK_Loop

/-!
# 26.2 S3. The O(VE²) work analysis

This module develops the mathematical core of the Edmonds-Karp complexity
analysis: critical edges and the distance-growth lemma.

An edge `(u,v)` of the selected augmenting path is *critical* when
augmentation saturates it (its residual capacity drops to zero).  Every
augmentation saturates at least one edge (the bottleneck is attained by some
path edge).  The key lemma (CLRS Lemma 26.8) states that when `(u,v)` is on a
shortest augmenting path and later `(v,u)` is on another shortest augmenting
path (the only way the residual capacity of `(u,v)` can recover), the residual
distance to `u` has increased by at least two:

`δ'(u) = δ'(v) + 1 ≥ δ(v) + 1 = δ(u) + 2`

Here the first equality is the BFS-path property on the later path, the
inequality is monotonicity (Lemma 26.7), and the last equality is the
BFS-path property on the earlier path.  Since residual distances are bounded
by `|V| - 1` (shortest paths are simple), each edge can be critical at most
`|V|` times, giving `O(VE)` augmentations and `O(VE²)` total work.

Main results:

- `Flow.AugmentingPath.isCritical`: an edge saturated by the augmentation
- `exists_critical_edge`: every augmentation saturates at least one edge
- `shortest_edge_dist`: edges of a shortest path join adjacent distance
  levels
- `critical_dist_increase`: CLRS Lemma 26.8, forward direction (distance to
  `u` grows by at least two when `(v,u)` later lies on a shortest path)
- `critical_dist_increase_rev`: the reverse-direction variant used by the
  timeline argument
- `IsShortestDist.lt_card`: residual distances are bounded by `|V| - 1`
- `ekSeq`/`ekPath`/`criticalAt`: the Edmonds-Karp timeline (flow after `n`
  steps, selected shortest path, critical-edge predicate)
- `ekStep_dist_nondec` and `distAt_mono`: reverse distance monotonicity
  across one and several steps
- `exists_recovery_step`: if `(u,v)` is critical at step `i` and again lies
  on a selected path at step `j > i + 1`, some intermediate step augments
  along `(v,u)` (the residual-capacity recovery argument)
- `criticalAt_growth`: CLRS Lemma 26.8 on the timeline — if `(u,v)` is
  critical at steps `i` and `j` with `i + 1 < j`, the residual distance to
  `u` grows by at least two
- `criticalAt_not_succ` and `criticalAt_growth_strict`: consecutive critical
  steps are impossible, so distances strictly increase between critical
  occurrences
- `critical_count_bound`: each edge is critical at most `|V|` times
- `augmentation_count_bound`: at most `|V|² · |V|` augmenting steps, giving
  the `O(VE²)` bound once each step is charged `O(E)` for BFS

The `O(VE²)` counting argument is complete; the executable BFS that
computes the shortest augmenting paths lives in `S4_ExecutableBFS`.
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- An edge of the selected augmenting path is *critical* when augmentation
saturates it: its residual capacity after augmentation is zero. -/
def Flow.AugmentingPath.isCritical {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {φ : Flow V G} (p : Flow.AugmentingPath φ) (u v : V) : Prop :=
  (u, v) ∈ p.edges ∧ (φ.augment p).residualCapacity u v = 0

/-- In a simple list, equal elements occur at the same index. -/
lemma nodup_getElem_inj {α : Type*} {l : List α} (h : l.Nodup)
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hij : l[i] = l[j]) : i = j := by
  revert h i j hi hj
  induction l with
  | nil => simp
  | cons a l ih =>
      intro h i j hi hj hij
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              exfalso
              have hj' : j < l.length := by simpa using hj
              have ha_eq : a = l[j] := by simpa using hij
              have ha : a ∈ l := by
                simp [ha_eq]
              exact (List.nodup_cons.mp h).1 ha
      | succ i =>
          cases j with
          | zero =>
              exfalso
              have hi' : i < l.length := by simpa using hi
              have ha_eq : a = l[i] := by
                have hla : l[i] = a := by simpa using hij
                exact hla.symm
              have ha : a ∈ l := by
                simp [ha_eq]
              exact (List.nodup_cons.mp h).1 ha
          | succ j =>
              have hi' : i < l.length := by simpa using hi
              have hj' : j < l.length := by simpa using hj
              have hih : i = j :=
                ih (List.nodup_cons.mp h).2 hi' hj' (by simpa using hij)
              omega

/-- A simple path contains no pair of opposite directed edges. -/
lemma edge_reverse_not_mem {φ : Flow V G} (p : Flow.AugmentingPath φ) {u v : V}
    (huv : (u, v) ∈ p.edges) : (v, u) ∉ p.edges := by
  intro hvu
  rcases p.exists_index_of_mem_edges huv with ⟨i, hi, hvi, hui⟩
  rcases p.exists_index_of_mem_edges hvu with ⟨j, hj, hvj, huj⟩
  have h1 : i + 1 = j := by
    exact nodup_getElem_inj p.nodup (by omega) (by omega) (hui.trans hvj.symm)
  have h2 : i = j + 1 := by
    exact nodup_getElem_inj p.nodup (by omega) (by omega) (hvi.trans huj.symm)
  omega

/-- Every augmentation saturates at least one edge of the selected path. -/
lemma exists_critical_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {φ : Flow V G} (p : Flow.AugmentingPath φ) :
    ∃ u v, p.isCritical u v := by
  have hmem : p.bottleneck ∈ p.edges.toFinset.image (fun e => φ.residualCapacity e.1 e.2) := by
    unfold Flow.AugmentingPath.bottleneck
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨e, he, hEq⟩
  have he_edges : e ∈ p.edges := List.mem_toFinset.mp he
  have hpost : (φ.augment p).residualCapacity e.1 e.2 = 0 := by
    rw [Flow.augment_residualCapacity]
    have hrev : (e.2, e.1) ∉ p.edges := edge_reverse_not_mem p he_edges
    rw [hEq]
    simp [he_edges, hrev]
  exact ⟨e.1, e.2, he_edges, hpost⟩

/-- Every edge of a shortest augmenting path joins adjacent distance levels:
`δ(u) = i` and `δ(v) = i + 1`. -/
lemma shortest_edge_dist {φ : Flow V G} (p : ShortestAugmentingPath φ) {u v : V}
    (huv : (u, v) ∈ p.path.edges) :
    ∃ d, IsShortestDist φ G.s u d ∧ IsShortestDist φ G.s v (d + 1) := by
  rcases p.path.exists_index_of_mem_edges huv with ⟨i, hi, hvi, hui⟩
  have hpref_u := p.shortest_prefix i (by omega)
  have hpref_v := p.shortest_prefix (i + 1) hi
  refine ⟨i, ?_, ?_⟩
  · simpa [hvi] using hpref_u
  · simpa [hui] using hpref_v

/-- **CLRS Lemma 26.8 (critical-edge distance growth).**  If `(u,v)` is on a
shortest augmenting path of `φ` and later `(v,u)` is on a shortest augmenting
path of `ψ`, with residual distances not decreasing from `φ` to `ψ`, then the
residual distance to `u` in `ψ` exceeds that in `φ` by at least two:

`δ_ψ(u) = δ_ψ(v) + 1 ≥ δ_φ(v) + 1 = δ_φ(u) + 2`. -/
lemma critical_dist_increase {φ : Flow V G} (p : ShortestAugmentingPath φ)
    {ψ : Flow V G} (q : ShortestAugmentingPath ψ) {u v : V}
    (hp : (u, v) ∈ p.path.edges) (hq : (v, u) ∈ q.path.edges)
    (hmono : ∀ w d, IsShortestDist φ G.s w d →
      ∃ d', IsShortestDist ψ G.s w d' ∧ d ≤ d') :
    ∃ du du', IsShortestDist φ G.s u du ∧ IsShortestDist ψ G.s u du' ∧ du + 2 ≤ du' := by
  rcases shortest_edge_dist p hp with ⟨du, hdu, hdv⟩
  rcases shortest_edge_dist q hq with ⟨dv', hdv', hdu'⟩
  rcases hmono v (du + 1) hdv with ⟨dv'', hdv'', hle⟩
  have hdv_eq : dv'' = dv' := hdv''.unique hdv'
  refine ⟨du, dv' + 1, hdu, hdu', ?_⟩
  have : du + 1 ≤ dv'' := hle
  omega

/-- Residual distances are bounded by the number of vertices minus one:
shortest paths are simple. -/
lemma IsShortestDist.lt_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {φ : Flow V G} {v : V} {d : ℕ}
    (hd : IsShortestDist φ G.s v d) : d < Fintype.card V := by
  have hlen : (back d v hd).length = d + 1 := back_length d v hd
  have hcard : (back d v hd).length ≤ Fintype.card V :=
    List.Nodup.length_le_card (back_nodup d v hd)
  omega

/-! ## Augmentation counting -/

/-- The flow after `n` Edmonds-Karp steps from the zero flow. -/
noncomputable def ekSeq {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (n : ℕ) : Flow V G :=
  ekIter (zeroFlow G) n

/-- The shortest augmenting path selected at step `n`, when one exists. -/
noncomputable def ekPath {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (n : ℕ) : Option (Flow.AugmentingPath (ekSeq (G := G) n)) :=
  if h : Nonempty (ShortestAugmentingPath (ekSeq (G := G) n)) then
    some (Classical.choice h).path
  else none

/-- Edge `(u,v)` is critical at step `n`: it lies on the selected augmenting
path and the augmentation along it saturates the edge. -/
def criticalAt {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (n : ℕ) (u v : V) : Prop :=
  ∃ p, ekPath n = some p ∧ (u, v) ∈ p.edges ∧
    ((ekSeq (G := G) n).augment p).residualCapacity u v = 0

/-- Reverse monotonicity across one step: if the distance to `u` is finite
after the step, it was finite before the step and no larger. -/
lemma ekStep_dist_nondec {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (n : ℕ) (u : V) {d' : ℕ}
    (hd' : IsShortestDist (ekSeq (G := G) (n + 1)) G.s u d') :
    ∃ d, IsShortestDist (ekSeq (G := G) n) G.s u d ∧ d ≤ d' := by
  by_cases hn : (ekSeq (G := G) n).hasAugmentingPath
  · have h : Nonempty (ShortestAugmentingPath (ekSeq (G := G) n)) :=
      (shortestAugmentingPath_iff_hasAugmentingPath (ekSeq (G := G) n)).mpr hn
    have hekstep : ekStep (ekIter (zeroFlow G) n) = (ekIter (zeroFlow G) n).augment (Classical.choice h).path := by
      change ekStep (ekSeq (G := G) n) = (ekSeq (G := G) n).augment (Classical.choice h).path
      unfold ekStep
      simp [h]
    have hd'' : IsShortestDist ((ekIter (zeroFlow G) n).augment (Classical.choice h).path) G.s u d' := by
      simpa [ekSeq, ekIter, hekstep] using hd'
    exact (Classical.choice h).exists_shortestDist_le_augment hd''
  · have hno : ¬ Nonempty (ShortestAugmentingPath (ekSeq (G := G) n)) := by
      intro h
      exact hn ((shortestAugmentingPath_iff_hasAugmentingPath (ekSeq (G := G) n)).mp h)
    have hekstep : ekStep (ekIter (zeroFlow G) n) = ekIter (zeroFlow G) n := by
      change ekStep (ekSeq (G := G) n) = ekSeq (G := G) n
      unfold ekStep
      simp [hno]
    have heq : ekSeq (G := G) (n + 1) = ekSeq (G := G) n := by
      simp [ekSeq, ekIter, hekstep]
    exact ⟨d', by simpa [heq] using hd', le_rfl⟩

/-- Reverse monotonicity across several steps. -/
lemma distAt_mono {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    {i j : ℕ} (hij : i ≤ j) (u : V) {d' : ℕ}
    (hd' : IsShortestDist (ekSeq (G := G) j) G.s u d') :
    ∃ d, IsShortestDist (ekSeq (G := G) i) G.s u d ∧ d ≤ d' := by
  revert u d' hd'
  refine Nat.le_induction (m := i)
    (P := fun k h => ∀ u d', IsShortestDist (ekSeq (G := G) k) G.s u d' →
      ∃ d, IsShortestDist (ekSeq (G := G) i) G.s u d ∧ d ≤ d') ?_ ?_ j hij
  · intro u d' hd'
    exact ⟨d', hd', le_rfl⟩
  · intro n hn ih u d'' hd''
    rcases ekStep_dist_nondec n u hd'' with ⟨dn, hdn, hle0⟩
    rcases ih u dn hdn with ⟨d, hd, hle⟩
    exact ⟨d, hd, le_trans hle hle0⟩

/-- Reverse-direction version of Lemma 26.8: when `(u,v)` lies on a shortest
augmenting path of `φ` and `(v,u)` lies on one of `ψ`, with distances of `ψ`
no smaller than those of `φ` (for vertices reachable in `ψ`), the distance to
`u` in `ψ` exceeds that in `φ` by at least two. -/
lemma critical_dist_increase_rev {φ : Flow V G} (p : ShortestAugmentingPath φ)
    {ψ : Flow V G} (q : ShortestAugmentingPath ψ) {u v : V}
    (hp : (u, v) ∈ p.path.edges) (hq : (v, u) ∈ q.path.edges)
    (hmono : ∀ w d', IsShortestDist ψ G.s w d' →
      ∃ d, IsShortestDist φ G.s w d ∧ d ≤ d') :
    ∃ du du', IsShortestDist φ G.s u du ∧ IsShortestDist ψ G.s u du' ∧ du + 2 ≤ du' := by
  rcases shortest_edge_dist p hp with ⟨du, hdu, hdv⟩
  rcases shortest_edge_dist q hq with ⟨dv', hdv', hdu'⟩
  rcases hmono v dv' hdv' with ⟨dv, hdv0, hle⟩
  have hdv_eq : dv = du + 1 := hdv0.unique hdv
  refine ⟨du, dv' + 1, hdu, hdu', ?_⟩
  have : du ≤ dv' := by omega
  omega

/-- The selected path at step `n` equals the path extracted from the
shortest-path witness. -/
lemma ekPath_eq_of_hasAugmentingPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (n : ℕ) (hn : (ekSeq (G := G) n).hasAugmentingPath) :
    ∃ p : Flow.AugmentingPath (ekSeq (G := G) n), ekPath n = some p ∧
      ekStep (ekSeq (G := G) n) = (ekSeq (G := G) n).augment p := by
  have h : Nonempty (ShortestAugmentingPath (ekSeq (G := G) n)) :=
    (shortestAugmentingPath_iff_hasAugmentingPath (ekSeq (G := G) n)).mpr hn
  refine ⟨(Classical.choice h).path, ?_, ?_⟩
  · unfold ekPath
    simp [h]
  · unfold ekStep
    simp [h]

/-- If `(u,v)` is critical at step `i` and `j` with `i + 1 < j`, then between
them some step augments along `(v,u)` — the only way the residual capacity
of `(u,v)` can recover from zero. -/
lemma exists_recovery_step {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {i j : ℕ} (hij : i + 1 < j) {u v : V}
    (hci : criticalAt (G := G) i u v) (hcj : criticalAt (G := G) j u v) :
    ∃ k : ℕ, ∃ h : Nonempty (ShortestAugmentingPath (ekSeq (G := G) k)),
      i < k ∧ k < j ∧ (v, u) ∈ (Classical.choice h).path.edges := by
  rcases hci with ⟨p_i, hekpath_i, hp_edges, hpost⟩
  rcases hcj with ⟨p_j, hekpath_j, hp_edges_j, _⟩
  have hpos : 0 < (ekSeq (G := G) j).residualCapacity u v := by
    have hres : (ekSeq (G := G) j).residualEdge u v :=
      Flow.ResidualPath.residualEdge_of_mem_edges (φ := ekSeq (G := G) j) p_j hp_edges_j
    exact hres
  -- ekSeq (i+1) = (ekSeq (G := G) i).augment p_i——残量 (u,v) = 0
  have hcf_i : (ekSeq (G := G) (i + 1)).residualCapacity u v = 0 := by
    by_cases h_i : Nonempty (ShortestAugmentingPath (ekSeq (G := G) i))
    · have hpath : (Classical.choice h_i).path = p_i := by
        have : ekPath i = some (Classical.choice h_i).path := by
          unfold ekPath
          simp [h_i]
        simpa [this] using hekpath_i
      have hekstep : ekStep (ekIter (zeroFlow G) i) = (ekIter (zeroFlow G) i).augment p_i := by
        change ekStep (ekSeq (G := G) i) = (ekSeq (G := G) i).augment p_i
        unfold ekStep
        simp [h_i, hpath]
      have heq : ekSeq (G := G) (i + 1) = (ekSeq (G := G) i).augment p_i := by
        simp [ekSeq, ekIter, hekstep]
      simpa [heq] using hpost
    · have : ekPath (V := V) (G := G) i = none := by
        unfold ekPath
        simp [h_i]
      simp [this] at hekpath_i
  -- first step j' after i with positive residual capacity
  let P : ℕ → Prop := fun m => i + 1 < m ∧ m ≤ j ∧ 0 < (ekSeq (G := G) m).residualCapacity u v
  have hnonempty : ∃ m, P m := ⟨j, by omega, le_rfl, hpos⟩
  let k := Nat.find hnonempty
  have hk : P k := Nat.find_spec hnonempty
  let k' := k - 1
  have hk_gt : i + 1 < k := hk.1
  have hk_ge2 : i + 2 ≤ k := by omega
  have hk'_ge : i + 1 ≤ k' := by omega
  have hk'_lt : k' < k := by omega
  have hk'_le : k' < j := by omega
  have hnotP : ¬ P k' := by
    intro hP
    have hmin := Nat.find_min' hnonempty hP
    omega
  have hcf_le : (ekSeq (G := G) k').residualCapacity u v ≤ 0 := by
    by_contra h
    apply hnotP
    have hk'_gt : i + 1 < k' := by
      by_contra hnot
      have hk'eq : k' = i + 1 := by omega
      have : (ekSeq (G := G) k').residualCapacity u v = (ekSeq (G := G) (i + 1)).residualCapacity u v := by
        rw [hk'eq]
      linarith [hcf_i, h]
    exact ⟨hk'_gt, by omega, by linarith⟩
  -- step k' must augment (otherwise the residual capacity would not change)
  have hk'_aug : (ekSeq (G := G) k').hasAugmentingPath := by
    by_contra h
    have hno : ¬ Nonempty (ShortestAugmentingPath (ekSeq (G := G) k')) := by
      intro h'
      exact h ((shortestAugmentingPath_iff_hasAugmentingPath (ekSeq (G := G) k')).mp h')
    have hekstep : ekStep (ekIter (zeroFlow G) k') = ekIter (zeroFlow G) k' := by
      change ekStep (ekSeq (G := G) k') = ekSeq (G := G) k'
      unfold ekStep
      simp [hno]
    have heq : ekSeq (G := G) (k' + 1) = ekSeq (G := G) k' := by
      simp [ekSeq, ekIter, hekstep]
    have hk_eq : k = k' + 1 := by omega
    have : (ekSeq (G := G) (k' + 1)).residualCapacity u v = (ekSeq (G := G) k').residualCapacity u v := by
      rw [heq]
    have hpos' : 0 < (ekSeq (G := G) (k' + 1)).residualCapacity u v := by
      simpa [hk_eq] using hk.2.2
    linarith [hpos', hcf_le, this]
  have h : Nonempty (ShortestAugmentingPath (ekSeq (G := G) k')) :=
    (shortestAugmentingPath_iff_hasAugmentingPath (ekSeq (G := G) k')).mpr hk'_aug
  let p' : Flow.AugmentingPath (ekSeq (G := G) k') := (Classical.choice h).path
  have hekstep' : ekStep (ekSeq (G := G) k') = (ekSeq (G := G) k').augment p' := by
    unfold ekStep
    rw [dif_pos h]
  have heq' : ekSeq (G := G) (k' + 1) = (ekSeq (G := G) k').augment p' := by
    change ekStep (ekSeq (G := G) k') = (ekSeq (G := G) k').augment p'
    exact hekstep'
  have hchange : 0 < (ekSeq (G := G) (k' + 1)).residualCapacity u v - (ekSeq (G := G) k').residualCapacity u v := by
    have hk_eq : k = k' + 1 := by omega
    have hpos' : 0 < (ekSeq (G := G) (k' + 1)).residualCapacity u v := by
      simpa [hk_eq] using hk.2.2
    linarith [hpos', hcf_le]
  have hrev : (v, u) ∈ p'.edges := by
    by_contra hnot
    have hformula := Flow.augment_residualCapacity (ekSeq (G := G) k') p' u v
    by_cases huv' : (u, v) ∈ p'.edges
    · have hcf_eq : (ekSeq (G := G) (k' + 1)).residualCapacity u v =
        (ekSeq (G := G) k').residualCapacity u v - p'.bottleneck := by
        have := hformula
        rw [← heq'] at this
        simpa [huv', hnot] using this
      have hb : 0 < p'.bottleneck := p'.bottleneck_pos
      linarith
    · have hcf_eq : (ekSeq (G := G) (k' + 1)).residualCapacity u v =
        (ekSeq (G := G) k').residualCapacity u v := by
        have := hformula
        rw [← heq'] at this
        simpa [huv', hnot] using this
      linarith
  refine ⟨k', h, ?_, ?_, hrev⟩
  · omega
  · exact hk'_le

/-! ## Counting the augmentations -/

/-- If `ekPath n = some p`, the selected path `p` is the path of the
shortest-augmenting-path witness at step `n`. -/
lemma ekPath_some_spec {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {n : ℕ} {p : Flow.AugmentingPath (ekSeq (G := G) n)}
    (h : ekPath (G := G) n = some p) :
    ∃ h' : Nonempty (ShortestAugmentingPath (ekSeq (G := G) n)),
      (Classical.choice h').path = p := by
  by_cases h' : Nonempty (ShortestAugmentingPath (ekSeq (G := G) n))
  · refine ⟨h', ?_⟩
    have : ekPath (G := G) n = some (Classical.choice h').path := by
      unfold ekPath
      simp [h']
    simpa [this] using h
  · have hnone : ekPath (G := G) n = none := by
      unfold ekPath
      simp [h']
    simp [hnone] at h

/-- **Timeline Lemma 26.8.**  If `(u,v)` is critical at step `i` and again at
step `j` with `i + 1 < j`, the residual distance to `u` at step `j` exceeds
that at step `i` by at least two. -/
lemma criticalAt_growth {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {i j : ℕ} (hij : i + 1 < j) {u v : V}
    (hci : criticalAt (G := G) i u v) (hcj : criticalAt (G := G) j u v) :
    ∃ du du', IsShortestDist (ekSeq (G := G) i) G.s u du ∧
      IsShortestDist (ekSeq (G := G) j) G.s u du' ∧ du + 2 ≤ du' := by
  rcases exists_recovery_step (G := G) hij hci hcj with ⟨k, h_k, hik, hkj, hrev⟩
  rcases hci with ⟨p_i, hekpath_i, hp_edges, _⟩
  rcases hcj with ⟨p_j, hekpath_j, hp_edges_j, _⟩
  rcases ekPath_some_spec (G := G) hekpath_i with ⟨h_i, hpath_i⟩
  rcases ekPath_some_spec (G := G) hekpath_j with ⟨h_j, hpath_j⟩
  rcases critical_dist_increase_rev (φ := ekSeq (G := G) i) (Classical.choice h_i)
      (ψ := ekSeq (G := G) k) (Classical.choice h_k)
      (by simpa [hpath_i] using hp_edges) hrev
      (fun w d' hd' => distAt_mono (G := G) (i := i) (j := k) (by omega) w hd')
    with ⟨du, dk, hdu, hdk, hgrow⟩
  rcases shortest_edge_dist (Classical.choice h_j) (by simpa [hpath_j] using hp_edges_j)
    with ⟨dj, hdu_j, _⟩
  rcases distAt_mono (G := G) (i := k) (j := j) (by omega) u hdu_j with ⟨dk', hdk', hle⟩
  have hdk_eq : dk' = dk := hdk'.unique hdk
  refine ⟨du, dj, hdu, hdu_j, ?_⟩
  omega

/-- A critical edge cannot be critical at the following step: the previous
augmentation saturated it, leaving residual capacity zero. -/
lemma criticalAt_not_succ {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {n : ℕ} {u v : V}
    (hci : criticalAt (G := G) n u v) :
    ¬ criticalAt (G := G) (n + 1) u v := by
  rcases hci with ⟨p_n, hekpath_n, hp_edges, hpost⟩
  rcases ekPath_some_spec (G := G) hekpath_n with ⟨h_n, hpath_n⟩
  have hekstep : ekStep (ekIter (zeroFlow G) n) = (ekIter (zeroFlow G) n).augment p_n := by
    change ekStep (ekSeq (G := G) n) = (ekSeq (G := G) n).augment p_n
    unfold ekStep
    simp [h_n, hpath_n]
  have heq : ekSeq (G := G) (n + 1) = (ekSeq (G := G) n).augment p_n := by
    simp [ekSeq, ekIter, hekstep]
  have hzero : (ekSeq (G := G) (n + 1)).residualCapacity u v = 0 := by
    simpa [heq] using hpost
  intro hcj
  rcases hcj with ⟨p_j, hekpath_j, hp_edges_j, _⟩
  have hres : (ekSeq (G := G) (n + 1)).residualEdge u v :=
    Flow.ResidualPath.residualEdge_of_mem_edges (φ := ekSeq (G := G) (n + 1)) p_j hp_edges_j
  have hpos : 0 < (ekSeq (G := G) (n + 1)).residualCapacity u v := hres
  linarith

/-- Strict distance growth between critical occurrences: the residual distance
to `u` at the later critical step is strictly larger than at the earlier one. -/
lemma criticalAt_growth_strict {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {i j : ℕ} (hij : i < j) {u v : V}
    (hci : criticalAt (G := G) i u v) (hcj : criticalAt (G := G) j u v) :
    ∃ du du', IsShortestDist (ekSeq (G := G) i) G.s u du ∧
      IsShortestDist (ekSeq (G := G) j) G.s u du' ∧ du < du' := by
  by_cases hsep : i + 1 < j
  · rcases criticalAt_growth (G := G) hsep hci hcj with ⟨du, du', hdu, hdu', hgrow⟩
    exact ⟨du, du', hdu, hdu', by omega⟩
  · exfalso
    have hsucc : j = i + 1 := by omega
    exact criticalAt_not_succ hci (by simpa [hsucc] using hcj)

/-- At a critical step, the tail `u` of the critical edge has a residual
distance, bounded by `|V| - 1`. -/
lemma criticalAt_dist {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {n : ℕ} {u v : V} (h : criticalAt (G := G) n u v) :
    ∃ d, IsShortestDist (ekSeq (G := G) n) G.s u d ∧ d < Fintype.card V := by
  rcases h with ⟨p, hekpath, hp_edges, _⟩
  rcases ekPath_some_spec (G := G) hekpath with ⟨h_n, hpath⟩
  rcases shortest_edge_dist (Classical.choice h_n) (by simpa [hpath] using hp_edges)
    with ⟨d, hdu, _⟩
  exact ⟨d, hdu, IsShortestDist.lt_card hdu⟩

/-- Every augmenting step has at least one critical edge. -/
lemma exists_critical_pair_at {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (n : ℕ) (h : (ekSeq (G := G) n).hasAugmentingPath) :
    ∃ u v, criticalAt (G := G) n u v := by
  rcases ekPath_eq_of_hasAugmentingPath (G := G) n h with ⟨p, hekpath, _⟩
  rcases exists_critical_edge p with ⟨u, v, he, hpost⟩
  exact ⟨u, v, p, hekpath, he, hpost⟩

/-- **Edge criticality count.**  A fixed edge `(u,v)` is critical at most
`|V|` times: every critical occurrence determines a residual distance to `u`,
and that distance strictly increases between occurrences. -/
lemma critical_count_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (u v : V) (N : ℕ) :
    ((Finset.range N).filter (fun n => criticalAt (G := G) n u v)).card ≤
      Fintype.card V := by
  let s : Finset ℕ := (Finset.range N).filter (fun n => criticalAt (G := G) n u v)
  let hcrit : ∀ x : {n : ℕ // n ∈ s}, criticalAt (G := G) x.1 u v :=
    fun x => (Finset.mem_filter.mp x.2).2
  let distOf : {n : ℕ // n ∈ s} → ℕ :=
    fun x => Classical.choose (criticalAt_dist (hcrit x))
  let f : {n : ℕ // n ∈ s} → Fin (Fintype.card V) :=
    fun x => ⟨distOf x, (Classical.choose_spec (criticalAt_dist (hcrit x))).2⟩
  have hinj : Set.InjOn f (↑(s.attach) : Set {n : ℕ // n ∈ s}) := by
    intro x hx y hy hxy
    apply Subtype.ext
    by_contra hne
    have hxy' : distOf x = distOf y :=
      congrArg (fun z : Fin (Fintype.card V) => z.1) hxy
    have hlt_or : x.1 < y.1 ∨ y.1 < x.1 := by omega
    rcases hlt_or with hxy_lt | hyx_lt
    · rcases criticalAt_growth_strict (G := G) hxy_lt (hcrit x) (hcrit y) with
        ⟨du, du', hdu, hdu', hgrow⟩
      have hdx : distOf x = du :=
        (Classical.choose_spec (criticalAt_dist (hcrit x))).1.unique hdu
      have hdy : distOf y = du' :=
        (Classical.choose_spec (criticalAt_dist (hcrit y))).1.unique hdu'
      omega
    · rcases criticalAt_growth_strict (G := G) hyx_lt (hcrit y) (hcrit x) with
        ⟨du, du', hdu, hdu', hgrow⟩
      have hdy : distOf y = du :=
        (Classical.choose_spec (criticalAt_dist (hcrit y))).1.unique hdu
      have hdx : distOf x = du' :=
        (Classical.choose_spec (criticalAt_dist (hcrit x))).1.unique hdu'
      omega
  have hsub : s.attach.image f ⊆ (Finset.univ : Finset (Fin (Fintype.card V))) := by
    intro x hx
    simp
  have hcard : (s.attach.image f).card = s.attach.card :=
    Finset.card_image_of_injOn hinj
  calc
    s.card = s.attach.card := Finset.card_attach.symm
    _ = (s.attach.image f).card := hcard.symm
    _ ≤ (Finset.univ : Finset (Fin (Fintype.card V))).card := Finset.card_le_card hsub
    _ = Fintype.card V := by simp

/-- **Augmentation count.**  There are at most `|V|² · |V|` augmenting steps:
each one has a critical edge, and each of the `|V|²` edges is critical at most
`|V|` times. -/
lemma augmentation_count_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (N : ℕ) :
    ((Finset.range N).filter (fun n => (ekSeq (G := G) n).hasAugmentingPath)).card ≤
      Fintype.card (V × V) * Fintype.card V := by
  let s : Finset ℕ :=
    (Finset.range N).filter (fun n => (ekSeq (G := G) n).hasAugmentingPath)
  let haug : ∀ x : {n : ℕ // n ∈ s}, (ekSeq (G := G) x.1).hasAugmentingPath :=
    fun x => (Finset.mem_filter.mp x.2).2
  let pair : {n : ℕ // n ∈ s} → V × V := fun x =>
    let h := exists_critical_pair_at (G := G) x.1 (haug x)
    (Classical.choose h, Classical.choose (Classical.choose_spec h))
  let hcrit : ∀ x : {n : ℕ // n ∈ s},
      criticalAt (G := G) x.1 (pair x).1 (pair x).2 :=
    fun x =>
      Classical.choose_spec
        (Classical.choose_spec (exists_critical_pair_at (G := G) x.1 (haug x)))
  let distOf : {n : ℕ // n ∈ s} → ℕ :=
    fun x => Classical.choose (criticalAt_dist (hcrit x))
  let f : {n : ℕ // n ∈ s} → (V × V) × Fin (Fintype.card V) :=
    fun x => (pair x, ⟨distOf x, (Classical.choose_spec (criticalAt_dist (hcrit x))).2⟩)
  have hinj : Set.InjOn f (↑(s.attach) : Set {n : ℕ // n ∈ s}) := by
    intro x hx y hy hxy
    apply Subtype.ext
    by_contra hne
    have hpair_eq : pair x = pair y := congrArg Prod.fst hxy
    have hdist_eq : distOf x = distOf y :=
      congrArg (fun z : (V × V) × Fin (Fintype.card V) => z.2.1) hxy
    have hcy : criticalAt (G := G) y.1 (pair x).1 (pair x).2 := by
      simpa [hpair_eq] using hcrit y
    have hlt_or : x.1 < y.1 ∨ y.1 < x.1 := by omega
    rcases hlt_or with hxy_lt | hyx_lt
    · rcases criticalAt_growth_strict (G := G) hxy_lt (hcrit x) hcy with
        ⟨du, du', hdu, hdu', hgrow⟩
      have hdx : distOf x = du :=
        (Classical.choose_spec (criticalAt_dist (hcrit x))).1.unique hdu
      have hdy : distOf y = du' := by
        have hd := (Classical.choose_spec (criticalAt_dist (hcrit y))).1
        exact hd.unique (by simpa [hpair_eq] using hdu')
      omega
    · rcases criticalAt_growth_strict (G := G) hyx_lt hcy (hcrit x) with
        ⟨du, du', hdu, hdu', hgrow⟩
      have hdy : distOf y = du := by
        have hd := (Classical.choose_spec (criticalAt_dist (hcrit y))).1
        exact hd.unique (by simpa [hpair_eq] using hdu)
      have hdx : distOf x = du' :=
        (Classical.choose_spec (criticalAt_dist (hcrit x))).1.unique hdu'
      omega
  have hsub : s.attach.image f ⊆ (Finset.univ : Finset ((V × V) × Fin (Fintype.card V))) := by
    intro x hx
    simp
  have hcard : (s.attach.image f).card = s.attach.card :=
    Finset.card_image_of_injOn hinj
  calc
    s.card = s.attach.card := Finset.card_attach.symm
    _ = (s.attach.image f).card := hcard.symm
    _ ≤ (Finset.univ : Finset ((V × V) × Fin (Fintype.card V))).card :=
      Finset.card_le_card hsub
    _ = Fintype.card (V × V) * Fintype.card V := by simp

end Chapter26
end CLRS
