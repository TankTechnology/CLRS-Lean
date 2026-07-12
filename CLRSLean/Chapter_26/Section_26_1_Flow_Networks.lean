import Mathlib

/-!
# 26.1. Flow Networks

This section formalizes the maximum-flow problem model from CLRS Chapter 26.  We
define a flow network as a finite directed graph with a nonnegative capacity
function, distinguished source and sink vertices, and formalize the notions of a
feasible flow, flow value, residual network, augmenting path, and cut.  The
section proves the fundamental property that the net flow across any cut equals
the flow value (Lemma 26.5) and the generic Ford-Fulkerson correctness
statement: if there is no augmenting path in the residual network, the flow is
maximal (the forward direction of the Max-Flow Min-Cut Theorem).

Main results:

- `FlowNetwork`: a finite directed graph with capacity `c : V → V → ℝ`,
  nonnegative, zero on self-loops, with source `s` and sink `t` (`s ≠ t`).
- `Flow`: a feasible flow satisfying capacity, skew-symmetry, and
  flow-conservation axioms.
- `Flow.value`: the flow value `|f| = ∑_{v} f(s,v)`.
- `Flow.netFlow_eq_value` (Lemma 26.5): for any cut `(S,T)` with
  `s ∈ S` and `t ∉ S`, the net flow across the cut equals `|f|`.
- `Flow.residualCapacity` and `Flow.residualEdge`: the residual network.
- `Flow.augmentingPathReachable`: reachability in the residual network.
- `Flow.maximal_of_noAugmentingPath`: if no augmenting path exists in the
  residual network, the flow is maximal (generic Ford-Fulkerson correctness).

**Current gaps**: the full Max-Flow Min-Cut Theorem (converse direction),
Edmonds-Karp analysis, and the executable augmenting-path loop.

Notation conventions:

- `G` : a flow network on a vertex type `V`
- `c u v` : capacity of edge `(u,v)`
- `f u v` : flow on edge `(u,v)`
- `cf u v` : residual capacity of `(u,v)` after flow `f`
- `|f|` : value of flow `f`
- `Sᶜ` : complement of set `S` (the `T` side of a cut)
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset
open Classical

/-- A finite flow network over vertex type `V` with capacity `c`, source `s`,
and sink `t`.

Capacities are nonnegative and zero on self-loops.  The source and sink are
distinct.
-/
structure FlowNetwork (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Capacity function `c(u,v) ≥ 0`.  Pairs with zero capacity are
  non-edges in the underlying directed graph. -/
  c : V → V → ℝ
  /-- The source vertex. -/
  s : V
  /-- The sink vertex. -/
  t : V
  /-- Capacities are nonnegative. -/
  hc_nonneg : ∀ u v, 0 ≤ c u v
  /-- Self-loop capacity is zero: `c u u = 0`. -/
  hc_self : ∀ u, c u u = 0
  /-- The source and sink are distinct vertices. -/
  hs_ne_t : s ≠ t

/-- A feasible flow on a flow network `G`.

A flow `f : V → V → ℝ` must satisfy:

1. **Capacity constraint**: `f u v ≤ c u v` for all `u,v`.
2. **Skew symmetry**: `f u v = -f v u` for all `u,v`.
3. **Flow conservation**: for all `u ≠ s, t`, `∑_{v} f u v = 0`.

The lower-bound `0 ≤ f u v` on forward edges is a derived consequence of the
capacity constraint on the reverse pair coupled with skew symmetry (see
`nonneg_of_zero_reverse_cap`).
-/
structure Flow (V : Type*) [Fintype V] [DecidableEq V] (G : FlowNetwork V) where
  /-- The flow function. -/
  f : V → V → ℝ
  /-- Capacity constraint: `f(u,v) ≤ c(u,v)`. -/
  hcapacity : ∀ u v, f u v ≤ G.c u v
  /-- Skew symmetry: `f(u,v) = -f(v,u)`. -/
  hskew_symm : ∀ u v, f u v = -f v u
  /-- Flow conservation: `∑_{v} f(u,v) = 0` for every non-source non-sink vertex. -/
  hconservation : ∀ u, u ≠ G.s → u ≠ G.t →
    Finset.sum (Finset.univ : Finset V) (fun v => f u v) = 0

/-! ## Flow value and auxiliary lemmas -/

/-- The flow value `|f| = ∑_{v} f(s,v)`, the net flow out of the source. -/
noncomputable def Flow.value {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : ℝ :=
  Finset.sum (Finset.univ : Finset V) (fun v => φ.f G.s v)

/-- Skew symmetry implies zero flow on self-loops. -/
theorem Flow.self_zero {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (u : V) : φ.f u u = 0 := by
  have h := φ.hskew_symm u u
  linarith

/-- If the reverse edge has zero capacity, flow is nonnegative on the forward
edge: `c(v,u) = 0` implies `0 ≤ f(u,v)`. -/
theorem Flow.nonneg_of_zero_reverse_cap {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (u v : V) (h : G.c v u = 0) : 0 ≤ φ.f u v := by
  have hcap_rev : φ.f v u ≤ 0 := by
    calc
      φ.f v u ≤ G.c v u := φ.hcapacity v u
      _ = 0 := h
  have hskew : φ.f u v = -φ.f v u := φ.hskew_symm u v
  linarith

/-- If the forward edge has zero capacity, flow is nonpositive on that edge:
`c(u,v) = 0` implies `f(u,v) ≤ 0`. -/
theorem Flow.nonpos_of_zero_cap {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (u v : V) (h : G.c u v = 0) : φ.f u v ≤ 0 := by
  have hcap : φ.f u v ≤ G.c u v := φ.hcapacity u v
  have h_nonneg : 0 ≤ G.c u v := G.hc_nonneg u v
  linarith

/-- On an edge with zero reverse capacity, flow is bounded by `0` and `c(u,v)`:
`0 ≤ f(u,v) ≤ c(u,v)`.  This recovers the CLRS capacity-constraint form for
graphs with no anti-parallel edges. -/
theorem Flow.range_of_zero_reverse_cap {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (u v : V) (h : G.c v u = 0) :
    0 ≤ φ.f u v ∧ φ.f u v ≤ G.c u v :=
  ⟨Flow.nonneg_of_zero_reverse_cap φ u v h, φ.hcapacity u v⟩

/-- Skew symmetry gives `f(u,v) + f(v,u) = 0`. -/
theorem Flow.add_skew {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (u v : V) : φ.f u v + φ.f v u = 0 := by
  have h := φ.hskew_symm u v
  linarith

/-! ## Lemma 26.5: Net flow across a cut equals the flow value -/

/-- The net flow across a cut `(S, Sᶜ)` is `∑_{u∈S} ∑_{v∈Sᶜ} f(u,v)`. -/
noncomputable def Flow.netFlowAcrossCut {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (S : Finset V) : ℝ :=
  Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => φ.f u v))

/-- Double sum of flow over a set `S` cancels to zero by skew symmetry. -/
lemma Flow.skew_symm_cancel {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (S : Finset V) :
    Finset.sum S (fun u => Finset.sum S (fun v => φ.f u v)) = 0 := by
  have hA : Finset.sum S (fun u => Finset.sum S (fun v => φ.f u v)) =
      -(Finset.sum S (fun u => Finset.sum S (fun v => φ.f u v))) := by
    calc
      Finset.sum S (fun u => Finset.sum S (fun v => φ.f u v))
          = Finset.sum S (fun u => Finset.sum S (fun v => -φ.f v u)) := by
        refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
        rw [φ.hskew_symm u v]
      _ = -(Finset.sum S (fun u => Finset.sum S (fun v => φ.f v u))) := by
        simp [Finset.sum_neg_distrib]
      _ = -(Finset.sum S (fun u => Finset.sum S (fun v => φ.f u v))) := by
        rw [Finset.sum_comm]
  linarith

/-- **Lemma 26.5 (CLRS).**  For any cut `(S, T)` with source in `S` and sink
not in `S`, the net flow across the cut equals the flow value:

`∑_{u∈S} ∑_{v∈T} f(u,v) = |f|`. -/
theorem Flow.netFlow_eq_value {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (S : Finset V) (hs : G.s ∈ S) (ht : G.t ∉ S) :
    φ.netFlowAcrossCut S = φ.value := by
  unfold Flow.netFlowAcrossCut Flow.value
  -- The total flow out of all vertices in S, summed over all V.
  have h_total_out : Finset.sum S (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v))
      = Finset.sum (Finset.univ : Finset V) (fun v => φ.f G.s v) := by
    -- For u ≠ s,t, conservation gives total flow out = 0
    have h_cons : ∀ u ∈ S, u ≠ G.s → Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v) = 0 := by
      intro u hu h_ne_s
      have h_ne_t : u ≠ G.t := by
        intro h_eq
        apply ht
        simpa [h_eq] using hu
      exact φ.hconservation u h_ne_s h_ne_t
    -- Partition S into {s} and (S \ {s})
    have h_not_mem : G.s ∉ S.erase G.s := by simp
    have h_disjoint : Disjoint ({G.s} : Finset V) (S.erase G.s) := by
      rw [Finset.disjoint_singleton_left]
      exact h_not_mem
    have h_union : ({G.s} : Finset V) ∪ (S.erase G.s) = S := by
      ext u; simp [hs, Finset.mem_insert, Finset.mem_erase, Finset.mem_union]
    have h_split : Finset.sum S (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v)) =
        Finset.sum (Finset.univ : Finset V) (fun v => φ.f G.s v) +
        (Finset.sum (S.erase G.s) (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v))) := by
      calc
        Finset.sum S (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v))
            = Finset.sum (({G.s} : Finset V) ∪ (S.erase G.s))
                (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v)) := by rw [h_union]
        _ = Finset.sum ({G.s} : Finset V) (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v))
            + Finset.sum (S.erase G.s) (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v)) := by
          rw [Finset.sum_union h_disjoint]
        _ = Finset.sum (Finset.univ : Finset V) (fun v => φ.f G.s v)
            + Finset.sum (S.erase G.s) (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v)) := by simp
    -- The remaining sum is 0 by conservation
    have h_rest_zero : Finset.sum (S.erase G.s)
        (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v)) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      apply h_cons x (Finset.mem_of_mem_erase hx)
      exact (Finset.mem_erase.mp hx).1
    rw [h_split, h_rest_zero, add_zero]

  -- Now decompose each total sum into S and Sᶜ parts.
  calc
    Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => φ.f u v))
        = Finset.sum S (fun u => (Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v))
            - Finset.sum S (fun v => φ.f u v)) := by
      refine Finset.sum_congr rfl fun u hu => ?_
      have hsplit : Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v)
          = Finset.sum S (fun v => φ.f u v) + Finset.sum (Sᶜ) (fun v => φ.f u v) := by
        linarith [Finset.sum_add_sum_compl S (fun v => φ.f u v)]
      have h_eq : Finset.sum (Sᶜ) (fun v => φ.f u v)
          = Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v)
            - Finset.sum S (fun v => φ.f u v) := by
        linarith
      rw [h_eq]
    _ = Finset.sum S (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v))
        - Finset.sum S (fun u => Finset.sum S (fun v => φ.f u v)) := by
      rw [Finset.sum_sub_distrib]
    _ = Finset.sum S (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v))
        - 0 := by rw [Flow.skew_symm_cancel φ S]
    _ = Finset.sum S (fun u => Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v)) := by simp
    _ = Finset.sum (Finset.univ : Finset V) (fun v => φ.f G.s v) := h_total_out

/-! ## Residual network and augmenting paths -/

/-- Residual capacity of edge `(u,v)` after pushing flow `φ`:

`cf(u,v) = c(u,v) - f(u,v)`.

Intuitively, `cf(u,v)` is the amount of additional flow that can be sent from
`u` to `v` without exceeding the capacity `c(u,v)`.  Because of skew symmetry,
a negative `f(u,v)` (equivalently `f(v,u) > 0`) makes `cf(u,v) > c(u,v)`,
reflecting the ability to cancel previously routed flow.
-/
noncomputable def Flow.residualCapacity {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (u v : V) : ℝ :=
  G.c u v - φ.f u v

/-- An edge `(u,v)` is present in the residual network when its residual
capacity is positive. -/
def Flow.residualEdge {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) (u v : V) : Prop :=
  Flow.residualCapacity φ u v > 0

/-- Reachability from `u` to `v` in the residual network.  This is the
reflexive-transitive closure of the `residualEdge` relation. -/
def Flow.augmentingPathReachable {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (u v : V) : Prop :=
  Relation.ReflTransGen (Flow.residualEdge φ) u v

/-- Source can reach sink via an augmenting path in the residual network. -/
def Flow.hasAugmentingPath {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : Prop :=
  Flow.augmentingPathReachable φ G.s G.t

/-! ## Maximal flow and Ford-Fulkerson correctness -/

/-- A flow `φ` is maximal (a maximum flow) if no other feasible flow has a
larger value. -/
def Flow.isMaximal {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Flow V G) : Prop :=
  ∀ ψ : Flow V G, ψ.value ≤ φ.value

/-- The value of any feasible flow is bounded above by the capacity of any cut
`(S,T)`:

`|ψ| ≤ ∑_{u∈S} ∑_{v∈T} c(u,v)`.

This is a direct consequence of Lemma 26.5 and the capacity constraint.
-/
theorem Flow.value_le_cut_capacity {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (ψ : Flow V G) (S : Finset V)
    (hs : G.s ∈ S) (ht : G.t ∉ S) :
    ψ.value ≤ Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) := by
  have hnet : ψ.value = ψ.netFlowAcrossCut S := (ψ.netFlow_eq_value S hs ht).symm
  have hle : ψ.netFlowAcrossCut S ≤ Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) := by
    unfold Flow.netFlowAcrossCut
    refine Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun v hv => ?_
    exact ψ.hcapacity u v
  linarith

/-- If no augmenting path exists from `s` to `t` in the residual network, then
the flow is maximal.

This is the generic Ford-Fulkerson correctness argument (the forward direction
of the Max-Flow Min-Cut Theorem, CLRS Theorem 26.6).  The proof constructs the
cut `S = {v | s → v in the residual network}` and shows that every edge across
this cut is saturated, so the cut capacity equals `|f|` and hence upper-bounds
any other flow.
-/
theorem Flow.maximal_of_noAugmentingPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (hNoPath : ¬ Flow.hasAugmentingPath φ) :
    Flow.isMaximal φ := by
  -- Build the cut S from residual-network reachability
  let S : Finset V := Finset.filter (fun v => Flow.augmentingPathReachable φ G.s v) Finset.univ
  have hs_S : G.s ∈ S := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have ht_not_S : G.t ∉ S := by
    intro h
    have h_reach : Flow.augmentingPathReachable φ G.s G.t :=
      (Finset.mem_filter.mp h).2
    exact hNoPath h_reach
  -- All edges crossing the cut are saturated: for every u∈S, v∉S, we have
  -- f(u,v) = c(u,v).  Because otherwise cf(u,v) > 0, making v reachable.
  have hcut_residual_nonpos : ∀ u, u ∈ S → ∀ v, v ∉ S → Flow.residualCapacity φ u v ≤ 0 := by
    intro u hu v hv
    by_contra! hpos
    have h_reach_u : Flow.augmentingPathReachable φ G.s u := (Finset.mem_filter.mp hu).2
    have h_edge : Flow.residualEdge φ u v := hpos
    have h_reach_v : Flow.augmentingPathReachable φ G.s v :=
      Relation.ReflTransGen.tail h_reach_u h_edge
    apply hv
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, h_reach_v⟩
  have h_saturated : ∀ u, u ∈ S → ∀ v, v ∉ S → φ.f u v = G.c u v := by
    intro u hu v hv
    have hcf_nonpos := hcut_residual_nonpos u hu v hv
    unfold Flow.residualCapacity at hcf_nonpos
    have hcap := φ.hcapacity u v
    linarith
  -- Show φ.value equals the capacity of cut (S, Sᶜ)
  have h_cut_capacity : φ.value = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) := by
    calc
      φ.value = φ.netFlowAcrossCut S := (φ.netFlow_eq_value S hs_S ht_not_S).symm
      _ = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => φ.f u v)) := rfl
      _ = Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) := by
        refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
        have hv_not_S : v ∉ S := by simpa using hv
        rw [h_saturated u hu v hv_not_S]
  -- For any other flow ψ, its value is bounded by the same cut capacity
  intro ψ
  have hψ_value_le : ψ.value ≤ Finset.sum S (fun u => Finset.sum (Sᶜ) (fun v => G.c u v)) :=
    Flow.value_le_cut_capacity φ ψ S hs_S ht_not_S
  linarith

end Chapter26
end CLRS
