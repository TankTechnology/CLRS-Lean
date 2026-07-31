import Mathlib
import CLRSLean.Chapter_26.Section_26_1_Flow_Networks

/-!
# 26.2. Ford--Fulkerson Augmentation

This file begins the constructive half of the Ford--Fulkerson method.  It
packages a simple residual path as an explicit list of vertices and defines
the path bottleneck as the minimum residual capacity of its directed edges.

The directed-edge representation is important for networks with anti-parallel
capacities: traversing an ordered edge always consumes its directed residual
capacity, whether that capacity comes from unused forward capacity,
cancellation of existing flow, or both.
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset Classical

namespace Flow

/-- A simple directed residual path between two specified vertices.

The endpoint equations ensure that the vertex list is nonempty.  The
no-duplicates field supplies the local edge-indicator formula, rules out the
simultaneous appearance of both orientations of one edge, and supports the
capacity proof.  Skew symmetry of the update itself does not require path
simplicity.
-/
structure ResidualPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (u v : V) where
  /-- Vertices in path order, including both endpoints. -/
  vertices : List V
  /-- Every consecutive pair is a residual edge. -/
  chain : vertices.IsChain φ.residualEdge
  /-- The first vertex is the requested path source. -/
  head_eq : vertices.head? = some u
  /-- The final vertex is the requested path target. -/
  last_eq : vertices.getLast? = some v
  /-- The path is simple. -/
  nodup : vertices.Nodup

/-- A simple residual path from the network source to its sink. -/
abbrev AugmentingPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) :=
  ResidualPath φ G.s G.t

/-- Consecutive directed edges of a residual path. -/
def ResidualPath.edges {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} {φ : Flow V G} {u v : V}
    (p : ResidualPath φ u v) : List (V × V) :=
  p.vertices.zip p.vertices.tail

private theorem residualEdge_of_mem_zip_tail {V : Type*}
    {r : V → V → Prop} {vertices : List V} (hchain : vertices.IsChain r)
    {u v : V} (hmem : (u, v) ∈ vertices.zip vertices.tail) : r u v := by
  induction vertices with
  | nil => simp at hmem
  | cons a l ih =>
      cases l with
      | nil => simp at hmem
      | cons b l =>
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hmem
          rcases hmem with hfirst | hrest
          · have hu : u = a := congrArg Prod.fst hfirst
            have hv : v = b := congrArg Prod.snd hfirst
            subst u
            subst v
            exact List.IsChain.rel_head hchain
          · exact ih hchain.tail hrest

/-- Every edge listed by a residual path has positive residual capacity. -/
theorem ResidualPath.residualEdge_of_mem_edges {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} {φ : Flow V G} {s t x y : V}
    (p : ResidualPath φ s t) (hxy : (x, y) ∈ p.edges) :
    φ.residualEdge x y := by
  exact residualEdge_of_mem_zip_tail p.chain hxy

/-- An augmenting path contains at least one directed edge. -/
theorem AugmentingPath.edges_nonempty {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} {φ : Flow V G}
    (p : AugmentingPath φ) : p.edges ≠ [] := by
  cases hvertices : p.vertices with
  | nil =>
      have hhead := p.head_eq
      simp [hvertices] at hhead
  | cons a l =>
      cases l with
      | nil =>
          have has : a = G.s := by simpa [hvertices] using p.head_eq
          have hat : a = G.t := by simpa [hvertices] using p.last_eq
          exfalso
          exact G.hs_ne_t (has.symm.trans hat)
      | cons b l => simp [ResidualPath.edges, hvertices]

private theorem reverse_not_mem_zip_tail {V : Type*} [DecidableEq V]
    {vertices : List V} (hnodup : vertices.Nodup) {u v : V}
    (huv : (u, v) ∈ vertices.zip vertices.tail) :
    (v, u) ∉ vertices.zip vertices.tail := by
  induction vertices with
  | nil => simp at huv
  | cons a l ih =>
      cases l with
      | nil => simp at huv
      | cons b l =>
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at huv ⊢
          simp only [List.nodup_cons] at hnodup
          rcases hnodup with ⟨ha, htail⟩
          rcases huv with hfirst | hrest
          · have hu : u = a := congrArg Prod.fst hfirst
            have hv : v = b := congrArg Prod.snd hfirst
            subst u
            subst v
            intro hreverse
            rcases hreverse with hba | hba
            · have hba' : b = a := congrArg Prod.fst hba
              exact ha (by simp [hba'])
            · exact ha (List.mem_of_mem_tail (List.of_mem_zip hba).2)
          · intro hreverse
            rcases hreverse with hfirst | hrest_reverse
            · have hv : v = a := congrArg Prod.fst hfirst
              have hu : u = b := congrArg Prod.snd hfirst
              subst v
              subst u
              exact ha (List.mem_of_mem_tail (List.of_mem_zip hrest).2)
            · exact ih (List.nodup_cons.mpr htail) hrest hrest_reverse

/-- A simple residual path cannot contain both orientations of the same edge.

This combinatorial fact is independent of capacities.  In particular, it
continues to hold when the network itself has positive capacities in both
directions.
-/
theorem ResidualPath.reverse_not_mem_edges {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} {φ : Flow V G} {s t u v : V}
    (p : ResidualPath φ s t) (huv : (u, v) ∈ p.edges) :
    (v, u) ∉ p.edges := by
  exact reverse_not_mem_zip_tail p.nodup huv

private theorem AugmentingPath.edgeFinset_nonempty {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} {φ : Flow V G}
    (p : AugmentingPath φ) : p.edges.toFinset.Nonempty := by
  exact (List.toFinset_nonempty_iff p.edges).2 p.edges_nonempty

private theorem AugmentingPath.capacityFinset_nonempty {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} {φ : Flow V G}
    (p : AugmentingPath φ) :
    (p.edges.toFinset.image
      (fun e => φ.residualCapacity e.1 e.2)).Nonempty := by
  exact Finset.image_nonempty.mpr p.edgeFinset_nonempty

/-- Minimum residual capacity among the directed edges of an augmenting path. -/
noncomputable def AugmentingPath.bottleneck {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} {φ : Flow V G}
    (p : AugmentingPath φ) : ℝ :=
  let capacities := p.edges.toFinset.image
    (fun e => φ.residualCapacity e.1 e.2)
  capacities.min' p.capacityFinset_nonempty

/-- The bottleneck of an augmenting path is strictly positive. -/
theorem AugmentingPath.bottleneck_pos {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} {φ : Flow V G}
    (p : AugmentingPath φ) : 0 < p.bottleneck := by
  unfold AugmentingPath.bottleneck
  rw [Finset.lt_min'_iff]
  intro capacity hcapacity
  rcases Finset.mem_image.mp hcapacity with ⟨edge, hedge, rfl⟩
  exact p.residualEdge_of_mem_edges (by simpa using hedge)

/-- The path bottleneck is at most the residual capacity of each path edge. -/
theorem AugmentingPath.bottleneck_le_residualCapacity {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} {φ : Flow V G}
    (p : AugmentingPath φ) {u v : V} (huv : (u, v) ∈ p.edges) :
    p.bottleneck ≤ φ.residualCapacity u v := by
  unfold AugmentingPath.bottleneck
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨(u, v), by simpa using huv, rfl⟩

/-! ## Path updates -/

/-- Skew-symmetric update contributed by one oriented path edge. -/
def edgeDelta {V : Type*} [DecidableEq V]
    (delta : ℝ) (a b u v : V) : ℝ :=
  (if u = a ∧ v = b then delta else 0) -
  (if u = b ∧ v = a then delta else 0)

/-- Sum of the skew-symmetric updates contributed by consecutive path edges. -/
def pathDelta {V : Type*} [DecidableEq V]
    (delta : ℝ) : List V → V → V → ℝ
  | [], _, _ => 0
  | [_], _, _ => 0
  | a :: b :: xs, u, v =>
      edgeDelta delta a b u v + pathDelta delta (b :: xs) u v
termination_by xs => xs.length

/-- A single oriented-edge update is skew-symmetric. -/
theorem edgeDelta_skew {V : Type*} [DecidableEq V]
    (delta : ℝ) (a b u v : V) :
    edgeDelta delta a b u v = -edgeDelta delta a b v u := by
  simp only [edgeDelta]
  by_cases hua : u = a <;> by_cases hvb : v = b <;>
    by_cases hub : u = b <;> by_cases hva : v = a <;>
    simp [hua, hvb, hub, hva, and_comm]

/-- The complete path update is skew-symmetric. -/
theorem pathDelta_skew {V : Type*} [DecidableEq V]
    (delta : ℝ) (xs : List V) (u v : V) :
    pathDelta delta xs u v = -pathDelta delta xs v u := by
  induction xs with
  | nil => simp [pathDelta]
  | cons a xs ih =>
      cases xs with
      | nil => simp [pathDelta]
      | cons b xs =>
          simp only [pathDelta]
          rw [edgeDelta_skew, ih]
          ring

/-- Net divergence of the update contributed by one oriented edge. -/
theorem edgeDelta_sum {V : Type*} [Fintype V] [DecidableEq V]
    (delta : ℝ) (a b u : V) :
    (Finset.univ : Finset V).sum (fun v => edgeDelta delta a b u v) =
      (if u = a then delta else 0) - (if u = b then delta else 0) := by
  rw [show (fun v => edgeDelta delta a b u v) =
      (fun v => (if u = a ∧ v = b then delta else 0) -
        (if u = b ∧ v = a then delta else 0)) by rfl]
  rw [Finset.sum_sub_distrib]
  have hforward :
      (Finset.univ : Finset V).sum
          (fun v => if u = a ∧ v = b then delta else 0) =
        (if u = a then delta else 0) := by
    by_cases h : u = a
    · simp [h]
    · simp [h]
  have hbackward :
      (Finset.univ : Finset V).sum
          (fun v => if u = b ∧ v = a then delta else 0) =
        (if u = b then delta else 0) := by
    by_cases h : u = b
    · simp [h]
    · simp [h]
  rw [hforward, hbackward]

/-- Net divergence of a path update is concentrated at its two endpoints. -/
theorem pathDelta_sum {V : Type*} [Fintype V] [DecidableEq V]
    (delta : ℝ) (xs : List V) (u : V) :
    (Finset.univ : Finset V).sum (fun v => pathDelta delta xs u v) =
      (if xs.head? = some u then delta else 0) -
      (if xs.getLast? = some u then delta else 0) := by
  induction xs with
  | nil => simp [pathDelta]
  | cons a xs ih =>
      cases xs with
      | nil => simp [pathDelta]
      | cons b xs =>
          simp only [pathDelta, Finset.sum_add_distrib]
          rw [edgeDelta_sum, ih]
          rw [List.getLast?_cons_cons]
          simp only [List.head?_cons, Option.some.injEq]
          by_cases hua : u = a <;> by_cases hub : u = b <;>
            simp [hua, hub, eq_comm]

private theorem fst_mem_of_mem_consecutivePairs {V : Type*}
    {a b : V} {xs : List V} (h : (a, b) ∈ xs.consecutivePairs) : a ∈ xs := by
  exact (List.of_mem_zip h).1

private theorem snd_mem_of_mem_consecutivePairs {V : Type*}
    {a b : V} {xs : List V} (h : (a, b) ∈ xs.consecutivePairs) : b ∈ xs := by
  exact List.mem_of_mem_tail (List.of_mem_zip h).2

/-- On a simple vertex list, the path update is exactly the difference of the
two directed edge-membership indicators. -/
theorem pathDelta_eq_edgeIndicators_of_nodup
    {V : Type*} [DecidableEq V]
    (delta : ℝ) (xs : List V) (u v : V) (hxs : xs.Nodup) :
    pathDelta delta xs u v =
      (if (u, v) ∈ xs.consecutivePairs then delta else 0) -
      (if (v, u) ∈ xs.consecutivePairs then delta else 0) := by
  induction xs with
  | nil => simp [pathDelta, List.consecutivePairs]
  | cons a xs ih =>
      cases xs with
      | nil => simp [pathDelta, List.consecutivePairs]
      | cons b xs =>
          have hparts := List.nodup_cons.mp hxs
          have ha_not : a ∉ b :: xs := hparts.1
          have htail : (b :: xs).Nodup := hparts.2
          have hab : a ≠ b := by
            intro hab
            apply ha_not
            simp [hab]
          have hab_not_tail : (a, b) ∉ (b :: xs).consecutivePairs := by
            intro h
            exact ha_not (fst_mem_of_mem_consecutivePairs h)
          have hba_not_tail : (b, a) ∉ (b :: xs).consecutivePairs := by
            intro h
            exact ha_not (snd_mem_of_mem_consecutivePairs h)
          have hcp : (a :: b :: xs).consecutivePairs =
              (a, b) :: (b :: xs).consecutivePairs := rfl
          rw [pathDelta]
          rw [ih htail]
          by_cases hf : (u, v) = (a, b)
          · have hu : u = a := congrArg Prod.fst hf
            have hv : v = b := congrArg Prod.snd hf
            subst u
            subst v
            simp [edgeDelta, hcp, hab, hab_not_tail, hba_not_tail]
          · by_cases hr : (v, u) = (a, b)
            · have hv : v = a := congrArg Prod.fst hr
              have hu : u = b := congrArg Prod.snd hr
              subst u
              subst v
              simp [edgeDelta, hcp, hab, hab_not_tail, hba_not_tail]
            · have hforward : ¬(u = a ∧ v = b) := by
                intro h
                exact hf (Prod.ext h.1 h.2)
              have hreverse : ¬(u = b ∧ v = a) := by
                intro h
                exact hr (Prod.ext h.2 h.1)
              simp [edgeDelta, hcp, hf, hr, hforward, hreverse]

/-- Augment a flow by a nonnegative amount bounded by every residual capacity
on the selected path. -/
def augmentBy {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (p : AugmentingPath φ)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hcap : ∀ e ∈ p.edges, delta ≤ φ.residualCapacity e.1 e.2) :
    Flow V G where
  f u v := φ.f u v + pathDelta delta p.vertices u v
  hcapacity := by
    intro u v
    rw [pathDelta_eq_edgeIndicators_of_nodup delta p.vertices u v p.nodup]
    by_cases huv : (u, v) ∈ p.vertices.consecutivePairs <;>
      by_cases hvu : (v, u) ∈ p.vertices.consecutivePairs
    · rw [if_pos huv, if_pos hvu]
      ring_nf
      exact φ.hcapacity u v
    · rw [if_pos huv, if_neg hvu]
      have hmem : (u, v) ∈ p.edges := by
        simpa [ResidualPath.edges] using huv
      have h := hcap (u, v) hmem
      unfold residualCapacity at h
      linarith
    · rw [if_neg huv, if_pos hvu]
      have h := φ.hcapacity u v
      linarith
    · rw [if_neg huv, if_neg hvu]
      ring_nf
      exact φ.hcapacity u v
  hskew_symm := by
    intro u v
    rw [φ.hskew_symm, pathDelta_skew]
    ring
  hconservation := by
    intro u hu_s hu_t
    simp only [Finset.sum_add_distrib]
    rw [φ.hconservation u hu_s hu_t]
    rw [pathDelta_sum]
    rw [p.head_eq, p.last_eq]
    simp [Ne.symm hu_s, Ne.symm hu_t]

/-- Augmenting by an admissible amount increases flow value by exactly that
amount. -/
theorem augmentBy_value {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (p : AugmentingPath φ)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (hcap : ∀ e ∈ p.edges, delta ≤ φ.residualCapacity e.1 e.2) :
    (φ.augmentBy p delta hdelta hcap).value = φ.value + delta := by
  unfold value augmentBy
  rw [Finset.sum_add_distrib]
  rw [pathDelta_sum]
  rw [p.head_eq, p.last_eq]
  simp [Ne.symm G.hs_ne_t]

/-- Augment a flow by the full bottleneck capacity of a selected augmenting
path. -/
noncomputable def augment {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (p : AugmentingPath φ) : Flow V G :=
  φ.augmentBy p p.bottleneck p.bottleneck_pos.le (by
    intro e he
    rcases e with ⟨u, v⟩
    exact p.bottleneck_le_residualCapacity (by simpa using he))

/-- Full bottleneck augmentation increases value by exactly the bottleneck. -/
theorem augment_value {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (p : AugmentingPath φ) :
    (φ.augment p).value = φ.value + p.bottleneck := by
  simpa [augment] using
    φ.augmentBy_value p p.bottleneck p.bottleneck_pos.le (by
      intro e he
      rcases e with ⟨u, v⟩
      exact p.bottleneck_le_residualCapacity (by simpa using he))

/-- Augmenting along a residual source-to-sink path strictly increases value. -/
theorem value_lt_augment {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Flow V G) (p : AugmentingPath φ) :
    φ.value < (φ.augment p).value := by
  rw [φ.augment_value p]
  linarith [p.bottleneck_pos]

end Flow

end Chapter26
end CLRS
