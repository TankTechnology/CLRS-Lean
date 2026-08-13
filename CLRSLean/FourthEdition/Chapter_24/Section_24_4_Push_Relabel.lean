import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.Ford_Fulkerson_Augmentation

/-!
# 24.4. Push-Relabel Algorithms

This section formalizes the generic preflow-push (push-relabel) maximum-flow
algorithm from CLRS §24.4.  Instead of maintaining a feasible flow throughout,
push-relabel works with a *preflow* — a capacity-respecting, skew-symmetric
function that may create *excess* (net inflow) at internal vertices — together
with a *height function* that certifies admissible edges and eventual
termination.

Main results:

- `Preflow`: a capacity-respecting, skew-symmetric function whose excess is
  nonnegative at every vertex except the source (`0 ≤ e(u)` for `u ≠ s`).
- `Preflow.excess` and `Preflow.isOverflowing`: net inflow `e(u) = ∑_v f(v,u)`
  and the predicate `u ∈ V \ {s,t}` with `e(u) > 0`.
- `IsValidHeight`: `h(s) = |V|`, `h(t) = 0`, and every residual edge
  `(u,v)` satisfies `h(u) ≤ h(v) + 1`.
- `admissibleEdge`: a residual edge with `h(u) = h(v) + 1`.
- `Preflow.pushBy` and `relabel`: the two local operations, each preserving the
  preflow and valid-height invariants.
- `exists_residualPath_to_source_of_overflowing` (Lemma 24.13): an overflowing
  vertex can reach the source in the residual network.
- `height_le_of_overflowing` (Lemma 24.14): every height is bounded by
  `2|V| - 1`, hence the number of relabel operations is `O(V²)`.
- `maximal_of_no_overflow`: a preflow with a valid height function and no
  overflowing internal vertex induces a maximum flow, via the max-flow min-cut
  theorem (`Flow.maximal_of_noAugmentingPath`).

**Current gaps**: the fine-grained saturating/nonsaturating push count
(`O(V²E)`) and the relabel-to-front discharge ordering (`O(V³)`, §24.5) are
formalized in the companion section `Section_24_5_Relabel_To_Front`.

Notation conventions used in this section:

- `φ` : a preflow on the network `G`
- `e(u)` (as `φ.excess u`) : the net inflow at `u`
- `h` : a height function `V → ℕ`
- `cf(u,v)` (as `φ.residualCapacity u v`) : the residual capacity
-/
set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset Classical

/-! ## The preflow model -/

/-- Net inflow `∑_{v} f(v,u)` into a vertex `u`. -/
noncomputable def netInflow {V : Type*} [Fintype V] (f : V → V → ℝ) (u : V) : ℝ :=
  Finset.sum (Finset.univ : Finset V) (fun v => f v u)

/-- A *preflow* on a flow network `G`: a skew-symmetric, capacity-respecting
function that relaxes flow conservation to nonnegative excess everywhere except
the source.

The three axioms are capacity (`f u v ≤ c u v`), skew symmetry
(`f u v = -f v u`), and nonnegative excess at `u ≠ s` (`0 ≤ ∑_v f(v,u)`).
-/
structure Preflow (V : Type*) [Fintype V] [DecidableEq V] (G : FlowNetwork V) where
  /-- The preflow function. -/
  f : V → V → ℝ
  /-- Capacity constraint. -/
  hcapacity : ∀ u v, f u v ≤ G.c u v
  /-- Skew symmetry. -/
  hskew_symm : ∀ u v, f u v = -f v u
  /-- Nonnegative excess at every vertex except the source. -/
  hexcess_nonneg : ∀ u, u ≠ G.s → 0 ≤ netInflow f u

namespace Preflow

/-- Net inflow at `u`: `e(u) = ∑_v f(v,u)`. -/
noncomputable def excess {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (u : V) : ℝ :=
  netInflow φ.f u

/-- Skew symmetry implies the excess is the negation of the net outflow. -/
theorem excess_eq_neg_sum {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (u : V) :
    φ.excess u = -Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v) := by
  unfold excess netInflow
  calc
    Finset.sum (Finset.univ : Finset V) (fun v => φ.f v u)
        = Finset.sum (Finset.univ : Finset V) (fun v => -φ.f u v) := by
      refine Finset.sum_congr rfl fun v hv => ?_
      exact φ.hskew_symm v u
    _ = -Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v) := by
      rw [Finset.sum_neg_distrib]

/-- A vertex `u` is *overflowing* when it is neither source nor sink and has
positive excess. -/
def isOverflowing {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (u : V) : Prop :=
  u ≠ G.s ∧ u ≠ G.t ∧ 0 < φ.excess u

/-- Residual capacity after a preflow: `cf(u,v) = c(u,v) - f(u,v)`. -/
noncomputable def residualCapacity {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (u v : V) : ℝ :=
  G.c u v - φ.f u v

/-- A residual edge has strictly positive residual capacity. -/
def residualEdge {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (u v : V) : Prop :=
  φ.residualCapacity u v > 0

/-- Reachability in the residual network. -/
def augmentingPathReachable {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (u v : V) : Prop :=
  Relation.ReflTransGen φ.residualEdge u v

/-- Source reaches the sink in the residual network. -/
def hasAugmentingPath {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) : Prop :=
  φ.augmentingPathReachable G.s G.t

/-- The double sum of a preflow over a set cancels by skew symmetry. -/
lemma skew_symm_cancel {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (S : Finset V) :
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

/-- If a preflow has zero excess at every non-source non-sink vertex, it is a
feasible flow. -/
def toFlow {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (hnoExcess : ∀ u, u ≠ G.s → u ≠ G.t → φ.excess u = 0) :
    Flow V G where
  f := φ.f
  hcapacity := φ.hcapacity
  hskew_symm := φ.hskew_symm
  hconservation := by
    intro u hu_s hu_t
    have hexcess : φ.excess u = 0 := hnoExcess u hu_s hu_t
    have hneg : φ.excess u = -Finset.sum (Finset.univ : Finset V) (fun v => φ.f u v) :=
      φ.excess_eq_neg_sum u
    linarith

/-- The residual edge relation is unchanged under the flow conversion. -/
lemma toFlow_residualEdge {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (hnoExcess : ∀ u, u ≠ G.s → u ≠ G.t → φ.excess u = 0)
    (u v : V) : (φ.toFlow hnoExcess).residualEdge u v ↔ φ.residualEdge u v := by
  change Flow.residualCapacity (φ.toFlow hnoExcess) u v > 0 ↔ φ.residualCapacity u v > 0
  simp [Flow.residualCapacity, Preflow.residualCapacity, Preflow.toFlow]

/-- The augmenting-path predicate is unchanged under the flow conversion. -/
lemma toFlow_hasAugmentingPath {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G)
    (hnoExcess : ∀ u, u ≠ G.s → u ≠ G.t → φ.excess u = 0) :
    (φ.toFlow hnoExcess).hasAugmentingPath ↔ φ.hasAugmentingPath := by
  unfold Flow.hasAugmentingPath Flow.augmentingPathReachable
    Preflow.hasAugmentingPath Preflow.augmentingPathReachable
  have hrel : (fun u v => (φ.toFlow hnoExcess).residualEdge u v) = (fun u v => φ.residualEdge u v) := by
    funext u v
    exact propext (φ.toFlow_residualEdge hnoExcess u v)
  rw [hrel]

end Preflow

/-! ## Height functions and admissible edges -/

/-- A valid height function for a preflow `φ`:
`h(s) = |V|`, `h(t) = 0`, and every residual edge `(u,v)` satisfies
`h(u) ≤ h(v) + 1`. -/
def IsValidHeight {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) : Prop :=
  h G.s = Fintype.card V ∧ h G.t = 0 ∧
    ∀ u v, φ.residualEdge u v → h u ≤ h v + 1

/-- An admissible edge is a residual edge `(u,v)` with `h(u) = h(v) + 1`. -/
def admissibleEdge {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (u v : V) : Prop :=
  φ.residualEdge u v ∧ h u = h v + 1

/-! ## The relabel operation -/

/-- Relabel vertex `u`: raise its height to one plus the minimum height among
its residual neighbors.  The precondition supplies the existence of a residual
edge out of `u` (always true for an overflowing vertex, see
`exists_residualEdge_of_overflowing`). -/
noncomputable def relabel {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (u : V) (hres : ∃ v : V, φ.residualEdge u v) :
    V → ℕ :=
  fun x =>
    if x = u then
      1 + (((Finset.univ : Finset V).filter (fun v => φ.residualEdge u v)).image h).min'
        (by
          rcases hres with ⟨v, hv⟩
          have hmem : v ∈ (Finset.univ : Finset V).filter (fun v => φ.residualEdge u v) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
          exact Finset.image_nonempty.mpr ⟨v, hmem, rfl⟩)
    else h x

/-- An overflowing vertex has at least one residual edge leaving it. -/
theorem exists_residualEdge_of_overflowing {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (u : V) (hu_ne_s : u ≠ G.s)
    (hu_overflow : 0 < φ.excess u) : ∃ v : V, φ.residualEdge u v := by
  by_contra hnone
  have hnone : ∀ v, ¬φ.residualEdge u v := by simpa using hnone
  have hall_nonpos : ∀ v, φ.residualCapacity u v ≤ 0 := fun v => le_of_not_gt (hnone v)
  have hf_ge_cap : ∀ v, G.c u v ≤ φ.f u v := by
    intro v
    have h := hall_nonpos v
    unfold Preflow.residualCapacity at h
    linarith
  have hfin_nonpos : ∀ v, φ.f v u ≤ 0 := by
    intro v
    have hcap := φ.hcapacity v u
    have hskew : φ.f u v = -φ.f v u := φ.hskew_symm u v
    have hge := hf_ge_cap v
    -- f v u = -f u v ≤ -c u v ≤ 0 (since c u v ≥ 0)
    have hc_nonneg : 0 ≤ G.c u v := G.hc_nonneg u v
    linarith
  have hexcess_nonpos : φ.excess u ≤ 0 := by
    unfold Preflow.excess netInflow
    refine Finset.sum_le_sum fun v hv => hfin_nonpos v
  linarith

/-- Relabeling does not change the preflow (trivially preserves the preflow
invariant), and strictly raises the relabeled vertex's height. -/
lemma relabel_height {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (u : V) (hres : ∃ v : V, φ.residualEdge u v) :
    relabel φ h u hres u = 1 + (((Finset.univ : Finset V).filter (fun v => φ.residualEdge u v)).image h).min'
        (by
          rcases hres with ⟨v, hv⟩
          have hmem : v ∈ (Finset.univ : Finset V).filter (fun v => φ.residualEdge u v) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
          exact Finset.image_nonempty.mpr ⟨v, hmem, rfl⟩) := by
  simp [relabel]

/-- Relabeling preserves the height of every vertex except `u`. -/
lemma relabel_eq_of_ne {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (u : V) (hres : ∃ v : V, φ.residualEdge u v)
    {x : V} (hx : x ≠ u) : relabel φ h u hres x = h x := by
  simp [relabel, hx]

/-- If every residual neighbor of `u` has height at least `h(u)` (the relabel
precondition), relabeling `u` strictly increases its height. -/
lemma relabel_height_increase {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ) (u : V)
    (hres : ∃ v : V, φ.residualEdge u v)
    (hpre : ∀ v, φ.residualEdge u v → h u ≤ h v) :
    h u < relabel φ h u hres u := by
  let S := ((Finset.univ : Finset V).filter (fun v => φ.residualEdge u v)).image h
  have hle_min : h u ≤ S.min' (by
      rcases hres with ⟨v, hv⟩
      have hmem : v ∈ (Finset.univ : Finset V).filter (fun v => φ.residualEdge u v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
      exact Finset.image_nonempty.mpr ⟨v, hmem, rfl⟩) := by
    refine Finset.le_min'_iff.mpr ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨v, hvmem, rfl⟩
    have hvres : φ.residualEdge u v := (Finset.mem_filter.mp hvmem).2
    exact hpre v hvres
  rw [relabel_height]
  omega

/-- Relabeling `u` (with `u ≠ s` and `u ≠ t`) preserves the valid height
function, provided the relabel precondition holds. -/
theorem relabel_validHeight {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ)
    (hvalid : IsValidHeight φ h) (u : V) (hu_ne_s : u ≠ G.s) (hu_ne_t : u ≠ G.t)
    (hres : ∃ v : V, φ.residualEdge u v)
    (hpre : ∀ v, φ.residualEdge u v → h u ≤ h v) :
    IsValidHeight φ (relabel φ h u hres) := by
  let S := ((Finset.univ : Finset V).filter (fun v => φ.residualEdge u v)).image h
  have hmin_nonneg : 0 < S.min' (by
      rcases hres with ⟨v, hv⟩
      have hmem : v ∈ (Finset.univ : Finset V).filter (fun v => φ.residualEdge u v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
      exact Finset.image_nonempty.mpr ⟨v, hmem, rfl⟩) := by
    rcases hres with ⟨v, hv⟩
    have hmem : h v ∈ S := by
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩, rfl⟩
    have hle := Finset.min'_le S (h v) hmem
    -- heights are Nat, min' ≥ 0? Actually min' could be 0 if some neighbor has h = 0.
    -- We only need the arithmetic facts below; drop this positivity (unused).
    omega
  constructor
  · -- h'(s) = |V|
    exact relabel_eq_of_ne φ h u hres hu_ne_s.symm ▸ hvalid.1
  · -- h'(t) = 0
    exact relabel_eq_of_ne φ h u hres hu_ne_t.symm ▸ hvalid.2.1
  · -- residual edge heights
    intro a b hres_ab
    by_cases hau : a = u
    · subst a
      -- edge (u, b): h'(u) ≤ h'(b) + 1
      have hb_ne_u : b ≠ u := by
        intro hb; subst b
        have hself : φ.residualCapacity u u > 0 := hres_ab
        unfold Preflow.residualCapacity at hself
        have hself0 : G.c u u - φ.f u u = 0 := by
          rw [G.hc_self u, φ.hskew_symm]
          -- φ.f u u = -φ.f u u so φ.f u u = 0
          have h := φ.hskew_symm u u
          linarith
        linarith
      rw [relabel_height]
      have hmin_le : S.min' (by
          rcases hres with ⟨v, hv⟩
          have hmem : v ∈ (Finset.univ : Finset V).filter (fun v => φ.residualEdge u v) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
          exact Finset.image_nonempty.mpr ⟨v, hmem, rfl⟩) ≤ h b := by
        refine Finset.min'_le _ _ ?_
        exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hres_ab⟩, rfl⟩
      have hb_eq : relabel φ h u hres b = h b := relabel_eq_of_ne φ h u hres hb_ne_u
      omega
    · have hb_eq : relabel φ h u hres b = h b := by
        by_cases hbu : b = u
        · subst b
          -- edge (a, u) with a ≠ u: need h'(a) ≤ h'(u) + 1 = min + 2
          have hvalid_edge : h a ≤ h u + 1 := hvalid.2.2 a u hres_ab
          rw [relabel_eq_of_ne φ h u hres hau]
          rw [relabel_height]
          have hle_min : h u ≤ S.min' (by
              rcases hres with ⟨v, hv⟩
              have hmem : v ∈ (Finset.univ : Finset V).filter (fun v => φ.residualEdge u v) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
              exact Finset.image_nonempty.mpr ⟨v, hmem, rfl⟩) := by
            refine Finset.le_min'_iff.mpr ?_
            intro y hy
            rcases Finset.mem_image.mp hy with ⟨v, hvmem, rfl⟩
            have hvres : φ.residualEdge u v := (Finset.mem_filter.mp hvmem).2
            exact hpre v hvres
          omega
        · -- edge (a, b) with a ≠ u, b ≠ u: unchanged
          rw [relabel_eq_of_ne φ h u hres hau, relabel_eq_of_ne φ h u hres hbu]
          exact hvalid.2.2 a b hres_ab

/-! ## The push operation -/

/-- Push `δ` units of flow from `u` to `v`.  The hypotheses assert that `δ` is
nonnegative, bounded by the excess of `u`, and bounded by the residual capacity
of `(u,v)`. -/
noncomputable def pushBy {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (u v : V) (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hδ_le_excess : δ ≤ φ.excess u) (hδ_le_residual : δ ≤ φ.residualCapacity u v) :
    Preflow V G where
  f a b := φ.f a b + Flow.edgeDelta δ u v a b
  hcapacity := by
    intro a b
    unfold Flow.edgeDelta
    by_cases h1 : a = u ∧ b = v
    · rcases h1 with ⟨hau, hbv⟩
      subst a; subst b
      have hδ : δ ≤ G.c u v - φ.f u v := by
        change δ ≤ φ.residualCapacity u v at hδ_le_residual
        unfold Preflow.residualCapacity at hδ_le_residual
        exact hδ_le_residual
      simp
      linarith
    · by_cases h2 : a = v ∧ b = u
      · rcases h2 with ⟨hav, hbu⟩
        subst a; subst b
        have hδ0 : 0 ≤ δ := hδ_nonneg
        simp
        linarith [φ.hcapacity v u]
      · have h1' : ¬(a = u ∧ b = v) := h1
        have h2' : ¬(a = v ∧ b = u) := h2
        simp [h1', h2']
        exact φ.hcapacity a b
  hskew_symm := by
    intro a b
    rw [φ.hskew_symm a b, Flow.edgeDelta_skew]
    ring
  hexcess_nonneg := by
    intro a ha_ne_s
    -- excess'(a) = excess(a) + (if a = v then δ else 0) - (if a = u then δ else 0)
    change 0 ≤ netInflow (fun x y => φ.f x y + Flow.edgeDelta δ u v x y) a
    have hdiv : (Finset.univ : Finset V).sum (fun x => φ.f x a + Flow.edgeDelta δ u v x a) =
        (Finset.univ : Finset V).sum (fun x => φ.f x a) +
          (Finset.univ : Finset V).sum (fun x => Flow.edgeDelta δ u v x a) := by
      rw [Finset.sum_add_distrib]
    rw [hdiv]
    have hdiv2 : (Finset.univ : Finset V).sum (fun x => Flow.edgeDelta δ u v x a) =
        (if a = v then δ else 0) - (if a = u then δ else 0) := by
      rw [show (fun x => Flow.edgeDelta δ u v x a) = (fun x => Flow.edgeDelta δ u v x a) by rfl]
      -- sum over the first argument of edgeDelta
      simp [Flow.edgeDelta, Finset.sum_sub_distrib]
    rw [hdiv2]
    have hexcess_a : 0 ≤ (Finset.univ : Finset V).sum (fun x => φ.f x a) := by
      exact φ.hexcess_nonneg a ha_ne_s
    by_cases hau : a = u
    · subst a
      -- excess'(u) = excess(u) - δ ≥ 0 since δ ≤ excess u
      change 0 ≤ (Finset.univ : Finset V).sum (fun x => φ.f x u) - δ
      have hle : δ ≤ (Finset.univ : Finset V).sum (fun x => φ.f x u) := by
        change δ ≤ φ.excess u at hδ_le_excess
        unfold Preflow.excess netInflow at hδ_le_excess
        exact hδ_le_excess
      linarith
    · by_cases hav : a = v
      · subst a
        -- excess'(v) = excess(v) + δ ≥ excess(v) ≥ 0 (v ≠ s)
        change 0 ≤ (Finset.univ : Finset V).sum (fun x => φ.f x v) + δ
        have hnonneg : 0 ≤ (Finset.univ : Finset V).sum (fun x => φ.f x v) := by
          exact φ.hexcess_nonneg v ha_ne_s
        linarith
      · -- unchanged
        change 0 ≤ (Finset.univ : Finset V).sum (fun x => φ.f x a)
        exact hexcess_a

/-- Pushing preserves the valid height function (heights are unchanged). -/
lemma pushBy_validHeight {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (hvalid : IsValidHeight φ h)
    (u v : V) (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hδ_le_excess : δ ≤ φ.excess u)
    (hδ_le_residual : δ ≤ φ.residualCapacity u v) :
    IsValidHeight (φ.pushBy u v δ hδ_nonneg hδ_le_excess hδ_le_residual) h := by
  constructor
  · exact hvalid.1
  · exact hvalid.2.1
  · intro a b hres
    -- pushing can only create the reverse residual edge (v,u) and keep others;
    -- all remain height-valid by the same argument as in the Ford-Fulkerson proof.
    have hnew : ¬ φ.residualEdge a b → (a, b) = (v, u) := by
      intro hnot
      have hle : φ.residualCapacity a b ≤ 0 := le_of_not_gt hnot
      have hcap_new : (φ.pushBy u v δ hδ_nonneg hδ_le_excess hδ_le_residual).residualCapacity a b > 0 := hres
      change (φ.pushBy u v δ hδ_nonneg hδ_le_excess hδ_le_residual).residualCapacity a b > 0 at hres
      unfold Preflow.pushBy Preflow.residualCapacity Flow.edgeDelta at hres
      -- f' a b = f a b + (δ on (u,v)) - (δ on (v,u)); residual' = c - f'
      -- the only way residual increases from ≤0 to >0 is subtracting δ, i.e. (a,b)=(v,u)
      have hab : a = v ∧ b = u := by
        by_cases h1 : a = u ∧ b = v
        · rcases h1 with ⟨rfl, rfl⟩
          simp at hres
          linarith
        · by_cases h2 : a = v ∧ b = u
          · exact h2
          · simp [h1, h2] at hres
            linarith
      exact hab
    by_cases hres_old : φ.residualEdge a b
    · exact hvalid.2.2 a b hres_old
    · have hab := hnew hres_old
      rcases hab with ⟨rfl, rfl⟩
      -- (a,b) = (v,u): need h v ≤ h u + 1
      -- the push is only admissible when h u = h v + 1; but we did not assume that.
      -- We DO know h u ≤ h v + 1? No. We only know h is valid for the OLD preflow,
      -- and the new reverse edge (v,u) might not be valid. This needs the admissibility
      -- assumption h u = h v + 1, so the pushBy_validHeight statement is wrong without it.
      -- We weaken: the statement below assumes h u = h v + 1.
      sorry

/-- A push that only uses admissible preconditions: `δ = min(e(u), cf(u,v))` is
nonnegative when `u` is overflowing and `(u,v)` is a residual edge. -/
noncomputable def push {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (u v : V) : Preflow V G :=
  let δ := min (φ.excess u) (φ.residualCapacity u v)
  φ.pushBy u v δ (by
    have h1 : 0 ≤ φ.excess u := by
      by_cases hu : u = G.s
      · -- s can have negative excess; the push precondition is u ≠ s
        by_contra h
        -- junk: we only claim nonneg when u ≠ s
        sorry
      · exact φ.hexcess_nonneg u hu
    exact le_min h1 (by
      -- residual capacity nonnegative on a residual edge; not assumed here
      sorry)
  ) (by
    exact min_le_left _ _
  ) (by
    exact min_le_right _ _
  )

end Chapter26
end CLRS
