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
- `IsValidHeight`: `h(s) = |V|`, `h(t) = 0`, and every residual edge `(u,v)`
  satisfies `h(u) ≤ h(v) + 1`.
- `admissibleEdge`: a residual edge with `h(u) = h(v) + 1`.
- `Preflow.pushBy` and `relabel`: the two local operations, each preserving the
  preflow and valid-height invariants.
- `exists_residualEdge_of_overflowing`: an overflowing vertex has a residual
  edge leaving it, so a relabel (or push) is always possible.
- `exists_residualPath_to_source_of_overflowing` (Lemma 24.13): an overflowing
  vertex can reach the source in the residual network.
- `height_le_of_overflowing` (Lemma 24.14): every height is bounded by
  `2|V| - 1`; combined with `relabel_height_increase` this bounds the number of
  relabel operations by `O(V²)`.
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
  have hrel : (fun u v => (φ.toFlow hnoExcess).residualEdge u v) =
      (fun u v => φ.residualEdge u v) := by
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

/-- The minimum height among the residual neighbors of `u` (used by `relabel`). -/
private noncomputable def relabelMin {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ) (u : V)
    (hres : ∃ v : V, φ.residualEdge u v) : ℕ :=
  (((Finset.univ : Finset V).filter (fun v => φ.residualEdge u v)).image h).min'
    (by
      rcases hres with ⟨v, hv⟩
      exact Finset.image_nonempty.mpr
        ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩, rfl⟩)

/-- `relabelMin` is at most the height of any residual neighbor. -/
private lemma relabelMin_le {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (u : V) (hres : ∃ v : V, φ.residualEdge u v)
    {b : V} (hb : φ.residualEdge u b) : relabelMin φ h u hres ≤ h b := by
  unfold relabelMin
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩, rfl⟩)

/-- Under the relabel precondition (`h u ≤ h v` for every residual neighbor),
`h u` is at most `relabelMin`. -/
private lemma le_relabelMin {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (u : V) (hres : ∃ v : V, φ.residualEdge u v)
    (hpre : ∀ v, φ.residualEdge u v → h u ≤ h v) : h u ≤ relabelMin φ h u hres := by
  unfold relabelMin
  refine Finset.le_min'_iff.mpr ?_
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨v, hvmem, rfl⟩
  exact hpre v (Finset.mem_filter.mp hvmem).2

/-- Relabel vertex `u`: raise its height to one plus the minimum height among
its residual neighbors.  The precondition supplies the existence of a residual
edge out of `u` (always true for an overflowing vertex, see
`exists_residualEdge_of_overflowing`). -/
noncomputable def relabel {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (u : V) (hres : ∃ v : V, φ.residualEdge u v) :
    V → ℕ :=
  fun x => if x = u then 1 + relabelMin φ h u hres else h x

/-- Relabeling sets the height of `u` to one plus `relabelMin`. -/
lemma relabel_eq_self {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (u : V) (hres : ∃ v : V, φ.residualEdge u v) :
    relabel φ h u hres u = 1 + relabelMin φ h u hres := by
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
  rw [relabel_eq_self]
  have hle : h u ≤ relabelMin φ h u hres := le_relabelMin φ h u hres hpre
  omega

/-- Relabeling `u` (with `u ≠ s` and `u ≠ t`) preserves the valid height
function, provided the relabel precondition holds. -/
theorem relabel_validHeight {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ)
    (hvalid : IsValidHeight φ h) (u : V) (hu_ne_s : u ≠ G.s) (hu_ne_t : u ≠ G.t)
    (hres : ∃ v : V, φ.residualEdge u v)
    (hpre : ∀ v, φ.residualEdge u v → h u ≤ h v) :
    IsValidHeight φ (relabel φ h u hres) := by
  constructor
  · exact (relabel_eq_of_ne φ h u hres (Ne.symm hu_ne_s)).trans hvalid.1
  · exact (relabel_eq_of_ne φ h u hres (Ne.symm hu_ne_t)).trans hvalid.2.1
  · intro a b hres_ab
    by_cases hau : a = u
    · subst a
      -- edge (u, b): h'(u) ≤ h'(b) + 1
      have hb_ne_u : b ≠ u := by
        intro hb
        subst b
        have hself0 : φ.residualCapacity u u = 0 := by
          unfold Preflow.residualCapacity
          rw [G.hc_self u]
          have hskew : φ.f u u = 0 := by
            have h := φ.hskew_symm u u
            linarith
          simp [hskew]
        linarith [hres_ab, hself0]
      rw [relabel_eq_self]
      have hmin_le : relabelMin φ h u hres ≤ h b := relabelMin_le φ h u hres hres_ab
      have hb_eq : relabel φ h u hres b = h b := relabel_eq_of_ne φ h u hres hb_ne_u
      omega
    · by_cases hbu : b = u
      · subst b
        -- edge (a, u) with a ≠ u: h'(a) ≤ h'(u) + 1 = relabelMin + 2
        have hvalid_edge : h a ≤ h u + 1 := hvalid.2.2 a u hres_ab
        rw [relabel_eq_of_ne φ h u hres hau, relabel_eq_self]
        have hle_min : h u ≤ relabelMin φ h u hres := le_relabelMin φ h u hres hpre
        omega
      · -- edge (a, b) with a ≠ u, b ≠ u: unchanged
        rw [relabel_eq_of_ne φ h u hres hau, relabel_eq_of_ne φ h u hres hbu]
        exact hvalid.2.2 a b hres_ab

/-! ## The push operation -/

/-- Net divergence of the single-edge update, summed over the first argument. -/
private lemma edgeDelta_sum_first {V : Type*} [Fintype V] [DecidableEq V]
    (δ : ℝ) (u v a : V) :
    (Finset.univ : Finset V).sum (fun x => Flow.edgeDelta δ u v x a) =
      (if a = v then δ else 0) - (if a = u then δ else 0) := by
  unfold Flow.edgeDelta
  rw [Finset.sum_sub_distrib]
  have hf : (Finset.univ : Finset V).sum (fun x => if x = u ∧ a = v then δ else 0) =
      (if a = v then δ else 0) := by
    by_cases hav : a = v
    · subst a
      simp
    · simp [hav]
  have hg : (Finset.univ : Finset V).sum (fun x => if x = v ∧ a = u then δ else 0) =
      (if a = u then δ else 0) := by
    by_cases hau : a = u
    · subst a
      simp
    · simp [hau]
  rw [hf, hg]

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
        unfold Preflow.residualCapacity at hδ_le_residual
        exact hδ_le_residual
      simp
      linarith
    · by_cases h2 : a = v ∧ b = u
      · rcases h2 with ⟨hav, hbu⟩
        subst a; subst b
        simp
        linarith [φ.hcapacity v u, hδ_nonneg]
      · have h1' : ¬(a = u ∧ b = v) := h1
        have h2' : ¬(a = v ∧ b = u) := h2
        simp [h1', h2']
        exact φ.hcapacity a b
  hskew_symm := by
    intro a b
    rw [φ.hskew_symm a b, Flow.edgeDelta_skew δ u v a b]
    ring
  hexcess_nonneg := by
    intro a ha_ne_s
    change 0 ≤ netInflow (fun x y => φ.f x y + Flow.edgeDelta δ u v x y) a
    unfold netInflow
    rw [Finset.sum_add_distrib]
    rw [edgeDelta_sum_first δ u v a]
    have hexcess_a : 0 ≤ (Finset.univ : Finset V).sum (fun x => φ.f x a) :=
      φ.hexcess_nonneg a ha_ne_s
    by_cases hau : a = u
    · subst a
      -- excess'(u) = excess(u) - δ ≥ 0 since δ ≤ excess u
      have hle : δ ≤ (Finset.univ : Finset V).sum (fun x => φ.f x u) := by
        unfold Preflow.excess netInflow at hδ_le_excess
        exact hδ_le_excess
      simp [hau]
      linarith
    · by_cases hav : a = v
      · subst a
        -- excess'(v) = excess(v) + δ ≥ excess(v) ≥ 0
        have hnonneg : 0 ≤ (Finset.univ : Finset V).sum (fun x => φ.f x v) :=
          φ.hexcess_nonneg v ha_ne_s
        simp [hau, hav]
        linarith
      · -- unchanged
        simp [hau, hav]
        exact hexcess_a

/-- Pushing can only create one new residual edge: the reverse `(v,u)`. -/
lemma pushBy_new_residualEdge {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (u v : V) (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hδ_le_excess : δ ≤ φ.excess u) (hδ_le_residual : δ ≤ φ.residualCapacity u v)
    {a b : V} (hnew : (φ.pushBy u v δ hδ_nonneg hδ_le_excess hδ_le_residual).residualEdge a b)
    (hold : ¬ φ.residualEdge a b) : a = v ∧ b = u := by
  have hcap : (φ.pushBy u v δ hδ_nonneg hδ_le_excess hδ_le_residual).residualCapacity a b > 0 := hnew
  have hcap0 : φ.residualCapacity a b ≤ 0 := le_of_not_gt hold
  unfold Preflow.pushBy Preflow.residualCapacity Flow.edgeDelta at hcap
  have hformula : (φ.pushBy u v δ hδ_nonneg hδ_le_excess hδ_le_residual).residualCapacity a b =
      φ.residualCapacity a b - (if a = u ∧ b = v then δ else 0) +
        (if a = v ∧ b = u then δ else 0) := by
    unfold Preflow.pushBy Preflow.residualCapacity Flow.edgeDelta
    ring
  rw [hformula] at hcap
  by_contra hnot
  have hnot_uv : ¬(a = v ∧ b = u) := hnot
  have hnot_rev : ¬(a = u ∧ b = v) := by
    intro h
    rw [h.1, h.2] at hnot_uv
    exact hnot_uv ⟨rfl, rfl⟩
  rw [if_neg hnot_rev, if_neg hnot_uv] at hcap
  linarith

/-- A push on an admissible edge preserves the valid height function (heights
are unchanged; the only new residual edge is the reverse edge, whose height
condition follows from admissibility). -/
lemma pushBy_validHeight {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (h : V → ℕ) (hvalid : IsValidHeight φ h)
    (u v : V) (δ : ℝ) (hδ_nonneg : 0 ≤ δ) (hδ_le_excess : δ ≤ φ.excess u)
    (hδ_le_residual : δ ≤ φ.residualCapacity u v) (hadm : h u = h v + 1) :
    IsValidHeight (φ.pushBy u v δ hδ_nonneg hδ_le_excess hδ_le_residual) h := by
  constructor
  · exact hvalid.1
  · exact hvalid.2.1
  · intro a b hres
    by_cases hold : φ.residualEdge a b
    · exact hvalid.2.2 a b hold
    · have hab := φ.pushBy_new_residualEdge u v δ hδ_nonneg hδ_le_excess hδ_le_residual hres hold
      rcases hab with ⟨rfl, rfl⟩
      -- need h v ≤ h u + 1, from h u = h v + 1
      rw [hadm]
      omega

/-- The admissible push: push `δ = min(e(u), cf(u,v))` from an overflowing `u`
along a residual edge `(u,v)`. -/
noncomputable def push {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}
    (φ : Preflow V G) (u v : V) (hu_ne_s : u ≠ G.s) (hres : φ.residualEdge u v) :
    Preflow V G :=
  let δ := min (φ.excess u) (φ.residualCapacity u v)
  φ.pushBy u v δ (le_min (φ.hexcess_nonneg u hu_ne_s) (le_of_lt hres))
    (min_le_left _ _) (min_le_right _ _)

/-! ## Height bound via reachability to the source -/

/-- An overflowing vertex has at least one residual edge leaving it. -/
theorem exists_residualEdge_of_overflowing {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (u : V) (hu_ne_s : u ≠ G.s)
    (hu_overflow : 0 < φ.excess u) : ∃ v : V, φ.residualEdge u v := by
  by_contra hnone
  have hnone : ∀ v, ¬φ.residualEdge u v := fun v => by
    intro hres
    exact hnone ⟨v, hres⟩
  have hall_nonpos : ∀ v, φ.residualCapacity u v ≤ 0 := fun v => le_of_not_gt (hnone v)
  have hf_ge_cap : ∀ v, G.c u v ≤ φ.f u v := by
    intro v
    have h := hall_nonpos v
    unfold Preflow.residualCapacity at h
    linarith
  have hfin_nonpos : ∀ v, φ.f v u ≤ 0 := by
    intro v
    have hskew : φ.f u v = -φ.f v u := φ.hskew_symm u v
    have hge := hf_ge_cap v
    have hc_nonneg : 0 ≤ G.c u v := G.hc_nonneg u v
    linarith
  have hexcess_nonpos : φ.excess u ≤ 0 := by
    unfold Preflow.excess netInflow
    refine Finset.sum_le_sum fun v hv => hfin_nonpos v
  linarith

/-- Every list with repeated vertices decomposes into a duplicated segment. -/
private lemma exists_dup_decomp {α : Type*} [DecidableEq α] :
    ∀ {xs : List α}, ¬xs.Nodup →
      ∃ (x : α) (left middle right : List α),
        xs = left ++ x :: middle ++ x :: right := by
  intro xs
  induction xs with
  | nil =>
      intro h
      simp at h
  | cons a tail ih =>
      intro h
      by_cases ha : a ∈ tail
      · obtain ⟨middle, right, htail⟩ := List.mem_iff_append.mp ha
        exact ⟨a, [], middle, right, by rw [htail]; simp⟩
      · have htail : ¬tail.Nodup := fun htail => h (List.nodup_cons.mpr ⟨ha, htail⟩)
        obtain ⟨x, left, middle, right, htail_eq⟩ := ih htail
        exact ⟨x, a :: left, middle, right, by rw [htail_eq]; simp⟩

/-- Any chain can be shortened to a simple (no-duplicates) chain with the same
endpoints. -/
private lemma exists_nodup_chain_same_ends {α : Type*} [DecidableEq α]
    {r : α → α → Prop} :
    ∀ (n : ℕ) (xs : List α), xs.length ≤ n → xs ≠ [] →
      xs.IsChain r →
      ∃ ys : List α,
        ys ≠ [] ∧ ys.IsChain r ∧ ys.head? = xs.head? ∧
          ys.getLast? = xs.getLast? ∧ ys.Nodup := by
  intro n
  induction n with
  | zero =>
      intro xs hlen hne _
      have hnil : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      exact (hne hnil).elim
  | succ n ih =>
      intro xs hlen hne hchain
      by_cases hnodup : xs.Nodup
      · exact ⟨xs, hne, hchain, rfl, rfl, hnodup⟩
      · obtain ⟨x, left, middle, right, hxs⟩ := exists_dup_decomp hnodup
        let shorter := left ++ x :: right
        have hleft_middle : (left ++ x :: middle) <+: xs := by
          refine ⟨x :: right, ?_⟩
          rw [hxs]
        have hright : (x :: right) <:+ xs := by
          refine ⟨left ++ x :: middle, ?_⟩
          rw [hxs]
        have hchain_left_middle : (left ++ x :: middle).IsChain r :=
          hchain.prefix hleft_middle
        have hchain_left : left.IsChain r := hchain_left_middle.left_of_append
        have hchain_right : (x :: right).IsChain r := hchain.suffix hright
        have hchain_shorter : shorter.IsChain r := by
          dsimp [shorter]
          refine hchain_left.append hchain_right ?_
          intro a ha b hb
          have hbx : b = x := (show x = b by simpa using hb).symm
          rw [hbx]
          exact (List.isChain_append.1 hchain_left_middle).2.2 a ha x (by simp)
        have hhead_shorter : shorter.head? = xs.head? := by
          dsimp [shorter]
          rw [hxs]
          cases left <;> simp
        have hlast_shorter : shorter.getLast? = xs.getLast? := by
          dsimp [shorter]
          have hxright : (x :: right).getLast? = xs.getLast? := by
            rw [hxs, List.getLast?_append_of_ne_nil _ (by simp : (x :: right) ≠ [])]
          rw [List.getLast?_append_of_ne_nil _ (by simp : (x :: right) ≠ [])]
          exact hxright
        have hshorter_ne : shorter ≠ [] := by
          dsimp [shorter]
          simp
        have hlen_xs : xs.length = left.length + middle.length + right.length + 2 := by
          rw [hxs]
          simp only [List.length_append, List.length_cons]
          omega
        have hlen_shorter : shorter.length = left.length + right.length + 1 := by
          dsimp [shorter]
          simp only [List.length_append, List.length_cons]
          omega
        have hshorter_le : shorter.length ≤ n := by omega
        obtain ⟨ys, hys_ne, hys_chain, hys_head, hys_last, hys_nodup⟩ :=
          ih shorter hshorter_le hshorter_ne hchain_shorter
        exact ⟨ys, hys_ne, hys_chain, hys_head.trans hhead_shorter,
          hys_last.trans hlast_shorter, hys_nodup⟩

/-- Along a residual chain `a :: xs`, the height of the head is at most the
height of the last vertex plus the chain length. -/
lemma height_le_of_residual_chain {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ)
    (hedge : ∀ u v, φ.residualEdge u v → h u ≤ h v + 1) :
    ∀ {a : V} {xs : List V}, (a :: xs).IsChain φ.residualEdge →
      h a ≤ h ((a :: xs).getLast (by simp)) + xs.length := by
  intro a xs hchain
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
      have hrel : φ.residualEdge a b := hchain.rel_head
      have htail : (b :: xs).IsChain φ.residualEdge := hchain.tail
      have hb := ih htail
      have hle : h a ≤ h b + 1 := hedge a b hrel
      simp only [List.getLast_cons, List.length_cons] at hb ⊢
      omega

/-- Same statement for an arbitrary nonempty chain. -/
lemma height_le_of_residual_chain_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ)
    (hedge : ∀ u v, φ.residualEdge u v → h u ≤ h v + 1)
    {ys : List V} (hchain : ys.IsChain φ.residualEdge) (hne : ys ≠ []) :
    h (ys.head hne) ≤ h (ys.getLast hne) + (ys.length - 1) := by
  cases ys with
  | nil => cases hne rfl
  | cons a xs =>
      have hle := height_le_of_residual_chain φ h hedge (a := a) (xs := xs) hchain
      simp only [List.head_cons, List.length_cons] at hle ⊢
      omega

/-- If heights satisfy the residual-edge inequality, then reachability in the
residual network bounds the height drop by `|V| - 1`. -/
lemma height_le_of_reachability {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ)
    (hedge : ∀ u v, φ.residualEdge u v → h u ≤ h v + 1)
    {a b : V} (hreach : Relation.ReflTransGen φ.residualEdge a b) :
    h a ≤ h b + (Fintype.card V - 1) := by
  rcases List.exists_isChain_ne_nil_of_relationReflTransGen hreach with
    ⟨xs, hne, hchain, hhead, hlast⟩
  obtain ⟨ys, hyne, hychain, hyhead, hylast, hynodup⟩ :=
    exists_nodup_chain_same_ends xs.length xs le_rfl hne hchain
  have hys_head : ys.head? = some a := hyhead.trans (by
    exact (List.head?_eq_some_head hne).trans (congrArg some hhead))
  have hys_last : ys.getLast? = some b := hylast.trans (by
    exact (List.getLast?_eq_some_getLast hne).trans (congrArg some hlast))
  have hhead_a : ys.head hyne = a := by
    rw [List.head?_eq_some_head hyne] at hys_head
    exact Option.some.inj hys_head
  have hlast_b : ys.getLast hyne = b := by
    rw [List.getLast?_eq_some_getLast hyne] at hys_last
    exact Option.some.inj hys_last
  have hle := height_le_of_residual_chain_nonempty φ h hedge hychain hyne
  rw [hhead_a, hlast_b] at hle
  have hlen_le : ys.length ≤ Fintype.card V := by
    have hcard : (ys.toFinset : Finset V).card = ys.length := by
      exact List.toFinset_card_of_nodup ys hynodup
    have hle2 : (ys.toFinset : Finset V).card ≤ (Finset.univ : Finset V).card := by
      exact Finset.card_le_card (by intro x hx; simp)
    simpa [hcard] using hle2
  have hlen_sub : ys.length - 1 ≤ Fintype.card V - 1 := by omega
  omega

/-- **Lemma 24.13 (CLRS).** An overflowing vertex `u ≠ s` can reach the source
in the residual network. -/
theorem exists_residualPath_to_source_of_overflowing {V : Type*} [Fintype V]
    [DecidableEq V] {G : FlowNetwork V} (φ : Preflow V G) (u : V) (hu_ne_s : u ≠ G.s)
    (hu_overflow : 0 < φ.excess u) : Relation.ReflTransGen φ.residualEdge u G.s := by
  let X : Finset V := Finset.filter (fun v => Relation.ReflTransGen φ.residualEdge u v) Finset.univ
  by_contra hnot
  have hs_not_mem : G.s ∉ X := by
    intro h
    exact hnot ((Finset.mem_filter.mp h).2)
  have hcut_no_res : ∀ a, a ∈ X → ∀ b, b ∉ X → ¬ φ.residualEdge a b := by
    intro a ha b hb hres
    apply hb
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ b, Relation.ReflTransGen.tail (Finset.mem_filter.mp ha).2 hres⟩
  have hf_eq_cap : ∀ a, a ∈ X → ∀ b, b ∉ X → φ.f a b = G.c a b := by
    intro a ha b hb
    have hnores := hcut_no_res a ha b hb
    have hcf_nonpos : φ.residualCapacity a b ≤ 0 := le_of_not_gt hnores
    have hle := φ.hcapacity a b
    unfold Preflow.residualCapacity at hcf_nonpos
    linarith
  have hsum_le_zero : (∑ a ∈ X, φ.excess a) ≤ 0 := by
    calc
      (∑ a ∈ X, φ.excess a)
          = ∑ a ∈ X, ∑ b : V, φ.f b a := by
            refine Finset.sum_congr rfl fun a ha => ?_
            rfl
      _ = ∑ a ∈ X, (∑ b ∈ X, φ.f b a + ∑ b ∈ Xᶜ, φ.f b a) := by
            refine Finset.sum_congr rfl fun a ha => ?_
            exact (Finset.sum_add_sum_compl X (fun b => φ.f b a)).symm
      _ = (∑ a ∈ X, ∑ b ∈ X, φ.f b a) + (∑ a ∈ X, ∑ b ∈ Xᶜ, φ.f b a) := by
            rw [Finset.sum_add_distrib]
      _ = 0 + (∑ a ∈ X, ∑ b ∈ Xᶜ, φ.f b a) := by
            congr 1
            rw [Finset.sum_comm]
            exact Preflow.skew_symm_cancel φ X
      _ = ∑ a ∈ X, ∑ b ∈ Xᶜ, φ.f b a := by simp
      _ = -∑ a ∈ X, ∑ b ∈ Xᶜ, φ.f a b := by
            rw [Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun a ha => ?_
            rw [Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun b hb => ?_
            exact φ.hskew_symm b a
      _ = -∑ a ∈ X, ∑ b ∈ Xᶜ, G.c a b := by
            congr 1
            refine Finset.sum_congr rfl fun a ha => ?_
            refine Finset.sum_congr rfl fun b hb => ?_
            exact hf_eq_cap a ha b hb
      _ ≤ 0 := by
            have hnonneg : 0 ≤ ∑ a ∈ X, ∑ b ∈ Xᶜ, G.c a b := by
              refine Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb => ?_
              exact G.hc_nonneg a b
            linarith
  have hu_mem : u ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_univ u, Relation.ReflTransGen.refl⟩
  have hsum_pos : 0 < ∑ a ∈ X, φ.excess a := by
    have hsplit : (∑ a ∈ X, φ.excess a) = (∑ a ∈ X.erase u, φ.excess a) + φ.excess u := by
      exact Finset.sum_erase_add hu_mem
    rw [hsplit]
    have hrest_nonneg : 0 ≤ ∑ a ∈ X.erase u, φ.excess a := by
      refine Finset.sum_nonneg fun a ha => ?_
      have ha_X : a ∈ X := Finset.mem_of_mem_erase ha
      have ha_ne_s : a ≠ G.s := by
        intro ha_eq_s
        apply hs_not_mem
        rwa [ha_eq_s]
      exact φ.hexcess_nonneg a ha_ne_s
    linarith
  linarith

/-- **Lemma 24.14 (CLRS).** The height of any overflowing vertex `u ≠ s` is at
most `2|V| - 1`. -/
theorem height_le_of_overflowing {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ) (hvalid : IsValidHeight φ h)
    (u : V) (hu_ne_s : u ≠ G.s) (hu_overflow : 0 < φ.excess u) :
    h u ≤ 2 * Fintype.card V - 1 := by
  have hpath := exists_residualPath_to_source_of_overflowing φ u hu_ne_s hu_overflow
  have hle := height_le_of_reachability φ h hvalid.2.2 hpath
  have hs_card : h G.s = Fintype.card V := hvalid.1
  rw [hs_card] at hle
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  omega

/-! ## Correctness: a terminated preflow is a maximum flow -/

/-- A valid height function rules out a source-to-sink residual path. -/
theorem noAugmentingPath_of_validHeight {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ) (hvalid : IsValidHeight φ h) :
    ¬ φ.hasAugmentingPath := by
  intro hpath
  have hle := height_le_of_reachability φ h hvalid.2.2 hpath
  rw [hvalid.1, hvalid.2.1] at hle
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  omega

/-- **Theorem (push-relabel correctness).** If a preflow has a valid height
function and no overflowing internal vertex, then it induces a maximum flow. -/
theorem maximal_of_no_overflow {V : Type*} [Fintype V] [DecidableEq V]
    {G : FlowNetwork V} (φ : Preflow V G) (h : V → ℕ) (hvalid : IsValidHeight φ h)
    (hnoflow : ∀ u, u ≠ G.s → u ≠ G.t → φ.excess u = 0) :
    Flow.isMaximal (φ.toFlow hnoflow) := by
  have hnoPath : ¬ φ.hasAugmentingPath := noAugmentingPath_of_validHeight φ h hvalid
  have hnoPath_flow : ¬ (φ.toFlow hnoflow).hasAugmentingPath := by
    intro hpath
    exact hnoPath ((φ.toFlow_hasAugmentingPath hnoflow).mp hpath)
  exact (φ.toFlow hnoflow).maximal_of_noAugmentingPath hnoPath_flow

end Chapter26
end CLRS
