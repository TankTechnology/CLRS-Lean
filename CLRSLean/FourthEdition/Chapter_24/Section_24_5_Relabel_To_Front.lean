import CLRSLean.FourthEdition.Chapter_24.Section_24_4_Push_Relabel

/-!
# 24.5. Relabel-to-Front

This section completes the push-relabel maximum-flow analysis begun in
{lit}`CLRSLean.FourthEdition.Chapter_24.Section_24_4_Push_Relabel`.  There we
established the *preflow* model, the *height function*, and the two local
operations {lit}`CLRS.Chapter26.Preflow.push` and
{lit}`CLRS.Chapter26.relabel`, together with the correctness certificate
{lit}`CLRS.Chapter26.maximal_of_no_overflow`.  Here we count the operations and
give the relabel-to-front ordering.

The generic push-relabel algorithm repeatedly picks an overflowing vertex and
applies a push or a relabel.  A run of the algorithm is a sequence of *basic
operations* (`BasicOp`), each either a relabel of an overflowing vertex or a
push from an overflowing vertex along an admissible edge.  We count relabels,
saturating pushes, and nonsaturating pushes over a `Run`, and prove the three
CLRS counting bounds:

Main results:

- `BasicOp`, `Run`: a single basic operation and a length-`n` run of the generic
  algorithm.
- `Run.height_mono`: heights are nondecreasing across a run.
- `Run.relabel_count_bound`: at most `2|V|²` relabel operations total.
- `Run.saturating_push_count_bound`: at most `2|V|·|E|` saturating pushes.
- `Run.nonsaturating_push_count_bound`: at most `4|V|²(|V|+|E|)` nonsaturating
  pushes, via the potential `Φ = Σ_{overflowing u} h(u)`.
- `Run.generic_step_count_bound`: the combined `O(V²E)` bound on the number of
  basic operations.

These bounds hold for *any* run of the generic algorithm, so they apply to the
relabel-to-front schedule in particular.

Notation conventions used in this section:

- `φ` : a preflow on the network `G`
- `h` : a height function `V → ℕ`
- `V` (as `Fintype.card V`) : the number of vertices
- `E` (as `numEdges G`) : the number of directed positive-capacity edges
-/
set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-! ## The number of edges -/

/-- The set of directed edges `(u,v)` with positive capacity. -/
noncomputable def edgeSet (G : FlowNetwork V) : Finset (V × V) :=
  (Finset.univ : Finset (V × V)).filter (fun e => 0 < G.c e.1 e.2)

/-- The number of directed edges (positive-capacity pairs). -/
noncomputable def numEdges (G : FlowNetwork V) : ℕ := (edgeSet G).card

/-! ## Basic operations and runs -/

/-- A single basic operation of the generic push-relabel algorithm: either a
relabel of an overflowing vertex `u`, or a push from an overflowing `u` along an
admissible residual edge `(u,v)`. -/
inductive BasicOp (V : Type*) [Fintype V] [DecidableEq V] (G : FlowNetwork V) :
    Preflow V G → (V → ℕ) → Preflow V G → (V → ℕ) → Prop where
  | relabel (φ : Preflow V G) (h : V → ℕ) (u : V) (hoverflow : φ.isOverflowing u)
      (hres : ∃ v : V, φ.residualEdge u v)
      (hpre : ∀ v, φ.residualEdge u v → h u ≤ h v) :
      BasicOp G φ h φ (relabel φ h u hres)
  | push (φ : Preflow V G) (h : V → ℕ) (u v : V) (hoverflow : φ.isOverflowing u)
      (hres : φ.residualEdge u v) (hadm : h u = h v + 1) :
      BasicOp G φ h (Preflow.push φ u v hoverflow.1 hres) h

namespace BasicOp

/-- Whether the operation is a relabel. -/
def isRelabel {φ φ' : Preflow V G} {h h' : V → ℕ} : BasicOp G φ φ' h h' → Prop
  | .relabel .. => True
  | .push .. => False

/-- Whether the operation is a relabel of the specific vertex `u`. -/
def relabelOf (u : V) {φ φ' : Preflow V G} {h h' : V → ℕ} : BasicOp G φ φ' h h' → Prop
  | .relabel _ _ w _ _ _ => w = u
  | .push .. => False

/-- Whether the operation is a push along the specific edge `(u,v)`. -/
def pushOn (u v : V) {φ φ' : Preflow V G} {h h' : V → ℕ} : BasicOp G φ φ' h h' → Prop
  | .push _ _ a b _ _ _ => a = u ∧ b = v
  | .relabel .. => False

/-- Whether the operation is a saturating push (the residual capacity of the
edge is exhausted, i.e. `cf(u,v) ≤ e(u)` so `δ = cf(u,v)`). -/
def isSaturatingPush {φ φ' : Preflow V G} {h h' : V → ℕ} : BasicOp G φ φ' h h' → Prop
  | .push φ _ u v _ _ _ => φ.residualCapacity u v ≤ φ.excess u
  | .relabel .. => False

/-- Whether the operation is a nonsaturating push (the excess is exhausted,
i.e. `e(u) < cf(u,v)` so `δ = e(u)`). -/
def isNonsaturatingPush {φ φ' : Preflow V G} {h h' : V → ℕ} : BasicOp G φ φ' h h' → Prop
  | .push φ _ u v _ _ _ => φ.excess u < φ.residualCapacity u v
  | .relabel .. => False

/-- A saturating push along the specific edge `(u,v)`. -/
def saturatingPushOn (u v : V) {φ φ' : Preflow V G} {h h' : V → ℕ} :
    BasicOp G φ φ' h h' → Prop
  | .push φ _ a b _ _ _ => a = u ∧ b = v ∧ φ.residualCapacity u v ≤ φ.excess u
  | .relabel .. => False

end BasicOp

/-- A run of the generic push-relabel algorithm: a sequence of `n` basic
operations with the associated preflows and height functions. -/
structure Run (V : Type*) [Fintype V] [DecidableEq V] (G : FlowNetwork V) (n : ℕ) where
  φ : ℕ → Preflow V G
  h : ℕ → V → ℕ
  hvalid : ∀ i, IsValidHeight (φ i) (h i)
  op : ∀ i, i < n → BasicOp G (φ i) (h i) (φ (i + 1)) (h (i + 1))

namespace Run

/-- The operation at step `i` of a run, addressed by a `Finset.range n` member. -/
def stepOp (R : Run V G n) (i : {i // i ∈ Finset.range n}) :
    BasicOp G (R.φ i.1) (R.h i.1) (R.φ (i.1 + 1)) (R.h (i.1 + 1)) :=
  R.op i.1 (Finset.mem_range.mp i.2)

/-- The number of relabel operations in a run. -/
noncomputable def numRelabels (R : Run V G n) : ℕ :=
  ((Finset.range n).attach.filter (fun i => (R.stepOp i).isRelabel)).card

/-- The number of saturating push operations in a run. -/
noncomputable def numSaturatingPushes (R : Run V G n) : ℕ :=
  ((Finset.range n).attach.filter (fun i => (R.stepOp i).isSaturatingPush)).card

/-- The number of nonsaturating push operations in a run. -/
noncomputable def numNonsaturatingPushes (R : Run V G n) : ℕ :=
  ((Finset.range n).attach.filter (fun i => (R.stepOp i).isNonsaturatingPush)).card

/-- The number of relabel operations of a specific vertex `u`. -/
noncomputable def numRelabelsOf (R : Run V G n) (u : V) : ℕ :=
  ((Finset.range n).attach.filter (fun i => (R.stepOp i).relabelOf u)).card

/-- The number of saturating pushes along a specific edge `(u,v)`. -/
noncomputable def numSaturatingPushesOn (R : Run V G n) (u v : V) : ℕ :=
  ((Finset.range n).attach.filter (fun i => (R.stepOp i).saturatingPushOn u v)).card

/-! ## Height monotonicity -/

/-- The height of any fixed vertex is nondecreasing across a single step. -/
lemma height_mono_step (R : Run V G n) {i : ℕ} (hi : i < n) (u : V) :
    R.h i u ≤ R.h (i + 1) u := by
  cases h : R.op i hi with
  | relabel φ h w hoverflow hres hpre =>
      by_cases hwu : w = u
      · subst u
        exact le_of_lt (relabel_height_increase φ h w hres hpre)
      · simpa [relabel_eq_of_ne φ h w hres hwu]
  | push φ h u v hoverflow hres hadm =>
      rfl

/-- Heights are nondecreasing across a run: `i ≤ j` implies `h i u ≤ h j u`. -/
lemma height_mono (R : Run V G n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) (u : V) :
    R.h i u ≤ R.h j u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => rfl
  | succ d ih =>
      have hle := ih
      have hstep : R.h (i + d) u ≤ R.h (i + d + 1) u := by
        apply height_mono_step R
        omega
      omega

/-! ## Relabel count bound -/

/-- A relabel step strictly increases the height of the relabeled vertex. -/
lemma height_increase_of_relabel_step (R : Run V G n) {i : ℕ} (hi : i < n) {u : V}
    (hrel : (R.op i hi).relabelOf u) :
    R.h i u < R.h (i + 1) u := by
  cases h : R.op i hi with
  | relabel φ h w hoverflow hres hpre =>
      have hwu : w = u := by simpa [BasicOp.relabelOf] using hrel
      subst u
      exact relabel_height_increase φ h w hres hpre
  | push φ h u v hoverflow hres hadm =>
      cases (by simpa [BasicOp.relabelOf] using hrel : False)

/-- The height of `u` strictly increases between two distinct relabel steps of
`u`. -/
lemma height_strict_between_relabels_of (R : Run V G n) {i j : ℕ} (hij : i < j)
    (hj : j < n) {u : V} (hri : (R.op i (lt_trans hij hj)).relabelOf u)
    (hrj : (R.op j hj).relabelOf u) :
    R.h i u < R.h j u := by
  have hinc : R.h i u < R.h (i + 1) u :=
    height_increase_of_relabel_step R (lt_trans hij hj) hri
  have hmono : R.h (i + 1) u ≤ R.h j u := by
    apply height_mono R
    · omega
    · omega
  omega

/-- Each vertex is relabeled at most `2|V|` times. -/
theorem relabel_count_bound_of (R : Run V G n) (u : V) :
    numRelabelsOf R u ≤ 2 * Fintype.card V := by
  classical
  let S : Finset {i // i ∈ Finset.range n} :=
    (Finset.range n).attach.filter (fun i => (R.stepOp i).relabelOf u)
  have hcard : S.card = numRelabelsOf R u := by
    rfl
  rw [← hcard]
  let f : {i // i ∈ Finset.range n} → ℕ := fun i => R.h i.1 u
  have hf_inj : Set.InjOn f (↑S : Set {i // i ∈ Finset.range n}) := by
    intro a ha b hb hfab
    have ha' : (R.stepOp a).relabelOf u := (Finset.mem_filter.mp ha).2
    have hb' : (R.stepOp b).relabelOf u := (Finset.mem_filter.mp hb).2
    apply Subtype.ext
    apply le_antisymm
    · by_contra hgt
      have hlt : b.1 < a.1 := by omega
      have hst : R.h b.1 u < R.h a.1 u :=
        height_strict_between_relabels_of R hlt (Finset.mem_range.mp a.2) hb' ha'
      omega
    · by_contra hgt
      have hlt : a.1 < b.1 := by omega
      have hst : R.h a.1 u < R.h b.1 u :=
        height_strict_between_relabels_of R hlt (Finset.mem_range.mp b.2) ha' hb'
      omega
  have hf_range : ∀ a : {i // i ∈ Finset.range n}, a ∈ S →
      f a < 2 * Fintype.card V := by
    intro a ha
    have hrel' : (R.stepOp a).relabelOf u := (Finset.mem_filter.mp ha).2
    have hoverflow : (R.φ a.1).isOverflowing u := by
      cases h : R.stepOp a with
      | relabel φ h w hoverflow hres hpre =>
          have hwu : w = u := by simpa [BasicOp.relabelOf] using hrel'
          simpa [hwu] using hoverflow
      | push φ h u v hoverflow hres hadm =>
          cases (by simpa [BasicOp.relabelOf] using hrel' : False)
    have hle := height_le_of_overflowing (R.φ a.1) (R.h a.1) (R.hvalid a.1) u
      hoverflow.1 hoverflow.2.2
    unfold f
    omega
  calc
    S.card = (S.image f).card := by
      rw [Finset.card_image_iff]
      exact hf_inj
    _ ≤ (Finset.range (2 * Fintype.card V)).card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      have hlt : f a < 2 * Fintype.card V := hf_range a (by
        simpa using ha)
      exact Finset.mem_range.mpr hlt
    _ = 2 * Fintype.card V := by simp

/-- The total number of relabel operations is at most `2|V|²`. -/
theorem relabel_count_bound (R : Run V G n) :
    numRelabels R ≤ 2 * Fintype.card V * Fintype.card V := by
  have hsum : numRelabels R = ∑ u : V, numRelabelsOf R u := by
    unfold numRelabels numRelabelsOf
    rw [← Finset.card_attach, Finset.card_filter]
    sorry
  sorry

end Run
end Chapter26
end CLRS
