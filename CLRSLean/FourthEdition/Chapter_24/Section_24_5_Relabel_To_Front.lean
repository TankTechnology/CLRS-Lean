import CLRSLean.FourthEdition.Chapter_24.Section_24_4_Push_Relabel

/-!
# 24.5. Relabel-to-Front

This section completes the push-relabel maximum-flow analysis begun in
{lit}`CLRSLean.FourthEdition.Chapter_24.Section_24_4_Push_Relabel`.  There we
established the *preflow* model, the *height function*, and the two local
operations {lit}`CLRS.Chapter26.push` and {lit}`CLRS.Chapter26.relabel`, together
with the correctness certificate {lit}`CLRS.Chapter26.maximal_of_no_overflow`.
Here we count the operations.

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
- `Run.saturating_push_count_bound`: at most `O(|V|·|E|)` saturating pushes.
- `Run.nonsaturating_push_count_bound`: at most `O(|V|²(|V|+|E|))` nonsaturating
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

universe u

open Finset Classical
open scoped BigOperators

variable {V : Type u} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-! ## The number of edges -/

/-- The set of directed edges `(u,v)` with positive capacity. -/
noncomputable def edgeSet (G : FlowNetwork V) : Finset (V × V) :=
  (Finset.univ : Finset (V × V)).filter (fun e => 0 < G.c e.1 e.2)

/-- The number of directed edges (positive-capacity pairs). -/
noncomputable def numEdges (G : FlowNetwork V) : ℕ := (edgeSet G).card

/-! ## Basic operations and runs -/

/-- A single basic operation of the generic push-relabel algorithm: either a
relabel of an overflowing vertex `u`, or a push from an overflowing `u` along an
admissible residual edge `(u,v)`.  The preflow `φ` and height `h` are the state
*before* the operation. -/
inductive BasicOp (V : Type u) [Fintype V] [DecidableEq V] (G : FlowNetwork V) : Type u where
  | relabel (φ : Preflow V G) (h : V → ℕ) (u : V) (hoverflow : φ.isOverflowing u)
      (hres : ∃ v : V, φ.residualEdge u v)
      (hpre : ∀ v, φ.residualEdge u v → h u ≤ h v) : BasicOp V G
  | push (φ : Preflow V G) (h : V → ℕ) (u v : V) (hoverflow : φ.isOverflowing u)
      (hres : φ.residualEdge u v) (hadm : h u = h v + 1) : BasicOp V G

namespace BasicOp

/-- The preflow before the operation. -/
def beforeφ : BasicOp V G → Preflow V G
  | .relabel φ _ _ _ _ _ => φ
  | .push φ _ _ _ _ _ _ => φ

/-- The height function before the operation. -/
def beforeh : BasicOp V G → V → ℕ
  | .relabel _ h _ _ _ _ => h
  | .push _ h _ _ _ _ _ => h

/-- The preflow after the operation. -/
noncomputable def resultφ : BasicOp V G → Preflow V G
  | .relabel φ _ _ _ _ _ => φ
  | .push φ _ u v hoverflow hres _ => Chapter26.push φ u v hoverflow.1 hres

/-- The height function after the operation. -/
noncomputable def resulth : BasicOp V G → V → ℕ
  | .relabel φ h u _ hres _ => Chapter26.relabel φ h u hres
  | .push _ h _ _ _ _ _ => h

/-- Whether the operation is a relabel. -/
def isRelabel : BasicOp V G → Bool
  | .relabel .. => true
  | .push .. => false

/-- Whether the operation is a relabel of the specific vertex `u`. -/
def relabelOf (u : V) : BasicOp V G → Bool
  | .relabel _ _ w _ _ _ => decide (w = u)
  | .push .. => false

/-- Whether the operation is a push along the specific edge `(u,v)`. -/
def pushOn (u v : V) : BasicOp V G → Bool
  | .push _ _ a b _ _ _ => decide (a = u ∧ b = v)
  | .relabel .. => false

/-- Whether the operation is a saturating push (the residual capacity of the
edge is exhausted, i.e. `cf(u,v) ≤ e(u)` so `δ = cf(u,v)`). -/
noncomputable def isSaturatingPush : BasicOp V G → Bool
  | .push φ _ u v _ _ _ => decide (φ.residualCapacity u v ≤ φ.excess u)
  | .relabel .. => false

/-- Whether the operation is a nonsaturating push (the excess is exhausted,
i.e. `e(u) < cf(u,v)` so `δ = e(u)`). -/
noncomputable def isNonsaturatingPush : BasicOp V G → Bool
  | .push φ _ u v _ _ _ => decide (φ.excess u < φ.residualCapacity u v)
  | .relabel .. => false

/-- A saturating push along the specific edge `(u,v)`. -/
noncomputable def saturatingPushOn (u v : V) : BasicOp V G → Bool
  | .push φ _ a b _ _ _ => decide (a = u ∧ b = v ∧ φ.residualCapacity a b ≤ φ.excess a)
  | .relabel .. => false

/-- A single operation is exactly one of relabel, saturating push, or
nonsaturating push. -/
lemma classification (o : BasicOp V G) :
    (if o.isRelabel then 1 else 0) + (if o.isSaturatingPush then 1 else 0) +
      (if o.isNonsaturatingPush then 1 else 0) = 1 := by
  cases o with
  | relabel φ h u ho hres hpre =>
      simp [isRelabel, isSaturatingPush, isNonsaturatingPush]
  | push φ h u v ho hres hadm =>
      by_cases hsat : φ.residualCapacity u v ≤ φ.excess u
      · simp [isRelabel, isSaturatingPush, isNonsaturatingPush, hsat]
      · have hlt : φ.excess u < φ.residualCapacity u v := lt_of_not_ge hsat
        simp [isRelabel, isSaturatingPush, isNonsaturatingPush, hsat, hlt]

/-- Relabels are characterized by the vertex they relabel. -/
lemma sum_relabelOf_eq_isRelabel (o : BasicOp V G) :
    (∑ u : V, (if o.relabelOf u then 1 else 0 : ℕ)) = (if o.isRelabel then 1 else 0 : ℕ) := by
  cases o with
  | relabel φ h w ho hres hpre =>
      simp only [relabelOf, isRelabel]
      rw [Finset.sum_eq_single w]
      · simp
      · intro b _ hbw
        simp [hbw.symm]
      · intro hw
        simp at hw
  | push φ h u v ho hres hadm =>
      simp [relabelOf, isRelabel]

/-- Saturating pushes are characterized by the edge they saturate. -/
lemma sum_saturatingPushOn_eq (o : BasicOp V G) :
    (∑ e : V × V, (if o.saturatingPushOn e.1 e.2 then 1 else 0 : ℕ)) =
      (if o.isSaturatingPush then 1 else 0 : ℕ) := by
  cases o with
  | relabel φ h u ho hres hpre =>
      simp [saturatingPushOn, isSaturatingPush]
  | push φ h u v ho hres hadm =>
      by_cases hsat : φ.residualCapacity u v ≤ φ.excess u
      · have hcard : ((Finset.univ.filter (fun e : V × V => u = e.1 ∧ v = e.2)).card) = 1 := by
          have hf : (Finset.univ.filter (fun e : V × V => u = e.1 ∧ v = e.2)) = {(u, v)} := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro h
              exact Prod.ext h.1.symm h.2.symm
            · intro h
              cases h
              exact ⟨rfl, rfl⟩
          rw [hf]
          simp
        simp [saturatingPushOn, isSaturatingPush, hsat, Finset.sum_boole, hcard]
      · simp [saturatingPushOn, isSaturatingPush, hsat]

/-- The height of any fixed vertex is nondecreasing across a single operation. -/
lemma height_mono (o : BasicOp V G) (u : V) : o.beforeh u ≤ o.resulth u := by
  cases o with
  | relabel φ h w ho hres hpre =>
      by_cases hwu : w = u
      · subst u
        exact le_of_lt (relabel_height_increase φ h w hres hpre)
      · simpa [beforeh, resulth, relabel_eq_of_ne φ h w hres (Ne.symm hwu)]
  | push φ h u v ho hres hadm =>
      simp [beforeh, resulth]

/-- A relabel operation strictly increases the height of the relabeled vertex. -/
lemma height_increase_of_relabel (o : BasicOp V G) {u : V} (hrel : o.relabelOf u = true) :
    o.beforeh u < o.resulth u := by
  cases o with
  | relabel φ h w ho hres hpre =>
      have hwu : w = u := by
        simpa [relabelOf] using (of_decide_eq_true hrel)
      subst u
      exact relabel_height_increase φ h w hres hpre
  | push φ h u v ho hres hadm =>
      simp [relabelOf] at hrel

end BasicOp

/-- A run of the generic push-relabel algorithm: a sequence of `n` basic
operations with the associated preflows and height functions. -/
structure Run (V : Type u) [Fintype V] [DecidableEq V] (G : FlowNetwork V) (n : ℕ) where
  φ : ℕ → Preflow V G
  h : ℕ → V → ℕ
  hvalid : ∀ i, IsValidHeight (φ i) (h i)
  op : ∀ i, i < n → BasicOp V G
  hop_beforeφ : ∀ i (hi : i < n), (op i hi).beforeφ = φ i
  hop_beforeh : ∀ i (hi : i < n), (op i hi).beforeh = h i
  hop_resultφ : ∀ i (hi : i < n), (op i hi).resultφ = φ (i + 1)
  hop_resulth : ∀ i (hi : i < n), (op i hi).resulth = h (i + 1)

namespace Run

open BasicOp (relabelOf pushOn saturatingPushOn isRelabel isSaturatingPush isNonsaturatingPush)

/-- The operation at a `Fin n` step. -/
def opFin (R : Run V G n) (i : Fin n) : BasicOp V G :=
  R.op i.1 (Fin.isLt i)

/-- The number of relabel operations in a run. -/
noncomputable def numRelabels (R : Run V G n) : ℕ :=
  ∑ i : Fin n, (if (R.opFin i).isRelabel then 1 else 0)

/-- The number of saturating push operations in a run. -/
noncomputable def numSaturatingPushes (R : Run V G n) : ℕ :=
  ∑ i : Fin n, (if (R.opFin i).isSaturatingPush then 1 else 0)

/-- The number of nonsaturating push operations in a run. -/
noncomputable def numNonsaturatingPushes (R : Run V G n) : ℕ :=
  ∑ i : Fin n, (if (R.opFin i).isNonsaturatingPush then 1 else 0)

/-- The number of relabel operations of a specific vertex `u`. -/
noncomputable def numRelabelsOf (R : Run V G n) (u : V) : ℕ :=
  ∑ i : Fin n, (if (R.opFin i).relabelOf u then 1 else 0)

/-- The number of saturating pushes along a specific edge `(u,v)`. -/
noncomputable def numSaturatingPushesOn (R : Run V G n) (u v : V) : ℕ :=
  ∑ i : Fin n, (if (R.opFin i).saturatingPushOn u v then 1 else 0)

/-! ## Height monotonicity -/

/-- The height of any fixed vertex is nondecreasing across a single step. -/
lemma height_mono_step (R : Run V G n) (i : Fin n) (u : V) :
    R.h i.1 u ≤ R.h (i.1 + 1) u := by
  have hb := BasicOp.height_mono (R.opFin i) u
  have hb' : (R.opFin i).beforeh u = R.h i.1 u := by
    exact congrFun (R.hop_beforeh i.1 (Fin.isLt i)) u
  have hr' : (R.opFin i).resulth u = R.h (i.1 + 1) u := by
    exact congrFun (R.hop_resulth i.1 (Fin.isLt i)) u
  rw [← hb', ← hr']
  exact hb

/-- Heights are nondecreasing across a run: `i ≤ j` implies `h i u ≤ h j u`. -/
lemma height_mono (R : Run V G n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) (u : V) :
    R.h i u ≤ R.h j u := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => rfl
  | succ d ih =>
      have hle := ih
      have hstep : R.h (i + d) u ≤ R.h (i + (d + 1)) u := by
        have hi : i + d < n := by omega
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          height_mono_step R ⟨i + d, hi⟩ u
      omega

/-! ## Relabel count bound -/

/-- The height of `u` strictly increases between two distinct relabel steps of
`u`. -/
lemma height_strict_between_relabels_of (R : Run V G n) {i j : Fin n} (hij : i.1 < j.1)
    {u : V} (hri : (R.opFin i).relabelOf u = true) (hrj : (R.opFin j).relabelOf u = true) :
    R.h i.1 u < R.h j.1 u := by
  have hinc : R.h i.1 u < R.h (i.1 + 1) u := by
    have hb := BasicOp.height_increase_of_relabel (R.opFin i) hri
    rw [show R.opFin i = R.op i.1 (Fin.isLt i) from rfl] at hb
    rw [R.hop_beforeh i.1 (Fin.isLt i)] at hb
    rw [R.hop_resulth i.1 (Fin.isLt i)] at hb
    exact hb
  have hmono : R.h (i.1 + 1) u ≤ R.h j.1 u := by
    apply height_mono R
    · omega
    · omega
  omega

/-- Each vertex is relabeled at most `2|V|` times. -/
theorem relabel_count_bound_of (R : Run V G n) (u : V) :
    numRelabelsOf R u ≤ 2 * Fintype.card V := by
  classical
  let S : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun i => (R.opFin i).relabelOf u = true)
  have hcard : numRelabelsOf R u = S.card := by
    rw [numRelabelsOf]
    rw [Finset.sum_boole]
    rfl
  rw [hcard]
  let f : Fin n → ℕ := fun i => R.h i.1 u
  have hf_inj : Set.InjOn f (↑S : Set (Fin n)) := by
    intro a ha b hb hfab
    have ha' : (R.opFin a).relabelOf u = true := (Finset.mem_filter.mp ha).2
    have hb' : (R.opFin b).relabelOf u = true := (Finset.mem_filter.mp hb).2
    apply Fin.ext
    apply le_antisymm
    · by_contra hgt
      have hlt : b.1 < a.1 := by omega
      have hst := height_strict_between_relabels_of R hlt hb' ha'
      unfold f at hfab
      omega
    · by_contra hgt
      have hlt : a.1 < b.1 := by omega
      have hst := height_strict_between_relabels_of R hlt ha' hb'
      unfold f at hfab
      omega
  have hf_range : ∀ a : Fin n, a ∈ S → f a < 2 * Fintype.card V := by
    intro a ha
    have hrel' : (R.opFin a).relabelOf u = true := (Finset.mem_filter.mp ha).2
    have hoverflow : (R.φ a.1).isOverflowing u := by
      cases hop : R.opFin a with
      | relabel φ h w ho hres hpre =>
          have hwu : w = u := of_decide_eq_true (by simpa [relabelOf, hop] using hrel')
          have hbφ : φ = R.φ a.1 := by
            have h : (R.opFin a).beforeφ = R.φ a.1 := R.hop_beforeφ a.1 (Fin.isLt a)
            simpa [BasicOp.beforeφ, hop] using h
          subst u
          simpa [hbφ] using ho
      | push φ h u' v ho hres hadm =>
          simp [relabelOf, hop] at hrel'
    have hle := height_le_of_overflowing (R.φ a.1) (R.h a.1) (R.hvalid a.1) u
      hoverflow.1 hoverflow.2.2
    have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨G.s⟩
    unfold f
    omega
  calc
    S.card = (S.image f).card := by
      exact (Finset.card_image_iff.mpr hf_inj).symm
    _ ≤ (Finset.range (2 * Fintype.card V)).card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      have hlt : f a < 2 * Fintype.card V := hf_range a (by simpa using ha)
      exact Finset.mem_range.mpr hlt
    _ = 2 * Fintype.card V := by simp

/-- The total number of relabel operations is at most `2|V|²`. -/
theorem relabel_count_bound (R : Run V G n) :
    numRelabels R ≤ 2 * Fintype.card V * Fintype.card V := by
  have hsum : numRelabels R = ∑ u : V, numRelabelsOf R u := by
    calc
      numRelabels R = ∑ i : Fin n, (if (R.opFin i).isRelabel then 1 else 0) := rfl
      _ = ∑ i : Fin n, ∑ u : V, (if (R.opFin i).relabelOf u then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (BasicOp.sum_relabelOf_eq_isRelabel (R.opFin i)).symm
      _ = ∑ u : V, ∑ i : Fin n, (if (R.opFin i).relabelOf u then 1 else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ u : V, numRelabelsOf R u := rfl
  calc
    numRelabels R = ∑ u : V, numRelabelsOf R u := hsum
    _ ≤ ∑ u : V, (2 * Fintype.card V) := by
      apply Finset.sum_le_sum
      intro u _
      exact relabel_count_bound_of R u
    _ = Fintype.card V * (2 * Fintype.card V) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * Fintype.card V * Fintype.card V := by rw [mul_comm]

/-! ## Saturating push count bound -/

/-- The exact effect of `pushBy` on residual capacity. -/
lemma pushBy_residualCapacity_eq (φ : Preflow V G) (u v : V) (huv : u ≠ v) (δ : ℝ)
    (hδ_nonneg : 0 ≤ δ) (hδ_le_excess : δ ≤ φ.excess u)
    (hδ_le_residual : δ ≤ φ.residualCapacity u v) (a b : V) :
    (pushBy φ u v huv δ hδ_nonneg hδ_le_excess hδ_le_residual).residualCapacity a b =
      φ.residualCapacity a b - (if a = u ∧ b = v then δ else 0) +
        (if a = v ∧ b = u then δ else 0) := by
  unfold pushBy Preflow.residualCapacity Flow.edgeDelta
  ring

/-- The exact effect of `push` on residual capacity. -/
lemma push_residualCapacity_eq (φ : Preflow V G) (u v : V) (hu_ne_s : u ≠ G.s)
    (hres : φ.residualEdge u v) (a b : V) :
    (push φ u v hu_ne_s hres).residualCapacity a b =
      φ.residualCapacity a b -
        (if a = u ∧ b = v then min (φ.excess u) (φ.residualCapacity u v) else 0) +
        (if a = v ∧ b = u then min (φ.excess u) (φ.residualCapacity u v) else 0) := by
  unfold push
  exact pushBy_residualCapacity_eq φ u v (residualEdge_ne φ hres)
    (min (φ.excess u) (φ.residualCapacity u v))
    (le_min (φ.hexcess_nonneg u hu_ne_s) (le_of_lt hres)) (min_le_left _ _)
    (min_le_right _ _) a b

/-- A push that does not run along the reverse edge `(v,u)` cannot increase the
residual capacity of `(u,v)`. -/
lemma residualCapacity_le_of_not_reverse_push (φ : Preflow V G) (a b : V) (hu_ne_s : a ≠ G.s)
    (hres : φ.residualEdge a b) (u v : V) (hnot : ¬ (a = v ∧ b = u)) :
    (push φ a b hu_ne_s hres).residualCapacity u v ≤ φ.residualCapacity u v := by
  rw [push_residualCapacity_eq φ a b hu_ne_s hres u v]
  have hno_add : (if u = b ∧ v = a then min (φ.excess a) (φ.residualCapacity a b) else 0) = 0 := by
    by_cases h : u = b ∧ v = a
    · have hrev : a = v ∧ b = u := ⟨h.2.symm, h.1.symm⟩
      exact (hnot hrev).elim
    · simp [h]
  rw [hno_add]
  by_cases h : u = a ∧ v = b
  · rcases h with ⟨hau, hbv⟩
    subst u
    subst v
    have hmin_nonneg : 0 ≤ min (φ.excess a) (φ.residualCapacity a b) :=
      le_min (φ.hexcess_nonneg a hu_ne_s) (le_of_lt hres)
    simp only [if_true, and_self]
    linarith
  · simp [h]

/-- A residual capacity that starts at `0` and becomes positive must at some
intermediate step be increased by a push along the reverse edge. -/
lemma exists_reverse_push_of_residual_recovery (R : Run V G n) {u v : V} {i j : ℕ}
    (hij : i + 1 ≤ j) (hj : j ≤ n) (hzero : (R.φ (i + 1)).residualCapacity u v = 0)
    (hpos : (R.φ j).residualCapacity u v > 0) :
    ∃ k : Fin n, i + 1 ≤ k.1 ∧ k.1 < j ∧ (R.opFin k).pushOn v u = true := by
  classical
  have hmain := Nat.le_induction (m := i + 1)
    (P := fun t _ => t ≤ n →
      (R.φ (i + 1)).residualCapacity u v = 0 →
      (R.φ t).residualCapacity u v > 0 →
      ∃ k : Fin n, i + 1 ≤ k.1 ∧ k.1 < t ∧ (R.opFin k).pushOn v u = true)
    (base := by
      intro _ hzero hpos
      linarith)
    (succ := by
      intro t ht ih ht_succ_n hzero hpos
      by_cases hpred : (R.φ t).residualCapacity u v > 0
      · obtain ⟨k, hk1, hk2, hk3⟩ := ih (by omega) hzero hpred
        exact ⟨k, hk1, by omega, hk3⟩
      · have hnonpos : (R.φ t).residualCapacity u v ≤ 0 := le_of_not_gt hpred
        have hpush : (R.opFin ⟨t, by omega⟩).pushOn v u = true := by
          cases hop : R.op t (by omega) with
          | relabel φ h w ho hres hpre =>
              exfalso
              have hb : R.φ t = φ := by
                simpa [BasicOp.beforeφ, hop] using (R.hop_beforeφ t (by omega)).symm
              have hr : R.φ (t + 1) = φ := by
                simpa [BasicOp.resultφ, hop] using (R.hop_resultφ t (by omega)).symm
              have hpos' : (R.φ t).residualCapacity u v > 0 := by
                rw [hb, ← hr]
                exact hpos
              linarith
          | push φ h a b ho hres hadm =>
              have hstep_pos : (R.φ (t + 1)).residualCapacity u v > 0 := by
                have hr : (R.op t (by omega)).resultφ = R.φ (t + 1) :=
                  R.hop_resultφ t (by omega)
                simpa [hop, BasicOp.resultφ, hr] using hpos
              by_contra hnot
              have hle : (R.φ (t + 1)).residualCapacity u v ≤
                  (R.φ t).residualCapacity u v := by
                have hb : (R.op t (by omega)).beforeφ = R.φ t :=
                  R.hop_beforeφ t (by omega)
                have hr : (R.op t (by omega)).resultφ = R.φ (t + 1) :=
                  R.hop_resultφ t (by omega)
                have hnot' : ¬ (a = v ∧ b = u) := by
                  intro hab
                  apply hnot
                  change (R.op t (by omega)).pushOn v u = true
                  simp [pushOn, hop, hab]
                rw [← hb, ← hr]
                simpa [BasicOp.resultφ, BasicOp.beforeφ, hop] using
                  residualCapacity_le_of_not_reverse_push φ a b ho.1 hres u v hnot'
              linarith
        refine ⟨⟨t, by omega⟩, ?_, ?_, hpush⟩
        · exact ht
        · exact Nat.lt_succ_self t)
    j hij hj hzero hpos
  exact hmain

/-- The height of `u` grows by at least two between two saturating pushes along
`(u,v)`. -/
lemma saturating_height_increase (R : Run V G n) {u v : V} {i j : Fin n} (hij : i.1 < j.1)
    (hsat_i : (R.opFin i).saturatingPushOn u v = true)
    (hsat_j : (R.opFin j).saturatingPushOn u v = true) :
    R.h i.1 u + 2 ≤ R.h j.1 u := by
  have hadm_i : R.h i.1 u = R.h i.1 v + 1 := by
    cases hop : R.opFin i with
    | relabel φ h w ho hres hpre =>
        simp [saturatingPushOn, hop] at hsat_i
    | push φ h a b ho hres hadm =>
        have hle : a = u ∧ b = v ∧ φ.residualCapacity a b ≤ φ.excess a :=
          of_decide_eq_true (by simpa [saturatingPushOn, hop] using hsat_i)
        rcases hle with ⟨ha, hb, _⟩
        have hb_h : R.h i.1 = h := by
          have h' : (R.opFin i).beforeh = R.h i.1 := R.hop_beforeh i.1 (Fin.isLt i)
          rw [← h']
          simp [BasicOp.beforeh, hop]
        subst a; subst b
        rw [hb_h]
        exact hadm
  have hzero : (R.φ (i.1 + 1)).residualCapacity u v = 0 := by
    cases hop : R.opFin i with
    | relabel φ h w ho hres hpre =>
        simp [saturatingPushOn, hop] at hsat_i
    | push φ h a b ho hres hadm =>
        have hle : a = u ∧ b = v ∧ φ.residualCapacity a b ≤ φ.excess a :=
          of_decide_eq_true (by simpa [saturatingPushOn, hop] using hsat_i)
        rcases hle with ⟨ha, hb, hsat⟩
        have hb_φ : R.φ i.1 = φ := by
          have h' : (R.opFin i).beforeφ = R.φ i.1 := R.hop_beforeφ i.1 (Fin.isLt i)
          rw [← h']
          simp [BasicOp.beforeφ, hop]
        have hr_φ : R.φ (i.1 + 1) = (R.opFin i).resultφ := (R.hop_resultφ i.1 (Fin.isLt i)).symm
        subst a; subst b
        rw [hr_φ]
        simp [BasicOp.resultφ, hop, push_residualCapacity_eq φ u v ho.1 hres u v, hsat,
          min_eq_right hsat, residualEdge_ne φ hres]
  have hpos : (R.φ j.1).residualCapacity u v > 0 := by
    cases hop : R.opFin j with
    | relabel φ h w ho hres hpre =>
        simp [saturatingPushOn, hop] at hsat_j
    | push φ h a b ho hres hadm =>
        have hle : a = u ∧ b = v := by
          have h := of_decide_eq_true (by simpa [saturatingPushOn, hop] using hsat_j)
          exact ⟨h.1, h.2.1⟩
        have hb_φ : R.φ j.1 = φ := by
          have h' : (R.opFin j).beforeφ = R.φ j.1 := R.hop_beforeφ j.1 (Fin.isLt j)
          rw [← h']
          simp [BasicOp.beforeφ, hop]
        rcases hle with ⟨ha, hb⟩
        subst a; subst b
        rw [hb_φ]
        exact hres
  obtain ⟨k, hk1, hk2, hk3⟩ := exists_reverse_push_of_residual_recovery R (by omega : i.1 + 1 ≤ j.1)
    (le_of_lt (Fin.isLt j)) hzero hpos
  have hadm_k : R.h k.1 v = R.h k.1 u + 1 := by
    cases hop : R.op k.1 (Fin.isLt k) with
    | relabel φ h w ho hres hpre =>
        simp [opFin, pushOn, hop] at hk3
    | push φ h a b ho hres hadm =>
        have hle : a = v ∧ b = u := of_decide_eq_true (by simpa [opFin, pushOn, hop] using hk3)
        have hb_h : R.h k.1 = h := by
          have h' : (R.op k.1 (Fin.isLt k)).beforeh = R.h k.1 := R.hop_beforeh k.1 (Fin.isLt k)
          rw [← h']
          simp [BasicOp.beforeh, hop]
        rcases hle with ⟨ha, hb⟩
        subst a; subst b
        rw [hb_h]
        exact hadm
  have hadm_j : R.h j.1 u = R.h j.1 v + 1 := by
    cases hop : R.opFin j with
    | relabel φ h w ho hres hpre =>
        simp [saturatingPushOn, hop] at hsat_j
    | push φ h a b ho hres hadm =>
        have hle : a = u ∧ b = v := by
          have h := of_decide_eq_true (by simpa [saturatingPushOn, hop] using hsat_j)
          exact ⟨h.1, h.2.1⟩
        have hb_h : R.h j.1 = h := by
          have h' : (R.opFin j).beforeh = R.h j.1 := R.hop_beforeh j.1 (Fin.isLt j)
          rw [← h']
          simp [BasicOp.beforeh, hop]
        rcases hle with ⟨ha, hb⟩
        subst a; subst b
        rw [hb_h]
        exact hadm
  have h_iu_ku : R.h i.1 u ≤ R.h k.1 u := height_mono R (by omega) (by omega) u
  have h_kv_jv : R.h k.1 v ≤ R.h j.1 v := height_mono R (by omega) (by omega) v
  omega

/-- Each edge admits at most `2|V|` saturating pushes. -/
theorem saturating_push_count_bound_on (R : Run V G n) (u v : V) :
    numSaturatingPushesOn R u v ≤ 2 * Fintype.card V := by
  classical
  let S : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun i => (R.opFin i).saturatingPushOn u v = true)
  have hcard : numSaturatingPushesOn R u v = S.card := by
    rw [numSaturatingPushesOn]
    rw [Finset.sum_boole]
    rfl
  rw [hcard]
  let f : Fin n → ℕ := fun i => R.h i.1 u
  have hf_inj : Set.InjOn f (↑S : Set (Fin n)) := by
    intro a ha b hb hfab
    have ha' : (R.opFin a).saturatingPushOn u v = true := (Finset.mem_filter.mp ha).2
    have hb' : (R.opFin b).saturatingPushOn u v = true := (Finset.mem_filter.mp hb).2
    apply Fin.ext
    apply le_antisymm
    · by_contra hgt
      have hlt : b.1 < a.1 := by omega
      have hst := saturating_height_increase R hlt hb' ha'
      unfold f at hfab
      omega
    · by_contra hgt
      have hlt : a.1 < b.1 := by omega
      have hst := saturating_height_increase R hlt ha' hb'
      unfold f at hfab
      omega
  have hf_range : ∀ a : Fin n, a ∈ S → f a < 2 * Fintype.card V := by
    intro a ha
    have hsat' : (R.opFin a).saturatingPushOn u v = true := (Finset.mem_filter.mp ha).2
    have hoverflow : (R.φ a.1).isOverflowing u := by
      cases hop : R.opFin a with
      | relabel φ h w ho hres hpre =>
          simp [saturatingPushOn, hop] at hsat'
      | push φ h a' b ho hres hadm =>
          have hle : a' = u := by
            have h := of_decide_eq_true (by simpa [saturatingPushOn, hop] using hsat')
            exact h.1
          have hbφ : φ = R.φ a.1 := by
            have h : (R.opFin a).beforeφ = R.φ a.1 := R.hop_beforeφ a.1 (Fin.isLt a)
            simpa [BasicOp.beforeφ, hop] using h
          subst u
          simpa [hbφ] using ho
    have hle := height_le_of_overflowing (R.φ a.1) (R.h a.1) (R.hvalid a.1) u
      hoverflow.1 hoverflow.2.2
    have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨G.s⟩
    unfold f
    omega
  calc
    S.card = (S.image f).card := by
      exact (Finset.card_image_iff.mpr hf_inj).symm
    _ ≤ (Finset.range (2 * Fintype.card V)).card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
      have hlt : f a < 2 * Fintype.card V := hf_range a (by simpa using ha)
      exact Finset.mem_range.mpr hlt
    _ = 2 * Fintype.card V := by simp

/-- A saturating push on `(u,v)` requires some direction of `{u,v}` to have
positive capacity: either `(u,v)` itself, or the reverse edge `(v,u)` (a
saturating push may cancel flow on the reverse edge). -/
lemma saturating_pushOn_imp_cap (R : Run V G n) (u v : V) :
    numSaturatingPushesOn R u v = 0 ∨ 0 < G.c u v ∨ 0 < G.c v u := by
  classical
  by_cases hcap_uv : 0 < G.c u v
  · exact Or.inr (Or.inl hcap_uv)
  · by_cases hcap_vu : 0 < G.c v u
    · exact Or.inr (Or.inr hcap_vu)
    · left
      rw [numSaturatingPushesOn]
      rw [Finset.sum_eq_zero]
      intro i _
      by_cases hsat : (R.opFin i).saturatingPushOn u v = true
      · have hres : (R.φ i.1).residualEdge u v := by
          cases hop : R.opFin i with
          | relabel φ h w ho hres hpre =>
              simp [saturatingPushOn, hop] at hsat
          | push φ h a b ho hres hadm =>
              have hle : a = u ∧ b = v := by
                have h := of_decide_eq_true (by simpa [saturatingPushOn, hop] using hsat)
                exact ⟨h.1, h.2.1⟩
              have hbφ : φ = R.φ i.1 := by
                have h : (R.opFin i).beforeφ = R.φ i.1 := R.hop_beforeφ i.1 (Fin.isLt i)
                simpa [BasicOp.beforeφ, hop] using h
              rcases hle with ⟨ha, hb⟩
              subst a; subst b
              simpa [hbφ] using hres
        have hc_uv_nonneg : 0 ≤ G.c u v := G.hc_nonneg u v
        have hc_vu_nonneg : 0 ≤ G.c v u := G.hc_nonneg v u
        have hc_uv_zero : G.c u v = 0 := le_antisymm (le_of_not_gt hcap_uv) hc_uv_nonneg
        have hc_vu_zero : G.c v u = 0 := le_antisymm (le_of_not_gt hcap_vu) hc_vu_nonneg
        have hcap_vu : (R.φ i.1).f v u ≤ G.c v u := (R.φ i.1).hcapacity v u
        have hskew : (R.φ i.1).f u v = -((R.φ i.1).f v u) := (R.φ i.1).hskew_symm u v
        unfold Preflow.residualEdge Preflow.residualCapacity at hres
        linarith
      · simp [hsat]

/-- The sum of `f` over `univ`, restricted by membership in `s`, equals the sum
over `s`. -/
private lemma sum_filter_univ_eq {s : Finset (V × V)} {f : V × V → ℕ} :
    (∑ x : V × V, (if x ∈ s then f x else 0)) = ∑ x ∈ s, f x := by
  classical
  have hfilter : (Finset.univ : Finset (V × V)).filter (fun x => x ∈ s) = s := by
    ext x
    simp
  simpa [hfilter] using (Finset.sum_filter (fun x => x ∈ s) f).symm

/-- The sum of `f` over `univ`, restricted by swapped membership in `s`, equals
the sum of `f ∘ swap` over `s`. -/
private lemma sum_filter_univ_swap_eq {s : Finset (V × V)} {f : V × V → ℕ} :
    (∑ x : V × V, (if x.swap ∈ s then f x else 0)) = ∑ x ∈ s, f x.swap := by
  classical
  have hfilter : (Finset.univ : Finset (V × V)).filter (fun x => x ∈ s) = s := by
    ext x
    simp
  have h1 : (∑ x : V × V, (if x.swap ∈ s then f x else 0)) =
      ∑ x : V × V, (if x ∈ s then f x.swap else 0) := by
    exact Equiv.sum_comp (Equiv.prodComm (α := V) (β := V)) (fun x => (if x ∈ s then f x.swap else 0))
  have h2 : (∑ x : V × V, (if x ∈ s then f x.swap else 0)) = ∑ x ∈ s, f x.swap := by
    simpa [hfilter] using (Finset.sum_filter (fun x => x ∈ s) (fun x => f x.swap)).symm
  rw [h1, h2]

/-- The total number of saturating pushes is at most `4|V|·|E|`. -/
theorem saturating_push_count_bound (R : Run V G n) :
    numSaturatingPushes R ≤ 4 * Fintype.card V * numEdges G := by
  classical
  have hsum : numSaturatingPushes R = ∑ e : V × V, numSaturatingPushesOn R e.1 e.2 := by
    calc
      numSaturatingPushes R = ∑ i : Fin n, (if (R.opFin i).isSaturatingPush then 1 else 0) := rfl
      _ = ∑ i : Fin n, ∑ e : V × V, (if (R.opFin i).saturatingPushOn e.1 e.2 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (BasicOp.sum_saturatingPushOn_eq (R.opFin i)).symm
      _ = ∑ e : V × V, ∑ i : Fin n, (if (R.opFin i).saturatingPushOn e.1 e.2 then 1 else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ e : V × V, numSaturatingPushesOn R e.1 e.2 := rfl
  have hle : (∑ e : V × V, numSaturatingPushesOn R e.1 e.2) ≤
      (∑ e ∈ edgeSet G, numSaturatingPushesOn R e.1 e.2) +
        (∑ e ∈ edgeSet G, numSaturatingPushesOn R e.2 e.1) := by
    calc
      (∑ e : V × V, numSaturatingPushesOn R e.1 e.2) ≤
          ∑ e : V × V, ((if e ∈ edgeSet G then numSaturatingPushesOn R e.1 e.2 else 0) +
            (if e.swap ∈ edgeSet G then numSaturatingPushesOn R e.1 e.2 else 0)) := by
        apply Finset.sum_le_sum
        intro e _
        have h := saturating_pushOn_imp_cap R e.1 e.2
        cases h with
        | inl hz => simp [hz]
        | inr hcap =>
            cases hcap with
            | inl h_uv =>
                have he : e ∈ edgeSet G := Finset.mem_filter.mpr ⟨Finset.mem_univ e, h_uv⟩
                simp [he]
            | inr h_vu =>
                have he : e.swap ∈ edgeSet G := Finset.mem_filter.mpr ⟨Finset.mem_univ e.swap, h_vu⟩
                simp [he]
      _ = (∑ e ∈ edgeSet G, numSaturatingPushesOn R e.1 e.2) +
          (∑ e ∈ edgeSet G, numSaturatingPushesOn R e.2 e.1) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · exact sum_filter_univ_eq
        · exact sum_filter_univ_swap_eq
  calc
    numSaturatingPushes R = ∑ e : V × V, numSaturatingPushesOn R e.1 e.2 := hsum
    _ ≤ (∑ e ∈ edgeSet G, numSaturatingPushesOn R e.1 e.2) +
        (∑ e ∈ edgeSet G, numSaturatingPushesOn R e.2 e.1) := hle
    _ ≤ (∑ e ∈ edgeSet G, (2 * Fintype.card V)) +
        (∑ e ∈ edgeSet G, (2 * Fintype.card V)) := by
        apply Nat.add_le_add
        · apply Finset.sum_le_sum
          intro e _
          exact saturating_push_count_bound_on R e.1 e.2
        · apply Finset.sum_le_sum
          intro e _
          exact saturating_push_count_bound_on R e.2 e.1
    _ = 4 * Fintype.card V * numEdges G := by
      rw [numEdges, edgeSet]
      simp only [Finset.sum_const, nsmul_eq_mul]
      nlinarith

/-! ## Potential and nonsaturating push count bound -/

/-- The set of overflowing vertices of a preflow. -/
noncomputable def overflowSet (φ : Preflow V G) : Finset V :=
  (Finset.univ : Finset V).filter (fun u => φ.isOverflowing u)

/-- The potential `Φ = Σ_{overflowing u} h(u)`. -/
noncomputable def potential (φ : Preflow V G) (h : V → ℕ) : ℕ :=
  ∑ u ∈ overflowSet φ, h u

/-- Sum of the single-edge skew update over the first argument. -/
private lemma edgeDelta_sum_first' (δ : ℝ) (u v a : V) :
    (Finset.univ : Finset V).sum (fun x => Flow.edgeDelta δ u v x a) =
      (if a = v then δ else 0) - (if a = u then δ else 0) := by
  unfold Flow.edgeDelta
  rw [Finset.sum_sub_distrib]
  have hf : (Finset.univ : Finset V).sum (fun x => if x = u ∧ a = v then δ else 0) =
      (if a = v then δ else 0) := by
    by_cases hav : a = v
    · subst a; simp
    · simp [hav]
  have hg : (Finset.univ : Finset V).sum (fun x => if x = v ∧ a = u then δ else 0) =
      (if a = u then δ else 0) := by
    by_cases hau : a = u
    · subst a; simp
    · simp [hau]
  rw [hf, hg]

/-- Telescoping: `∑ i in range n, (f (i+1) - f i) = f n - f 0`. -/
private lemma sum_range_sub_eq (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The potential is bounded by `2|V|²`. -/
lemma potential_le (φ : Preflow V G) (h : V → ℕ) (hvalid : IsValidHeight φ h) :
    potential φ h ≤ 2 * Fintype.card V * Fintype.card V := by
  calc
    potential φ h = ∑ u ∈ overflowSet φ, h u := rfl
    _ ≤ ∑ u ∈ overflowSet φ, (2 * Fintype.card V) := by
      apply Finset.sum_le_sum
      intro u hu
      have hoverflow : φ.isOverflowing u := (Finset.mem_filter.mp hu).2
      have hle : h u ≤ 2 * Fintype.card V - 1 :=
        height_le_of_overflowing φ h hvalid u hoverflow.1 hoverflow.2.2
      omega
    _ = (overflowSet φ).card * (2 * Fintype.card V) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card V * (2 * Fintype.card V) := by
      exact Nat.mul_le_mul_right (2 * Fintype.card V) (Finset.card_le_univ (overflowSet φ))
    _ = 2 * Fintype.card V * Fintype.card V := by rw [mul_comm]

/-- The exact change of the potential under a relabel. -/
private lemma potential_relabel_eq (φ : Preflow V G) (h : V → ℕ) (u : V)
    (hres : ∃ v : V, φ.residualEdge u v) (hoverflow : φ.isOverflowing u) :
    ((potential φ (relabel φ h u hres) : ℤ) - (potential φ h : ℤ)) =
      ((relabel φ h u hres u : ℕ) : ℤ) - (h u : ℤ) := by
  unfold potential overflowSet
  rw [Nat.cast_sum, Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single u]
  · intro b hb hbu
    rw [relabel_eq_of_ne φ h u hres hbu]
    simp
  · intro hu
    have : u ∈ (Finset.univ : Finset V).filter (fun u => φ.isOverflowing u) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ u, hoverflow⟩
    exact (hu this).elim

/-- A push increases the potential by at most `2|V|`. -/
lemma potential_push_le (φ : Preflow V G) (h : V → ℕ) (u v : V) (hu_ne_s : u ≠ G.s)
    (hres : φ.residualEdge u v) (hadm : h u = h v + 1) (hvalid : IsValidHeight φ h)
    (hoverflow : φ.isOverflowing u) :
    ((potential (push φ u v hu_ne_s hres) h : ℤ) - (potential φ h : ℤ)) ≤ 2 * Fintype.card V := by
  let φ' := push φ u v hu_ne_s hres
  have hsubset : overflowSet φ' ⊆ overflowSet φ ∪ {v} := by
    intro a ha
    have ha' : φ'.isOverflowing a := (Finset.mem_filter.mp ha).2
    by_cases hav : a = v
    · rw [Finset.mem_union]
      right
      simpa [hav]
    · rw [Finset.mem_union]
      left
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ a
      · have hne_s : a ≠ G.s := ha'.1
        have hne_t : a ≠ G.t := ha'.2.1
        have hpos' : 0 < φ'.excess a := ha'.2.2
        have hle_excess : φ'.excess a ≤ φ.excess a := by
          unfold φ' push pushBy Preflow.excess netInflow
          rw [Finset.sum_add_distrib]
          rw [edgeDelta_sum_first' (min (∑ w : V, φ.f w u) (φ.residualCapacity u v)) u v a]
          have hno_add : (if a = v then min (∑ w : V, φ.f w u) (φ.residualCapacity u v) else 0) = 0 := by
            simp [hav]
          rw [hno_add]
          have hnonneg : 0 ≤ (if a = u then min (∑ w : V, φ.f w u) (φ.residualCapacity u v) else 0) := by
            split
            · exact le_min (φ.hexcess_nonneg u hu_ne_s) (le_of_lt hres)
            · simp
          linarith
        exact ⟨hne_s, hne_t, lt_of_lt_of_le hpos' hle_excess⟩
  have hdiff_le : ((potential φ' h : ℤ) - (potential φ h : ℤ)) ≤ (h v : ℤ) := by
    unfold potential
    have hsum_le : (∑ x ∈ overflowSet φ', h x) ≤ (∑ x ∈ overflowSet φ, h x) + h v := by
      have hle_subset : (∑ x ∈ overflowSet φ', h x) ≤ ∑ x ∈ overflowSet φ ∪ {v}, h x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
      have hle_union : (∑ x ∈ overflowSet φ ∪ {v}, h x) ≤ (∑ x ∈ overflowSet φ, h x) + h v := by
        have hdecomp : (∑ x ∈ overflowSet φ ∪ {v}, h x) =
            (∑ x ∈ overflowSet φ, h x) + (∑ x ∈ ({v} : Finset V) \ overflowSet φ, h x) := by
          rw [show overflowSet φ ∪ {v} = overflowSet φ ∪ (({v} : Finset V) \ overflowSet φ) by
            ext x
            by_cases hx : x ∈ overflowSet φ <;> simp [hx]]
          rw [Finset.sum_union]
          exact Finset.disjoint_sdiff
        have hle_singleton : (∑ x ∈ ({v} : Finset V) \ overflowSet φ, h x) ≤ h v := by
          have hsub : (∑ x ∈ ({v} : Finset V) \ overflowSet φ, h x) ≤ ∑ x ∈ ({v} : Finset V), h x :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.zero_le _)
          simpa using hsub
        rw [hdecomp]
        exact Nat.add_le_add_left hle_singleton (∑ x ∈ overflowSet φ, h x)
      exact le_trans hle_subset hle_union
    have hz : ((∑ x ∈ overflowSet φ', h x : ℕ) : ℤ) ≤ ((∑ x ∈ overflowSet φ, h x : ℕ) : ℤ) + (h v : ℤ) := by
      exact_mod_cast hsum_le
    omega
  have hv_le : (h v : ℤ) ≤ 2 * Fintype.card V := by
    have hu_le : h u ≤ 2 * Fintype.card V - 1 :=
      height_le_of_overflowing φ h hvalid u hoverflow.1 hoverflow.2.2
    have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨G.s⟩
    have hadm' : (h u : ℤ) = (h v : ℤ) + 1 := by omega
    have hu_le_z : (h u : ℤ) ≤ (2 * Fintype.card V : ℤ) := by
      have h' : h u ≤ 2 * Fintype.card V := by omega
      exact_mod_cast h'
    nlinarith
  nlinarith

/-- A nonsaturating push decreases the potential by at least one. -/
lemma potential_nonsaturating_push_le (φ : Preflow V G) (h : V → ℕ) (u v : V)
    (hu_ne_s : u ≠ G.s) (hres : φ.residualEdge u v) (hadm : h u = h v + 1)
    (hoverflow : φ.isOverflowing u) (hnonsat : φ.excess u < φ.residualCapacity u v) :
    ((potential (push φ u v hu_ne_s hres) h : ℤ) - (potential φ h : ℤ)) ≤ -1 := by
  let φ' := push φ u v hu_ne_s hres
  have hu_not : ¬ φ'.isOverflowing u := by
    intro h
    have hpos : 0 < φ'.excess u := h.2.2
    have hexcess : φ'.excess u = 0 := by
      unfold φ' push pushBy Preflow.excess netInflow
      rw [Finset.sum_add_distrib]
      rw [edgeDelta_sum_first' (min (∑ w : V, φ.f w u) (φ.residualCapacity u v)) u v u]
      have hmin : min (∑ w : V, φ.f w u) (φ.residualCapacity u v) = ∑ w : V, φ.f w u := by
        apply min_eq_left
        exact le_of_lt hnonsat
      rw [hmin]
      simp [residualEdge_ne φ hres]
    linarith
  have hsubset : overflowSet φ' ⊆ (overflowSet φ \ {u}) ∪ {v} := by
    intro a ha
    have ha' : φ'.isOverflowing a := (Finset.mem_filter.mp ha).2
    by_cases hav : a = v
    · rw [Finset.mem_union]
      right
      simpa [hav]
    · rw [Finset.mem_union]
      left
      apply Finset.mem_sdiff.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ a
        · have hne_s : a ≠ G.s := ha'.1
          have hne_t : a ≠ G.t := ha'.2.1
          have hpos' : 0 < φ'.excess a := ha'.2.2
          have hle_excess : φ'.excess a ≤ φ.excess a := by
            unfold φ' push pushBy Preflow.excess netInflow
            rw [Finset.sum_add_distrib]
            rw [edgeDelta_sum_first' (min (∑ w : V, φ.f w u) (φ.residualCapacity u v)) u v a]
            have hno_add : (if a = v then min (∑ w : V, φ.f w u) (φ.residualCapacity u v) else 0) = 0 := by
              simp [hav]
            rw [hno_add]
            have hnonneg : 0 ≤ (if a = u then min (∑ w : V, φ.f w u) (φ.residualCapacity u v) else 0) := by
              split
              · exact le_min (φ.hexcess_nonneg u hu_ne_s) (le_of_lt hres)
              · simp
            linarith
          exact ⟨hne_s, hne_t, lt_of_lt_of_le hpos' hle_excess⟩
      · intro hau
        apply hu_not
        exact (Finset.mem_singleton.mp hau) ▸ ha'
  have hu_mem : u ∈ overflowSet φ := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hoverflow⟩
  have hdiff_le : ((potential φ' h : ℤ) - (potential φ h : ℤ)) ≤ -1 := by
    unfold potential
    have hsum_le : (∑ x ∈ overflowSet φ', h x) + h u ≤ (∑ x ∈ overflowSet φ, h x) + h v := by
      have hle_subset : (∑ x ∈ overflowSet φ', h x) ≤ ∑ x ∈ (overflowSet φ \ {u}) ∪ {v}, h x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
      have hle_add : (∑ x ∈ overflowSet φ', h x) + h u ≤
          (∑ x ∈ (overflowSet φ \ {u}) ∪ {v}, h x) + h u :=
        Nat.add_le_add_right hle_subset (h u)
      have hle_union : (∑ x ∈ (overflowSet φ \ {u}) ∪ {v}, h x) ≤
          (∑ x ∈ overflowSet φ \ {u}, h x) + h v := by
        have hdecomp : (∑ x ∈ (overflowSet φ \ {u}) ∪ {v}, h x) =
            (∑ x ∈ overflowSet φ \ {u}, h x) + (∑ x ∈ ({v} : Finset V) \ (overflowSet φ \ {u}), h x) := by
          rw [show (overflowSet φ \ {u}) ∪ {v} =
              (overflowSet φ \ {u}) ∪ (({v} : Finset V) \ (overflowSet φ \ {u})) by
            ext x
            by_cases hx : x ∈ overflowSet φ \ {u} <;> simp [hx]]
          rw [Finset.sum_union]
          exact Finset.disjoint_sdiff
        have hle_singleton : (∑ x ∈ ({v} : Finset V) \ (overflowSet φ \ {u}), h x) ≤ h v := by
          have hsub : (∑ x ∈ ({v} : Finset V) \ (overflowSet φ \ {u}), h x) ≤
              ∑ x ∈ ({v} : Finset V), h x :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.zero_le _)
          simpa using hsub
        rw [hdecomp]
        exact Nat.add_le_add_left hle_singleton (∑ x ∈ overflowSet φ \ {u}, h x)
      have hsum_sdiff : (∑ x ∈ overflowSet φ \ {u}, h x) + h u = ∑ x ∈ overflowSet φ, h x := by
        simpa using (Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hu_mem) :
          (∑ x ∈ overflowSet φ \ {u}, h x) + (∑ x ∈ ({u} : Finset V), h x) = ∑ x ∈ overflowSet φ, h x)
      have hle_mid : (∑ x ∈ (overflowSet φ \ {u}) ∪ {v}, h x) + h u ≤
          (∑ x ∈ overflowSet φ, h x) + h v := by
        omega
      exact le_trans hle_add hle_mid
    have hz : ((∑ x ∈ overflowSet φ', h x : ℕ) : ℤ) + (h u : ℤ) ≤
        ((∑ x ∈ overflowSet φ, h x : ℕ) : ℤ) + (h v : ℤ) := by
      exact_mod_cast hsum_le
    have hadm' : (h u : ℤ) = (h v : ℤ) + 1 := by omega
    omega
  exact hdiff_le

/-- The potential increases across a single step by at most the total height
increase plus `2|V|` times the number of saturating pushes, minus one per
nonsaturating push. -/
private lemma potential_step_bound_tight (R : Run V G n) (i : Fin n) :
    ((potential (R.φ (i.1 + 1)) (R.h (i.1 + 1)) : ℤ) - (potential (R.φ i.1) (R.h i.1) : ℤ)) ≤
      (∑ x : V, (((R.h (i.1 + 1) x : ℕ) : ℤ) - (R.h i.1 x : ℤ))) +
      (2 * Fintype.card V : ℤ) * (if (R.opFin i).isSaturatingPush then 1 else 0) -
      (if (R.opFin i).isNonsaturatingPush then 1 else 0) := by
  cases hop : R.opFin i with
  | relabel φ h u ho hres hpre =>
      have hb_φ : φ = R.φ i.1 := by
        have h' : (R.opFin i).beforeφ = R.φ i.1 := R.hop_beforeφ i.1 (Fin.isLt i)
        rw [← h']
        simp [BasicOp.beforeφ, hop]
      have hb_h : h = R.h i.1 := by
        have h' : (R.opFin i).beforeh = R.h i.1 := R.hop_beforeh i.1 (Fin.isLt i)
        rw [← h']
        simp [BasicOp.beforeh, hop]
      have hr_φ : R.φ (i.1 + 1) = R.φ i.1 := by
        have h' : (R.opFin i).resultφ = R.φ (i.1 + 1) := R.hop_resultφ i.1 (Fin.isLt i)
        rw [← h']
        simp [BasicOp.resultφ, hop, hb_φ]
      let hres' : ∃ v : V, (R.φ i.1).residualEdge u v := by simpa [hb_φ] using hres
      have hr_h : R.h (i.1 + 1) = Chapter26.relabel (R.φ i.1) (R.h i.1) u hres' := by
        have h' : (R.opFin i).resulth = R.h (i.1 + 1) := R.hop_resulth i.1 (Fin.isLt i)
        rw [← h']
        simp [BasicOp.resulth, hop, hb_φ, hb_h]
      have hdiff := potential_relabel_eq (R.φ i.1) (R.h i.1) u hres' (by simpa [hb_φ] using ho)
      have hsum_eq : (∑ w : V, (((Chapter26.relabel (R.φ i.1) (R.h i.1) u hres' w : ℕ) : ℤ) - (R.h i.1 w : ℤ))) =
          ((Chapter26.relabel (R.φ i.1) (R.h i.1) u hres' u : ℕ) : ℤ) - (R.h i.1 u : ℤ) := by
        rw [Finset.sum_eq_single u]
        · intro b _ hbu
          rw [relabel_eq_of_ne (R.φ i.1) (R.h i.1) u hres' hbu]
          simp
        · intro hu
          simp at hu
      rw [hr_φ, hr_h, hdiff, hsum_eq]
      simp [isSaturatingPush, isNonsaturatingPush, hop]
  | push φ h u v ho hres hadm =>
      have hb_φ : φ = R.φ i.1 := by
        have h' : (R.opFin i).beforeφ = R.φ i.1 := R.hop_beforeφ i.1 (Fin.isLt i)
        rw [← h']
        simp [BasicOp.beforeφ, hop]
      have hb_h : h = R.h i.1 := by
        have h' : (R.opFin i).beforeh = R.h i.1 := R.hop_beforeh i.1 (Fin.isLt i)
        rw [← h']
        simp [BasicOp.beforeh, hop]
      have hr_φ : R.φ (i.1 + 1) = Chapter26.push (R.φ i.1) u v (by simpa [hb_φ] using ho.1)
          (by simpa [hb_φ] using hres) := by
        have h' : (R.opFin i).resultφ = R.φ (i.1 + 1) := R.hop_resultφ i.1 (Fin.isLt i)
        rw [← h']
        simp [BasicOp.resultφ, hop, hb_φ]
      have hr_h : R.h (i.1 + 1) = R.h i.1 := by
        have h' : (R.opFin i).resulth = R.h (i.1 + 1) := R.hop_resulth i.1 (Fin.isLt i)
        rw [← h']
        simp [BasicOp.resulth, hop, hb_h]
      have hsum_zero : (∑ w : V, (((R.h i.1 w : ℕ) : ℤ) - (R.h i.1 w : ℤ))) = 0 := by
        simp
      by_cases hsat : φ.residualCapacity u v ≤ φ.excess u
      · have hle := potential_push_le (R.φ i.1) (R.h i.1) u v (by simpa [hb_φ] using ho.1)
            (by simpa [hb_φ] using hres) (by simpa [hb_h] using hadm) (R.hvalid i.1)
            (by simpa [hb_φ] using ho)
        have hnot_lt : ¬ φ.excess u < φ.residualCapacity u v := not_lt_of_ge hsat
        rw [hr_φ, hr_h, hsum_zero]
        simp [isSaturatingPush, isNonsaturatingPush, hop, hsat, hnot_lt]
        nlinarith [hle]
      · have hlt : φ.excess u < φ.residualCapacity u v := lt_of_not_ge hsat
        have hle := potential_nonsaturating_push_le (R.φ i.1) (R.h i.1) u v (by simpa [hb_φ] using ho.1)
            (by simpa [hb_φ] using hres) (by simpa [hb_h] using hadm) (by simpa [hb_φ] using ho)
            (by simpa [hb_φ] using hlt)
        rw [hr_φ, hr_h, hsum_zero]
        simp [isSaturatingPush, isNonsaturatingPush, hop, hsat, hlt]
        nlinarith [hle]

/-- The total height increase across a run is at most `2|V|` per vertex. -/
private lemma height_le_add_bound : ∀ (n : ℕ) (R : Run V G n) (u : V),
    R.h n u ≤ R.h 0 u + 2 * Fintype.card V := by
  intro n
  induction n with
  | zero =>
      intro R u
      omega
  | succ m ih =>
      intro R u
      let R' : Run V G m := {
        φ := R.φ
        h := R.h
        hvalid := R.hvalid
        op := fun i hi => R.op i (Nat.lt_trans hi (Nat.lt_succ_self m))
        hop_beforeφ := fun i hi => R.hop_beforeφ i (Nat.lt_trans hi (Nat.lt_succ_self m))
        hop_beforeh := fun i hi => R.hop_beforeh i (Nat.lt_trans hi (Nat.lt_succ_self m))
        hop_resultφ := fun i hi => R.hop_resultφ i (Nat.lt_trans hi (Nat.lt_succ_self m))
        hop_resulth := fun i hi => R.hop_resulth i (Nat.lt_trans hi (Nat.lt_succ_self m)) }
      have hb := ih R' u
      change R.h m u ≤ R.h 0 u + 2 * Fintype.card V at hb
      cases hop : R.op m (Nat.lt_succ_self m) with
      | relabel φ h w ho hres hpre =>
          by_cases hwu : w = u
          · subst u
            have hoverflow : (R.φ (m + 1)).isOverflowing w := by
              have hrφ : R.φ (m + 1) = φ := by
                simpa [BasicOp.resultφ, hop] using
                  (R.hop_resultφ m (Nat.lt_succ_self m)).symm
              rw [hrφ]
              exact ho
            have hle' := height_le_of_overflowing (R.φ (m + 1)) (R.h (m + 1)) (R.hvalid (m + 1)) w
              hoverflow.1 hoverflow.2.2
            omega
          · have hstep : R.h (m + 1) u = R.h m u := by
              rw [← R.hop_resulth m (Nat.lt_succ_self m), ← R.hop_beforeh m (Nat.lt_succ_self m)]
              simp [BasicOp.resulth, BasicOp.beforeh, hop, relabel_eq_of_ne φ h w hres (Ne.symm hwu)]
            omega
      | push φ h a b ho hres hadm =>
          have hstep : R.h (m + 1) u = R.h m u := by
            rw [← R.hop_resulth m (Nat.lt_succ_self m), ← R.hop_beforeh m (Nat.lt_succ_self m)]
            simp [BasicOp.resulth, BasicOp.beforeh, hop]
          omega

/-- The potential telescopes over a run. -/
private lemma potential_telescope (R : Run V G n) :
    ((potential (R.φ n) (R.h n) : ℤ) = (potential (R.φ 0) (R.h 0) : ℤ) +
      ∑ i ∈ Finset.range n, (((potential (R.φ (i + 1)) (R.h (i + 1)) : ℤ) -
        (potential (R.φ i) (R.h i) : ℤ)))) := by
  have h := sum_range_sub_eq (fun i => (potential (R.φ i) (R.h i) : ℤ)) n
  omega

/-- The total number of nonsaturating pushes is bounded by `O(|V|²(|V|+|E|))`. -/
theorem nonsaturating_push_count_bound (R : Run V G n) :
    numNonsaturatingPushes R ≤ 12 * Fintype.card V * Fintype.card V * (Fintype.card V + numEdges G) := by
  classical
  let Vc := Fintype.card V
  have htel := potential_telescope R
  have hnonneg : 0 ≤ (potential (R.φ n) (R.h n) : ℤ) := by
    exact Int.natCast_nonneg (potential (R.φ n) (R.h n))
  have hinit_ℕ : potential (R.φ 0) (R.h 0) ≤ 2 * Vc * Vc := by
    exact potential_le (R.φ 0) (R.h 0) (R.hvalid 0)
  have hrel_inc_ℕ : (∑ u : V, (R.h n u - R.h 0 u)) ≤ 2 * Vc * Vc := by
    have hbound : ∀ u, R.h n u - R.h 0 u ≤ 2 * Fintype.card V := by
      intro u
      have h : R.h n u ≤ R.h 0 u + 2 * Fintype.card V := height_le_add_bound n R u
      omega
    calc
      (∑ u : V, (R.h n u - R.h 0 u)) ≤ ∑ u : V, (2 * Fintype.card V) := by
        apply Finset.sum_le_sum
        intro u _
        exact hbound u
      _ = Fintype.card V * (2 * Fintype.card V) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = 2 * Vc * Vc := by dsimp [Vc]; rw [mul_comm]
  have hsum_le : (∑ i ∈ Finset.range n,
      (((potential (R.φ (i + 1)) (R.h (i + 1)) : ℤ) - (potential (R.φ i) (R.h i) : ℤ)))) ≤
      (∑ u : V, (((R.h n u : ℕ) : ℤ) - (R.h 0 u : ℤ))) +
        (2 * Vc : ℤ) * (numSaturatingPushes R : ℤ) -
        (numNonsaturatingPushes R : ℤ) := by
    have hfin : (∑ i : Fin n,
        ((potential (R.φ (i.1 + 1)) (R.h (i.1 + 1)) : ℤ) - (potential (R.φ i.1) (R.h i.1) : ℤ))) ≤
        (∑ u : V, (((R.h n u : ℕ) : ℤ) - (R.h 0 u : ℤ))) +
          (2 * Vc : ℤ) * (numSaturatingPushes R : ℤ) -
          (numNonsaturatingPushes R : ℤ) := by
      calc
        (∑ i : Fin n,
          ((potential (R.φ (i.1 + 1)) (R.h (i.1 + 1)) : ℤ) - (potential (R.φ i.1) (R.h i.1) : ℤ))) ≤
          ∑ i : Fin n, ((∑ u : V, (((R.h (i.1 + 1) u : ℕ) : ℤ) - (R.h i.1 u : ℤ))) +
            (2 * Vc : ℤ) * (if (R.opFin i).isSaturatingPush then 1 else 0) -
            (if (R.opFin i).isNonsaturatingPush then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro i _
            exact potential_step_bound_tight R i
        _ = (∑ u : V, (((R.h n u : ℕ) : ℤ) - (R.h 0 u : ℤ))) +
            (2 * Vc : ℤ) * (∑ i : Fin n, (if (R.opFin i).isSaturatingPush then 1 else 0)) -
            (∑ i : Fin n, (if (R.opFin i).isNonsaturatingPush then 1 else 0)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            congr 1
            congr 1
            · rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro u _
              have htel_u := sum_range_sub_eq (fun i => (R.h i u : ℤ)) n
              rw [Finset.sum_fin_eq_sum_range]
              exact (Finset.sum_congr rfl (fun x hx => by
                simp [Finset.mem_range.mp hx])).trans htel_u
            · rw [← Finset.mul_sum]
        _ = (∑ u : V, (((R.h n u : ℕ) : ℤ) - (R.h 0 u : ℤ))) +
            (2 * Vc : ℤ) * (numSaturatingPushes R : ℤ) -
            (numNonsaturatingPushes R : ℤ) := by
            simp [numSaturatingPushes, numNonsaturatingPushes]
    have hfin' : (∑ i ∈ Finset.range n,
        ((potential (R.φ (i + 1)) (R.h (i + 1)) : ℤ) - (potential (R.φ i) (R.h i) : ℤ))) =
        (∑ i : Fin n,
          ((potential (R.φ (i.1 + 1)) (R.h (i.1 + 1)) : ℤ) - (potential (R.φ i.1) (R.h i.1) : ℤ))) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_range.mp hi]
    rw [hfin']
    exact hfin
  have hsum_cast : (∑ u : V, (((R.h n u : ℕ) : ℤ) - (R.h 0 u : ℤ))) =
      ((∑ u : V, (R.h n u - R.h 0 u) : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro u _
    have hmono : R.h 0 u ≤ R.h n u := height_mono R (Nat.zero_le n) (Nat.le_refl n) u
    exact (Int.ofNat_sub hmono).symm
  have hmain_ℤ : (numNonsaturatingPushes R : ℤ) ≤
      (potential (R.φ 0) (R.h 0) : ℤ) +
        (∑ u : V, (((R.h n u : ℕ) : ℤ) - (R.h 0 u : ℤ))) +
        (2 * Vc : ℤ) * (numSaturatingPushes R : ℤ) := by
    have hsum' := hsum_le
    have : (potential (R.φ 0) (R.h 0) : ℤ) + (∑ i ∈ Finset.range n,
        ((potential (R.φ (i + 1)) (R.h (i + 1)) : ℤ) - (potential (R.φ i) (R.h i) : ℤ))) ≥ 0 := by
      simpa [htel] using hnonneg
    omega
  have hmain_ℕ : numNonsaturatingPushes R ≤ 2 * Vc * Vc + (∑ u : V, (R.h n u - R.h 0 u)) +
      2 * Vc * numSaturatingPushes R := by
    have hinit_z : (potential (R.φ 0) (R.h 0) : ℤ) ≤ ((2 * Vc * Vc : ℕ) : ℤ) := by
      exact_mod_cast hinit_ℕ
    have hz : (numNonsaturatingPushes R : ℤ) ≤
        ((2 * Vc * Vc + (∑ u : V, (R.h n u - R.h 0 u)) + 2 * Vc * numSaturatingPushes R : ℕ) : ℤ) := by
      rw [hsum_cast] at hmain_ℤ
      have hcast : ((2 * Vc * numSaturatingPushes R : ℕ) : ℤ) = (2 * (Vc : ℤ)) * (numSaturatingPushes R : ℤ) := by
        norm_num
      have hcast_add : ((2 * Vc * Vc + (∑ u : V, (R.h n u - R.h 0 u)) + 2 * Vc * numSaturatingPushes R : ℕ) : ℤ) =
          ((2 * Vc * Vc : ℕ) : ℤ) + ((∑ u : V, (R.h n u - R.h 0 u) : ℕ) : ℤ) + ((2 * Vc * numSaturatingPushes R : ℕ) : ℤ) := by
        simp only [Nat.cast_add]
      nlinarith [hmain_ℤ, hinit_z, hcast, hcast_add]
    exact_mod_cast hz
  have hsat := saturating_push_count_bound R
  have hV : 1 ≤ Vc := Fintype.card_pos_iff.mpr ⟨G.s⟩
  dsimp [Vc] at hmain_ℕ hrel_inc_ℕ hsat ⊢
  nlinarith [hmain_ℕ, hrel_inc_ℕ, hsat, hV]

/-- Every step is exactly one of relabel, saturating push, or nonsaturating push. -/
theorem op_count_decomp (R : Run V G n) :
    n = numRelabels R + numSaturatingPushes R + numNonsaturatingPushes R := by
  have hclass : (∑ i : Fin n, (1 : ℕ)) =
      ∑ i : Fin n, ((if (R.opFin i).isRelabel then 1 else 0) +
         (if (R.opFin i).isSaturatingPush then 1 else 0) +
         (if (R.opFin i).isNonsaturatingPush then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (BasicOp.classification (R.opFin i)).symm
  calc
    n = ∑ i : Fin n, (1 : ℕ) := by simp
    _ = ∑ i : Fin n, ((if (R.opFin i).isRelabel then 1 else 0) +
           (if (R.opFin i).isSaturatingPush then 1 else 0) +
           (if (R.opFin i).isNonsaturatingPush then 1 else 0)) := hclass
    _ = numRelabels R + numSaturatingPushes R + numNonsaturatingPushes R := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp [numRelabels, numSaturatingPushes, numNonsaturatingPushes]

/-- The combined `O(V²E)` bound on the number of basic operations of the
generic push-relabel algorithm. -/
theorem generic_step_count_bound (R : Run V G n) :
    n ≤ 12 * Fintype.card V * Fintype.card V * Fintype.card V +
        12 * Fintype.card V * Fintype.card V * numEdges G +
        4 * Fintype.card V * numEdges G + 4 * Fintype.card V * Fintype.card V := by
  have hdecomp : n = numRelabels R + numSaturatingPushes R + numNonsaturatingPushes R :=
    op_count_decomp R
  rw [hdecomp]
  have hr : numRelabels R ≤ 2 * Fintype.card V * Fintype.card V := relabel_count_bound R
  have hs : numSaturatingPushes R ≤ 4 * Fintype.card V * numEdges G := saturating_push_count_bound R
  have hn : numNonsaturatingPushes R ≤ 12 * Fintype.card V * Fintype.card V *
      (Fintype.card V + numEdges G) := nonsaturating_push_count_bound R
  nlinarith

end Run
end Chapter26
end CLRS
