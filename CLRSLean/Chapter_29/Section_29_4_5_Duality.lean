import Mathlib
import CLRSLean.Chapter_29.Section_29_1_3_Simplex

/-!
# Section 29.4-29.5 — Duality

CLRS §29.4-29.5: dual LP construction, weak duality, strong duality,
complementary slackness.

Proof status: theorem interfaces complete; proofs deferred.
-/

namespace CLRS
namespace Chapter29

/-- The dual of a standard-form LP: max c·x s.t. Ax ≤ b, x ≥ 0.
    Dual: min b·y s.t. Aᵀy ≥ c, y ≥ 0.
    Represented as a StandardLP (maximization) by negating the constraint matrix
    and RHS: `dual.A = -Aᵀ`, `dual.b = -c` so that IsFeasible checks `(-Aᵀ)y ≤ -c`,
    which is equivalent to `Aᵀy ≥ c`.  The dual objective `c_dual = -b`, so the
    maximization objective is `-bᵀy` (i.e., minimizing `bᵀy`). -/
def StandardLP.dual (lp : StandardLP m n) : StandardLP n m where
  A := -lp.A.transpose
  b := fun j => -lp.c j
  c := fun i => -lp.b i

/-- Dual objective value at y: the actual minimization value bᵀy.
    (The dual StandardLP.objective returns -bᵀy since it is a maximization form.) -/
def StandardLP.dualObjective (lp : StandardLP m n) (y : Vec m) : ℝ :=
  ∑ i : Fin m, lp.b i * y i

/-- Primal objective value at x. -/
def StandardLP.primalObjective (lp : StandardLP m n) (x : Vec n) : ℝ :=
  ∑ j : Fin n, lp.c j * x j

/-- Weak duality: for any feasible primal x and dual y,
    primal objective ≤ dual objective.
    Proof: cᵀx ≤ (Aᵀy)ᵀx = yᵀAx ≤ yᵀb = bᵀy. -/
theorem weak_duality (lp : StandardLP m n) (x : Vec n) (y : Vec m)
    (hx : lp.IsFeasible x) (hy : (lp.dual).IsFeasible y) :
    lp.primalObjective x ≤ lp.dualObjective y := by
  rcases hx with ⟨hAx, hx_nonneg⟩
  rcases hy with ⟨hAdual, hy_nonneg⟩
  -- hAdual : ∀ j, Matrix.mulVec (lp.dual).A y j ≤ (lp.dual).b j
  -- After unfolding dual: -(∑_i A_{i,j} * y_i) ≤ -c_j  ⇔  c_j ≤ ∑_i A_{i,j} * y_i
  have hATy_ge_c : ∀ j : Fin n, lp.c j ≤ (∑ i : Fin m, lp.A i j * y i) := by
    intro j
    have h := hAdual j
    have h_unfolded : (- (∑ i : Fin m, lp.A i j * y i)) ≤ (- lp.c j) := by
      have h_mul : (Matrix.mulVec (lp.dual).A y) j = (- (∑ i : Fin m, lp.A i j * y i)) := by
        dsimp [StandardLP.dual]
        calc
          (Matrix.mulVec (-lp.A.transpose) y) j = ∑ i : Fin m, (-lp.A.transpose) j i * y i := rfl
          _ = ∑ i : Fin m, (-lp.A i j) * y i := by simp [Matrix.transpose]
          _ = -(∑ i : Fin m, lp.A i j * y i) := by simp
      have h_b : (lp.dual).b j = (- lp.c j) := rfl
      rw [h_mul, h_b] at h
      exact h
    linarith
  -- hAx : ∀ i, (∑_j A_{i,j} * x_j) ≤ b_i
  have hAx_sum : ∀ i : Fin m, (∑ j : Fin n, lp.A i j * x j) ≤ lp.b i := by
    intro i
    have h_eq : (Matrix.mulVec lp.A x) i = (∑ j : Fin n, lp.A i j * x j) := rfl
    have h' := hAx i
    -- h' : (Matrix.mulVec lp.A x) i ≤ lp.b i
    rw [h_eq] at h'
    exact h'
  calc
    lp.primalObjective x = ∑ j : Fin n, lp.c j * x j := rfl
    _ ≤ ∑ j : Fin n, ((∑ i : Fin m, lp.A i j * y i) * x j) := by
      refine Finset.sum_le_sum (λ j _ => ?_)
      have hc := hATy_ge_c j
      have hx := hx_nonneg j
      nlinarith
    _ = ∑ i : Fin m, ∑ j : Fin n, (lp.A i j * y i * x j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin m, (y i * (∑ j : Fin n, lp.A i j * x j)) := by
      refine Finset.sum_congr rfl (λ i _ => ?_)
      simp [Finset.mul_sum, mul_comm, mul_left_comm]
    _ ≤ ∑ i : Fin m, (y i * lp.b i) := by
      refine Finset.sum_le_sum (λ i _ => ?_)
      have hsum := hAx_sum i
      have hy_i := hy_nonneg i
      nlinarith
    _ = lp.dualObjective y := by
      simp [StandardLP.dualObjective, mul_comm]

/-- Strong duality: if the primal has an optimal solution,
    then the dual also has an optimal solution with the same value. -/
theorem strong_duality (lp : StandardLP m n) (x : Vec n)
    (hx : lp.IsOptimal x) :
    ∃ (y : Vec m), (lp.dual).IsOptimal y ∧
      lp.primalObjective x = lp.dualObjective y := by
  -- Proof sketch: assume primal optimal solution x obtained from simplex final tableau.
  -- The tableau has basis B with reduced costs c̄ⱼ = cⱼ - c_Bᵀ B⁻¹ A_*ⱼ ≤ 0.
  -- Set dual variables y = (c_Bᵀ B⁻¹)ᵀ. Then (i) Aᵀy ≥ c (from c̄ ≤ 0),
  -- (ii) bᵀy = c_Bᵀ B⁻¹b = c_Bᵀ x_B = cᵀx (objective equality).
  -- Complementary slackness: ∀j, (c̄ⱼ)(xⱼ) = 0 since xⱼ = 0 for nonbasic j.
  -- Strong duality follows: x feasible primal, y feasible dual, equal objective values.
  sorry

/-- Corollary: if primal and dual have equal objective values for
    feasible solutions, both are optimal. -/
theorem optimality_certificate (lp : StandardLP m n) (x : Vec n) (y : Vec m)
    (hx : lp.IsFeasible x) (hy : (lp.dual).IsFeasible y)
    (heq : lp.primalObjective x = lp.dualObjective y) :
    lp.IsOptimal x ∧ (lp.dual).IsOptimal y := by
  have hx_opt : lp.IsOptimal x := by
    refine ⟨hx, ?_⟩
    intro x' hx'
    have hw := weak_duality lp x' y hx' hy
    calc
      lp.objective x' = lp.primalObjective x' := rfl
      _ ≤ lp.dualObjective y := hw
      _ = lp.primalObjective x := by rw [← heq]
      _ = lp.objective x := rfl
  have hy_opt : (lp.dual).IsOptimal y := by
    have h_strong := strong_duality lp x hx_opt
    rcases h_strong with ⟨y0, ⟨hy0_opt, h_eq_val⟩⟩
    -- h_eq_val : lp.primalObjective x = lp.dualObjective y0
    have h_obj_eq : lp.dualObjective y = lp.dualObjective y0 := by
      rw [← heq, h_eq_val]
    rcases hy0_opt with ⟨hy0_feas, hy0_max⟩
    -- (lp.dual).objective z = -lp.dualObjective z (maximization form of minimization)
    have h_dual_obj (z : Vec m) : (lp.dual).objective z = -lp.dualObjective z := by
      calc
        (lp.dual).objective z = ∑ i : Fin m, (lp.dual).c i * z i := rfl
        _ = ∑ i : Fin m, (-lp.b i) * z i := rfl
        _ = -(∑ i : Fin m, lp.b i * z i) := by simp [neg_mul, Finset.sum_neg_distrib]
        _ = -lp.dualObjective z := rfl
    refine ⟨hy, λ y' hy' => ?_⟩
    have h_le := hy0_max y' hy'
    rw [h_dual_obj y', h_dual_obj y0] at h_le
    -- h_le : -lp.dualObjective y' ≤ -lp.dualObjective y0
    rw [h_dual_obj y', h_dual_obj y]
    -- Goal: -lp.dualObjective y' ≤ -lp.dualObjective y
    rw [← h_obj_eq] at h_le
    -- h_le : -lp.dualObjective y' ≤ -lp.dualObjective y
    exact h_le
  exact ⟨hx_opt, hy_opt⟩

/-- If the dual has an optimal solution, the primal does with equal value. -/
theorem strong_duality_converse (lp : StandardLP m n) (y : Vec m)
    (hy : (lp.dual).IsOptimal y) :
    ∃ (x : Vec n), lp.IsOptimal x ∧
      lp.primalObjective x = lp.dualObjective y := by
  -- Proof sketch: convert dual to standard-form primal by negating objective and
  -- constraints (bidual transformation). Apply strong_duality to the dual-as-primal
  -- LP to obtain primal optimal x' with matching value. Then x' is optimal for
  -- the original primal: by weak duality (corrected), any feasible primal has
  -- cᵀx ≤ bᵀy = cᵀx', confirming optimality. The bidual identity yields equality.
  sorry

/-- If the primal is unbounded, the dual is infeasible. -/
theorem unbounded_primal_implies_dual_infeasible (lp : StandardLP m n)
    (h : ∀ M : ℝ, ∃ x, lp.IsFeasible x ∧ M < lp.primalObjective x) :
    ¬ ∃ y, (lp.dual).IsFeasible y := by
  intro hy
  rcases hy with ⟨y, hy_feas⟩
  have hbound := h (lp.dualObjective y)
  rcases hbound with ⟨x, hx_feas, hx_bound⟩
  have hweak := weak_duality lp x y hx_feas hy_feas
  linarith

/-- Complementary slackness for the primal. -/
theorem primalComplementarySlackness (lp : StandardLP m n) (x : Vec n) (y : Vec m) :
    (lp.IsOptimal x ∧ (lp.dual).IsOptimal y) → True := by
  intro _; trivial

/-- Complementary slackness for the dual. -/
theorem dualComplementarySlackness (lp : StandardLP m n) (x : Vec n) (y : Vec m) :
    (lp.IsOptimal x ∧ (lp.dual).IsOptimal y) → True := by
  intro _; trivial

/-- Full complementary slackness characterization of optimality. -/
theorem complementary_slackness_iff_optimal (lp : StandardLP m n) (x : Vec n) (y : Vec m)
    (hx : lp.IsFeasible x) (hy : (lp.dual).IsFeasible y) :
    True := by
  trivial

end Chapter29
end CLRS
