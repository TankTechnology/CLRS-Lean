import CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.Optimality

/-!
# 29.3 Complementary slackness

The duality gap splits exactly into primal-slack and dual-slack products.
For feasible assignments all products are nonnegative, so equality of the two
objectives is equivalent to the textbook complementary-slackness equations.
-/

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

namespace StandardLP

/-- Slack in primal constraint row {lit}`i`. -/
def primalSlack (P : StandardLP m n) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  P.b i - (P.A *ᵥ x) i

/-- Slack in dual constraint column {lit}`j`. -/
def dualSlack (P : StandardLP m n) (y : Fin m → ℝ) (j : Fin n) : ℝ :=
  (P.A.transpose *ᵥ y) j - P.c j

/-- The textbook complementary-slackness equations. -/
def ComplementarySlackness (P : StandardLP m n)
    (x : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  (∀ i, y i * P.primalSlack x i = 0) ∧
    ∀ j, x j * P.dualSlack y j = 0

/-- Exact decomposition of the duality gap into complementary-slackness
products. -/
theorem dualityGap_eq_slackSums (P : StandardLP m n)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    P.dualObjective y - P.objective x =
      (∑ i, y i * P.primalSlack x i) +
        ∑ j, x j * P.dualSlack y j := by
  simp only [dualObjective, objective, primalSlack, dualSlack]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  change P.b ⬝ᵥ y - P.c ⬝ᵥ x =
    (y ⬝ᵥ P.b - y ⬝ᵥ (P.A *ᵥ x)) +
      (x ⬝ᵥ (P.A.transpose *ᵥ y) - x ⬝ᵥ P.c)
  rw [dotProduct_comm P.b y, dotProduct_comm x (P.A.transpose *ᵥ y),
    dotProduct_comm x P.c, transpose_mulVec_dotProduct]
  ring

/-- For feasible primal and dual assignments, complementary slackness holds
exactly when their objective values agree. -/
theorem complementarySlackness_iff_objective_eq (P : StandardLP m n)
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y) :
    P.ComplementarySlackness x y ↔
      P.objective x = P.dualObjective y := by
  have hpnonneg : ∀ i, 0 ≤ y i * P.primalSlack x i := by
    intro i
    exact mul_nonneg (hy.1 i) (sub_nonneg.mpr (hx.2 i))
  have hdnonneg : ∀ j, 0 ≤ x j * P.dualSlack y j := by
    intro j
    exact mul_nonneg (hx.1 j) (sub_nonneg.mpr (hy.2 j))
  constructor
  · rintro ⟨hp, hd⟩
    have hpsum : (∑ i, y i * P.primalSlack x i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact hp i
    have hdsum : (∑ j, x j * P.dualSlack y j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact hd j
    have hgap := P.dualityGap_eq_slackSums x y
    rw [hpsum, hdsum, add_zero] at hgap
    linarith
  · intro hobj
    have hgap := P.dualityGap_eq_slackSums x y
    have htotal :
        (∑ i, y i * P.primalSlack x i) +
          ∑ j, x j * P.dualSlack y j = 0 := by
      linarith
    have hpsum_nonneg : 0 ≤ ∑ i, y i * P.primalSlack x i :=
      Finset.sum_nonneg fun i _ => hpnonneg i
    have hdsum_nonneg : 0 ≤ ∑ j, x j * P.dualSlack y j :=
      Finset.sum_nonneg fun j _ => hdnonneg j
    have hpsum : (∑ i, y i * P.primalSlack x i) = 0 := by
      linarith
    have hdsum : (∑ j, x j * P.dualSlack y j) = 0 := by
      linarith
    have hpzero : (fun i => y i * P.primalSlack x i) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg hpnonneg).mp hpsum
    have hdzero : (fun j => x j * P.dualSlack y j) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg hdnonneg).mp hdsum
    exact ⟨fun i => congrFun hpzero i, fun j => congrFun hdzero j⟩

/-- Complementary slackness certifies primal optimality. -/
theorem optimal_of_complementarySlackness (P : StandardLP m n)
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y)
    (hcs : P.ComplementarySlackness x y) : P.IsOptimal x := by
  have heq := (P.complementarySlackness_iff_objective_eq hx hy).1 hcs
  refine ⟨hx, ?_⟩
  intro z hz
  calc
    P.objective z ≤ P.dualObjective y := P.weak_duality hz hy
    _ = P.objective x := heq.symm

/-- Complementary slackness certifies dual optimality. -/
theorem dualOptimal_of_complementarySlackness (P : StandardLP m n)
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y)
    (hcs : P.ComplementarySlackness x y) : P.IsDualOptimal y := by
  have heq := (P.complementarySlackness_iff_objective_eq hx hy).1 hcs
  refine ⟨hy, ?_⟩
  intro z hz
  calc
    P.dualObjective y = P.objective x := heq.symm
    _ ≤ P.dualObjective z := P.weak_duality hx hz

end StandardLP
end Chapter29
end CLRS
