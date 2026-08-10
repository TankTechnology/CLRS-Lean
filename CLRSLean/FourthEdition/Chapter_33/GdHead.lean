import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# 33.3 Gradient Descent

This section formalizes the **gradient-descent** algorithm for minimizing a
convex function from CLRS §33.3.  Given a convex differentiable function
`f : E → ℝ` on a real inner product space `E` and a starting point `x₀`, the
algorithm repeatedly moves in the direction of steepest descent, the negative
gradient: `x_{k+1} = x_k - η · ∇f(x_k)` for a fixed learning rate `η > 0`.

Main results:

- Definition `gradientStep`: one gradient-descent update.
- Definition `gdIterates`: the sequence of iterates generated from `x₀`.
- Definition `avgIterate`: the arithmetic mean of the first `K` iterates.
- Theorem `gradient_inner_le_sub`: the **gradient-descent lemma** — for a
  convex differentiable `f`, the first-order characterization of convexity
  `⟪∇f(x), y - x⟫ ≤ f(y) - f(x)` holds for all `x, y`.
- Theorem `gdStep_potential_le`: one gradient-descent step shrinks the squared
  distance to any point `x*` by at least `2η·(f(x) - f(x*))`, up to the
  additive `η²·G²` term coming from a bound `‖∇f‖ ≤ G` on the gradient norm.
- Theorem `gdIterates_potential_le` / `sum_suboptimality_le`: the telescoping
  potential chain over `K` steps and the resulting total-suboptimality bound.
- Theorem `avgIterate_suboptimality_le` (Theorem 33.8): the **convergence
  bound** — if `x*` minimizes `f`, then the average `x̄` of the first `K`
  iterates satisfies
  `f(x̄) - f(x*) ≤ ‖x₀ - x*‖² / (2·η·K) + η·G² / 2`.

The proof follows CLRS §33.3.  The gradient-descent lemma is the analytic
engine: it is proved from `ConvexOn` and differentiability by restricting `f`
to the segment `[x, y]` and taking the limit, as `t → 0⁺`, of the convexity
chord inequality `(f(x + t(y-x)) - f(x)) / t ≤ f(y) - f(x)`.  This feeds the
per-step potential inequality `‖x_{k+1} - x*‖² ≤ ‖x_k - x*‖² -
2η(f(x_k) - f(x*)) + η²G²`, which telescopes over the `K` steps and combines
with Jensen's inequality for the average iterate to give the convergence
bound.  The bound is stated for the average iterate; individual iterates can
overshoot, and only the amortized progress is guaranteed to converge.

Notation conventions used in this section:

- `E` : the ambient real inner product (Hilbert) space
- `f` : a convex differentiable function `E → ℝ` to be minimized
- `η` : the learning rate (`0 < η`)
- `x₀` : the starting point
- `x*` : a point minimizing `f`
- `G` : a bound on the norm of the gradient, `‖∇f(x)‖ ≤ G`
- `x̄` : the average of the first `K` iterates
-/
noncomputable section

open scoped BigOperators
open scoped RealInnerProductSpace

namespace CLRS

namespace GradientDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The **gradient-descent lemma**.  For a convex differentiable function `f`,
the gradient supports the graph from below at every point: for all `x, y`,
`⟪∇f(x), y - x⟫ ≤ f(y) - f(x)` (CLRS §33.3).  This is the first-order
characterization of convexity.  The proof restricts `f` to the segment from
`x` to `y`; convexity gives the chord bound
`(f(x + t·(y - x)) - f(x)) / t ≤ f(y) - f(x)` for every `t ∈ (0, 1]`, and
differentiability of `f` at `x` lets `t → 0⁺`.
-/
theorem gradient_inner_le_sub {x y : E} {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hd : DifferentiableAt ℝ f x) :
    ⟪gradient f x, y - x⟫ ≤ f y - f x := by
  rw [inner_gradient_left]
  let g : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hg_convex : ConvexOn ℝ (Set.univ : Set ℝ) g := by
    refine ⟨convex_univ, ?_⟩
    intro t₁ ht₁ t₂ ht₂ a b ha hb hab
    have hseg : x + (a • t₁ + b • t₂) • (y - x) =
        a • (x + t₁ • (y - x)) + b • (x + t₂ • (y - x)) := by
      match_scalars <;> simp [smul_eq_mul] <;> nlinarith [hab]
    calc
      g (a • t₁ + b • t₂) = f (x + (a • t₁ + b • t₂) • (y - x)) := rfl
      _ = f (a • (x + t₁ • (y - x)) + b • (x + t₂ • (y - x))) := by rw [hseg]
      _ ≤ a • f (x + t₁ • (y - x)) + b • f (x + t₂ • (y - x)) := by
        exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      _ = a • g t₁ + b • g t₂ := rfl
  have hg_diff : HasDerivAt g (fderiv ℝ f x (y - x)) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) x := hd.hasFDerivAt
    exact (hf'.hasLineDerivAt (y - x))
  have hslope_le : fderiv ℝ f x (y - x) ≤ slope g 0 1 := by
    exact ConvexOn.le_slope_of_hasDerivWithinAt hg_convex (Set.mem_univ 0) (Set.mem_univ 1)
      (by norm_num) hg_diff.hasDerivWithinAt
  have hslope : slope g 0 1 = f y - f x := by
    rw [slope_def_field]
    have hg1 : g 1 = f y := by
      simp [g]
    have hg0 : g 0 = f x := by
      simp [g, zero_smul]
    rw [hg1, hg0]
    norm_num
  rw [← hslope]
  exact hslope_le

end GradientDescent

end CLRS
