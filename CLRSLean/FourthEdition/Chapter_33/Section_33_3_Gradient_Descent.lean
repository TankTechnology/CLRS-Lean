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
    (hf : ConvexOn ℝ Set.univ f) (hd : DifferentiableAt ℝ f x) :
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
        have hx : x + t₁ • (y - x) ∈ (Set.univ : Set E) := by simp
        have hy : x + t₂ • (y - x) ∈ (Set.univ : Set E) := by simp
        exact hf.2 hx hy ha hb hab
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

/--
One **gradient-descent step**: `x ↦ x - η·∇f(x)`, moving from `x` in the
direction of steepest descent (the negative gradient) with learning rate `η`
(CLRS §33.3).
-/
def gradientStep (η : ℝ) (x : E) (f : E → ℝ) : E :=
  x - η • gradient f x

/--
The **sequence of gradient-descent iterates** generated from `x₀`:
`x_{k+1} = x_k - η·∇f(x_k)` (CLRS §33.3).
-/
def gdIterates (η : ℝ) (x₀ : E) (f : E → ℝ) : ℕ → E
  | 0 => x₀
  | k + 1 => gradientStep η (gdIterates η x₀ f k) f

/--
The **average iterate** `x̄` after `K` steps: the arithmetic mean of the first
`K` iterates `x₀, ..., x_{K-1}` (CLRS §33.3).  For `K = 0` the junk value `0`
is returned, since `(0 : ℝ)⁻¹ = 0`.
-/
def avgIterate (η : ℝ) (x₀ : E) (f : E → ℝ) (K : ℕ) : E :=
  (K : ℝ)⁻¹ • ∑ k ∈ Finset.range K, gdIterates η x₀ f k

/--
**Per-step potential bound.**  One gradient-descent step from `x` shrinks the
squared distance to any point `x*` by at least `2·η·(f x - f x*)`, up to the
additive `η²·G²` term:

`‖gradientStep η x f - x*‖² ≤ ‖x - x*‖² - 2·η·(f x - f x*) + η²·G²`,

where `G` bounds the gradient norm at `x`.  This is the engine of the
convergence analysis: each step makes progress proportional to the current
suboptimality, minus a small error term (CLRS §33.3).
-/
lemma gdStep_potential_le {x xstar : E} {η G : ℝ} {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : DifferentiableAt ℝ f x) (hη : 0 ≤ η)
    (hG : ‖gradient f x‖ ≤ G) :
    ‖gradientStep η x f - xstar‖ ^ 2 ≤ ‖x - xstar‖ ^ 2 - 2 * η * (f x - f xstar) + η ^ 2 * G ^ 2 := by
  have hg : f x - f xstar ≤ ⟪gradient f x, x - xstar⟫ := by
    have hle := gradient_inner_le_sub (x := x) (y := xstar) hf hd
    have hrewrite : ⟪gradient f x, x - xstar⟫ = -⟪gradient f x, xstar - x⟫ := by
      rw [inner_sub_right]
      rw [inner_sub_right]
      ring
    rw [hrewrite]
    linarith
  have hgnorm : ‖gradient f x‖ ^ 2 ≤ G ^ 2 := by
    nlinarith [hG, norm_nonneg (gradient f x)]
  calc
    ‖gradientStep η x f - xstar‖ ^ 2 = ‖(x - xstar) - η • gradient f x‖ ^ 2 := by
      rw [gradientStep]
      congr 1
      abel
    _ = ‖x - xstar‖ ^ 2 - 2 * ⟪η • gradient f x, x - xstar⟫ + ‖η • gradient f x‖ ^ 2 := by
      rw [norm_sub_sq (𝕜 := ℝ)]
      simp [real_inner_smul_left, real_inner_comm]
    _ = ‖x - xstar‖ ^ 2 - 2 * η * ⟪gradient f x, x - xstar⟫ + ‖η • gradient f x‖ ^ 2 := by
      rw [real_inner_smul_left]
      ring
    _ ≤ ‖x - xstar‖ ^ 2 - 2 * η * (f x - f xstar) + ‖η • gradient f x‖ ^ 2 := by
      have hinner : 2 * η * (f x - f xstar) ≤ 2 * η * ⟪gradient f x, x - xstar⟫ := by
        exact mul_le_mul_of_nonneg_left hg (by positivity)
      nlinarith
    _ ≤ ‖x - xstar‖ ^ 2 - 2 * η * (f x - f xstar) + η ^ 2 * G ^ 2 := by
      have hsmul : ‖η • gradient f x‖ ^ 2 = η ^ 2 * ‖gradient f x‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
        ring
      have hsqG : η ^ 2 * ‖gradient f x‖ ^ 2 ≤ η ^ 2 * G ^ 2 := by
        exact mul_le_mul_of_nonneg_left hgnorm (sq_nonneg η)
      rw [hsmul]
      nlinarith

/--
**Telescoping potential chain.**  After `K` gradient-descent steps the squared
distance to `x*` satisfies

`‖x_K - x*‖² ≤ ‖x₀ - x*‖² - 2·η·Σ_{k<K}(f(x_k) - f(x*)) + K·η²·G²`.

Each step's potential loss compounds into a cumulative suboptimality sum
(CLRS §33.3).
-/
lemma gdIterates_potential_le {x₀ xstar : E} {η G : ℝ} {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : ∀ y, DifferentiableAt ℝ f y)
    (hη : 0 ≤ η) (hG : ∀ y, ‖gradient f y‖ ≤ G) (K : ℕ) :
    ‖gdIterates η x₀ f K - xstar‖ ^ 2 ≤
      ‖x₀ - xstar‖ ^ 2 -
        2 * η * (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) +
        (K : ℝ) * η ^ 2 * G ^ 2 := by
  induction K with
  | zero =>
      simp [gdIterates]
  | succ K ih =>
      let xK : E := gdIterates η x₀ f K
      have hrec : ‖gdIterates η x₀ f (K + 1) - xstar‖ ^ 2 ≤
          ‖xK - xstar‖ ^ 2 - 2 * η * (f xK - f xstar) + η ^ 2 * G ^ 2 := by
        simpa [xK, gdIterates] using
          (gdStep_potential_le hf (hd xK) hη (hG xK))
      calc
        ‖gdIterates η x₀ f (K + 1) - xstar‖ ^ 2
            ≤ ‖xK - xstar‖ ^ 2 - 2 * η * (f xK - f xstar) + η ^ 2 * G ^ 2 := hrec
        _ ≤ ‖x₀ - xstar‖ ^ 2 -
              2 * η * (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) +
              (K : ℝ) * η ^ 2 * G ^ 2 - 2 * η * (f xK - f xstar) + η ^ 2 * G ^ 2 := by
              dsimp [xK]
              nlinarith [ih]
        _ = ‖x₀ - xstar‖ ^ 2 -
              2 * η * (∑ k ∈ Finset.range (K + 1), (f (gdIterates η x₀ f k) - f xstar)) +
              ((K + 1 : ℕ) : ℝ) * η ^ 2 * G ^ 2 := by
              rw [Finset.sum_range_succ]
              simp [xK]
              ring

/--
**Total-suboptimality bound.**  The sum of suboptimalities over the first `K`
iterates is bounded by `‖x₀ - x*‖²/(2·η) + K·η·G²/2`:

`Σ_{k<K} (f(x_k) - f(x*)) ≤ ‖x₀ - x*‖²/(2·η) + (K:ℝ)·η·G²/2`.

This is the telescoped potential chain with the (nonnegative) final-distance
term dropped (CLRS §33.3).
-/
lemma sum_suboptimality_le {x₀ xstar : E} {η G : ℝ} {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : ∀ y, DifferentiableAt ℝ f y)
    (hη : 0 < η) (hG : ∀ y, ‖gradient f y‖ ≤ G) (K : ℕ) :
    (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) ≤
      ‖x₀ - xstar‖ ^ 2 / (2 * η) + (K : ℝ) * η * G ^ 2 / 2 := by
  have hpot : ‖gdIterates η x₀ f K - xstar‖ ^ 2 ≤
      ‖x₀ - xstar‖ ^ 2 -
        2 * η * (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) +
        (K : ℝ) * η ^ 2 * G ^ 2 :=
    gdIterates_potential_le hf hd (le_of_lt hη) hG K
  have h0 : 0 ≤ ‖gdIterates η x₀ f K - xstar‖ ^ 2 := sq_nonneg _
  have hlin : 2 * η * (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) ≤
      ‖x₀ - xstar‖ ^ 2 + (K : ℝ) * η ^ 2 * G ^ 2 := by
    nlinarith [hpot, h0]
  have hdiv : (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) ≤
      (‖x₀ - xstar‖ ^ 2 + (K : ℝ) * η ^ 2 * G ^ 2) / (2 * η) := by
    rw [le_div_iff₀ (by positivity : 0 < 2 * η)]
    simpa [mul_comm] using hlin
  exact le_trans hdiv (by
    field_simp [hη.ne']
    exact le_rfl)

/--
**Convergence bound (Theorem 33.8).**  If `x*` minimizes `f`, then the average
iterate `x̄` of the first `K` iterates satisfies

`f(x̄) - f(x*) ≤ ‖x₀ - x*‖²/(2·η·K) + η·G²/2`.

The proof combines Jensen's inequality for the convex `f` — the average
suboptimality is at most the average of the suboptimalities — with the
total-suboptimality bound divided by `K` (CLRS §33.3).
-/
theorem avgIterate_suboptimality_le {x₀ xstar : E} {η G : ℝ} {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hd : ∀ y, DifferentiableAt ℝ f y)
    (hη : 0 < η) (hG : ∀ y, ‖gradient f y‖ ≤ G) {K : ℕ} (hK : 0 < K) :
    f (avgIterate η x₀ f K) - f xstar ≤
      ‖x₀ - xstar‖ ^ 2 / (2 * η * K) + η * G ^ 2 / 2 := by
  have hKc : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  have hJ : f (∑ k ∈ Finset.range K, (K : ℝ)⁻¹ • gdIterates η x₀ f k) ≤
      ∑ k ∈ Finset.range K, (K : ℝ)⁻¹ • f (gdIterates η x₀ f k) := by
    refine hf.map_sum_le ?_ ?_ ?_
    · intro i hi
      exact inv_nonneg.mpr (Nat.cast_nonneg K)
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hKc]
    · intro i hi
      exact Set.mem_univ _
  have hJensen : f (avgIterate η x₀ f K) ≤
      (K : ℝ)⁻¹ • (∑ k ∈ Finset.range K, f (gdIterates η x₀ f k)) := by
    calc
      f (avgIterate η x₀ f K) =
          f (∑ k ∈ Finset.range K, (K : ℝ)⁻¹ • gdIterates η x₀ f k) := by
            rw [avgIterate, Finset.smul_sum]
      _ ≤ ∑ k ∈ Finset.range K, (K : ℝ)⁻¹ • f (gdIterates η x₀ f k) := hJ
      _ = (K : ℝ)⁻¹ • (∑ k ∈ Finset.range K, f (gdIterates η x₀ f k)) := by
            rw [Finset.smul_sum]
  have hCancel : (K : ℝ)⁻¹ * ((K : ℝ) * f xstar) = f xstar := by
    rw [← mul_assoc, inv_mul_cancel₀ hKc]
    simp
  have hshift_in : (∑ k ∈ Finset.range K, f (gdIterates η x₀ f k)) - (K : ℝ) * f xstar =
      ∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar) := by
    rw [show (K : ℝ) * f xstar = ∑ k ∈ Finset.range K, f xstar by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
    rw [← Finset.sum_sub_distrib]
  have hshift : (K : ℝ)⁻¹ • (∑ k ∈ Finset.range K, f (gdIterates η x₀ f k)) - f xstar =
      (K : ℝ)⁻¹ • (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) := by
    rw [smul_eq_mul, smul_eq_mul, ← hshift_in, mul_sub, hCancel]
  have hmain : f (avgIterate η x₀ f K) - f xstar ≤
      (K : ℝ)⁻¹ • (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) := by
    calc
      f (avgIterate η x₀ f K) - f xstar ≤
          (K : ℝ)⁻¹ • (∑ k ∈ Finset.range K, f (gdIterates η x₀ f k)) - f xstar := by
            linarith [hJensen]
      _ = (K : ℝ)⁻¹ • (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) := hshift
  have hsum : (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) ≤
      ‖x₀ - xstar‖ ^ 2 / (2 * η) + (K : ℝ) * η * G ^ 2 / 2 :=
    sum_suboptimality_le hf hd hη hG K
  have hscale : (K : ℝ)⁻¹ * (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) ≤
      (K : ℝ)⁻¹ * (‖x₀ - xstar‖ ^ 2 / (2 * η) + (K : ℝ) * η * G ^ 2 / 2) := by
    exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg K))
  have hfinal : f (avgIterate η x₀ f K) - f xstar ≤
      (K : ℝ)⁻¹ * (‖x₀ - xstar‖ ^ 2 / (2 * η) + (K : ℝ) * η * G ^ 2 / 2) := by
    calc
      f (avgIterate η x₀ f K) - f xstar ≤
          (K : ℝ)⁻¹ • (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) := hmain
      _ = (K : ℝ)⁻¹ * (∑ k ∈ Finset.range K, (f (gdIterates η x₀ f k) - f xstar)) := by rfl
      _ ≤ (K : ℝ)⁻¹ * (‖x₀ - xstar‖ ^ 2 / (2 * η) + (K : ℝ) * η * G ^ 2 / 2) := hscale
  have hsimpl : (K : ℝ)⁻¹ * (‖x₀ - xstar‖ ^ 2 / (2 * η) + (K : ℝ) * η * G ^ 2 / 2) =
      ‖x₀ - xstar‖ ^ 2 / (2 * η * K) + η * G ^ 2 / 2 := by
    field_simp [hKc, hη.ne']
  exact le_trans hfinal (le_of_eq hsimpl)

end GradientDescent

end CLRS
