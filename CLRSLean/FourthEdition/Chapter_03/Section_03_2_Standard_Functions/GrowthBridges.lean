import CLRSLean.FourthEdition.Chapter_03.Section_03_2_Standard_Functions.Core
import Mathlib.Analysis.Polynomial.Basic

open Filter
open Asymptotics
open Polynomial

/-!
# Real-exponent and polynomial growth bridges

These are the two substantive generalizations requested by the Chapter 3
semantic audit: CLRS permits real exponents in its polynomial/exponential and
polylogarithmic comparisons, and its polynomial-growth statement concerns an
arbitrary nonzero polynomial rather than just a monomial.
-/

namespace CLRS
namespace Chapter03

/-- CLRS's predicate that `f` is bounded by some real polynomial power. -/
def PolynomiallyBounded (f : ℕ → ℝ) : Prop :=
  ∃ k : ℝ, isBigO f (fun n : ℕ => (n : ℝ) ^ k)

/-- CLRS's predicate that `f` is bounded by some real power of `log n`. -/
def PolylogarithmicallyBounded (f : ℕ → ℝ) : Prop :=
  ∃ k : ℝ, isBigO f (fun n : ℕ => Real.log (n : ℝ) ^ k)

/-- For every real exponent `a` and real base `c > 1`, `nᵃ = o(cⁿ)`. -/
theorem isLittleO_rpow_const_exp {a c : ℝ} (hc : 1 < c) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => c ^ n) := by
  unfold isLittleO
  have hreal := isLittleO_rpow_exp_pos_mul_atTop a (Real.log_pos hc)
  have hcomp := hreal.comp_tendsto tendsto_natCast_atTop_atTop
  refine hcomp.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards with n
  simp only [Function.comp_apply]
  calc
    Real.exp (Real.log c * (n : ℝ)) = Real.exp ((n : ℝ) * Real.log c) := by rw [mul_comm]
    _ = Real.exp (Real.log c) ^ n := Real.exp_nat_mul (Real.log c) n
    _ = c ^ n := by rw [Real.exp_log (lt_trans zero_lt_one hc)]

/-- For real `a` and positive real `r`, `(log n)ᵃ = o(nʳ)`. -/
theorem isLittleO_log_rpow_rpow {a r : ℝ} (hr : 0 < r) :
    isLittleO (fun n : ℕ => Real.log (n : ℝ) ^ a)
      (fun n : ℕ => (n : ℝ) ^ r) := by
  unfold isLittleO
  exact (isLittleO_log_rpow_rpow_atTop a hr).comp_tendsto
    tendsto_natCast_atTop_atTop

/-- A polynomial is asymptotically equivalent to its leading term. -/
theorem polynomial_isEquivalent_leadingTerm (P : ℝ[X]) :
    (fun n : ℕ => P.eval (n : ℝ)) ~[atTop]
      (fun n : ℕ => P.leadingCoeff * (n : ℝ) ^ P.natDegree) := by
  exact (P.isEquivalent_atTop_lead.comp_tendsto tendsto_natCast_atTop_atTop).congr
    (by simp) (by simp)

/-- Every nonzero real polynomial has `Θ(nᵈ)` growth, where `d` is its degree. -/
theorem polynomial_isBigTheta_degree (P : ℝ[X]) (hP : P ≠ 0) :
    isBigTheta (fun n : ℕ => P.eval (n : ℝ))
      (fun n : ℕ => (n : ℝ) ^ P.natDegree) := by
  have hlead :
      (fun n : ℕ => P.eval (n : ℝ)) =Θ[atTop]
        (fun n : ℕ => P.leadingCoeff * (n : ℝ) ^ P.natDegree) :=
    (polynomial_isEquivalent_leadingTerm P).isTheta
  have hc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hscale :
      (fun n : ℕ => P.leadingCoeff * (n : ℝ) ^ P.natDegree) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ P.natDegree) :=
    IsTheta.const_mul_left hc (isTheta_refl _ _)
  have h := hlead.trans hscale
  exact ⟨by unfold isBigO; exact h.1, by unfold isBigOmega; exact h.2⟩

end Chapter03
end CLRS
