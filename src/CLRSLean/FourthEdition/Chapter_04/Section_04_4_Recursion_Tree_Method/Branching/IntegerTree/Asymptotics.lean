import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree.Balanced
import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree.Unbalanced
import CLRSLean.FourthEdition.Chapter_04.Section_04_7_Akra_Bazzi

/-!
# Connections to Chapter 4 asymptotic interfaces

The costs of the generated rounded trees satisfy the textbook bounds on all
natural inputs: the balanced tree has quadratic cost, and the unequal-depth
tree has {lit}`Θ(n log n)` cost. The proofs use their actual recurrence
equations, including the floor and ceiling operations and base cases.
-/

namespace CLRS
namespace Chapter04

/-- The integer unequal-depth example uses the classic Akra--Bazzi root {lit}`p=1`. -/
theorem unbalancedInteger_akraBazziRoot :
    IsAkraBazziRoot [(1, (3 : Real)), (1, (3 : Real) / 2)] 1 :=
  akraBazziRoot_two_thirds_one


/-- The balanced tree has nonnegative cost and a quadratic upper potential,
including zero-size leaves. -/
theorem balancedIntegerCost_bounds {c base : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ base)
    (n : ℕ) :
    0 ≤ balancedIntegerCost c base n ∧
      balancedIntegerCost c base n ≤ (4*c+base)*((n : ℝ)+1)^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · rw [balancedIntegerCost_base hn]
        constructor
        · exact hb
        · have hsq : 1 ≤ ((n : ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
          have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*c+base by positivity)
          nlinarith
      · have hn' : 1 < n := by omega
        have hq : n/4 < n := Nat.div_lt_self (by omega) (by norm_num)
        obtain ⟨hl, hu⟩ := ih (n/4) hq
        rw [balancedIntegerCost_step hn']
        constructor
        · positivity
        · have hhalfNat : 2*(n/4+1) ≤ n+1 := by omega
          have hhalf : 2*((n/4 : ℕ)+1 : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hhalfNat
          have hq0 : 0 ≤ ((n/4 : ℕ) : ℝ) := by positivity
          have hn0 : 0 ≤ (n : ℝ) := by positivity
          have hK0 : 0 ≤ 4*c+base := by positivity
          have hsq : 4*(((n/4 : ℕ) : ℝ)+1)^2 ≤ ((n : ℝ)+1)^2 := by nlinarith
          have hw := mul_le_mul_of_nonneg_left hsq hK0
          have hlocal := mul_nonneg hc
            (show 0 ≤ ((n : ℝ)+1)^2-(n : ℝ)^2 by nlinarith)
          have hbase := mul_nonneg hb (sq_nonneg ((n : ℝ)+1))
          nlinarith

/-- The generated balanced rounded tree has {lit}`Θ(n²)` cost whenever its
quadratic local charge is positive and its leaf charge is nonnegative. -/
theorem balancedIntegerCost_isBigTheta {c base : ℝ} (hc : 0 < c) (hb : 0 ≤ base) :
    Chapter03.isBigTheta (balancedIntegerCost c base) (fun n : ℕ => (n : ℝ)^2) := by
  constructor
  · apply (Chapter03.isBigO_iff _ _).mpr
    refine ⟨4*(4*c+base), by positivity, 2, ?_⟩
    intro n hn
    obtain ⟨hl, hu⟩ := balancedIntegerCost_bounds hc.le hb n
    rw [abs_of_nonneg hl, abs_of_nonneg (sq_nonneg _)]
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hsq : ((n : ℝ)+1)^2 ≤ 4*(n : ℝ)^2 := by nlinarith
    have hw := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4*c+base by positivity)
    nlinarith
  · apply (Chapter03.isBigOmega_iff _ _).mpr
    refine ⟨c, hc, 2, ?_⟩
    intro n hn
    rw [abs_of_nonneg (balancedIntegerCost_bounds hc.le hb n).1,
      abs_of_nonneg (sq_nonneg _), balancedIntegerCost_step (by omega)]
    have hchild := (balancedIntegerCost_bounds hc.le hb (n/4)).1
    linarith

private theorem rounded_thirds_bounds (n : ℕ) (hn : 2 < n) :
    n/3 + twoThirdsCeil n = n ∧ 0 < n/3 ∧ 0 < twoThirdsCeil n ∧
      n ≤ 5*(n/3) ∧ n ≤ 5*twoThirdsCeil n ∧
      5*(n/3) ≤ 4*n ∧ 5*twoThirdsCeil n ≤ 4*n := by
  rw [twoThirdsCeil, Nat.ceilDiv_eq_add_pred_div]
  by_cases hsmall : n < 6
  · interval_cases n <;> norm_num at *
  · omega

private theorem split_log_gap (n x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hs : x+y=n) (hlx : n ≤ 5*x) (hly : n ≤ 5*y)
    (hux : 5*x ≤ 4*n) (huy : 5*y ≤ 4*n) :
    n/5 ≤ n*Real.log n-x*Real.log x-y*Real.log y ∧
      n*Real.log n-x*Real.log x-y*Real.log y ≤ 4*n := by
  have hn : 0 < n := by linarith
  have hlogLow : (1:ℝ)/5 ≤ Real.log ((5:ℝ)/4) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (5:ℝ)/4) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlogHigh : Real.log (5:ℝ) ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (x := (5:ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlogs (z : ℝ) (hz : 0 < z) (hl : n ≤ 5*z) (hu : 5*z ≤ 4*n) :
      (1:ℝ)/5 ≤ Real.log n-Real.log z ∧ Real.log n-Real.log z ≤ 4 := by
    have hlo : (5:ℝ)/4 ≤ n/z := (le_div_iff₀ hz).mpr (by nlinarith)
    have hhi : n/z ≤ 5 := (div_le_iff₀ hz).mpr hl
    rw [← Real.log_div hn.ne' hz.ne']
    exact ⟨hlogLow.trans (Real.log_le_log (by norm_num) hlo),
      (Real.log_le_log (div_pos hn hz) hhi).trans hlogHigh⟩
  have hxl := mul_le_mul_of_nonneg_left (hlogs x hx hlx hux).1 hx.le
  have hxu := mul_le_mul_of_nonneg_left (hlogs x hx hlx hux).2 hx.le
  have hyl := mul_le_mul_of_nonneg_left (hlogs y hy hly huy).1 hy.le
  have hyu := mul_le_mul_of_nonneg_left (hlogs y hy hly huy).2 hy.le
  have heq : n*Real.log n-x*Real.log x-y*Real.log y =
      x*(Real.log n-Real.log x)+y*(Real.log n-Real.log y) := by
    rw [← hs]
    ring
  rw [heq]
  constructor <;> nlinarith

/-- Explicit affine logarithmic potentials for the actual unequal-depth tree.
The linear terms absorb the base cases and cancel at each rounded split. -/
theorem unbalancedIntegerCost_bounds {c base : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ base)
    (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ unbalancedIntegerCost c base n ∧
      (c/4)*(n : ℝ)*(Real.log (n : ℝ)-1) ≤ unbalancedIntegerCost c base n ∧
      unbalancedIntegerCost c base n ≤ 5*c*(n : ℝ)*Real.log (n : ℝ)+base*(n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hbase : n ≤ 2
      · rw [unbalancedIntegerCost_base hbase]
        have hlog2 : Real.log (2:ℝ) ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (x := (2:ℝ)) (by norm_num)
          norm_num at h ⊢
          exact h
        have hlog2pos : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
        interval_cases n <;> norm_num at *
        · exact ⟨hb, by nlinarith⟩
        · exact ⟨hb, by nlinarith [mul_nonneg hc (sub_nonneg.mpr hlog2)],
            by nlinarith [mul_nonneg hc hlog2pos]⟩
      · have hrec : 2 < n := by omega
        obtain ⟨hs, hx, hy, hlx, hly, hux, huy⟩ := rounded_thirds_bounds n hrec
        have hsR : ((n/3 : ℕ) : ℝ)+(twoThirdsCeil n : ℝ)=(n : ℝ) := by exact_mod_cast hs
        have hgap := split_log_gap (n : ℝ) ((n/3 : ℕ) : ℝ) (twoThirdsCeil n : ℝ)
          (by exact_mod_cast hx) (by exact_mod_cast hy) hsR
          (by exact_mod_cast hlx) (by exact_mod_cast hly)
          (by exact_mod_cast hux) (by exact_mod_cast huy)
        obtain ⟨hx0, hxL, hxU⟩ := ih (n/3) (thirdFloor_lt_self hrec) (by omega)
        obtain ⟨hy0, hyL, hyU⟩ := ih (twoThirdsCeil n) (twoThirdsCeil_lt_self hrec) (by omega)
        rw [unbalancedIntegerCost_step hrec]
        refine ⟨by positivity, ?_, ?_⟩
        · have hw := mul_le_mul_of_nonneg_left hgap.2 (show 0 ≤ c/4 by positivity)
          have hcancel : (c/4)*((n/3 : ℕ) : ℝ)+(c/4)*(twoThirdsCeil n : ℝ)=
              (c/4)*(n : ℝ) := by rw [← mul_add, hsR]
          nlinarith
        · have hw := mul_le_mul_of_nonneg_left hgap.1 (show 0 ≤ 5*c by positivity)
          have hcancel : base*((n/3 : ℕ) : ℝ)+base*(twoThirdsCeil n : ℝ)=
              base*(n : ℝ) := by rw [← mul_add, hsR]
          nlinarith

private theorem two_le_log_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) :
    2 ≤ Real.log (n : ℝ) := by
  have hhalf := Real.one_sub_inv_le_log_of_pos (x := (2:ℝ)) (by norm_num)
  have hm := Real.log_le_log (by norm_num : (0:ℝ)<16) (show (16:ℝ) ≤ n by exact_mod_cast hn)
  have hpow : Real.log (16:ℝ) = 4*Real.log (2:ℝ) := by
    rw [show (16:ℝ)=2^4 by norm_num, Real.log_pow]
    norm_num
  rw [hpow] at hm
  norm_num at hhalf
  linarith

/-- The generated floor/ceiling unequal-depth tree has {lit}`Θ(n log n)` cost.
This follows from its recurrence and rounding arithmetic, without an assumed
asymptotic comparison or an Akra--Bazzi certificate. -/
theorem unbalancedIntegerCost_isBigTheta {c base : ℝ} (hc : 0 < c) (hb : 0 ≤ base) :
    Chapter03.isBigTheta (unbalancedIntegerCost c base)
      (fun n : ℕ => (n : ℝ)*Real.log (n : ℝ)) := by
  constructor
  · apply (Chapter03.isBigO_iff _ _).mpr
    refine ⟨5*c+base, by positivity, 16, ?_⟩
    intro n hn
    obtain ⟨h0, _, hU⟩ := unbalancedIntegerCost_bounds hc.le hb n (by omega)
    have hlog := two_le_log_of_sixteen_le hn
    rw [abs_of_nonneg h0, abs_of_nonneg (by positivity)]
    have hw := mul_nonneg (mul_nonneg hb (Nat.cast_nonneg n))
      (show 0 ≤ Real.log (n : ℝ)-1 by linarith)
    nlinarith
  · apply (Chapter03.isBigOmega_iff _ _).mpr
    refine ⟨c/8, by positivity, 16, ?_⟩
    intro n hn
    obtain ⟨h0, hL, _⟩ := unbalancedIntegerCost_bounds hc.le hb n (by omega)
    have hlog := two_le_log_of_sixteen_le hn
    rw [abs_of_nonneg h0, abs_of_nonneg (by positivity)]
    have hw := mul_nonneg (mul_nonneg hc.le (Nat.cast_nonneg n))
      (show 0 ≤ Real.log (n : ℝ)-2 by linarith)
    nlinarith

end Chapter04
end CLRS
