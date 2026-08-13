import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input

open Finset
open scoped BigOperators

/-!
# Section 4.6 — Proof of the continuous master theorem

The continuous master theorem (CLRS §4.6) treats the divide-and-conquer
recurrence {lit}`T(n) = a T(n/b) + f(n)` with *exact* division {lit}`n/b`.
Unrolling the recurrence to the bottom of the recursion tree expresses the work
as the geometric sum

```
  T(b^k) = Θ(1) + Σ_{j = 0}^{k - 1} a^j · f(b^(k - j))
```

whose three textbook cases are governed by the ratio {lit}`r = a / b^p` when the
forcing is polynomial {lit}`f(n) = n^p`.  This section formalizes the analytic
core — the real geometric series — and the three continuous cases, then bridges
the continuous scale back to the discrete comparison scales used by the
all-input Master-theorem wrappers.

Main results:

- Definition {lit}`geomSum`: the real geometric partial sum {lit}`Σ_{j<k} r^j`.
- Theorem {lit}`geomSum_le_of_lt_one`: a ratio {lit}`0 ≤ r < 1` yields a partial
  sum bounded independently of the number of terms.
- Theorem {lit}`geomSum_eq_of_one`: a ratio {lit}`r = 1` yields exactly
  {lit}`k` terms.
- Theorem {lit}`geomSum_bigTheta_of_gt_one`: a ratio {lit}`r > 1` yields a
  geometric tail {lit}`Θ(r^k)`.
- Definition {lit}`continuousWork`: the recursion-tree work
  {lit}`Σ_{j<k} a^j (b^(k-j))^p` with polynomial forcing.
- Theorem {lit}`continuousWork_eq_geomSum`: the work equals
  {lit}`b^(p·k) · geomSum (a / b^p) k`.
- Theorems {lit}`continuous_master_case1`, {lit}`continuous_master_case2`, and
  {lit}`continuous_master_case3`: the three continuous cases.
- Theorem {lit}`continuous_case1_scale_eq_criticalPowerScale`: the continuous
  case-1 scale equals the discrete critical-power scale on exact powers.

Status: `proved` for the continuous geometric-series core and its bridge to the
discrete comparison scales.  Floors, ceilings, and the non-polynomial forcing
of the full all-input transfer remain in
{lit}`CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input`.

Notation conventions used in this section:

- `a` : number of subproblems
- `b` : factor by which the subproblem size shrinks
- `p` : exponent of the polynomial forcing {lit}`f(n) = n^p`
- `k` : continuous level count (so {lit}`n = b^k`)
-/

namespace CLRS
namespace Chapter04

/-! ## The real geometric series -/

/-- The real geometric partial sum {lit}`Σ_{j ∈ range k} r^j`. -/
noncomputable def geomSum (r : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range k, r ^ j

/-- A geometric partial sum with a nonnegative ratio is nonnegative. -/
theorem geomSum_nonneg {r : ℝ} (hr0 : 0 ≤ r) (k : ℕ) : 0 ≤ geomSum r k := by
  rw [geomSum]
  exact Finset.sum_nonneg (by intro j hj; exact pow_nonneg hr0 j)

/--
**Continuous master theorem, case-1 ratio.**  For a ratio {lit}`0 ≤ r < 1` the
partial sum is bounded by {lit}`(1 - r)⁻¹`, independently of the number of
terms.  This is the analytic reason the forcing in the third Master case (whose
ratio is smaller than one) contributes only {lit}`Θ(f(n))` rather than growing
with the recursion tree.
-/
theorem geomSum_le_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    geomSum r k ≤ (1 - r)⁻¹ := by
  have hr_ne : r ≠ 1 := by linarith
  have hpos : 0 < 1 - r := by linarith
  rw [geomSum, geom_sum_eq hr_ne]
  have hrk_nonneg : 0 ≤ r ^ k := pow_nonneg hr0 _
  have hnum : 1 - r ^ k ≤ 1 := by linarith
  have hdiv : (1 - r ^ k) / (1 - r) ≤ 1 / (1 - r) :=
    (div_le_div_iff_of_pos_right hpos).mpr hnum
  have hcast : (r ^ k - 1) / (r - 1) = (1 - r ^ k) / (1 - r) := by
    field_simp [ne_of_gt hpos]
    ring
  rw [hcast]
  rw [inv_eq_one_div]
  exact hdiv

/--
**Continuous master theorem, case-2 ratio.**  For a ratio {lit}`r = 1` the
partial sum has exactly {lit}`k` unit terms, the logarithmic factor in the
second Master case.
-/
theorem geomSum_eq_of_one (k : ℕ) : geomSum 1 k = (k : ℝ) := by
  rw [geomSum]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- For a ratio {lit}`r > 1` the partial sum is at most a constant times its last
    term {lit}`r^k`. -/
theorem geomSum_le_geometric_of_gt_one {r : ℝ} (hr1 : 1 < r) (k : ℕ) :
    geomSum r k ≤ (r - 1)⁻¹ * r ^ k := by
  have hr_ne : r ≠ 1 := by linarith
  rw [geomSum, geom_sum_eq hr_ne]
  calc
    (r ^ k - 1) / (r - 1) ≤ r ^ k / (r - 1) :=
      (div_le_div_iff_of_pos_right (sub_pos.mpr hr1)).mpr (by linarith)
    _ = (r - 1)⁻¹ * r ^ k := by
      rw [div_eq_mul_inv]
      ring

/-- For a ratio {lit}`r > 1` and a nonempty partial sum, the sum is at least a
    constant times its last term {lit}`r^k`. -/
theorem geometric_le_geomSum_of_gt_one {r : ℝ} (hr1 : 1 < r) {k : ℕ} (hk : 1 ≤ k) :
    (r : ℝ)⁻¹ * r ^ k ≤ geomSum r k := by
  have hr_pos : 0 < r := lt_trans zero_lt_one hr1
  have hlast : r ^ (k - 1) ≤ geomSum r k := by
    rw [geomSum]
    exact Finset.single_le_sum (by intro j hj; exact pow_nonneg hr_pos.le j)
      (by rw [mem_range]; omega)
  have hfac : (r : ℝ)⁻¹ * r ^ k = r ^ (k - 1) := by
    field_simp [ne_of_gt hr_pos]
    rw [mul_comm, ← pow_succ]
    rw [show (k - 1) + 1 = k by omega]
  rw [hfac]
  exact hlast

/--
**Continuous master theorem, case-3 ratio.**  For a ratio {lit}`r > 1` the
partial sum is {lit}`Θ(r^k)`, dominated by its largest (last) term.  This is the
analytic reason the forcing in the first Master case (whose ratio exceeds one)
grows to {lit}`Θ(n^(log_b a))`.
-/
theorem geomSum_bigTheta_of_gt_one {r : ℝ} (hr1 : 1 < r) :
    Chapter03.isBigTheta (geomSum r) (fun k => r ^ k) := by
  have hr_pos : 0 < r := lt_trans zero_lt_one hr1
  constructor
  · rw [Chapter03.isBigO_iff]
    refine ⟨(r - 1)⁻¹, inv_pos.mpr (sub_pos.mpr hr1), 0, ?_⟩
    intro k hk
    rw [abs_of_nonneg (geomSum_nonneg hr_pos.le k)]
    rw [abs_of_nonneg (pow_nonneg hr_pos.le k)]
    exact geomSum_le_geometric_of_gt_one hr1 k
  · rw [Chapter03.isBigOmega_iff]
    refine ⟨(r : ℝ)⁻¹, inv_pos.mpr hr_pos, 1, ?_⟩
    intro k hk
    rw [abs_of_nonneg (geomSum_nonneg hr_pos.le k)]
    rw [abs_of_nonneg (pow_nonneg hr_pos.le k)]
    exact geometric_le_geomSum_of_gt_one hr1 hk

/-! ## The continuous recursion-tree work -/

/--
The recursion-tree work of a divide-and-conquer recurrence with polynomial
forcing {lit}`f(n) = n^p`: level {lit}`j` has {lit}`a^j` subproblems, each of
size {lit}`b^(k-j)` and cost {lit}`(b^(k-j))^p` (here {lit}`n = b^k` is an exact
power, so division {lit}`n/b` is exact).
-/
noncomputable def continuousWork (a b p k : ℕ) : ℝ :=
  ∑ j ∈ range k, (a : ℝ) ^ j * ((b : ℝ) ^ (k - j)) ^ p

/-- The continuous ratio {lit}`a / b^p` that governs the geometric series. -/
noncomputable def continuousRatio (a b p : ℕ) : ℝ :=
  (a : ℝ) / (b : ℝ) ^ p

/-- The recursion-tree work is nonnegative. -/
theorem continuousWork_nonneg (a b p k : ℕ) : 0 ≤ continuousWork a b p k := by
  rw [continuousWork]
  exact Finset.sum_nonneg (by
    intro j hj
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg a) j)
      (pow_nonneg (pow_nonneg (Nat.cast_nonneg b) (k - j)) p))

/--
The recursion-tree work factors as {lit}`b^(p·k)` times the geometric series with
ratio {lit}`a / b^p`: each level's work {lit}`a^j (b^(k-j))^p` equals
{lit}`b^(p·k) (a / b^p)^j`.
-/
theorem continuousWork_eq_geomSum (a b p : ℕ) (hb : (b : ℝ) ≠ 0) (k : ℕ) :
    continuousWork a b p k =
      (b : ℝ) ^ (p * k) * geomSum (continuousRatio a b p) k := by
  unfold continuousWork geomSum continuousRatio
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < k := by simpa [mem_range] using hj
  calc
    (a : ℝ) ^ j * ((b : ℝ) ^ (k - j)) ^ p
        = (a : ℝ) ^ j * (b : ℝ) ^ ((k - j) * p) := by rw [← pow_mul]
    _ = (a : ℝ) ^ j * (b : ℝ) ^ (p * (k - j)) := by rw [Nat.mul_comm (k - j) p]
    _ = (a : ℝ) ^ j * (b : ℝ) ^ (p * k - p * j) := by
        rw [show p * (k - j) = p * k - p * j by exact Nat.mul_sub_left_distrib p k j]
    _ = (a : ℝ) ^ j * ((b : ℝ) ^ (p * k) / (b : ℝ) ^ (p * j)) := by
        rw [pow_sub₀ (b : ℝ) hb (Nat.mul_le_mul_left p (le_of_lt hjlt))]
        rw [div_eq_mul_inv]
    _ = (b : ℝ) ^ (p * k) * ((a : ℝ) ^ j / (b : ℝ) ^ (p * j)) := by ring
    _ = (b : ℝ) ^ (p * k) * ((a : ℝ) / (b : ℝ) ^ p) ^ j := by
        rw [div_pow, ← pow_mul]

/-! ## The three continuous cases -/

/--
**Continuous master theorem, case 1.**  When the ratio {lit}`a / b^p > 1` (so
{lit}`p < log_b a`, i.e. the forcing {lit}`n^p` is polynomially smaller than the
critical {lit}`n^(log_b a)`), the recursion-tree work is {lit}`Θ(a^k)`, matching
{lit}`Θ(n^(log_b a))` on the exact power {lit}`n = b^k`.
-/
theorem continuous_master_case1 (a b p : ℕ) (hb : (b : ℝ) ≠ 0)
    (hr : 1 < continuousRatio a b p) :
    Chapter03.isBigTheta (continuousWork a b p) (fun k => (a : ℝ) ^ k) := by
  have hratio : 1 < (a : ℝ) / (b : ℝ) ^ p := by simpa [continuousRatio] using hr
  have hpow_identity : ∀ k, (b : ℝ) ^ (p * k) * ((a : ℝ) / (b : ℝ) ^ p) ^ k = (a : ℝ) ^ k := by
    intro k
    calc
      (b : ℝ) ^ (p * k) * ((a : ℝ) / (b : ℝ) ^ p) ^ k
          = (b : ℝ) ^ (p * k) * ((a : ℝ) ^ k / (b : ℝ) ^ (p * k)) := by
            rw [div_pow, ← pow_mul]
      _ = (a : ℝ) ^ k := by
            field_simp [pow_ne_zero (p * k) hb]
  constructor
  · rw [Chapter03.isBigO_iff]
    refine ⟨((a : ℝ) / (b : ℝ) ^ p - 1)⁻¹, inv_pos.mpr (sub_pos.mpr hratio), 0, ?_⟩
    intro k hk
    rw [abs_of_nonneg (continuousWork_nonneg a b p k)]
    rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg a) k)]
    rw [continuousWork_eq_geomSum a b p hb k]
    have hgeom : geomSum ((a : ℝ) / (b : ℝ) ^ p) k
        ≤ ((a : ℝ) / (b : ℝ) ^ p - 1)⁻¹ * ((a : ℝ) / (b : ℝ) ^ p) ^ k :=
      geomSum_le_geometric_of_gt_one hratio k
    have hterm : (b : ℝ) ^ (p * k) * geomSum ((a : ℝ) / (b : ℝ) ^ p) k
        ≤ ((a : ℝ) / (b : ℝ) ^ p - 1)⁻¹ * (a : ℝ) ^ k := by
      calc
        (b : ℝ) ^ (p * k) * geomSum ((a : ℝ) / (b : ℝ) ^ p) k
            ≤ (b : ℝ) ^ (p * k) *
                (((a : ℝ) / (b : ℝ) ^ p - 1)⁻¹ * ((a : ℝ) / (b : ℝ) ^ p) ^ k) :=
              mul_le_mul_of_nonneg_left hgeom (pow_nonneg (Nat.cast_nonneg b) (p * k))
        _ = ((a : ℝ) / (b : ℝ) ^ p - 1)⁻¹ *
                ((b : ℝ) ^ (p * k) * ((a : ℝ) / (b : ℝ) ^ p) ^ k) := by ring
        _ = ((a : ℝ) / (b : ℝ) ^ p - 1)⁻¹ * (a : ℝ) ^ k := by rw [hpow_identity k]
    exact hterm
  · rw [Chapter03.isBigOmega_iff]
    refine ⟨((a : ℝ) / (b : ℝ) ^ p)⁻¹, inv_pos.mpr (lt_trans zero_lt_one hratio), 1, ?_⟩
    intro k hk
    rw [abs_of_nonneg (continuousWork_nonneg a b p k)]
    rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg a) k)]
    rw [continuousWork_eq_geomSum a b p hb k]
    have hgeom : ((a : ℝ) / (b : ℝ) ^ p)⁻¹ * ((a : ℝ) / (b : ℝ) ^ p) ^ k
        ≤ geomSum ((a : ℝ) / (b : ℝ) ^ p) k :=
      geometric_le_geomSum_of_gt_one hratio hk
    have hterm : ((a : ℝ) / (b : ℝ) ^ p)⁻¹ * (a : ℝ) ^ k
        ≤ (b : ℝ) ^ (p * k) * geomSum ((a : ℝ) / (b : ℝ) ^ p) k := by
      calc
        ((a : ℝ) / (b : ℝ) ^ p)⁻¹ * (a : ℝ) ^ k
            = ((a : ℝ) / (b : ℝ) ^ p)⁻¹ *
                ((b : ℝ) ^ (p * k) * ((a : ℝ) / (b : ℝ) ^ p) ^ k) := by rw [hpow_identity k]
        _ = (b : ℝ) ^ (p * k) *
                (((a : ℝ) / (b : ℝ) ^ p)⁻¹ * ((a : ℝ) / (b : ℝ) ^ p) ^ k) := by ring
        _ ≤ (b : ℝ) ^ (p * k) * geomSum ((a : ℝ) / (b : ℝ) ^ p) k :=
              mul_le_mul_of_nonneg_left hgeom (pow_nonneg (Nat.cast_nonneg b) (p * k))
    exact hterm

/--
**Continuous master theorem, case 2.**  When the ratio {lit}`a / b^p = 1` (so
{lit}`a = b^p`, i.e. the forcing {lit}`n^p` matches the critical
{lit}`n^(log_b a)`), the recursion-tree work is {lit}`Θ(k · a^k)`, the
logarithmic case.
-/
theorem continuous_master_case2 (a b p : ℕ) (hb : (b : ℝ) ≠ 0)
    (hr : continuousRatio a b p = 1) :
    Chapter03.isBigTheta (continuousWork a b p) (fun k => (k : ℝ) * (a : ℝ) ^ k) := by
  have hratio : (a : ℝ) / (b : ℝ) ^ p = 1 := by simpa [continuousRatio] using hr
  have hbp : (b : ℝ) ^ p ≠ 0 := pow_ne_zero p hb
  have hbase : (b : ℝ) ^ p = (a : ℝ) := by
    field_simp [hbp] at hratio
    exact hratio.symm
  have hpow_identity : ∀ k, (b : ℝ) ^ (p * k) = (a : ℝ) ^ k := by
    intro k
    rw [← hbase]
    rw [← pow_mul]
  constructor
  · rw [Chapter03.isBigO_iff]
    refine ⟨1, by norm_num, 0, ?_⟩
    intro k hk
    rw [abs_of_nonneg (continuousWork_nonneg a b p k)]
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (Nat.cast_nonneg a) k))]
    rw [continuousWork_eq_geomSum a b p hb k]
    rw [continuousRatio, hratio, geomSum_eq_of_one k]
    rw [hpow_identity k]
    nlinarith
  · rw [Chapter03.isBigOmega_iff]
    refine ⟨1, by norm_num, 0, ?_⟩
    intro k hk
    rw [abs_of_nonneg (continuousWork_nonneg a b p k)]
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (Nat.cast_nonneg a) k))]
    rw [continuousWork_eq_geomSum a b p hb k]
    rw [continuousRatio, hratio, geomSum_eq_of_one k]
    rw [hpow_identity k]
    nlinarith

/--
**Continuous master theorem, case 3.**  When the ratio {lit}`a / b^p < 1` (so
{lit}`p > log_b a`, i.e. the forcing {lit}`n^p` dominates the critical
{lit}`n^(log_b a)`), the recursion-tree work is {lit}`Θ(b^(p·k))`, matching
{lit}`Θ(f(n)) = Θ(n^p)` on the exact power {lit}`n = b^k`.
-/
theorem continuous_master_case3 (a b p : ℕ) (hb : (b : ℝ) ≠ 0)
    (hr0 : 0 ≤ continuousRatio a b p) (hr1 : continuousRatio a b p < 1) :
    Chapter03.isBigTheta (continuousWork a b p) (fun k => (b : ℝ) ^ (p * k)) := by
  have hratio0 : 0 ≤ (a : ℝ) / (b : ℝ) ^ p := by simpa [continuousRatio] using hr0
  have hratio1 : (a : ℝ) / (b : ℝ) ^ p < 1 := by simpa [continuousRatio] using hr1
  constructor
  · rw [Chapter03.isBigO_iff]
    refine ⟨(1 - (a : ℝ) / (b : ℝ) ^ p)⁻¹, inv_pos.mpr (sub_pos.mpr hratio1), 0, ?_⟩
    intro k hk
    rw [abs_of_nonneg (continuousWork_nonneg a b p k)]
    rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg b) (p * k))]
    rw [continuousWork_eq_geomSum a b p hb k]
    rw [continuousRatio]
    have hgeom : geomSum ((a : ℝ) / (b : ℝ) ^ p) k ≤ (1 - (a : ℝ) / (b : ℝ) ^ p)⁻¹ :=
      geomSum_le_of_lt_one hratio0 hratio1 k
    have hle := mul_le_mul_of_nonneg_left hgeom (pow_nonneg (Nat.cast_nonneg b) (p * k))
    simpa [mul_comm, mul_left_comm, mul_assoc] using hle
  · rw [Chapter03.isBigOmega_iff]
    refine ⟨1, by norm_num, 1, ?_⟩
    intro k hk
    have hk1 : 1 ≤ k := hk
    rw [abs_of_nonneg (continuousWork_nonneg a b p k)]
    rw [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg b) (p * k))]
    rw [continuousWork_eq_geomSum a b p hb k]
    rw [continuousRatio]
    have hgeom : 1 ≤ geomSum ((a : ℝ) / (b : ℝ) ^ p) k := by
      rw [geomSum]
      rw [show (1 : ℝ) = ((a : ℝ) / (b : ℝ) ^ p) ^ 0 by simp]
      exact Finset.single_le_sum (f := fun j => ((a : ℝ) / (b : ℝ) ^ p) ^ j)
        (by intro j hj; exact pow_nonneg hratio0 j) (a := 0)
        (by rw [mem_range]; exact lt_of_lt_of_le zero_lt_one hk1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left hgeom (pow_nonneg (Nat.cast_nonneg b) (p * k)))

/-! ## Bridge to the discrete comparison scales -/

/--
The continuous case-1 scale {lit}`a^k` at the exact power {lit}`n = b^k` is
exactly the discrete critical-power scale {name}`CLRS.Chapter04.criticalPowerScale`,
so the continuous master theorem's {lit}`Θ(a^k)` conclusion is the
{lit}`Θ(n^(log_b a))` scale of the all-input wrappers (through
{name}`CLRS.Chapter04.criticalPowerScale_isBigTheta_realLogScale`).
-/
theorem continuous_case1_scale_eq_criticalPowerScale (a b : ℕ) (hb : 1 < b) (k : ℕ) :
    (a : ℝ) ^ k = criticalPowerScale a b (b ^ k) := by
  unfold criticalPowerScale
  rw [Nat.log_pow hb]

/--
The discrete case-2 scale {name}`CLRS.Chapter04.criticalPowerLogScale` on the
exact power {lit}`n = b^k` is exactly {lit}`(k + 1) · a^k`, matching the
continuous case-2 scale {lit}`k · a^k` up to the leading {lit}`+ 1`.
-/
theorem continuous_case2_criticalPowerLogScale_eq (a b : ℕ) (hb : 1 < b) (k : ℕ) :
    criticalPowerLogScale a b (b ^ k) = ((k : ℝ) + 1) * (a : ℝ) ^ k := by
  unfold criticalPowerLogScale
  rw [continuous_case1_scale_eq_criticalPowerScale a b hb k]
  rw [Nat.log_pow hb]

end Chapter04
end CLRS
