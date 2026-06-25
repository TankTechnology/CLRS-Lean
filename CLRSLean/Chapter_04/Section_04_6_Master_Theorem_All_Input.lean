import CLRSLean.Chapter_04.Section_04_5_Master_Theorem

/-!
# CLRS Section 4.6 - All-input Master-theorem bridge

Section 4.5 proves the exact-power Master-theorem core for values
{lit}`T(b^i)`.  The full CLRS theorem needs a second bridge from exact powers
to arbitrary natural input sizes, including floor and ceiling recurrences.

This file proves the reusable transfer layer for that bridge.  It first keeps
the power-sandwich facts as explicit hypotheses, then gives a reusable way to
discharge them from a monotonicity hypothesis plus a one-step scale bound
between adjacent powers of the base.  It also proves a real-log comparison
bridge that connects the discrete scale {lit}`a^(⌊log_b n⌋)` to the textbook
scale {lit}`n^(log_b a)` for all {lit}`a ≥ 1` and {lit}`b > 1`.
-/

namespace CLRS
namespace Chapter04

/-! ## Monotone and sandwich interfaces -/

/-- Absolute-value monotonicity for a cost function. -/
def MonotoneAbs (T : ℕ → ℝ) : Prop :=
  ∀ {m n : ℕ}, m ≤ n → |T m| ≤ |T n|

/--
Eventual one-step control for a comparison scale across one multiplication by
the Master-theorem base.  This is the local regularity assumption that turns
the adjacent-power interval {lit}`b^i ≤ n < b^(i+1)` into the global power-sandwich
hypotheses below.
-/
def EventuallyPowerStepBound (b : ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → |g (b * n)| ≤ A * |g n|

/--
Discrete critical-power scale for the exact-power Master theorem case 1.  On
exact powers it satisfies
{lit}`criticalPowerScale a b (b^i) = a^i`; between exact powers it is the
step function determined by {lit}`Nat.log b n`.

This, {lit}`criticalPowerLogScale`, and {lit}`tailDominatedScale` are
deliberately weaker and cleaner than the analytic scales
{lit}`n^(log_b a)`, but it is enough to make the exact-power-to-all-input
bridge concrete for the three Master cases.
-/
def criticalPowerScale (a b : ℕ) (n : ℕ) : ℝ :=
  (a : ℝ) ^ Nat.log b n

/--
Discrete case-2 Master scale.  On exact powers this is
{lit}`(i+1) a^i`; between exact powers it is the step function determined by
{lit}`Nat.log b n`.
-/
def criticalPowerLogScale (a b : ℕ) (n : ℕ) : ℝ :=
  ((Nat.log b n : ℝ) + 1) * criticalPowerScale a b n

/--
Discrete case-3 Master scale.  On exact powers this is the scale from
{name}`master_case3_tail_dominated`; between exact powers it is again the
step function determined by {lit}`Nat.log b n`.
-/
noncomputable def tailDominatedScale (a b : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (if Nat.log b n = 0 then 1 else normalizedForcing a b f (Nat.log b n - 1)) *
    criticalPowerScale a b n

theorem criticalPowerScale_exactPower
    (a b i : ℕ) (hb : 1 < b) :
    criticalPowerScale a b (b ^ i) = (a : ℝ) ^ i := by
  simp [criticalPowerScale, Nat.log_pow hb]

theorem criticalPowerLogScale_exactPower
    (a b i : ℕ) (hb : 1 < b) :
    criticalPowerLogScale a b (b ^ i) =
      ((i : ℝ) + 1) * ((a : ℝ) ^ i) := by
  simp [criticalPowerLogScale, criticalPowerScale, Nat.log_pow hb]

theorem tailDominatedScale_exactPower
    (a b : ℕ) (f : ℕ → ℝ) (i : ℕ) (hb : 1 < b) :
    tailDominatedScale a b f (b ^ i) =
      (if i = 0 then 1 else normalizedForcing a b f (i - 1)) *
        ((a : ℝ) ^ i) := by
  simp [tailDominatedScale, criticalPowerScale, Nat.log_pow hb]

theorem criticalPowerLogScale_nonneg (a b n : ℕ) :
    0 ≤ criticalPowerLogScale a b n := by
  unfold criticalPowerLogScale criticalPowerScale
  positivity

theorem criticalPowerScale_monotoneAbs
    (a b : ℕ) (ha : 1 ≤ a) :
    MonotoneAbs (criticalPowerScale a b) := by
  intro m n hmn
  have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
  have ha_one : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have hlog : Nat.log b m ≤ Nat.log b n :=
    Nat.log_mono_right hmn
  calc
    |criticalPowerScale a b m| = (a : ℝ) ^ Nat.log b m := by
      rw [criticalPowerScale, abs_of_nonneg (pow_nonneg ha_nonneg _)]
    _ ≤ (a : ℝ) ^ Nat.log b n :=
      pow_le_pow_right₀ ha_one hlog
    _ = |criticalPowerScale a b n| := by
      rw [criticalPowerScale, abs_of_nonneg (pow_nonneg ha_nonneg _)]

theorem criticalPowerScale_powerStepBound
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 < b) :
    EventuallyPowerStepBound b (criticalPowerScale a b) := by
  refine ⟨(a : ℝ), ?_, 1, ?_⟩
  · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  · intro n hn
    have hn_ne_zero : n ≠ 0 := by omega
    have hlog : Nat.log b (b * n) = Nat.log b n + 1 := by
      rw [Nat.mul_comm]
      exact Nat.log_mul_base hb hn_ne_zero
    simp [criticalPowerScale, hlog, abs_of_nonneg (pow_nonneg ha_nonneg _),
      pow_succ, mul_comm]

theorem criticalPowerLogScale_monotoneAbs
    (a b : ℕ) (ha : 1 ≤ a) :
    MonotoneAbs (criticalPowerLogScale a b) := by
  intro m n hmn
  have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
  have ha_one : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have hlog : Nat.log b m ≤ Nat.log b n :=
    Nat.log_mono_right hmn
  have hlog_real :
      (Nat.log b m : ℝ) + 1 ≤ (Nat.log b n : ℝ) + 1 := by
    have hcast : (Nat.log b m : ℝ) ≤ Nat.log b n := by
      exact_mod_cast hlog
    linarith
  have hpow :
      (a : ℝ) ^ Nat.log b m ≤ (a : ℝ) ^ Nat.log b n :=
    pow_le_pow_right₀ ha_one hlog
  rw [abs_of_nonneg (criticalPowerLogScale_nonneg a b m),
    abs_of_nonneg (criticalPowerLogScale_nonneg a b n)]
  unfold criticalPowerLogScale criticalPowerScale
  exact mul_le_mul hlog_real hpow (pow_nonneg ha_nonneg _)
    (by positivity)

theorem criticalPowerLogScale_powerStepBound
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 < b) :
    EventuallyPowerStepBound b (criticalPowerLogScale a b) := by
  refine ⟨2 * (a : ℝ), ?_, 1, ?_⟩
  · have ha_pos : 0 < (a : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha
    positivity
  · intro n hn
    have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
    have hn_ne_zero : n ≠ 0 := by omega
    have hlog : Nat.log b (b * n) = Nat.log b n + 1 := by
      rw [Nat.mul_comm]
      exact Nat.log_mul_base hb hn_ne_zero
    have hratio :
        (Nat.log b n : ℝ) + 2 ≤
          2 * ((Nat.log b n : ℝ) + 1) := by
      have hlog_nonneg : 0 ≤ (Nat.log b n : ℝ) := by positivity
      linarith
    calc
      |criticalPowerLogScale a b (b * n)|
          = ((Nat.log b n : ℝ) + 2) *
              ((a : ℝ) * (a : ℝ) ^ Nat.log b n) := by
            rw [abs_of_nonneg (criticalPowerLogScale_nonneg a b (b * n))]
            simp [criticalPowerLogScale, criticalPowerScale, hlog, pow_succ,
              Nat.cast_add]
            ring
      _ = (a : ℝ) *
            (((Nat.log b n : ℝ) + 2) *
              (a : ℝ) ^ Nat.log b n) := by ring
      _ ≤ (a : ℝ) *
            (2 * ((Nat.log b n : ℝ) + 1) *
              (a : ℝ) ^ Nat.log b n) := by
            gcongr
      _ = (2 * (a : ℝ)) * |criticalPowerLogScale a b n| := by
            rw [abs_of_nonneg (criticalPowerLogScale_nonneg a b n)]
            simp [criticalPowerLogScale, criticalPowerScale]
            ring

/-! ## Polynomial comparison scales -/

/--
The usual polynomial comparison scale {lit}`n^p`.  This is the
textbook-facing specialization of the critical Master scale when
{lit}`a = b^p`.
-/
noncomputable def polynomialScale (p : ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ p

/--
The polynomial-logarithmic comparison scale
{lit}`(⌊log_b n⌋ + 1)n^p`.  It is a discrete-log version of the CLRS
case-2 scale {lit}`n^p log n`, chosen so that it connects directly to the
all-input exact-power bridge.
-/
noncomputable def polynomialLogScale (b p : ℕ) (n : ℕ) : ℝ :=
  ((Nat.log b n : ℝ) + 1) * polynomialScale p n

theorem criticalPowerScale_of_base_pow (b p n : ℕ) :
    criticalPowerScale (b ^ p) b n =
      (((b ^ Nat.log b n : ℕ) : ℝ) ^ p) := by
  simp only [criticalPowerScale, Nat.cast_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem pow_succ_pow_eq_mul_pow (b i p : ℕ) :
    (b ^ (i + 1)) ^ p = (b ^ p) * (b ^ i) ^ p := by
  rw [show b ^ (i + 1) = b * b ^ i by
    rw [pow_succ, Nat.mul_comm]]
  rw [Nat.mul_pow]

private theorem one_le_base_pow_of_one_lt (b p : ℕ) (hb : 1 < b) :
    1 ≤ b ^ p := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  exact Nat.succ_le_iff.mpr (pow_pos hb_pos p)

/--
When {lit}`a = b^p`, the discrete critical-power scale is asymptotic to the
ordinary polynomial scale {lit}`n^p`.  This is the main comparison lemma that
turns case-1 all-input Master wrappers into textbook-looking statements
whenever {lit}`log_b a` is a natural number.
-/
theorem criticalPowerScale_isBigTheta_polynomialScale
    (b p : ℕ) (hb : 1 < b) :
    Chapter03.isBigTheta (criticalPowerScale (b ^ p) b) (polynomialScale p) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ?_
    refine ⟨1, by norm_num, 1, ?_⟩
    intro n hn
    have hn_ne_zero : n ≠ 0 := by omega
    have hlow : b ^ Nat.log b n ≤ n :=
      Nat.pow_log_le_self b hn_ne_zero
    have hpow :
        ((b ^ Nat.log b n : ℕ) : ℝ) ^ p ≤ (n : ℝ) ^ p := by
      exact_mod_cast Nat.pow_le_pow_left hlow p
    calc
      |criticalPowerScale (b ^ p) b n|
          = ((b ^ Nat.log b n : ℕ) : ℝ) ^ p := by
            rw [criticalPowerScale_of_base_pow]
            exact abs_of_nonneg (pow_nonneg (by positivity) p)
      _ ≤ (n : ℝ) ^ p := hpow
      _ = 1 * |polynomialScale p n| := by
            rw [polynomialScale,
              abs_of_nonneg (pow_nonneg (by positivity) p)]
            ring
  · refine (Chapter03.isBigOmega_iff _ _).mpr ?_
    let B : ℝ := ((b ^ p : ℕ) : ℝ)
    have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
    have hB_pos_nat : 0 < b ^ p := pow_pos hb_pos p
    have hB_pos : 0 < B := by
      dsimp [B]
      exact_mod_cast hB_pos_nat
    refine ⟨B⁻¹, inv_pos.mpr hB_pos, 1, ?_⟩
    intro n hn
    have hn_ne_zero : n ≠ 0 := by omega
    let i := Nat.log b n
    have hhigh : n < b ^ (i + 1) := by
      simpa [i] using Nat.lt_pow_succ_log_self hb n
    have hupper_nat : n ^ p ≤ (b ^ p) * (b ^ i) ^ p := by
      calc
        n ^ p ≤ (b ^ (i + 1)) ^ p :=
          Nat.pow_le_pow_left (Nat.le_of_lt hhigh) p
        _ = (b ^ p) * (b ^ i) ^ p :=
          pow_succ_pow_eq_mul_pow b i p
    have hupper_real :
        (n : ℝ) ^ p ≤ B * (((b ^ i : ℕ) : ℝ) ^ p) := by
      dsimp [B]
      exact_mod_cast hupper_nat
    calc
      B⁻¹ * |polynomialScale p n|
          = B⁻¹ * (n : ℝ) ^ p := by
            rw [polynomialScale,
              abs_of_nonneg (pow_nonneg (by positivity) p)]
      _ ≤ B⁻¹ * (B * (((b ^ i : ℕ) : ℝ) ^ p)) := by
            gcongr
      _ = ((b ^ i : ℕ) : ℝ) ^ p := by
            field_simp [ne_of_gt hB_pos]
      _ = |criticalPowerScale (b ^ p) b n| := by
            rw [criticalPowerScale_of_base_pow]
            simp [i, abs_of_nonneg (pow_nonneg (by positivity) p)]

/--
When {lit}`a = b^p`, the discrete case-2 Master scale is asymptotic to
{lit}`(⌊log_b n⌋ + 1)n^p`.  This keeps the statement discrete while matching
the standard {lit}`n^p log n` shape used in CLRS.
-/
theorem criticalPowerLogScale_isBigTheta_polynomialLogScale
    (b p : ℕ) (hb : 1 < b) :
    Chapter03.isBigTheta (criticalPowerLogScale (b ^ p) b)
      (polynomialLogScale b p) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ?_
    refine ⟨1, by norm_num, 1, ?_⟩
    intro n hn
    have hn_ne_zero : n ≠ 0 := by omega
    have hlow : b ^ Nat.log b n ≤ n :=
      Nat.pow_log_le_self b hn_ne_zero
    have hpow :
        ((b ^ Nat.log b n : ℕ) : ℝ) ^ p ≤ (n : ℝ) ^ p := by
      exact_mod_cast Nat.pow_le_pow_left hlow p
    have hL_nonneg : 0 ≤ (Nat.log b n : ℝ) + 1 := by positivity
    calc
      |criticalPowerLogScale (b ^ p) b n|
          = ((Nat.log b n : ℝ) + 1) *
              (((b ^ Nat.log b n : ℕ) : ℝ) ^ p) := by
            rw [abs_of_nonneg (criticalPowerLogScale_nonneg (b ^ p) b n)]
            simp [criticalPowerLogScale, criticalPowerScale_of_base_pow]
      _ ≤ ((Nat.log b n : ℝ) + 1) * ((n : ℝ) ^ p) := by
            gcongr
      _ = 1 * |polynomialLogScale b p n| := by
            rw [polynomialLogScale, polynomialScale,
              abs_of_nonneg
                (mul_nonneg hL_nonneg (pow_nonneg (by positivity) p))]
            ring
  · refine (Chapter03.isBigOmega_iff _ _).mpr ?_
    let B : ℝ := ((b ^ p : ℕ) : ℝ)
    have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
    have hB_pos_nat : 0 < b ^ p := pow_pos hb_pos p
    have hB_pos : 0 < B := by
      dsimp [B]
      exact_mod_cast hB_pos_nat
    refine ⟨B⁻¹, inv_pos.mpr hB_pos, 1, ?_⟩
    intro n hn
    have hn_ne_zero : n ≠ 0 := by omega
    let i := Nat.log b n
    have hhigh : n < b ^ (i + 1) := by
      simpa [i] using Nat.lt_pow_succ_log_self hb n
    have hupper_nat : n ^ p ≤ (b ^ p) * (b ^ i) ^ p := by
      calc
        n ^ p ≤ (b ^ (i + 1)) ^ p :=
          Nat.pow_le_pow_left (Nat.le_of_lt hhigh) p
        _ = (b ^ p) * (b ^ i) ^ p :=
          pow_succ_pow_eq_mul_pow b i p
    have hupper_real :
        (n : ℝ) ^ p ≤ B * (((b ^ i : ℕ) : ℝ) ^ p) := by
      dsimp [B]
      exact_mod_cast hupper_nat
    have hL_nonneg : 0 ≤ (Nat.log b n : ℝ) + 1 := by positivity
    calc
      B⁻¹ * |polynomialLogScale b p n|
          = B⁻¹ * (((Nat.log b n : ℝ) + 1) * (n : ℝ) ^ p) := by
            rw [polynomialLogScale, polynomialScale,
              abs_of_nonneg
                (mul_nonneg hL_nonneg (pow_nonneg (by positivity) p))]
      _ ≤ B⁻¹ * (((Nat.log b n : ℝ) + 1) *
            (B * (((b ^ i : ℕ) : ℝ) ^ p))) := by
            gcongr
      _ = ((Nat.log b n : ℝ) + 1) * (((b ^ i : ℕ) : ℝ) ^ p) := by
            field_simp [ne_of_gt hB_pos]
      _ = |criticalPowerLogScale (b ^ p) b n| := by
            rw [abs_of_nonneg (criticalPowerLogScale_nonneg (b ^ p) b n)]
            simp [criticalPowerLogScale, criticalPowerScale_of_base_pow, i]

/-! ## Real-logarithmic comparison scales -/

/--
The real-valued exponent {lit}`log_b a = log a / log b`.  This is the exponent that
appears in the standard CLRS Master-theorem statement as {lit}`n^(log_b a)`.

When {lit}`a = b^p` for natural {lit}`p`, this reduces to {lit}`(p : ℝ)`, and the
{name}`criticalPowerScale_isBigTheta_polynomialScale` comparison above is a
special case of the general comparison proved here.
-/
noncomputable def realLogExponent (a b : ℕ) : ℝ :=
  Real.log (a : ℝ) / Real.log (b : ℝ)

/--
The real-log comparison scale {lit}`n^(log_b a)`.  This is the textbook scale used in
the standard CLRS statement of the Master theorem: the homogeneous-solution
growth rate without floors and ceilings.

For integer exponents it coincides with the ordinary polynomial scale
{name}`polynomialScale`.
-/
noncomputable def realLogScale (a b : ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (realLogExponent a b)

/--
The textbook case-2 Master scale {lit}`n^(log_b a) log n`.
-/
noncomputable def realLogLogScale (a b : ℕ) (n : ℕ) : ℝ :=
  realLogScale a b n * Real.log (n : ℝ)

/--
When {lit}`1 ≤ a` and {lit}`1 < b`, the discrete critical-power scale
{lit}`a^(⌊log_b n⌋)` is asymptotically equivalent to the real-log scale
{lit}`n^(log_b a)`.

This is the main bridge between the discrete all-input Master-theorem proof
and the standard CLRS statement in terms of {lit}`n^(log_b a)`.  The constant
factor is at most {lit}`a` in the Ω direction and {lit}`1` in the O direction, so the
asymptotic class is exact.
-/
theorem criticalPowerScale_isBigTheta_realLogScale
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 < b) :
    Chapter03.isBigTheta (criticalPowerScale a b) (realLogScale a b) := by
  have ha1 : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have ha_pos : 0 < (a : ℝ) := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ha1
  have ha_nonneg : 0 ≤ (a : ℝ) := ha_pos.le
  have hb1 : 1 < (b : ℝ) := by exact_mod_cast hb
  have hb_pos : 0 < (b : ℝ) := by exact_mod_cast Nat.lt_trans Nat.zero_lt_one hb
  have hb_nonneg : 0 ≤ (b : ℝ) := hb_pos.le
  have hb_log_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  have hb_log_ne_zero : Real.log (b : ℝ) ≠ 0 := ne_of_gt hb_log_pos
  have ha_log_nonneg : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg ha1
  -- The exponent α = log_b a
  have hα_nonneg : 0 ≤ realLogExponent a b := by
    dsimp [realLogExponent]
    exact div_nonneg ha_log_nonneg hb_log_pos.le
  -- Key identity: b^α = a
  have h_base_identity : (b : ℝ) ^ (realLogExponent a b) = (a : ℝ) := by
    dsimp [realLogExponent]
    calc
      (b : ℝ) ^ (Real.log (a : ℝ) / Real.log (b : ℝ))
          = Real.exp (Real.log (b : ℝ) * (Real.log (a : ℝ) / Real.log (b : ℝ))) := by
        rw [Real.rpow_def_of_pos hb_pos]
      _ = Real.exp (Real.log (a : ℝ)) := by
        field_simp [hb_log_ne_zero]
      _ = (a : ℝ) := Real.exp_log ha_pos
  -- formula for criticalPowerScale as a real power
  have hcrit_formula (n : ℕ) : (criticalPowerScale a b n : ℝ) =
      (a : ℝ) ^ (Nat.log b n : ℝ) := by
    dsimp [criticalPowerScale]
    simp [Real.rpow_natCast]
  constructor
  · -- O direction: criticalPowerScale a b = O(realLogScale a b)
    refine (Chapter03.isBigO_iff _ _).mpr ?_
    refine ⟨1, by norm_num, 1, ?_⟩
    intro n hn
    have hn_ne_zero : n ≠ 0 := by omega
    set k := Nat.log b n with hk_def
    have hpow_le : (b : ℕ) ^ k ≤ n := Nat.pow_log_le_self b hn_ne_zero
    have hpow_le_real : ((b : ℕ) ^ k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow_le
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hcrit_nonneg : 0 ≤ criticalPowerScale a b n := by
      rw [hcrit_formula n]
      exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le a) _
    have hreal_nonneg : 0 ≤ realLogScale a b n := by
      dsimp [realLogScale]
      apply Real.rpow_nonneg hn_nonneg
    set α := realLogExponent a b with hα_def
    -- Core identity: a^k = (b^k)^α
    have hlog_mul : Real.log (b : ℝ) * α = Real.log (a : ℝ) := by
      dsimp [α, realLogExponent]
      field_simp [hb_log_ne_zero]
    have h_key : (a : ℝ) ^ (k : ℝ) = ((b : ℝ) ^ (k : ℝ)) ^ α := by
      calc
        (a : ℝ) ^ (k : ℝ) = Real.exp (Real.log (a : ℝ) * (k : ℝ)) := by
          rw [Real.rpow_def_of_pos ha_pos]
        _ = Real.exp ((k : ℝ) * Real.log (a : ℝ)) := by ring
        _ = Real.exp ((k : ℝ) * (Real.log (b : ℝ) * α)) := by rw [hlog_mul]
        _ = Real.exp ((Real.log (b : ℝ) * α) * (k : ℝ)) := by ring
        _ = Real.exp (Real.log (b : ℝ) * (α * (k : ℝ))) := by ring
        _ = Real.exp (Real.log (b : ℝ) * ((k : ℝ) * α)) := by ring
        _ = (b : ℝ) ^ ((k : ℝ) * α) := by rw [Real.rpow_def_of_pos hb_pos]
        _ = ((b : ℝ) ^ (k : ℝ)) ^ α := by rw [Real.rpow_mul hb_nonneg (k : ℝ) α]
    have hbpow_nonneg : 0 ≤ (b : ℝ) ^ (k : ℝ) :=
      Real.rpow_nonneg hb_nonneg _
    have hbpow_le_n : (b : ℝ) ^ (k : ℝ) ≤ (n : ℝ) := by
      rw [Real.rpow_natCast]
      simpa [Nat.cast_pow] using hpow_le_real
    calc
      |criticalPowerScale a b n| = criticalPowerScale a b n :=
        abs_of_nonneg hcrit_nonneg
      _ = (a : ℝ) ^ (k : ℝ) := by
        rw [hcrit_formula n, hk_def]
      _ = ((b : ℝ) ^ (k : ℝ)) ^ α := by rw [h_key]
      _ ≤ (n : ℝ) ^ α :=
        Real.rpow_le_rpow hbpow_nonneg hbpow_le_n hα_nonneg
      _ = realLogScale a b n := rfl
      _ = |realLogScale a b n| := by rw [abs_of_nonneg hreal_nonneg]
      _ = 1 * |realLogScale a b n| := by ring
  · -- Ω direction: realLogScale a b = O(criticalPowerScale a b)
    have ha_inv_pos : 0 < (a : ℝ)⁻¹ := inv_pos.mpr ha_pos
    refine (Chapter03.isBigOmega_iff _ _).mpr ?_
    refine ⟨(a : ℝ)⁻¹, ha_inv_pos, 1, ?_⟩
    intro n hn
    have hn_ne_zero : n ≠ 0 := by omega
    set k := Nat.log b n with hk_def
    have hpow_lt : n < b ^ (k + 1) := Nat.lt_pow_succ_log_self hb n
    have hcrit_nonneg : 0 ≤ criticalPowerScale a b n := by
      rw [hcrit_formula n]
      exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le a) _
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hreal_nonneg : 0 ≤ realLogScale a b n := by
      dsimp [realLogScale]
      apply Real.rpow_nonneg hn_nonneg
    set α := realLogExponent a b with hα_def
    have hlog_mul : Real.log (b : ℝ) * α = Real.log (a : ℝ) := by
      dsimp [α, realLogExponent]
      field_simp [hb_log_ne_zero]
    have h_key : (a : ℝ) ^ (k : ℝ) = ((b : ℝ) ^ (k : ℝ)) ^ α := by
      calc
        (a : ℝ) ^ (k : ℝ) = Real.exp (Real.log (a : ℝ) * (k : ℝ)) := by
          rw [Real.rpow_def_of_pos ha_pos]
        _ = Real.exp ((k : ℝ) * Real.log (a : ℝ)) := by ring
        _ = Real.exp ((k : ℝ) * (Real.log (b : ℝ) * α)) := by rw [hlog_mul]
        _ = Real.exp ((Real.log (b : ℝ) * α) * (k : ℝ)) := by ring
        _ = Real.exp (Real.log (b : ℝ) * (α * (k : ℝ))) := by ring
        _ = Real.exp (Real.log (b : ℝ) * ((k : ℝ) * α)) := by ring
        _ = (b : ℝ) ^ ((k : ℝ) * α) := by rw [Real.rpow_def_of_pos hb_pos]
        _ = ((b : ℝ) ^ (k : ℝ)) ^ α := by rw [Real.rpow_mul hb_nonneg (k : ℝ) α]
    have hbpow_nonneg : 0 ≤ (b : ℝ) ^ (k : ℝ) :=
      Real.rpow_nonneg hb_nonneg _
    -- n < b^(k+1) in ℕ → (n:ℝ) ≤ (b:ℝ) * (b:ℝ)^(k:ℝ) in ℝ
    have h_n_le_b_mul_bpow : (n : ℝ) ≤ (b : ℝ) * (b : ℝ) ^ (k : ℝ) := by
      have h_n_lt_bpow_succ_nat : n < b ^ (k + 1) := hpow_lt
      have h_n_lt_bpow_succ_real : (n : ℝ) < ((b : ℕ) ^ (k + 1) : ℝ) := by
        exact_mod_cast h_n_lt_bpow_succ_nat
      have h_bpow_succ_eq : ((b : ℕ) ^ (k + 1) : ℝ) = (b : ℝ) * (b : ℝ) ^ (k : ℝ) := by
        simp [pow_succ, Real.rpow_natCast, mul_comm]
      linarith
    -- n^α ≤ (b * b^k)^α = b^α * (b^k)^α = a * a^k = a * criticalPowerScale
    have h_bound : realLogScale a b n ≤ (a : ℝ) * (criticalPowerScale a b n : ℝ) := by
      calc
        realLogScale a b n = (n : ℝ) ^ α := rfl
        _ ≤ ((b : ℝ) * (b : ℝ) ^ (k : ℝ)) ^ α :=
          Real.rpow_le_rpow hn_nonneg h_n_le_b_mul_bpow hα_nonneg
        _ = ((b : ℝ) ^ α) * (((b : ℝ) ^ (k : ℝ)) ^ α) := by
          rw [Real.mul_rpow (z := α) hb_nonneg hbpow_nonneg]
        _ = (a : ℝ) * (((b : ℝ) ^ (k : ℝ)) ^ α) := by rw [h_base_identity]
        _ = (a : ℝ) * ((a : ℝ) ^ (k : ℝ)) := by rw [h_key]
        _ = (a : ℝ) * (criticalPowerScale a b n : ℝ) := by
          rw [hcrit_formula n, hk_def]
    calc
      (a : ℝ)⁻¹ * |realLogScale a b n|
          = (a : ℝ)⁻¹ * realLogScale a b n := by
            rw [abs_of_nonneg hreal_nonneg]
      _ ≤ (a : ℝ)⁻¹ * ((a : ℝ) * (criticalPowerScale a b n : ℝ)) := by
        gcongr
      _ = criticalPowerScale a b n := by
        field_simp [ne_of_gt ha_pos]
      _ = |criticalPowerScale a b n| := by
        rw [abs_of_nonneg hcrit_nonneg]

/--
When {lit}`1 ≤ a` and {lit}`1 < b`, the discrete case-2 scale
{lit}`(⌊log_b n⌋+1)a^(⌊log_b n⌋)` is asymptotically equivalent to the textbook
scale {lit}`n^(log_b a) log n`.
-/
theorem criticalPowerLogScale_isBigTheta_realLogLogScale
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 < b) :
    Chapter03.isBigTheta (criticalPowerLogScale a b) (realLogLogScale a b) := by
  have hb1 : 1 < (b : ℝ) := by exact_mod_cast hb
  have hb_pos_nat : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  have hb_log_pos : 0 < Real.log (b : ℝ) := Real.log_pos hb1
  have hb_log_nonneg : 0 ≤ Real.log (b : ℝ) := hb_log_pos.le
  have hscale := criticalPowerScale_isBigTheta_realLogScale a b ha hb
  constructor
  · rcases (Chapter03.isBigO_iff _ _).mp hscale.1 with
      ⟨Cscale, hCscale_pos, nScale, hScale⟩
    let Clog : ℝ := 2 / Real.log (b : ℝ)
    have hClog_pos : 0 < Clog := by
      dsimp [Clog]
      exact div_pos (by norm_num) hb_log_pos
    refine (Chapter03.isBigO_iff _ _).mpr ?_
    refine ⟨Cscale * Clog, mul_pos hCscale_pos hClog_pos, max nScale b, ?_⟩
    intro n hn
    have hnScale : nScale ≤ n := le_trans (Nat.le_max_left nScale b) hn
    have hnb : b ≤ n := le_trans (Nat.le_max_right nScale b) hn
    have hn_pos_nat : 0 < n := lt_of_lt_of_le hb_pos_nat hnb
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hbn_real : (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnb
    have hlogb_le_logn : Real.log (b : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hb_pos_nat) hbn_real
    have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) :=
      le_trans hb_log_nonneg hlogb_le_logn
    let k := Nat.log b n
    have hk_def : k = Nat.log b n := rfl
    have hpow_le : b ^ k ≤ n := by
      rw [hk_def]
      exact Nat.pow_log_le_self b (ne_of_gt hn_pos_nat)
    have hpow_le_real : ((b : ℕ) ^ k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hpow_le
    have hpow_pos : 0 < ((b : ℕ) ^ k : ℝ) := by
      exact_mod_cast pow_pos hb_pos_nat k
    have hlog_lower := Real.log_le_log hpow_pos hpow_le_real
    have hklog_le : (k : ℝ) * Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
      simpa [Real.log_pow] using hlog_lower
    have hsum :
        ((k : ℝ) + 1) * Real.log (b : ℝ) ≤ 2 * Real.log (n : ℝ) := by
      calc
        ((k : ℝ) + 1) * Real.log (b : ℝ)
            = (k : ℝ) * Real.log (b : ℝ) + Real.log (b : ℝ) := by ring
        _ ≤ Real.log (n : ℝ) + Real.log (n : ℝ) := by gcongr
        _ = 2 * Real.log (n : ℝ) := by ring
    have hdiv := (div_le_div_iff_of_pos_right hb_log_pos).mpr hsum
    have hlog_upper :
        ((k : ℝ) + 1) ≤ Clog * Real.log (n : ℝ) := by
      calc
        (k : ℝ) + 1 =
            (((k : ℝ) + 1) * Real.log (b : ℝ)) / Real.log (b : ℝ) := by
              field_simp [ne_of_gt hb_log_pos]
        _ ≤ (2 * Real.log (n : ℝ)) / Real.log (b : ℝ) := hdiv
        _ = Clog * Real.log (n : ℝ) := by
              dsimp [Clog]
              ring
    have hL_nonneg : 0 ≤ (k : ℝ) + 1 := by positivity
    have hcrit_nonneg : 0 ≤ criticalPowerScale a b n := by
      unfold criticalPowerScale
      positivity
    have hreal_nonneg : 0 ≤ realLogScale a b n := by
      unfold realLogScale
      exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le n) _
    have hscale_bound :
        criticalPowerScale a b n ≤ Cscale * realLogScale a b n := by
      have h := hScale n hnScale
      simpa [abs_of_nonneg hcrit_nonneg, abs_of_nonneg hreal_nonneg] using h
    have hright_nonneg :
        0 ≤ realLogScale a b n * Real.log (n : ℝ) :=
      mul_nonneg hreal_nonneg hlogn_nonneg
    calc
      |criticalPowerLogScale a b n|
          = ((k : ℝ) + 1) * criticalPowerScale a b n := by
            rw [abs_of_nonneg (criticalPowerLogScale_nonneg a b n)]
            simp [criticalPowerLogScale, k, criticalPowerScale]
      _ ≤ ((k : ℝ) + 1) * (Cscale * realLogScale a b n) := by
            gcongr
      _ ≤ (Clog * Real.log (n : ℝ)) * (Cscale * realLogScale a b n) := by
            gcongr
      _ = (Cscale * Clog) * (realLogScale a b n * Real.log (n : ℝ)) := by
            ring
      _ = (Cscale * Clog) * |realLogLogScale a b n| := by
            rw [realLogLogScale, abs_of_nonneg hright_nonneg]
  · rcases (Chapter03.isBigOmega_iff _ _).mp hscale.2 with
      ⟨Cscale, hCscale_pos, nScale, hScale⟩
    let Clog : ℝ := (Real.log (b : ℝ))⁻¹
    have hClog_pos : 0 < Clog := by
      dsimp [Clog]
      exact inv_pos.mpr hb_log_pos
    refine (Chapter03.isBigOmega_iff _ _).mpr ?_
    refine ⟨Cscale * Clog, mul_pos hCscale_pos hClog_pos, max nScale b, ?_⟩
    intro n hn
    have hnScale : nScale ≤ n := le_trans (Nat.le_max_left nScale b) hn
    have hnb : b ≤ n := le_trans (Nat.le_max_right nScale b) hn
    have hn_pos_nat : 0 < n := lt_of_lt_of_le hb_pos_nat hnb
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hbn_real : (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnb
    have hlogb_le_logn : Real.log (b : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hb_pos_nat) hbn_real
    have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) :=
      le_trans hb_log_nonneg hlogb_le_logn
    let k := Nat.log b n
    have hk_def : k = Nat.log b n := rfl
    have hpow_lt : n < b ^ (k + 1) := by
      rw [hk_def]
      exact Nat.lt_pow_succ_log_self hb n
    have hpow_le_real : (n : ℝ) ≤ ((b : ℕ) ^ (k + 1) : ℝ) := by
      exact_mod_cast Nat.le_of_lt hpow_lt
    have hlog_le := Real.log_le_log hn_pos hpow_le_real
    have hlog_upper_by_L :
        Real.log (n : ℝ) ≤ Real.log (b : ℝ) * ((k : ℝ) + 1) := by
      calc
        Real.log (n : ℝ) ≤ ((k : ℝ) + 1) * Real.log (b : ℝ) := by
          simpa [Real.log_pow, Nat.cast_add, add_mul] using hlog_le
        _ = Real.log (b : ℝ) * ((k : ℝ) + 1) := by ring
    have hlog_lower :
        Clog * Real.log (n : ℝ) ≤ (k : ℝ) + 1 := by
      calc
        Clog * Real.log (n : ℝ)
            ≤ Clog * (Real.log (b : ℝ) * ((k : ℝ) + 1)) := by
              gcongr
        _ = (k : ℝ) + 1 := by
              dsimp [Clog]
              field_simp [ne_of_gt hb_log_pos]
    have hL_nonneg : 0 ≤ (k : ℝ) + 1 := by positivity
    have hcrit_nonneg : 0 ≤ criticalPowerScale a b n := by
      unfold criticalPowerScale
      positivity
    have hreal_nonneg : 0 ≤ realLogScale a b n := by
      unfold realLogScale
      exact Real.rpow_nonneg (by exact_mod_cast Nat.zero_le n) _
    have hscale_bound :
        Cscale * realLogScale a b n ≤ criticalPowerScale a b n := by
      have h := hScale n hnScale
      simpa [abs_of_nonneg hcrit_nonneg, abs_of_nonneg hreal_nonneg] using h
    have hright_nonneg :
        0 ≤ realLogScale a b n * Real.log (n : ℝ) :=
      mul_nonneg hreal_nonneg hlogn_nonneg
    calc
      (Cscale * Clog) * |realLogLogScale a b n|
          = (Clog * Real.log (n : ℝ)) *
              (Cscale * realLogScale a b n) := by
            rw [realLogLogScale, abs_of_nonneg hright_nonneg]
            ring
      _ ≤ ((k : ℝ) + 1) * criticalPowerScale a b n := by
            gcongr
      _ = |criticalPowerLogScale a b n| := by
            rw [abs_of_nonneg (criticalPowerLogScale_nonneg a b n)]
            simp [criticalPowerLogScale, k, criticalPowerScale]

/-! ## Floor/ceiling recurrence interfaces -/

/--
All-input floor-division form of the Master-theorem recurrence:
{lit}`T(n) = a T(⌊n / b⌋) + f(n)`.
-/
structure FloorDivideRecurrence (a b : ℕ) (f T : ℕ → ℝ) : Prop where
  step : ∀ n : ℕ, T n = (a : ℝ) * T (n / b) + f n

/--
All-input ceiling-division form of the Master-theorem recurrence:
{lit}`T(n) = a T(⌈n / b⌉) + f(n)`, represented over natural numbers as
{lit}`(n + b - 1) / b`.
-/
structure CeilDivideRecurrence (a b : ℕ) (f T : ℕ → ℝ) : Prop where
  step : ∀ n : ℕ, T n = (a : ℝ) * T ((n + (b - 1)) / b) + f n

theorem pow_succ_div_base {b i : ℕ} (hb : 0 < b) :
    b ^ (i + 1) / b = b ^ i := by
  rw [show b ^ (i + 1) = b * b ^ i by
    rw [pow_succ, Nat.mul_comm]]
  exact Nat.mul_div_right (b ^ i) hb

theorem pow_succ_add_pred_div_base {b i : ℕ} (hb : 0 < b) :
    (b ^ (i + 1) + (b - 1)) / b = b ^ i := by
  apply Nat.div_eq_of_lt_le
  · rw [show b ^ i * b = b ^ (i + 1) by rw [pow_succ]]
    exact Nat.le_add_right _ _
  · rw [Nat.add_mul, one_mul]
    rw [show b ^ i * b = b ^ (i + 1) by rw [pow_succ]]
    omega

theorem exactPowerRecurrence_of_floorDivideRecurrence
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence a b f T) (hb : 0 < b) :
    ExactPowerRecurrence a b f T := by
  refine ⟨?_⟩
  intro i
  rw [h_rec.step (b ^ (i + 1))]
  rw [pow_succ_div_base (b := b) (i := i) hb]

theorem exactPowerRecurrence_of_ceilDivideRecurrence
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence a b f T) (hb : 0 < b) :
    ExactPowerRecurrence a b f T := by
  refine ⟨?_⟩
  intro i
  rw [h_rec.step (b ^ (i + 1))]
  rw [pow_succ_add_pred_div_base (b := b) (i := i) hb]

/--
Eventually every large input can be bounded above by a large enough exact
power, with the comparison scale at that power controlled by the scale at the
original input.
-/
def EventuallyPowerUpperSandwich (b : ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧
    ∀ i₀ : ℕ, ∃ n₀ : ℕ, ∀ n, n ≥ n₀ →
      ∃ i : ℕ, i ≥ i₀ ∧ n ≤ b ^ i ∧ |g (b ^ i)| ≤ A * |g n|

/--
Eventually every large input has a large enough exact power below it, with the
comparison scale at the original input controlled by the scale at that power.
-/
def EventuallyPowerLowerSandwich (b : ℕ) (g : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧
    ∀ i₀ : ℕ, ∃ n₀ : ℕ, ∀ n, n ≥ n₀ →
      ∃ i : ℕ, i ≥ i₀ ∧ b ^ i ≤ n ∧ |g n| ≤ A * |g (b ^ i)|

/-! ## Adjacent powers generate sandwich witnesses -/

/--
Every positive natural input lies between adjacent powers of a base
{lit}`b > 1`.
This is the arithmetic step that CLRS uses implicitly when it extends
exact-power recurrence bounds to all input sizes.
-/
theorem powerInterval_of_pos (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) :
    b ^ Nat.log b n ≤ n ∧ n < b ^ (Nat.log b n + 1) :=
  ⟨Nat.pow_log_le_self b hn, by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hb n⟩

private theorem power_log_ge_step_threshold
    {b step n j₀ : ℕ} (hb : 1 < b)
    (hj₀_step : Nat.log b step + 1 ≤ j₀)
    (hj₀_log : j₀ ≤ Nat.log b n) :
    step ≤ b ^ Nat.log b n := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  have hstep_lt : step < b ^ (Nat.log b step + 1) :=
    Nat.lt_pow_succ_log_self hb step
  have hpow_le :
      b ^ (Nat.log b step + 1) ≤ b ^ Nat.log b n :=
    Nat.pow_le_pow_right hb_pos (Nat.le_trans hj₀_step hj₀_log)
  exact Nat.le_trans (Nat.le_of_lt hstep_lt) hpow_le

/--
Monotone scales with eventual one-step control automatically satisfy the upper
power-sandwich hypothesis: for every large {lit}`n`, choose the next exact
power above it.
-/
theorem eventuallyPowerUpperSandwich_of_powerStep
    (b : ℕ) (g : ℕ → ℝ) (hb : 1 < b)
    (hg_mono : MonotoneAbs g)
    (hg_step : EventuallyPowerStepBound b g) :
    EventuallyPowerUpperSandwich b g := by
  rcases hg_step with ⟨A, hA_pos, step₀, hstep⟩
  refine ⟨A, hA_pos, ?_⟩
  intro i₀
  let j₀ := max i₀ (Nat.log b step₀ + 1)
  refine ⟨b ^ j₀, ?_⟩
  intro n hn
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  have hn_ne_zero : n ≠ 0 := by
    have hpow_pos : 0 < b ^ j₀ := pow_pos hb_pos j₀
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hpow_pos hn)
  have hj₀_log : j₀ ≤ Nat.log b n :=
    Nat.le_log_of_pow_le hb hn
  let i := Nat.log b n + 1
  refine ⟨i, ?_, ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_max_left i₀ (Nat.log b step₀ + 1))
      (Nat.le_trans hj₀_log (Nat.le_succ _))
  · exact Nat.le_of_lt (powerInterval_of_pos b n hb hn_ne_zero).2
  · have hstep_arg : step₀ ≤ b ^ Nat.log b n :=
      power_log_ge_step_threshold (b := b) (step := step₀) (n := n)
        (j₀ := j₀) hb (Nat.le_max_right _ _) hj₀_log
    have hlocal := hstep (b ^ Nat.log b n) hstep_arg
    have hmono_to_n : |g (b ^ Nat.log b n)| ≤ |g n| :=
      hg_mono (Nat.pow_log_le_self b hn_ne_zero)
    calc
      |g (b ^ i)| = |g (b * b ^ Nat.log b n)| := by
        simp [i, pow_succ, Nat.mul_comm]
      _ ≤ A * |g (b ^ Nat.log b n)| := hlocal
      _ ≤ A * |g n| := by
        gcongr

/--
Monotone scales with eventual one-step control automatically satisfy the lower
power-sandwich hypothesis: for every large {lit}`n`, choose the previous exact
power below it.
-/
theorem eventuallyPowerLowerSandwich_of_powerStep
    (b : ℕ) (g : ℕ → ℝ) (hb : 1 < b)
    (hg_mono : MonotoneAbs g)
    (hg_step : EventuallyPowerStepBound b g) :
    EventuallyPowerLowerSandwich b g := by
  rcases hg_step with ⟨A, hA_pos, step₀, hstep⟩
  refine ⟨A, hA_pos, ?_⟩
  intro i₀
  let j₀ := max i₀ (Nat.log b step₀ + 1)
  refine ⟨b ^ j₀, ?_⟩
  intro n hn
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  have hn_ne_zero : n ≠ 0 := by
    have hpow_pos : 0 < b ^ j₀ := pow_pos hb_pos j₀
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hpow_pos hn)
  have hj₀_log : j₀ ≤ Nat.log b n :=
    Nat.le_log_of_pow_le hb hn
  let i := Nat.log b n
  refine ⟨i, ?_, ?_, ?_⟩
  · exact Nat.le_trans (Nat.le_max_left i₀ (Nat.log b step₀ + 1)) hj₀_log
  · exact (powerInterval_of_pos b n hb hn_ne_zero).1
  · have hstep_arg : step₀ ≤ b ^ Nat.log b n :=
      power_log_ge_step_threshold (b := b) (step := step₀) (n := n)
        (j₀ := j₀) hb (Nat.le_max_right _ _) hj₀_log
    have hlocal := hstep (b ^ Nat.log b n) hstep_arg
    have hn_le_next :
        n ≤ b ^ (Nat.log b n + 1) :=
      Nat.le_of_lt (powerInterval_of_pos b n hb hn_ne_zero).2
    calc
      |g n| ≤ |g (b ^ (Nat.log b n + 1))| := hg_mono hn_le_next
      _ = |g (b * b ^ Nat.log b n)| := by
        simp [pow_succ, Nat.mul_comm]
      _ ≤ A * |g (b ^ Nat.log b n)| := hlocal
      _ = A * |g (b ^ i)| := by simp [i]

/-! ## Exact powers to all inputs -/

/--
Transfer an exact-power big-O bound to all natural inputs, provided the cost is
monotone in absolute value and the comparison function admits an eventual upper
power sandwich.
-/
theorem allInput_bigO_of_power_upper_sandwich
    (b : ℕ) (T g : ℕ → ℝ)
    (hT_mono : MonotoneAbs T)
    (hg_sandwich : EventuallyPowerUpperSandwich b g)
    (h_power :
      Chapter03.isBigO
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => g (b ^ i))) :
    Chapter03.isBigO T g := by
  rcases (Chapter03.isBigO_iff
      (fun i : ℕ => T (b ^ i))
      (fun i : ℕ => g (b ^ i))).mp h_power with
    ⟨C, hC_pos, i₀, hC⟩
  rcases hg_sandwich with ⟨A, hA_pos, hA⟩
  rcases hA i₀ with ⟨n₀, hn₀⟩
  refine (Chapter03.isBigO_iff T g).mpr ?_
  refine ⟨C * A, mul_pos hC_pos hA_pos, n₀, ?_⟩
  intro n hn
  rcases hn₀ n hn with ⟨i, hi_ge, hn_le_pow, hg⟩
  calc
    |T n| ≤ |T (b ^ i)| := hT_mono hn_le_pow
    _ ≤ C * |g (b ^ i)| := hC i hi_ge
    _ ≤ C * (A * |g n|) := by
      gcongr
    _ = (C * A) * |g n| := by ring

/--
Transfer an exact-power big-Omega bound to all natural inputs, provided the
cost is monotone in absolute value and the comparison function admits an
eventual lower power sandwich.
-/
theorem allInput_bigOmega_of_power_lower_sandwich
    (b : ℕ) (T g : ℕ → ℝ)
    (hT_mono : MonotoneAbs T)
    (hg_sandwich : EventuallyPowerLowerSandwich b g)
    (h_power :
      Chapter03.isBigOmega
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => g (b ^ i))) :
    Chapter03.isBigOmega T g := by
  rcases (Chapter03.isBigOmega_iff
      (fun i : ℕ => T (b ^ i))
      (fun i : ℕ => g (b ^ i))).mp h_power with
    ⟨c, hc_pos, i₀, hc⟩
  rcases hg_sandwich with ⟨A, hA_pos, hA⟩
  rcases hA i₀ with ⟨n₀, hn₀⟩
  refine (Chapter03.isBigOmega_iff T g).mpr ?_
  refine ⟨c / A, div_pos hc_pos hA_pos, n₀, ?_⟩
  intro n hn
  rcases hn₀ n hn with ⟨i, hi_ge, hpow_le_n, hg⟩
  have hA_ne_zero : A ≠ 0 := ne_of_gt hA_pos
  have hdiv_nonneg : 0 ≤ c / A := (div_pos hc_pos hA_pos).le
  calc
    (c / A) * |g n| ≤ (c / A) * (A * |g (b ^ i)|) := by
      gcongr
    _ = c * |g (b ^ i)| := by
      field_simp [hA_ne_zero]
    _ ≤ |T (b ^ i)| := hc i hi_ge
    _ ≤ |T n| := hT_mono hpow_le_n

/--
Transfer an exact-power big-Theta bound to all natural inputs using both power
sandwich directions.
-/
theorem allInput_bigTheta_of_power_sandwich
    (b : ℕ) (T g : ℕ → ℝ)
    (hT_mono : MonotoneAbs T)
    (hg_upper : EventuallyPowerUpperSandwich b g)
    (hg_lower : EventuallyPowerLowerSandwich b g)
    (h_power :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => g (b ^ i))) :
    Chapter03.isBigTheta T g := by
  exact
    ⟨allInput_bigO_of_power_upper_sandwich b T g hT_mono hg_upper h_power.1,
      allInput_bigOmega_of_power_lower_sandwich b T g hT_mono hg_lower h_power.2⟩

/--
Direct all-input transfer theorem from exact powers using adjacent-power
regularity of the comparison scale.  This packages the CLRS proof step:
choose the exact power immediately below or above an arbitrary input {lit}`n`,
use monotonicity for {lit}`T`, and use one-step regularity for {lit}`g`.
-/
theorem allInput_bigTheta_of_powerStep
    (b : ℕ) (T g : ℕ → ℝ) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (hg_mono : MonotoneAbs g)
    (hg_step : EventuallyPowerStepBound b g)
    (h_power :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => g (b ^ i))) :
    Chapter03.isBigTheta T g :=
  allInput_bigTheta_of_power_sandwich b T g hT_mono
    (eventuallyPowerUpperSandwich_of_powerStep b g hb hg_mono hg_step)
    (eventuallyPowerLowerSandwich_of_powerStep b g hb hg_mono hg_step)
    h_power

/--
Concrete all-input bridge for the first exact-power Master scale.  If the
exact-power sequence {lit}`T(b^i)` is {lit}`Θ(a^i)` and the cost is monotone in
absolute value, then the all-input cost is {lit}`Θ(a^(⌊log_b n⌋))`, represented
by {name}`criticalPowerScale`.

This theorem is intentionally discrete: a later analytic comparison can relate
{name}`criticalPowerScale` to {lit}`n^(log_b a)` when that real-valued scale is
needed.
-/
theorem allInput_bigTheta_of_criticalPowerScale
    (a b : ℕ) (T : ℕ → ℝ) (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_power :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => (a : ℝ) ^ i)) :
    Chapter03.isBigTheta T (criticalPowerScale a b) := by
  have h_power_scale :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => criticalPowerScale a b (b ^ i)) := by
    have hscale :
        (fun i : ℕ => criticalPowerScale a b (b ^ i)) =
          (fun i : ℕ => (a : ℝ) ^ i) := by
      funext i
      exact criticalPowerScale_exactPower a b i hb
    rw [hscale]
    exact h_power
  exact allInput_bigTheta_of_powerStep b T (criticalPowerScale a b) hb
    hT_mono
    (criticalPowerScale_monotoneAbs a b ha)
    (criticalPowerScale_powerStepBound a b ha hb)
    h_power_scale

theorem allInput_bigTheta_of_criticalPowerLogScale
    (a b : ℕ) (T : ℕ → ℝ) (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_power :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => ((i : ℝ) + 1) * ((a : ℝ) ^ i))) :
    Chapter03.isBigTheta T (criticalPowerLogScale a b) := by
  have h_power_scale :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => criticalPowerLogScale a b (b ^ i)) := by
    have hscale :
        (fun i : ℕ => criticalPowerLogScale a b (b ^ i)) =
          (fun i : ℕ => ((i : ℝ) + 1) * ((a : ℝ) ^ i)) := by
      funext i
      exact criticalPowerLogScale_exactPower a b i hb
    rw [hscale]
    exact h_power
  exact allInput_bigTheta_of_powerStep b T (criticalPowerLogScale a b) hb
    hT_mono
    (criticalPowerLogScale_monotoneAbs a b ha)
    (criticalPowerLogScale_powerStepBound a b ha hb)
    h_power_scale

theorem allInput_bigTheta_of_tailDominatedScale
    (a b : ℕ) (f T : ℕ → ℝ) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (hscale_mono : MonotoneAbs (tailDominatedScale a b f))
    (hscale_step : EventuallyPowerStepBound b (tailDominatedScale a b f))
    (h_power :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ =>
          (if i = 0 then 1 else normalizedForcing a b f (i - 1)) *
            ((a : ℝ) ^ i))) :
    Chapter03.isBigTheta T (tailDominatedScale a b f) := by
  have h_power_scale :
      Chapter03.isBigTheta
        (fun i : ℕ => T (b ^ i))
        (fun i : ℕ => tailDominatedScale a b f (b ^ i)) := by
    have hscale :
        (fun i : ℕ => tailDominatedScale a b f (b ^ i)) =
          (fun i : ℕ =>
            (if i = 0 then 1 else normalizedForcing a b f (i - 1)) *
              ((a : ℝ) ^ i)) := by
      funext i
      exact tailDominatedScale_exactPower a b f i hb
    rw [hscale]
    exact h_power
  exact allInput_bigTheta_of_powerStep b T (tailDominatedScale a b f) hb
    hT_mono hscale_mono hscale_step h_power_scale

/-! ## Packaged all-input Master case 1 wrappers -/

/--
All-input wrapper for exact-power Master case 1, using the discrete critical
scale.  This packages three already-proved layers:

* exact-power Master case 1;
* adjacent-power all-input transfer;
* the concrete scale {name}`criticalPowerScale`.
-/
theorem exactPower_allInput_masterCase1_criticalPowerScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (criticalPowerScale a b) := by
  have ha_pos : 0 < (a : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  exact allInput_bigTheta_of_criticalPowerScale a b T ha hb hT_mono
    (master_case1_geometric a b f T h_rec ha_pos h_base_pos h_term_nonneg
      hr_nonneg hr_lt_one hC_pos h_term_upper)

/--
Floor-division all-input Master case 1 wrapper.  The theorem starts from the
all-input recurrence {lit}`T(n) = a T(⌊n/b⌋) + f(n)`, extracts the exact-power
recurrence, applies exact-power case 1, and transfers the result back to every
natural input.
-/
theorem floorDivide_allInput_masterCase1_criticalPowerScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (criticalPowerScale a b) := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  exact exactPower_allInput_masterCase1_criticalPowerScale a b f T
    (exactPowerRecurrence_of_floorDivideRecurrence a b f T h_rec hb_pos)
    ha hb hT_mono h_base_pos h_term_nonneg hr_nonneg hr_lt_one hC_pos
    h_term_upper

/--
Ceiling-division all-input Master case 1 wrapper.  This is the ceiling analogue
of {name}`floorDivide_allInput_masterCase1_criticalPowerScale`, using the
natural-number encoding {lit}`⌈n/b⌉ = (n + b - 1) / b`.
-/
theorem ceilDivide_allInput_masterCase1_criticalPowerScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (criticalPowerScale a b) := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  exact exactPower_allInput_masterCase1_criticalPowerScale a b f T
    (exactPowerRecurrence_of_ceilDivideRecurrence a b f T h_rec hb_pos)
    ha hb hT_mono h_base_pos h_term_nonneg hr_nonneg hr_lt_one hC_pos
    h_term_upper

/--
Exact-power all-input Master case 1 stated in the textbook real-log scale
{lit}`n^(log_b a)`.
-/
theorem exactPower_allInput_masterCase1_realLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (realLogScale a b) := by
  exact Chapter03.isBigTheta_trans
    (exactPower_allInput_masterCase1_criticalPowerScale a b f T h_rec
      ha hb hT_mono h_base_pos h_term_nonneg hr_nonneg hr_lt_one hC_pos
      h_term_upper)
    (criticalPowerScale_isBigTheta_realLogScale a b ha hb)

/--
Floor-division all-input Master case 1 stated in the textbook real-log scale
{lit}`n^(log_b a)`.
-/
theorem floorDivide_allInput_masterCase1_realLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (realLogScale a b) := by
  exact Chapter03.isBigTheta_trans
    (floorDivide_allInput_masterCase1_criticalPowerScale a b f T h_rec
      ha hb hT_mono h_base_pos h_term_nonneg hr_nonneg hr_lt_one hC_pos
      h_term_upper)
    (criticalPowerScale_isBigTheta_realLogScale a b ha hb)

/--
Ceiling-division all-input Master case 1 stated in the textbook real-log scale
{lit}`n^(log_b a)`.
-/
theorem ceilDivide_allInput_masterCase1_realLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (realLogScale a b) := by
  exact Chapter03.isBigTheta_trans
    (ceilDivide_allInput_masterCase1_criticalPowerScale a b f T h_rec
      ha hb hT_mono h_base_pos h_term_nonneg hr_nonneg hr_lt_one hC_pos
      h_term_upper)
    (criticalPowerScale_isBigTheta_realLogScale a b ha hb)

/--
Exact-power all-input Master case 1 specialized to {lit}`a = b^p`, with the
result stated directly as {lit}`Θ(n^p)`.
-/
theorem exactPower_allInput_masterCase1_polynomialScale
    (b p : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence (b ^ p) b f T)
    (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue (b ^ p) b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing (b ^ p) b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing (b ^ p) b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (polynomialScale p) := by
  exact Chapter03.isBigTheta_trans
    (exactPower_allInput_masterCase1_criticalPowerScale (b ^ p) b f T h_rec
      (one_le_base_pow_of_one_lt b p hb) hb hT_mono h_base_pos
      h_term_nonneg hr_nonneg hr_lt_one hC_pos h_term_upper)
    (criticalPowerScale_isBigTheta_polynomialScale b p hb)

/--
Floor-division all-input Master case 1 specialized to {lit}`a = b^p`, with
the result stated directly as {lit}`Θ(n^p)`.
-/
theorem floorDivide_allInput_masterCase1_polynomialScale
    (b p : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence (b ^ p) b f T)
    (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue (b ^ p) b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing (b ^ p) b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing (b ^ p) b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (polynomialScale p) := by
  exact Chapter03.isBigTheta_trans
    (floorDivide_allInput_masterCase1_criticalPowerScale (b ^ p) b f T h_rec
      (one_le_base_pow_of_one_lt b p hb) hb hT_mono h_base_pos
      h_term_nonneg hr_nonneg hr_lt_one hC_pos h_term_upper)
    (criticalPowerScale_isBigTheta_polynomialScale b p hb)

/--
Ceiling-division all-input Master case 1 specialized to {lit}`a = b^p`, with
the result stated directly as {lit}`Θ(n^p)`.
-/
theorem ceilDivide_allInput_masterCase1_polynomialScale
    (b p : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence (b ^ p) b f T)
    (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_pos : 0 < normalizedValue (b ^ p) b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing (b ^ p) b f k)
    {r C : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) (hC_pos : 0 < C)
    (h_term_upper : ∀ k, normalizedForcing (b ^ p) b f k ≤ C * r ^ k) :
    Chapter03.isBigTheta T (polynomialScale p) := by
  exact Chapter03.isBigTheta_trans
    (ceilDivide_allInput_masterCase1_criticalPowerScale (b ^ p) b f T h_rec
      (one_le_base_pow_of_one_lt b p hb) hb hT_mono h_base_pos
      h_term_nonneg hr_nonneg hr_lt_one hC_pos h_term_upper)
    (criticalPowerScale_isBigTheta_polynomialScale b p hb)

/-! ## Packaged all-input Master case 2 wrappers -/

/--
All-input wrapper for exact-power Master case 2, using the discrete
{name}`criticalPowerLogScale`.  This is the all-input analogue of the exact
power theorem {lit}`T(b^i) = Θ((i+1)a^i)`.
-/
theorem exactPower_allInput_masterCase2_criticalPowerLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing a b f k)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C) :
    Chapter03.isBigTheta T (criticalPowerLogScale a b) := by
  have ha_pos : 0 < (a : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  exact allInput_bigTheta_of_criticalPowerLogScale a b T ha hb hT_mono
    (master_case2_constant_forcing a b f T h_rec ha_pos h_base_nonneg
      hc_pos hC_pos h_term_lower h_term_upper)

/--
Floor-division all-input Master case 2 wrapper.  It extracts the exact-power
recurrence from {lit}`T(n) = a T(⌊n/b⌋) + f(n)`, applies exact-power case 2, and
transfers the result to every natural input through the discrete log scale.
-/
theorem floorDivide_allInput_masterCase2_criticalPowerLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing a b f k)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C) :
    Chapter03.isBigTheta T (criticalPowerLogScale a b) := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  exact exactPower_allInput_masterCase2_criticalPowerLogScale a b f T
    (exactPowerRecurrence_of_floorDivideRecurrence a b f T h_rec hb_pos)
    ha hb hT_mono h_base_nonneg hc_pos hC_pos h_term_lower h_term_upper

/--
Ceiling-division all-input Master case 2 wrapper.  This is the ceiling analogue
of {name}`floorDivide_allInput_masterCase2_criticalPowerLogScale`.
-/
theorem ceilDivide_allInput_masterCase2_criticalPowerLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing a b f k)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C) :
    Chapter03.isBigTheta T (criticalPowerLogScale a b) := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  exact exactPower_allInput_masterCase2_criticalPowerLogScale a b f T
    (exactPowerRecurrence_of_ceilDivideRecurrence a b f T h_rec hb_pos)
    ha hb hT_mono h_base_nonneg hc_pos hC_pos h_term_lower h_term_upper

/--
Exact-power all-input Master case 2 stated in the textbook real-log-log scale
{lit}`n^(log_b a) log n`.
-/
theorem exactPower_allInput_masterCase2_realLogLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing a b f k)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C) :
    Chapter03.isBigTheta T (realLogLogScale a b) := by
  exact Chapter03.isBigTheta_trans
    (exactPower_allInput_masterCase2_criticalPowerLogScale a b f T h_rec
      ha hb hT_mono h_base_nonneg hc_pos hC_pos h_term_lower h_term_upper)
    (criticalPowerLogScale_isBigTheta_realLogLogScale a b ha hb)

/--
Floor-division all-input Master case 2 stated in the textbook real-log-log scale
{lit}`n^(log_b a) log n`.
-/
theorem floorDivide_allInput_masterCase2_realLogLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing a b f k)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C) :
    Chapter03.isBigTheta T (realLogLogScale a b) := by
  exact Chapter03.isBigTheta_trans
    (floorDivide_allInput_masterCase2_criticalPowerLogScale a b f T h_rec
      ha hb hT_mono h_base_nonneg hc_pos hC_pos h_term_lower h_term_upper)
    (criticalPowerLogScale_isBigTheta_realLogLogScale a b ha hb)

/--
Ceiling-division all-input Master case 2 stated in the textbook real-log-log
scale {lit}`n^(log_b a) log n`.
-/
theorem ceilDivide_allInput_masterCase2_realLogLogScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing a b f k)
    (h_term_upper : ∀ k, normalizedForcing a b f k ≤ C) :
    Chapter03.isBigTheta T (realLogLogScale a b) := by
  exact Chapter03.isBigTheta_trans
    (ceilDivide_allInput_masterCase2_criticalPowerLogScale a b f T h_rec
      ha hb hT_mono h_base_nonneg hc_pos hC_pos h_term_lower h_term_upper)
    (criticalPowerLogScale_isBigTheta_realLogLogScale a b ha hb)

/--
Exact-power all-input Master case 2 specialized to {lit}`a = b^p`, with the
result stated directly as {lit}`Θ((⌊log_b n⌋+1)n^p)`.
-/
theorem exactPower_allInput_masterCase2_polynomialLogScale
    (b p : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence (b ^ p) b f T)
    (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue (b ^ p) b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing (b ^ p) b f k)
    (h_term_upper : ∀ k, normalizedForcing (b ^ p) b f k ≤ C) :
    Chapter03.isBigTheta T (polynomialLogScale b p) := by
  exact Chapter03.isBigTheta_trans
    (exactPower_allInput_masterCase2_criticalPowerLogScale (b ^ p) b f T h_rec
      (one_le_base_pow_of_one_lt b p hb) hb hT_mono h_base_nonneg
      hc_pos hC_pos h_term_lower h_term_upper)
    (criticalPowerLogScale_isBigTheta_polynomialLogScale b p hb)

/--
Floor-division all-input Master case 2 specialized to {lit}`a = b^p`, with
the result stated directly as {lit}`Θ((⌊log_b n⌋+1)n^p)`.
-/
theorem floorDivide_allInput_masterCase2_polynomialLogScale
    (b p : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence (b ^ p) b f T)
    (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue (b ^ p) b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing (b ^ p) b f k)
    (h_term_upper : ∀ k, normalizedForcing (b ^ p) b f k ≤ C) :
    Chapter03.isBigTheta T (polynomialLogScale b p) := by
  exact Chapter03.isBigTheta_trans
    (floorDivide_allInput_masterCase2_criticalPowerLogScale (b ^ p) b f T h_rec
      (one_le_base_pow_of_one_lt b p hb) hb hT_mono h_base_nonneg
      hc_pos hC_pos h_term_lower h_term_upper)
    (criticalPowerLogScale_isBigTheta_polynomialLogScale b p hb)

/--
Ceiling-division all-input Master case 2 specialized to {lit}`a = b^p`, with
the result stated directly as {lit}`Θ((⌊log_b n⌋+1)n^p)`.
-/
theorem ceilDivide_allInput_masterCase2_polynomialLogScale
    (b p : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence (b ^ p) b f T)
    (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (h_base_nonneg : 0 ≤ normalizedValue (b ^ p) b T 0)
    {c C : ℝ} (hc_pos : 0 < c) (hC_pos : 0 < C)
    (h_term_lower : ∀ k, c ≤ normalizedForcing (b ^ p) b f k)
    (h_term_upper : ∀ k, normalizedForcing (b ^ p) b f k ≤ C) :
    Chapter03.isBigTheta T (polynomialLogScale b p) := by
  exact Chapter03.isBigTheta_trans
    (ceilDivide_allInput_masterCase2_criticalPowerLogScale (b ^ p) b f T h_rec
      (one_le_base_pow_of_one_lt b p hb) hb hT_mono h_base_nonneg
      hc_pos hC_pos h_term_lower h_term_upper)
    (criticalPowerLogScale_isBigTheta_polynomialLogScale b p hb)

/-! ## Packaged all-input Master case 3 wrappers -/

/--
All-input wrapper for exact-power Master case 3, using the discrete
{name}`tailDominatedScale`.  The last-forcing scale depends on the concrete
forcing function, so its monotonicity and adjacent-power regularity are
explicit hypotheses rather than built-in facts.
-/
theorem exactPower_allInput_masterCase3_tailDominatedScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : ExactPowerRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (hscale_mono : MonotoneAbs (tailDominatedScale a b f))
    (hscale_step : EventuallyPowerStepBound b (tailDominatedScale a b f))
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    (h_tail_upper :
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ i, i ≥ n₀ → 1 ≤ i →
        normalizedValue a b T i ≤ C * normalizedForcing a b f (i - 1)) :
    Chapter03.isBigTheta T (tailDominatedScale a b f) := by
  have ha_pos : 0 < (a : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  exact allInput_bigTheta_of_tailDominatedScale a b f T hb hT_mono
    hscale_mono hscale_step
    (master_case3_tail_dominated a b f T h_rec ha_pos h_base_nonneg
      h_term_nonneg h_tail_upper)

/--
Floor-division all-input Master case 3 wrapper.  It extracts the exact-power
recurrence from the all-input floor recurrence, applies the tail-dominated
exact-power theorem, and transfers the result through {name}`tailDominatedScale`.
-/
theorem floorDivide_allInput_masterCase3_tailDominatedScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : FloorDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (hscale_mono : MonotoneAbs (tailDominatedScale a b f))
    (hscale_step : EventuallyPowerStepBound b (tailDominatedScale a b f))
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    (h_tail_upper :
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ i, i ≥ n₀ → 1 ≤ i →
        normalizedValue a b T i ≤ C * normalizedForcing a b f (i - 1)) :
    Chapter03.isBigTheta T (tailDominatedScale a b f) := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  exact exactPower_allInput_masterCase3_tailDominatedScale a b f T
    (exactPowerRecurrence_of_floorDivideRecurrence a b f T h_rec hb_pos)
    ha hb hT_mono hscale_mono hscale_step h_base_nonneg h_term_nonneg
    h_tail_upper

/--
Ceiling-division all-input Master case 3 wrapper.  This is the ceiling analogue
of {name}`floorDivide_allInput_masterCase3_tailDominatedScale`.
-/
theorem ceilDivide_allInput_masterCase3_tailDominatedScale
    (a b : ℕ) (f T : ℕ → ℝ)
    (h_rec : CeilDivideRecurrence a b f T)
    (ha : 1 ≤ a) (hb : 1 < b)
    (hT_mono : MonotoneAbs T)
    (hscale_mono : MonotoneAbs (tailDominatedScale a b f))
    (hscale_step : EventuallyPowerStepBound b (tailDominatedScale a b f))
    (h_base_nonneg : 0 ≤ normalizedValue a b T 0)
    (h_term_nonneg : ∀ k, 0 ≤ normalizedForcing a b f k)
    (h_tail_upper :
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ i, i ≥ n₀ → 1 ≤ i →
        normalizedValue a b T i ≤ C * normalizedForcing a b f (i - 1)) :
    Chapter03.isBigTheta T (tailDominatedScale a b f) := by
  have hb_pos : 0 < b := Nat.lt_trans Nat.zero_lt_one hb
  exact exactPower_allInput_masterCase3_tailDominatedScale a b f T
    (exactPowerRecurrence_of_ceilDivideRecurrence a b f T h_rec hb_pos)
    ha hb hT_mono hscale_mono hscale_step h_base_nonneg h_term_nonneg
    h_tail_upper

end Chapter04
end CLRS
