import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Correctness
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input
import Mathlib.Data.Nat.Log

/-! # Chapter 30.2: Recursive FFT costs and padding

All exact counts below are projections of `recursiveFFTExec`.  The independent
numeric closed form is introduced only after those execution equations.
-/

namespace CLRS
namespace Chapter30

/-- Work measured by the canonical value-producing FFT execution. -/
def recursiveFFTWork [Ring K] {k : Nat} (omega : K) (a : PowTwoVec K k) : Nat :=
  (recursiveFFTExec omega a).work

/-- The execution charges exactly one lower sum and one upper subtraction per
output at each recursive level. -/
theorem recursiveFFTExec_addSubtractions [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (recursiveFFTExec omega a).addSubtractions = k * 2 ^ k := by
  induction k generalizing omega with
  | zero => rfl
  | succ k ih =>
      simp only [recursiveFFTExec]
      rw [ih, ih]
      simp [butterflyLayerFromTwiddleExec, pow_succ]
      ring

/-- The execution charges every butterfly product and every successive
twiddle update, giving the same exact count as addition/subtraction. -/
theorem recursiveFFTExec_multiplications [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (recursiveFFTExec omega a).multiplications = k * 2 ^ k := by
  induction k generalizing omega with
  | zero => rfl
  | succ k ih =>
      simp only [recursiveFFTExec]
      rw [ih, ih]
      simp [butterflyLayerFromTwiddleExec,
        twiddlePowersAuxExec_multiplications, pow_succ]
      ring

/-- Exact total work of the canonical recursive FFT execution. -/
theorem recursiveFFTWork_exact [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    recursiveFFTWork omega a = 2 * k * 2 ^ k := by
  rw [recursiveFFTWork, FFTExecution.work,
    recursiveFFTExec_addSubtractions, recursiveFFTExec_multiplications]
  ring

/-- Numeric closed form extracted from the execution theorem. -/
def radix2FFTWork (k : Nat) : Nat := 2 * k * 2 ^ k

theorem recursiveFFTWork_eq_radix2FFTWork [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    recursiveFFTWork omega a = radix2FFTWork k := by
  rw [recursiveFFTWork_exact]
  rfl

/-- The exact-power execution work is `Theta(k * 2^k)`. -/
theorem radix2FFTWork_bigTheta :
    Chapter03.isBigTheta
      (fun k => (radix2FFTWork k : ℝ))
      (fun k => (k : ℝ) * (2 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨2, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    norm_num [radix2FFTWork]
    simpa only [mul_assoc] using
      (le_refl ((2 : ℝ) * (k : ℝ) * (2 : ℝ) ^ k))
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨(2 : ℝ), by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    norm_num [radix2FFTWork]
    simpa only [mul_assoc] using
      (le_refl ((2 : ℝ) * (k : ℝ) * (2 : ℝ) ^ k))

/-- Least power-of-two exponent used for total zero padding. -/
def fftExponent (n : Nat) : Nat := Nat.clog 2 (max 1 n)

/-- Nonempty power-of-two transform capacity covering `n`. -/
def fftCapacity (n : Nat) : Nat := 2 ^ fftExponent n

/-- Work of the canonical recursive FFT at the padded capacity. -/
def paddedFFTWork (n : Nat) : Nat := radix2FFTWork (fftExponent n)

/-- Padding never loses an original slot. -/
theorem fftCapacity_ge (n : Nat) : n ≤ fftCapacity n := by
  exact (Nat.le_max_right 1 n).trans
    (Nat.le_pow_clog (by norm_num) (max 1 n))

/-- Every FFT capacity is explicitly a power of two. -/
theorem fftCapacity_isPowerOfTwo (n : Nat) : ∃ k, fftCapacity n = 2 ^ k :=
  ⟨fftExponent n, rfl⟩

/-- FFT capacity is always positive, including at input zero. -/
theorem fftCapacity_pos (n : Nat) : 0 < fftCapacity n := by
  simp [fftCapacity]

/-- Above one, padding uses strictly less than twice the input capacity. -/
theorem fftCapacity_lt_two_mul {n : Nat} (hn : 1 < n) :
    fftCapacity n < 2 * n := by
  have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hn
  have hclog : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) hn
  rw [fftCapacity, fftExponent, max_eq_right (by omega)]
  rw [show Nat.clog 2 n = (Nat.clog 2 n).pred + 1 from
    (Nat.succ_pred_eq_of_pos hclog).symm, pow_succ]
  rw [Nat.mul_comm]
  exact (Nat.mul_lt_mul_left (a := 2) (b := 2 ^ (Nat.clog 2 n).pred)
    (c := n) (by norm_num)).mpr hpred

theorem fftExponent_monotone : Monotone fftExponent := by
  intro m n hmn
  exact Nat.clog_mono_right 2 (max_le_max_left 1 hmn)

theorem fftCapacity_monotone : Monotone fftCapacity := by
  intro m n hmn
  exact Nat.pow_le_pow_right (by norm_num) (fftExponent_monotone hmn)

private theorem radix2FFTWork_monotone : Monotone radix2FFTWork := by
  intro k l hkl
  unfold radix2FFTWork
  have hpow : 2 ^ k ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hkl
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 (Nat.mul_le_mul hkl hpow)

theorem paddedFFTWork_monotone : Monotone paddedFFTWork := by
  intro m n hmn
  exact radix2FFTWork_monotone (fftExponent_monotone hmn)

/-- Padding is exact on power-of-two input sizes. -/
theorem paddedFFTWork_pow (k : Nat) :
    paddedFFTWork (2 ^ k) = 2 * k * 2 ^ k := by
  rw [paddedFFTWork, fftExponent, max_eq_right Nat.one_le_two_pow,
    Nat.clog_pow 2 k (by norm_num)]
  rfl

private theorem paddedFFTWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : Nat => (paddedFFTWork (2 ^ k) : ℝ))
      (fun k : Nat => ((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨2, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    rw [paddedFFTWork_pow]
    push_cast
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 1, ?_⟩
    intro k hk_one
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (Nat.cast_nonneg _)]
    rw [paddedFFTWork_pow]
    push_cast
    have hk : 1 ≤ (k : ℝ) := by exact_mod_cast hk_one
    have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
    nlinarith

/-- Zero padding lifts the exact power-of-two count to the textbook
`Theta(n log n)` scale on every input size. -/
theorem paddedFFTWork_allInput_bigTheta :
    Chapter03.isBigTheta
      (fun n : Nat => (paddedFFTWork n : ℝ))
      (Chapter04.realLogLogScale 2 2) := by
  have hcritical :
      Chapter03.isBigTheta
        (fun n : Nat => (paddedFFTWork n : ℝ))
        (Chapter04.criticalPowerLogScale 2 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerLogScale 2 2
      (fun n : Nat => (paddedFFTWork n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast paddedFFTWork_monotone)
      paddedFFTWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical
    (Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale 2 2
      (by norm_num) (by norm_num))

/-- Zero-pad a vector to its least nonempty power-of-two capacity. -/
def zeroPadToFFTCapacity [Zero K] {n : Nat} (a : CoeffVector K n) :
    CoeffVector K (fftCapacity n) :=
  fun i => if h : i.1 < n then a ⟨i.1, h⟩ else 0

/-- The original coefficient at `i` survives zero padding. -/
theorem zeroPadToFFTCapacity_original [Zero K] {n : Nat}
    (a : CoeffVector K n) (i : Fin n) :
    zeroPadToFFTCapacity a ⟨i.1, i.2.trans_le (fftCapacity_ge n)⟩ = a i := by
  simp [zeroPadToFFTCapacity]

/-- Every added padding slot is zero. -/
theorem zeroPadToFFTCapacity_added [Zero K] {n : Nat}
    (a : CoeffVector K n) (i : Fin (fftCapacity n)) (hi : n ≤ i.1) :
    zeroPadToFFTCapacity a i = 0 := by
  simp [zeroPadToFFTCapacity, Nat.not_lt.mpr hi]

/-- Padded work remains attached to the actual recursive execution. -/
theorem recursiveFFTExec_zeroPad_work [Ring K] {n : Nat}
    (omega : K) (a : CoeffVector K n) :
    (recursiveFFTExec (k := fftExponent n) omega
      (zeroPadToFFTCapacity a)).work = paddedFFTWork n := by
  rw [← recursiveFFTWork]
  rw [recursiveFFTWork_eq_radix2FFTWork]
  rfl

end Chapter30
end CLRS
