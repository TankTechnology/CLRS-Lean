import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Correctness
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Costs
import Mathlib.Tactic

/-! # Chapter 30.3: Iterative FFT costs

All counts below are projections of the value-producing bit-reversal and stage
executions.  Data movement is kept separate from field arithmetic.
-/

namespace CLRS
namespace Chapter30

def FFTStageExecution.work (r : FFTStageExecution K k) : Nat :=
  r.addSubtractions + r.multiplications

def IterativeFFTExecution.arithmeticWork
    (r : IterativeFFTExecution K k) : Nat :=
  r.addSubtractions + r.multiplications

def IterativeFFTExecution.totalWork
    (r : IterativeFFTExecution K k) : Nat :=
  r.bitReversalMoves + r.arithmeticWork

@[simp] theorem fftStageExec_addSubtractions [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) (s : Fin k) :
    (fftStageExec omega a s).addSubtractions = 2 ^ k := by
  induction k generalizing omega with
  | zero => exact Fin.elim0 s
  | succ k ih =>
      by_cases h : s.1 = k
      · simp [fftStageExec, h, butterflyLayerExec_addSubtractions, pow_succ]
        omega
      · have hs : s.1 < k := by omega
        simp [fftStageExec, h, ih, pow_succ]
        omega

@[simp] theorem fftStageExec_multiplications [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) (s : Fin k) :
    (fftStageExec omega a s).multiplications = 2 ^ k := by
  induction k generalizing omega with
  | zero => exact Fin.elim0 s
  | succ k ih =>
      by_cases h : s.1 = k
      · simp [fftStageExec, h, butterflyLayerExec_multiplications, pow_succ]
        omega
      · have hs : s.1 < k := by omega
        simp [fftStageExec, h, ih, pow_succ]
        omega

@[simp] theorem runFFTStagePrefixExec_addSubtractions [Ring K]
    {k m : Nat} (omega : K) (a : PowTwoVec K k) (hm : m ≤ k) :
    (runFFTStagePrefixExec omega a m hm).addSubtractions = m * 2 ^ k := by
  induction m with
  | zero => simp [runFFTStagePrefixExec]
  | succ m ih =>
      simp [runFFTStagePrefixExec, ih, Nat.succ_mul]

@[simp] theorem runFFTStagePrefixExec_multiplications [Ring K]
    {k m : Nat} (omega : K) (a : PowTwoVec K k) (hm : m ≤ k) :
    (runFFTStagePrefixExec omega a m hm).multiplications = m * 2 ^ k := by
  induction m with
  | zero => simp [runFFTStagePrefixExec]
  | succ m ih =>
      simp [runFFTStagePrefixExec, ih, Nat.succ_mul]

@[simp] theorem iterativeRadix2FFTExec_bitReversalMoves [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).bitReversalMoves = 2 ^ k := by
  simp [iterativeRadix2FFTExec]

@[simp] theorem iterativeRadix2FFTExec_addSubtractions [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).addSubtractions = k * 2 ^ k := by
  simp [iterativeRadix2FFTExec, runAllFFTStagesExec]

@[simp] theorem iterativeRadix2FFTExec_multiplications [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).multiplications = k * 2 ^ k := by
  simp [iterativeRadix2FFTExec, runAllFFTStagesExec]

theorem iterativeRadix2FFTExec_arithmeticWork [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).arithmeticWork = radix2FFTWork k := by
  simp [IterativeFFTExecution.arithmeticWork, radix2FFTWork, Nat.two_mul]
  rw [Nat.add_mul]

/-- Total iterative work, including one bit-reversal move per element. -/
def iterativeRadix2FFTTotalWork (k : Nat) : Nat :=
  2 ^ k + radix2FFTWork k

@[simp] theorem radix2FFTWork_closed (k : Nat) :
    radix2FFTWork k = 2 * k * 2 ^ k := rfl

@[simp] theorem iterativeRadix2FFTTotalWork_closed (k : Nat) :
    iterativeRadix2FFTTotalWork k = 2 ^ k + 2 * k * 2 ^ k := rfl

theorem iterativeRadix2FFTExec_totalWork [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).totalWork =
      iterativeRadix2FFTTotalWork k := by
  simp [IterativeFFTExecution.totalWork, iterativeRadix2FFTTotalWork,
    iterativeRadix2FFTExec_arithmeticWork]

/-- Bit-reversal moves do not change the exact-power FFT asymptotic scale. -/
theorem iterativeRadix2FFTTotalWork_bigTheta :
    Chapter03.isBigTheta
      (fun k => (iterativeRadix2FFTTotalWork k : ℝ))
      (fun k => (k : ℝ) * (2 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨3, by norm_num, 1, ?_⟩
    intro k hk
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    simp [iterativeRadix2FFTTotalWork, radix2FFTWork]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨2, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (Nat.cast_nonneg _)]
    simp [iterativeRadix2FFTTotalWork, radix2FFTWork]
    have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
    nlinarith

/-- Total iterative work at the least nonempty padded FFT capacity. -/
def paddedIterativeFFTWork (n : Nat) : Nat :=
  fftCapacity n + paddedFFTWork n

theorem paddedIterativeFFTWork_monotone : Monotone paddedIterativeFFTWork := by
  intro m n hmn
  exact Nat.add_le_add (fftCapacity_monotone hmn) (paddedFFTWork_monotone hmn)

/-- Padded total work remains attached to the actual iterative execution. -/
theorem iterativeRadix2FFTExec_zeroPad_totalWork [Ring K] {n : Nat}
    (omega : K) (a : CoeffVector K n) :
    (iterativeRadix2FFTExec (k := fftExponent n) omega
      (zeroPadToFFTCapacity a)).totalWork = paddedIterativeFFTWork n := by
  rw [iterativeRadix2FFTExec_totalWork]
  rfl

private theorem fftExponent_pos_of_two_le {n : Nat} (hn : 2 ≤ n) :
    0 < fftExponent n := by
  rw [fftExponent, max_eq_right (by omega)]
  exact Nat.clog_pos (by norm_num) (by omega)

private theorem fftCapacity_le_paddedFFTWork {n : Nat} (hn : 2 ≤ n) :
    fftCapacity n ≤ paddedFFTWork n := by
  have hexp : 1 ≤ fftExponent n := fftExponent_pos_of_two_le hn
  have hfactor : 1 ≤ 2 * fftExponent n := by omega
  unfold fftCapacity paddedFFTWork radix2FFTWork
  simpa [Nat.mul_assoc] using
    Nat.mul_le_mul_right (2 ^ fftExponent n) hfactor

theorem paddedFFTWork_le_paddedIterativeFFTWork (n : Nat) :
    paddedFFTWork n ≤ paddedIterativeFFTWork n := by
  simp [paddedIterativeFFTWork]

theorem paddedIterativeFFTWork_le_two_mul {n : Nat} (hn : 2 ≤ n) :
    paddedIterativeFFTWork n ≤ 2 * paddedFFTWork n := by
  have hcap := fftCapacity_le_paddedFFTWork hn
  unfold paddedIterativeFFTWork
  omega

private theorem paddedIterativeFFTWork_isBigTheta_paddedFFTWork :
    Chapter03.isBigTheta
      (fun n : Nat => (paddedIterativeFFTWork n : ℝ))
      (fun n : Nat => (paddedFFTWork n : ℝ)) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨2, by norm_num, 2, ?_⟩
    intro n hn
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast paddedIterativeFFTWork_le_two_mul hn
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro n _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    norm_num
    exact_mod_cast paddedFFTWork_le_paddedIterativeFFTWork n

/-- Padding lifts the iterative execution, including bit-reversal moves, to
the all-input textbook linear-logarithmic scale. -/
theorem paddedIterativeFFTWork_allInput_bigTheta :
    Chapter03.isBigTheta
      (fun n : Nat => (paddedIterativeFFTWork n : ℝ))
      (Chapter04.realLogLogScale 2 2) := by
  exact Chapter03.isBigTheta_trans
    paddedIterativeFFTWork_isBigTheta_paddedFFTWork
    paddedFFTWork_allInput_bigTheta

end Chapter30
end CLRS
