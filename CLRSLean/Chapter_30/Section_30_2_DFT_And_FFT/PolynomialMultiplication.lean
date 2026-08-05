import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Costs

/-! # Chapter 30.2: FFT polynomial multiplication

The generic pipeline below composes three actual recursive FFT executions,
one pointwise-product execution, and one inverse-scaling execution.  Its
counters charge field additions/subtractions and multiplications.  Coefficient
reads, finite-index bookkeeping, primitive-root certificates, and polynomial
reconstruction are outside this arithmetic-operation metric.
-/

namespace CLRS
namespace Chapter30

open Polynomial

/-- Polynomial result and arithmetic counters of the FFT multiplication
pipeline. -/
structure FFTMultiplicationExecution (K : Type*) [Semiring K] where
  value : Polynomial K
  addSubtractions : Nat
  multiplications : Nat

/-- Total charged field arithmetic of an FFT multiplication execution. -/
def FFTMultiplicationExecution.work [Semiring K]
    (r : FFTMultiplicationExecution K) : Nat :=
  r.addSubtractions + r.multiplications

/-- Pointwise scalar multiplication, used for inverse-transform scaling. -/
def scaleVectorExec [Mul K] {n : Nat} (c : K) (a : CoeffVector K n) :
    VectorArithmeticExecution K n :=
  ⟨fun i => c * a i, 0, n⟩

/-- Inverse scaling charges exactly one multiplication per output slot. -/
theorem scaleVectorExec_work_exact [Mul K] {n : Nat}
    (c : K) (a : CoeffVector K n) :
    (scaleVectorExec c a).work = n := by
  simp [scaleVectorExec, VectorArithmeticExecution.work]

/-- The canonical fixed-capacity FFT multiplication execution. -/
noncomputable def fftMultiplyExecAt [Field K] {k : Nat} (omega : K)
    (p q : K[X]) : FFTMultiplicationExecution K :=
  let a := coeffVector (2 ^ k) p
  let b := coeffVector (2 ^ k) q
  let leftRun := recursiveFFTExec omega a
  let rightRun := recursiveFFTExec omega b
  let productRun := pointwiseMulExec leftRun.value rightRun.value
  let inverseRun := recursiveFFTExec omega⁻¹ productRun.value
  let scaleRun := scaleVectorExec ((2 ^ k : Nat) : K)⁻¹ inverseRun.value
  ⟨vectorToPolynomial scaleRun.value,
    leftRun.addSubtractions + rightRun.addSubtractions +
      inverseRun.addSubtractions + productRun.additions + scaleRun.additions,
    leftRun.multiplications + rightRun.multiplications +
      inverseRun.multiplications + productRun.multiplications +
      scaleRun.multiplications⟩

/-- Value projection of fixed-capacity FFT multiplication. -/
noncomputable def fftMultiplyAt [Field K] {k : Nat} (omega : K)
    (p q : K[X]) : K[X] :=
  (fftMultiplyExecAt (k := k) omega p q).value

/-- Public erasure equation for the costed multiplication execution. -/
theorem fftMultiplyExecAt_value [Field K] {k : Nat} (omega : K)
    (p q : K[X]) :
    (fftMultiplyExecAt (k := k) omega p q).value =
      fftMultiplyAt (k := k) omega p q := rfl

/-- The vector produced by the actual execution is the semantic inverse-DFT
pipeline.  This isolates all counter fields from polynomial correctness. -/
theorem fftMultiplyExecAt_vector_semantics [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k)) (p q : K[X]) :
    let a := coeffVector (2 ^ k) p
    let b := coeffVector (2 ^ k) q
    let leftRun := recursiveFFTExec omega a
    let rightRun := recursiveFFTExec omega b
    let productRun := pointwiseMulExec leftRun.value rightRun.value
    let inverseRun := recursiveFFTExec omega⁻¹ productRun.value
    let scaleRun := scaleVectorExec ((2 ^ k : Nat) : K)⁻¹ inverseRun.value
    scaleRun.value =
      idft omega (pointwiseMul (dft omega a) (dft omega b)) := by
  dsimp only
  change recursiveIFFT omega
      (pointwiseMul (recursiveFFT omega (coeffVector (2 ^ k) p))
        (recursiveFFT omega (coeffVector (2 ^ k) q))) =
    idft omega
      (pointwiseMul (dft omega (coeffVector (2 ^ k) p))
        (dft omega (coeffVector (2 ^ k) q)))
  rw [recursiveIFFT_eq_idft homega,
    recursiveFFT_eq_dft homega, recursiveFFT_eq_dft homega]

/-- Fixed-capacity FFT multiplication is exact whenever the product fits in
the declared transform capacity. -/
theorem fftMultiplyAt_correct [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (p q : K[X])
    (hfit : (p * q).degree < ((2 ^ k : Nat) : WithBot Nat)) :
    fftMultiplyAt (k := k) omega p q = p * q := by
  rw [fftMultiplyAt, fftMultiplyExecAt]
  dsimp only
  rw [fftMultiplyExecAt_vector_semantics homega p q]
  rw [idft_pointwiseMul (by positivity) homega]
  calc
    vectorToPolynomial
          (cyclicConvolution (by positivity)
            (coeffVector (2 ^ k) p) (coeffVector (2 ^ k) q)) =
        vectorToPolynomial (coeffVector (2 ^ k) (p * q)) := by
          congr 1
          exact cyclicConvolution_eq_coeffVector_mul
            (by positivity) p q hfit
    _ = p * q := vectorToPolynomial_coeffVector (p * q) hfit

/-- A support-bound wrapper deriving the minimal no-wrap premise from operand
degree bounds and a declared capacity. -/
theorem fftMultiplyAt_correct_of_degree_lt [Field K] [CharZero K]
    {k m n : Nat} {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (p q : K[X]) (hp : p.degree < m) (hq : q.degree < n)
    (hcapacity : m + n ≤ 2 ^ k) :
    fftMultiplyAt (k := k) omega p q = p * q := by
  apply fftMultiplyAt_correct homega p q
  by_cases hp0 : p = 0
  · subst p
    simp only [zero_mul, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  by_cases hq0 : q = 0
  · subst q
    simp only [mul_zero, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  have hpnat : p.natDegree < m :=
    (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
  have hqnat : q.natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hq
  have hpq0 : p * q ≠ 0 := mul_ne_zero hp0 hq0
  apply (Polynomial.natDegree_lt_iff_degree_lt hpq0).mp
  rw [Polynomial.natDegree_mul hp0 hq0]
  omega

/-! ## Arbitrary-input complex wrapper -/

/-- Positive coefficient capacity associated with a polynomial, including the
zero polynomial. -/
def polySize [Semiring K] (p : K[X]) : Nat :=
  p.natDegree + 1

theorem polySize_pos [Semiring K] (p : K[X]) : 0 < polySize p := by
  simp [polySize]

/-- A symmetric positive size sufficient for multiplying two operands. -/
def multiplicationInputSize [Semiring K] (p q : K[X]) : Nat :=
  2 * max (polySize p) (polySize q)

theorem multiplicationInputSize_pos [Semiring K] (p q : K[X]) :
    0 < multiplicationInputSize p q := by
  have hmax : 0 < max (polySize p) (polySize q) :=
    (polySize_pos p).trans_le (Nat.le_max_left _ _)
  simp [multiplicationInputSize, hmax]

/-- Every polynomial fits in its positive coefficient-size convention. -/
theorem degree_lt_polySize [Semiring K] (p : K[X]) :
    p.degree < ((polySize p : Nat) : WithBot Nat) := by
  by_cases hp : p = 0
  · subst p
    simp [polySize]
  · apply (Polynomial.natDegree_lt_iff_degree_lt hp).mp
    simp [polySize]

/-- The symmetric wrapper size strictly exceeds the product degree, including
zero and constant operands. -/
theorem mul_degree_lt_multiplicationInputSize [Semiring K] (p q : K[X]) :
    (p * q).degree <
      ((multiplicationInputSize p q : Nat) : WithBot Nat) := by
  have hnat :
      (p * q).natDegree < multiplicationInputSize p q := by
    calc
      (p * q).natDegree ≤ p.natDegree + q.natDegree :=
        Polynomial.natDegree_mul_le
      _ < 2 * max (polySize p) (polySize q) := by
        have hpmax : p.natDegree + 1 ≤ max (polySize p) (polySize q) := by
          simpa [polySize] using Nat.le_max_left (polySize p) (polySize q)
        have hqmax : q.natDegree + 1 ≤ max (polySize p) (polySize q) := by
          simpa [polySize] using Nat.le_max_right (polySize p) (polySize q)
        omega
      _ = multiplicationInputSize p q := rfl
  exact (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hnat))

/-- Least radix-2 exponent selected by the complex convenience wrapper. -/
def complexFFTExponent (p q : ℂ[X]) : Nat :=
  fftExponent (multiplicationInputSize p q)

/-- Power-of-two transform capacity selected by the complex wrapper. -/
def complexFFTCapacity (p q : ℂ[X]) : Nat :=
  2 ^ complexFFTExponent p q

theorem complexFFTCapacity_pos (p q : ℂ[X]) :
    0 < complexFFTCapacity p q := by
  simp [complexFFTCapacity]

/-- The automatically chosen complex capacity contains the entire product. -/
theorem complex_product_fits (p q : ℂ[X]) :
    (p * q).degree <
      ((complexFFTCapacity p q : Nat) : WithBot Nat) := by
  exact (mul_degree_lt_multiplicationInputSize p q).trans_le
    (by
      exact_mod_cast (fftCapacity_ge (multiplicationInputSize p q)))

/-- Positive-sign principal root matching the generic DFT convention. -/
noncomputable def complexFFTRoot (p q : ℂ[X]) : ℂ :=
  Complex.exp
    (2 * Real.pi * Complex.I / (complexFFTCapacity p q : ℂ))

theorem complexFFTRoot_isPrimitive (p q : ℂ[X]) :
    IsPrimitiveRoot (complexFFTRoot p q) (complexFFTCapacity p q) := by
  simpa [complexFFTRoot] using
    Complex.isPrimitiveRoot_exp (complexFFTCapacity p q)
      (Nat.ne_of_gt (complexFFTCapacity_pos p q))

/-- Arbitrary-input exact complex polynomial multiplication. -/
noncomputable def complexFFTMultiply (p q : ℂ[X]) : ℂ[X] :=
  fftMultiplyAt (k := complexFFTExponent p q) (complexFFTRoot p q) p q

/-- The complex wrapper constructs a sufficient capacity and primitive root
internally, so callers need no fit premise. -/
theorem complexFFTMultiply_correct (p q : ℂ[X]) :
    complexFFTMultiply p q = p * q := by
  apply fftMultiplyAt_correct (complexFFTRoot_isPrimitive p q)
  exact complex_product_fits p q

/-! ## Execution-attached multiplication costs -/

/-- Exact-capacity composition: two forward FFTs, one inverse-root FFT, one
pointwise product per slot, and one inverse-scale product per slot. -/
def radix2FFTMultiplyWork (k : Nat) : Nat :=
  3 * radix2FFTWork k + 2 * 2 ^ k

/-- The work field of the actual multiplication execution equals the numeric
composition; no pipeline stage is charged by a detached recurrence. -/
theorem fftMultiplyExecAt_work_exact [Field K] {k : Nat}
    (omega : K) (p q : K[X]) :
    (fftMultiplyExecAt (k := k) omega p q).work =
      radix2FFTMultiplyWork k := by
  simp [fftMultiplyExecAt, FFTMultiplicationExecution.work,
    radix2FFTMultiplyWork, recursiveFFTExec_addSubtractions,
    recursiveFFTExec_multiplications, pointwiseMulExec, scaleVectorExec,
    radix2FFTWork]
  ring

/-- Transform exponent charged for two operands each advertised with
coefficient capacity `n`. -/
def fftMultiplyExponent (n : Nat) : Nat :=
  fftExponent (2 * max 1 n)

/-- Declared all-input arithmetic cost.  Every operand with `degree < n` is
charged at this capacity, even if its leading coefficients vanish. -/
def fftMultiplyWork (n : Nat) : Nat :=
  radix2FFTMultiplyWork (fftMultiplyExponent n)

/-- The actual execution selected for advertised operand capacity `n`. -/
noncomputable def fftMultiplyExecution [Field K] (n : Nat) (omega : K)
    (p q : K[X]) : FFTMultiplicationExecution K :=
  fftMultiplyExecAt (k := fftMultiplyExponent n) omega p q

/-- The declared cost is exactly the work field of the selected execution. -/
theorem fftMultiplyExecution_work_eq [Field K] (n : Nat) (omega : K)
    (p q : K[X]) :
    (fftMultiplyExecution n omega p q).work = fftMultiplyWork n := by
  exact fftMultiplyExecAt_work_exact omega p q

/-- Correctness and cost use the same selected execution for bounded
operands. -/
theorem fftMultiplyExecution_correct [Field K] [CharZero K] {n : Nat}
    {omega : K}
    (homega : IsPrimitiveRoot omega (2 ^ fftMultiplyExponent n))
    (p q : K[X]) (hp : p.degree < n) (hq : q.degree < n) :
    (fftMultiplyExecution n omega p q).value = p * q := by
  rw [fftMultiplyExecution, fftMultiplyExecAt_value]
  apply fftMultiplyAt_correct_of_degree_lt (m := n) (n := n) homega p q hp hq
  have hnmax : n ≤ max 1 n := Nat.le_max_right 1 n
  exact (by omega : n + n ≤ 2 * max 1 n) |>.trans
    (fftCapacity_ge (2 * max 1 n))

private theorem radix2FFTMultiplyWork_monotone :
    Monotone radix2FFTMultiplyWork := by
  intro k l hkl
  have hpow : 2 ^ k ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hkl
  have hfft : radix2FFTWork k ≤ radix2FFTWork l := by
    unfold radix2FFTWork
    simpa [Nat.mul_assoc] using
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul hkl hpow)
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 3 hfft) (Nat.mul_le_mul_left 2 hpow)

theorem fftMultiplyExponent_monotone : Monotone fftMultiplyExponent := by
  intro m n hmn
  exact fftExponent_monotone
    (Nat.mul_le_mul_left 2 (max_le_max_left 1 hmn))

theorem fftMultiplyWork_monotone : Monotone fftMultiplyWork := by
  intro m n hmn
  exact radix2FFTMultiplyWork_monotone
    (fftMultiplyExponent_monotone hmn)

theorem fftMultiplyExponent_pow (k : Nat) :
    fftMultiplyExponent (2 ^ k) = k + 1 := by
  rw [fftMultiplyExponent, max_eq_right Nat.one_le_two_pow]
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by
    simp [pow_succ, Nat.mul_comm]]
  rw [fftExponent, max_eq_right Nat.one_le_two_pow,
    Nat.clog_pow 2 (k + 1) (by norm_num)]

/-- Closed form of multiplication work at advertised power-of-two operand
capacity.  The linear pointwise/scaling term is retained explicitly. -/
theorem fftMultiplyWork_pow (k : Nat) :
    fftMultiplyWork (2 ^ k) = (12 * k + 16) * 2 ^ k := by
  rw [fftMultiplyWork, fftMultiplyExponent_pow]
  simp [radix2FFTMultiplyWork, radix2FFTWork, pow_succ]
  ring

private theorem fftMultiplyWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k : Nat => (fftMultiplyWork (2 ^ k) : ℝ))
      (fun k : Nat => ((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
  constructor
  · refine (Chapter03.isBigO_iff _ _).mpr ⟨16, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
    rw [fftMultiplyWork_pow]
    push_cast
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
    have hkp : 0 ≤ (k : ℝ) * (2 : ℝ) ^ k := mul_nonneg hk hpow
    nlinarith
  · refine (Chapter03.isBigOmega_iff _ _).mpr ⟨1, by norm_num, 0, ?_⟩
    intro k _
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (Nat.cast_nonneg _)]
    rw [fftMultiplyWork_pow]
    push_cast
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpow : 0 ≤ (2 : ℝ) ^ k := by positivity
    have hkp : 0 ≤ (k : ℝ) * (2 : ℝ) ^ k := mul_nonneg hk hpow
    nlinarith

/-- Fixed-capacity FFT multiplication has all-input `Theta(n log n)` charged
field arithmetic. -/
theorem fftMultiplyWork_allInput_bigTheta :
    Chapter03.isBigTheta
      (fun n : Nat => (fftMultiplyWork n : ℝ))
      (Chapter04.realLogLogScale 2 2) := by
  have hcritical :
      Chapter03.isBigTheta
        (fun n : Nat => (fftMultiplyWork n : ℝ))
        (Chapter04.criticalPowerLogScale 2 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerLogScale 2 2
      (fun n : Nat => (fftMultiplyWork n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast fftMultiplyWork_monotone)
      fftMultiplyWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical
    (Chapter04.criticalPowerLogScale_isBigTheta_realLogLogScale 2 2
      (by norm_num) (by norm_num))

end Chapter30
end CLRS
