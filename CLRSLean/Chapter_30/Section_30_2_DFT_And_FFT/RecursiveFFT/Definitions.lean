import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S3_InversionAndConvolution
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-! # Chapter 30.2: Executable recursive radix-2 FFT

The execution below generates twiddles successively, reuses that same trace to
obtain the child root, and records arithmetic operations in the value-producing
recursion.
-/

namespace CLRS
namespace Chapter30

/-- A successor power-of-two length splits into two equal halves. -/
private theorem powTwo_succ_split (k : Nat) :
    2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [pow_succ]
  omega

/-- Embed a half-size index as an even full-size coefficient index. -/
def evenIndex {k : Nat} (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 * i.1, by
    have := i.2
    simp [pow_succ]
    omega⟩

/-- Embed a half-size index as an odd full-size coefficient index. -/
def oddIndex {k : Nat} (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  ⟨2 * i.1 + 1, by
    have := i.2
    simp [pow_succ]
    omega⟩

/-- The natural value of an embedded even coefficient index. -/
@[simp] theorem evenIndex_val {k : Nat} (i : Fin (2 ^ k)) :
    (evenIndex i).1 = 2 * i.1 := rfl

/-- The natural value of an embedded odd coefficient index. -/
@[simp] theorem oddIndex_val {k : Nat} (i : Fin (2 ^ k)) :
    (oddIndex i).1 = 2 * i.1 + 1 := rfl

/-- The even-indexed coefficient half. -/
def evenCoeffs {K : Type*} {k : Nat} (a : PowTwoVec K (k + 1)) :
    PowTwoVec K k := fun i => a (evenIndex i)

/-- The odd-indexed coefficient half. -/
def oddCoeffs {K : Type*} {k : Nat} (a : PowTwoVec K (k + 1)) :
    PowTwoVec K k := fun i => a (oddIndex i)

/-- Reading the even coefficient half uses the corresponding even index. -/
@[simp] theorem evenCoeffs_apply {K : Type*} {k : Nat}
    (a : PowTwoVec K (k + 1)) (i : Fin (2 ^ k)) :
    evenCoeffs a i = a (evenIndex i) := rfl

/-- Reading the odd coefficient half uses the corresponding odd index. -/
@[simp] theorem oddCoeffs_apply {K : Type*} {k : Nat}
    (a : PowTwoVec K (k + 1)) (i : Fin (2 ^ k)) :
    oddCoeffs a i = a (oddIndex i) := rfl

/-- Reassociate the successor power-of-two index type into two halves. -/
def powTwoSuccEquiv (k : Nat) :
    Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k + 2 ^ k) :=
  finCongr (powTwo_succ_split k)

/-- Index into the lower half of a successor power-of-two vector. -/
def lowerHalfIndex {k : Nat} (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  (powTwoSuccEquiv k).symm (Fin.castAdd (2 ^ k) i)

/-- Index into the upper half of a successor power-of-two vector. -/
def upperHalfIndex {k : Nat} (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  (powTwoSuccEquiv k).symm (Fin.natAdd (2 ^ k) i)

/-- The lower-half embedding preserves the natural index value. -/
@[simp] theorem lowerHalfIndex_val {k : Nat} (i : Fin (2 ^ k)) :
    (lowerHalfIndex i).1 = i.1 := by
  simp [lowerHalfIndex, powTwoSuccEquiv]

/-- The upper-half embedding offsets the natural index by the half length. -/
@[simp] theorem upperHalfIndex_val {k : Nat} (i : Fin (2 ^ k)) :
    (upperHalfIndex i).1 = 2 ^ k + i.1 := by
  simp [upperHalfIndex, powTwoSuccEquiv]
  omega

/-- Join two equal power-of-two halves without leaking casts downstream. -/
def joinHalves {K : Type*} {k : Nat} (lower upper : PowTwoVec K k) :
    PowTwoVec K (k + 1) :=
  fun i => Fin.append lower upper (powTwoSuccEquiv k i)

/-- Reading the lower embedding of joined vectors returns the lower input. -/
@[simp] theorem joinHalves_lower {K : Type*} {k : Nat}
    (lower upper : PowTwoVec K k) (i : Fin (2 ^ k)) :
    joinHalves lower upper (lowerHalfIndex i) = lower i := by
  simp [joinHalves, lowerHalfIndex, powTwoSuccEquiv]

/-- Reading the upper embedding of joined vectors returns the upper input. -/
@[simp] theorem joinHalves_upper {K : Type*} {k : Nat}
    (lower upper : PowTwoVec K k) (i : Fin (2 ^ k)) :
    joinHalves lower upper (upperHalfIndex i) = upper i := by
  change Fin.append lower upper (Fin.natAdd (2 ^ k) i) = upper i
  exact Fin.append_right lower upper i

/-- A successive twiddle-generation execution.  `next` is the accumulator
after the last charged multiplication. -/
structure TwiddleExecution (K : Type*) where
  value : List K
  next : K
  multiplications : Nat

/-- Generate `n` successive values, charging every accumulator update. -/
def twiddlePowersAuxExec [Monoid K] (omega : K) :
    Nat → K → TwiddleExecution K
  | 0, current => ⟨[], current, 0⟩
  | n + 1, current =>
      let child := twiddlePowersAuxExec omega n (current * omega)
      ⟨current :: child.value, child.next, child.multiplications + 1⟩

/-- Value projection of the successive twiddle generator. -/
def twiddlePowersAux [Monoid K] (omega : K) (n : Nat) (current : K) : List K :=
  (twiddlePowersAuxExec omega n current).value

/-- Successive twiddle generation returns exactly the requested number of values. -/
theorem twiddlePowersAuxExec_length [Monoid K]
    (omega : K) (n : Nat) (current : K) :
    (twiddlePowersAuxExec omega n current).value.length = n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih => simp [twiddlePowersAuxExec, ih]

/-- The value-only twiddle generator has the requested length. -/
theorem twiddlePowersAux_length [Monoid K]
    (omega : K) (n : Nat) (current : K) :
    (twiddlePowersAux omega n current).length = n :=
  twiddlePowersAuxExec_length omega n current

/-- Successive twiddle generation charges one multiplication per output. -/
theorem twiddlePowersAuxExec_multiplications [Monoid K]
    (omega : K) (n : Nat) (current : K) :
    (twiddlePowersAuxExec omega n current).multiplications = n := by
  induction n generalizing current with
  | zero => rfl
  | succ n ih => simp [twiddlePowersAuxExec, ih]

/-- The final twiddle accumulator is the initial value times `omega ^ n`. -/
private theorem twiddlePowersAuxExec_next [Monoid K]
    (omega : K) (n : Nat) (current : K) :
    (twiddlePowersAuxExec omega n current).next = current * omega ^ n := by
  induction n generalizing current with
  | zero => simp [twiddlePowersAuxExec]
  | succ n ih =>
      simp [twiddlePowersAuxExec, ih, pow_succ', mul_assoc]

/-- Every generated twiddle equals the corresponding successive power. -/
private theorem twiddlePowersAuxExec_get [Monoid K]
    (omega : K) (n : Nat) (current : K) (i : Nat) (hi : i < n) :
    (twiddlePowersAuxExec omega n current).value.getD i current =
      current * omega ^ i := by
  induction n generalizing current i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [twiddlePowersAuxExec]
      | succ i =>
          simp only [twiddlePowersAuxExec, List.getD_cons_succ]
          have hlen :
              (twiddlePowersAuxExec omega n (current * omega)).value.length = n :=
            twiddlePowersAuxExec_length omega n (current * omega)
          have hi' :
              i < (twiddlePowersAuxExec omega n (current * omega)).value.length := by
            omega
          rw [List.getD_eq_getElem _ _ hi']
          rw [← List.getD_eq_getElem _ (current * omega) hi']
          rw [ih (current * omega) i (by omega)]
          simp [pow_succ', mul_assoc]

/-- Convert a checked twiddle trace to a fixed-capacity vector. -/
def twiddleVectorOfExecution {K : Type*} (run : TwiddleExecution K) {n : Nat}
    (hlen : run.value.length = n) : CoeffVector K n :=
  fun i => run.value.get (Fin.cast hlen.symm i)

/-- The first `n` powers, obtained from one successive generator execution. -/
def twiddlePowers [Monoid K] (omega : K) (n : Nat) : CoeffVector K n :=
  let run := twiddlePowersAuxExec omega n 1
  twiddleVectorOfExecution run (twiddlePowersAuxExec_length omega n 1)

/-- The checked twiddle vector contains the first successive powers of `omega`. -/
theorem twiddlePowers_eq_pow [Monoid K]
    (omega : K) (n : Nat) (i : Fin n) :
    twiddlePowers omega n i = omega ^ i.1 := by
  change (twiddlePowersAuxExec omega n (1 : K)).value.get
      (Fin.cast (twiddlePowersAuxExec_length omega n 1).symm i) = omega ^ i.1
  rw [← List.getD_eq_get
    (twiddlePowersAuxExec omega n (1 : K)).value 1
    (Fin.cast (twiddlePowersAuxExec_length omega n 1).symm i)]
  simpa using twiddlePowersAuxExec_get omega n (1 : K) i.1 i.2

/-- Recover the squared child root from the charged twiddle trace. -/
def twiddleChildRoot [One K] (k : Nat) (_omega : K)
    (run : TwiddleExecution K) : K :=
  if k = 0 then 1 else run.value.getD 2 run.next

/-- A positive-size twiddle trace exposes the squared root used by child FFTs. -/
theorem twiddleChildRoot_eq_square [Monoid K] {k : Nat} (hk : 0 < k)
    (omega : K) :
    twiddleChildRoot k omega (twiddlePowersAuxExec omega (2 ^ k) 1) =
      omega ^ 2 := by
  rw [twiddleChildRoot, if_neg (Nat.ne_of_gt hk)]
  by_cases hlen : 2 < 2 ^ k
  · have hactual :
        2 < (twiddlePowersAuxExec omega (2 ^ k) (1 : K)).value.length := by
      simpa [twiddlePowersAuxExec_length] using hlen
    rw [List.getD_eq_getElem _ _ hactual]
    rw [← List.getD_eq_getElem _ (1 : K) hactual]
    rw [twiddlePowersAuxExec_get omega (2 ^ k) (1 : K) 2 hlen]
    simp
  · have hk_le_one : k ≤ 1 := by
      by_contra hnot
      have htwo : 2 ≤ k := by omega
      have hp : 2 ^ 2 ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by omega) htwo
      norm_num at hp
      omega
    have hkone : k = 1 := by omega
    subst k
    simp [twiddlePowersAuxExec, pow_two]

/-- One radix-2 butterfly layer and its actual arithmetic counters. -/
structure ButterflyExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K (k + 1)
  addSubtractions : Nat
  multiplications : Nat

/-- Consume a previously evaluated twiddle trace in a butterfly layer. -/
def butterflyLayerFromTwiddleExec [Ring K] {k : Nat} (omega : K)
    (twiddleRun : TwiddleExecution K)
    (hrun : twiddleRun = twiddlePowersAuxExec omega (2 ^ k) 1)
    (u v : PowTwoVec K k) : ButterflyExecution K k :=
  let w := twiddleVectorOfExecution twiddleRun
    (by simpa [hrun] using twiddlePowersAuxExec_length omega (2 ^ k) 1)
  ⟨joinHalves
      (fun j => u j + w j * v j)
      (fun j => u j - w j * v j),
    2 * 2 ^ k,
    2 ^ k + twiddleRun.multiplications⟩

/-- Execute one standalone butterfly layer, including twiddle generation. -/
def butterflyLayerExec [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) : ButterflyExecution K k :=
  let twiddleRun := twiddlePowersAuxExec omega (2 ^ k) 1
  butterflyLayerFromTwiddleExec omega twiddleRun rfl u v

/-- Value projection of one butterfly execution. -/
def butterflyLayer [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) : PowTwoVec K (k + 1) :=
  (butterflyLayerExec omega u v).value

/-- The canonical checked execution vector is the public twiddle vector. -/
private theorem twiddleVectorOfExecution_canonical [Monoid K]
    (omega : K) (n : Nat) :
    twiddleVectorOfExecution (twiddlePowersAuxExec omega n 1)
      (twiddlePowersAuxExec_length omega n 1) = twiddlePowers omega n := rfl

/-- The lower butterfly output is the sum with its twiddle product. -/
@[simp] theorem butterflyLayer_lower [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) (j : Fin (2 ^ k)) :
    butterflyLayer omega u v (lowerHalfIndex j) =
      u j + omega ^ j.1 * v j := by
  simp [butterflyLayer, butterflyLayerExec, butterflyLayerFromTwiddleExec,
    twiddleVectorOfExecution_canonical, twiddlePowers_eq_pow]

/-- The upper butterfly output is the difference with its twiddle product. -/
@[simp] theorem butterflyLayer_upper [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) (j : Fin (2 ^ k)) :
    butterflyLayer omega u v (upperHalfIndex j) =
      u j - omega ^ j.1 * v j := by
  simp [butterflyLayer, butterflyLayerExec, butterflyLayerFromTwiddleExec,
    twiddleVectorOfExecution_canonical, twiddlePowers_eq_pow]

/-- A butterfly layer charges two additions/subtractions per local offset. -/
theorem butterflyLayerExec_addSubtractions [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) :
    (butterflyLayerExec omega u v).addSubtractions = 2 * 2 ^ k := rfl

/-- A butterfly layer charges data products and successive twiddle updates. -/
theorem butterflyLayerExec_multiplications [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) :
    (butterflyLayerExec omega u v).multiplications = 2 * 2 ^ k := by
  simp [butterflyLayerExec, butterflyLayerFromTwiddleExec,
    twiddlePowersAuxExec_multiplications]
  omega

/-- Result and counters of the canonical recursive FFT. -/
structure FFTExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  addSubtractions : Nat
  multiplications : Nat

/-- Total charged arithmetic operations. -/
def FFTExecution.work (r : FFTExecution K k) : Nat :=
  r.addSubtractions + r.multiplications

/-- The canonical radix-2 execution.  Its child root is extracted from the
same twiddle trace consumed by the butterfly. -/
def recursiveFFTExec [Ring K] :
    {k : Nat} → K → PowTwoVec K k → FFTExecution K k
  | 0, _, a => ⟨a, 0, 0⟩
  | k + 1, omega, a =>
      let twiddleRun := twiddlePowersAuxExec omega (2 ^ k) 1
      let childRoot := twiddleChildRoot k omega twiddleRun
      let evenRun := recursiveFFTExec childRoot (evenCoeffs a)
      let oddRun := recursiveFFTExec childRoot (oddCoeffs a)
      let layer := butterflyLayerFromTwiddleExec omega twiddleRun rfl
        evenRun.value oddRun.value
      ⟨layer.value,
        evenRun.addSubtractions + oddRun.addSubtractions + layer.addSubtractions,
        evenRun.multiplications + oddRun.multiplications + layer.multiplications⟩

/-- Value projection of the canonical recursive execution. -/
def recursiveFFT [Ring K] {k : Nat} (omega : K) (a : PowTwoVec K k) :
    PowTwoVec K k :=
  (recursiveFFTExec omega a).value

/-- Erasing the counters of a recursive execution yields the public FFT value. -/
theorem recursiveFFTExec_value [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    (recursiveFFTExec omega a).value = recursiveFFT omega a := rfl

/-- Recursive inverse FFT: inverse-root recursive FFT followed by scaling. -/
def recursiveIFFT [Field K] {k : Nat} (omega : K) (a : PowTwoVec K k) :
    PowTwoVec K k :=
  fun i => ((2 ^ k : Nat) : K)⁻¹ * recursiveFFT omega⁻¹ a i

end Chapter30
end CLRS
