import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.BitReversal
import Mathlib.Tactic

/-! # Chapter 30.3: Executable iterative radix-2 FFT

The complete transform folds globally ordered stages over a bit-reversed
vector.  A stage recursively enumerates its independent contiguous blocks and
uses the already verified butterfly execution at each block.
-/

namespace CLRS
namespace Chapter30

/-- Extract the contiguous lower half of a successor-size vector. -/
def lowerHalf {K : Type*} {k : Nat} (a : PowTwoVec K (k + 1)) :
    PowTwoVec K k := fun i => a (lowerHalfIndex i)

/-- Extract the contiguous upper half of a successor-size vector. -/
def upperHalf {K : Type*} {k : Nat} (a : PowTwoVec K (k + 1)) :
    PowTwoVec K k := fun i => a (upperHalfIndex i)

/-- Reading a lower half uses the canonical lower-half embedding. -/
@[simp] theorem lowerHalf_apply {K : Type*} {k : Nat}
    (a : PowTwoVec K (k + 1)) (i : Fin (2 ^ k)) :
    lowerHalf a i = a (lowerHalfIndex i) := rfl

/-- Reading an upper half uses the canonical upper-half embedding. -/
@[simp] theorem upperHalf_apply {K : Type*} {k : Nat}
    (a : PowTwoVec K (k + 1)) (i : Fin (2 ^ k)) :
    upperHalf a i = a (upperHalfIndex i) := rfl

/-- Extracting the lower half of joined vectors returns the lower input. -/
@[simp] theorem lowerHalf_joinHalves {K : Type*} {k : Nat}
    (lower upper : PowTwoVec K k) :
    lowerHalf (joinHalves lower upper) = lower := by
  funext i
  simp [lowerHalf]

/-- Extracting the upper half of joined vectors returns the upper input. -/
@[simp] theorem upperHalf_joinHalves {K : Type*} {k : Nat}
    (lower upper : PowTwoVec K k) :
    upperHalf (joinHalves lower upper) = upper := by
  funext i
  simp [upperHalf]

/-- Value and arithmetic counters for one global iterative FFT stage. -/
structure FFTStageExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  addSubtractions : Nat
  multiplications : Nat

/-- Execute one indexed stage.  The final stage is one full butterfly layer; every
earlier stage acts independently on the two halves with squared root. -/
def fftStageExec [Ring K] :
    {k : Nat} → K → PowTwoVec K k → Fin k → FFTStageExecution K k
  | 0, _, _, s => Fin.elim0 s
  | k + 1, omega, a, s =>
      if hfinal : s.1 = k then
        let layer := butterflyLayerExec omega (lowerHalf a) (upperHalf a)
        ⟨layer.value, layer.addSubtractions, layer.multiplications⟩
      else
        let childStage : Fin k := ⟨s.1, by omega⟩
        let lowerRun := fftStageExec (omega ^ 2) (lowerHalf a) childStage
        let upperRun := fftStageExec (omega ^ 2) (upperHalf a) childStage
        ⟨joinHalves lowerRun.value upperRun.value,
          lowerRun.addSubtractions + upperRun.addSubtractions,
          lowerRun.multiplications + upperRun.multiplications⟩

/-- Value projection of one global stage. -/
def fftStage [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) (s : Fin k) : PowTwoVec K k :=
  (fftStageExec omega a s).value

/-- The final indexed stage is one full butterfly layer. -/
@[simp] theorem fftStage_final [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K (k + 1)) :
    fftStage omega a (Fin.last k) =
      butterflyLayer omega (lowerHalf a) (upperHalf a) := by
  simp [fftStage, fftStageExec, butterflyLayer]

/-- A nonfinal indexed stage acts independently on the two halves. -/
@[simp] theorem fftStage_nonfinal [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K (k + 1)) (s : Fin k) :
    fftStage omega a s.castSucc =
      joinHalves
        (fftStage (omega ^ 2) (lowerHalf a) s)
        (fftStage (omega ^ 2) (upperHalf a) s) := by
  simp [fftStage, fftStageExec, Fin.castSucc, Nat.ne_of_lt s.2]

/-- Value and accumulated counters after an ordered stage prefix. -/
structure FFTStageSequenceExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  addSubtractions : Nat
  multiplications : Nat

/-- Execute the requested initial number of stages in increasing order. -/
def runFFTStagePrefixExec [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) :
    (m : Nat) → m ≤ k → FFTStageSequenceExecution K k
  | 0, _ => ⟨a, 0, 0⟩
  | m + 1, hm =>
      let previous := runFFTStagePrefixExec omega a m (by omega)
      let current := fftStageExec omega previous.value ⟨m, by omega⟩
      ⟨current.value,
        previous.addSubtractions + current.addSubtractions,
        previous.multiplications + current.multiplications⟩

/-- Value projection after an ordered stage prefix. -/
def runFFTStagePrefix [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) (m : Nat) (hm : m ≤ k) : PowTwoVec K k :=
  (runFFTStagePrefixExec omega a m hm).value

/-- The empty ordered stage prefix leaves its input unchanged. -/
@[simp] theorem runFFTStagePrefix_zero [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) (hm : 0 ≤ k) :
    runFFTStagePrefix omega a 0 hm = a := rfl

/-- Extending a stage prefix applies the next admissible stage. -/
theorem runFFTStagePrefix_succ [Ring K] {k m : Nat} (omega : K)
    (a : PowTwoVec K k) (hm : m + 1 ≤ k) :
    runFFTStagePrefix omega a (m + 1) hm =
      fftStage omega
        (runFFTStagePrefix omega a m (by omega)) ⟨m, by omega⟩ := rfl

/-- Execute all admissible stages. -/
def runAllFFTStagesExec [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) : FFTStageSequenceExecution K k :=
  runFFTStagePrefixExec omega a k le_rfl

/-- Value projection after all stages. -/
def runAllFFTStages [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  (runAllFFTStagesExec omega a).value

/-- A complete successor-size run ends with the final stage. -/
theorem runAllFFTStages_succ [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K (k + 1)) :
    runAllFFTStages omega a =
      fftStage omega
        (runFFTStagePrefix omega a k (Nat.le_succ k)) (Fin.last k) := by
  exact runFFTStagePrefix_succ omega a le_rfl

/-- Result and counters of bit reversal followed by all ordered stages. -/
structure IterativeFFTExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  bitReversalMoves : Nat
  addSubtractions : Nat
  multiplications : Nat

/-- The functional iterative radix-2 FFT execution. -/
def iterativeRadix2FFTExec [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) : IterativeFFTExecution K k :=
  let reversal := bitReverseExec a
  let stages := runAllFFTStagesExec omega reversal.value
  ⟨stages.value, reversal.moves,
    stages.addSubtractions, stages.multiplications⟩

/-- Value projection of the iterative radix-2 execution. -/
def iterativeRadix2FFT [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  (iterativeRadix2FFTExec omega a).value

/-- The iterative FFT is bit-reversal followed by all ordered stages. -/
theorem iterativeRadix2FFT_eq_runAll [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) :
    iterativeRadix2FFT omega a =
      runAllFFTStages omega (bitReverseCopy a) := rfl

/-- Erasing iterative execution counters yields the public transform value. -/
theorem iterativeRadix2FFTExec_value [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) :
    (iterativeRadix2FFTExec omega a).value =
      iterativeRadix2FFT omega a := rfl

/-- The singleton iterative transform is the identity. -/
@[simp] theorem iterativeRadix2FFT_zero [Ring K] (omega : K)
    (a : PowTwoVec K 0) :
    iterativeRadix2FFT omega a = a := by
  funext i
  have hi : i = ⟨0, by norm_num⟩ := Fin.ext (by omega)
  subst i
  rfl

end Chapter30
end CLRS
