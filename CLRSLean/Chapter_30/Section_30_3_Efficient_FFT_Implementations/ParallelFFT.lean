import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Costs
import Mathlib.Tactic

/-! # Chapter 30.3: Layered parallel FFT network

The network exposes one typed layer per iterative stage and one typed position
per independent butterfly.  Twiddle powers are fixed circuit constants;
bit-reversal is wiring rather than an arithmetic gate.
-/

namespace CLRS
namespace Chapter30

/-- A butterfly is identified by its contiguous block and its within-half
offset at one stage. -/
abbrev FFTButterflyPosition (k : Nat) (s : Fin k) :=
  Fin (2 ^ (k - s.1 - 1)) × Fin (2 ^ s.1)

/-- One logical butterfly layer of the canonical network. -/
structure FFTLayer (K : Type*) (k : Nat) where
  omega : K
  stage : Fin k

def fftLayer (omega : K) {k : Nat} (s : Fin k) : FFTLayer K k :=
  ⟨omega, s⟩

/-- The stage root used by every block in this layer. -/
def FFTLayer.root [Monoid K] (layer : FFTLayer K k) : K :=
  layer.omega ^ (2 ^ (k - layer.stage.1 - 1))

/-- The fixed twiddle constant at one butterfly position. -/
def FFTLayer.twiddle [Monoid K] (layer : FFTLayer K k)
    (position : FFTButterflyPosition k layer.stage) : K :=
  layer.root ^ position.2.1

/-- A typed family of logical FFT layers. -/
structure FFTNetwork (K : Type*) (k : Nat) where
  layers : Fin k → FFTLayer K k

/-- The canonical network contains the ordered stages for one supplied root. -/
def fftNetwork {K : Type*} {k : Nat} (omega : K) : FFTNetwork K k :=
  ⟨fun s => fftLayer omega s⟩

/-- Evaluate the requested prefix of a typed network. -/
def FFTNetwork.evalPrefix [Ring K] (network : FFTNetwork K k)
    (a : PowTwoVec K k) : (m : Nat) → m ≤ k → PowTwoVec K k
  | 0, _ => a
  | m + 1, hm =>
      let previous := network.evalPrefix a m (by omega)
      let layer := network.layers ⟨m, by omega⟩
      fftStage layer.omega previous layer.stage

/-- Evaluate all arithmetic layers, without bit-reversal wiring. -/
def FFTNetwork.evalLayers [Ring K] (network : FFTNetwork K k)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  network.evalPrefix a k le_rfl

/-- Evaluate bit-reversal wiring followed by all arithmetic layers. -/
def FFTNetwork.eval [Ring K] (network : FFTNetwork K k)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  network.evalLayers (bitReverseCopy a)

private theorem fftNetwork_evalPrefix [Ring K] {k m : Nat} (omega : K)
    (a : PowTwoVec K k) (hm : m ≤ k) :
    (fftNetwork omega).evalPrefix a m hm =
      runFFTStagePrefix omega a m hm := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change fftStage omega
          ((fftNetwork omega).evalPrefix a m (by omega)) ⟨m, by omega⟩ =
        fftStage omega
          (runFFTStagePrefix omega a m (by omega)) ⟨m, by omega⟩
      rw [ih]

theorem fftNetwork_evalLayers [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) :
    (fftNetwork omega).evalLayers a = runAllFFTStages omega a := by
  exact fftNetwork_evalPrefix omega a le_rfl

/-- The explicit canonical network evaluates to the iterative FFT. -/
theorem fftNetwork_eval [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) :
    (fftNetwork omega).eval a = iterativeRadix2FFT omega a := by
  rw [FFTNetwork.eval, fftNetwork_evalLayers,
    iterativeRadix2FFT_eq_runAll]

/-- Number of independent butterflies represented by one layer. -/
def FFTLayer.butterflyCount (layer : FFTLayer K k) : Nat :=
  Fintype.card (FFTButterflyPosition k layer.stage)

/-- Sum of butterfly positions across all layers. -/
def FFTNetwork.butterflyCount (network : FFTNetwork K k) : Nat :=
  ∑ s : Fin k, (network.layers s).butterflyCount

theorem fftLayer_butterflyCount {K : Type*} {k : Nat}
    (omega : K) (s : Fin k) :
    (fftLayer omega s).butterflyCount = 2 ^ (k - 1) := by
  simp [FFTLayer.butterflyCount, FFTButterflyPosition]
  rw [← pow_add]
  congr 1
  omega

/-- A length-`2^k` FFT network has `k * 2^(k-1)` butterflies. -/
theorem fftNetwork_butterflyCount {K : Type*} {k : Nat} (omega : K) :
    (fftNetwork omega : FFTNetwork K k).butterflyCount =
      k * 2 ^ (k - 1) := by
  change (∑ s : Fin k, (fftLayer omega s).butterflyCount) =
    k * 2 ^ (k - 1)
  simp [fftLayer_butterflyCount]

/-- Logical depth measured in complete butterfly layers. -/
def FFTNetwork.butterflyDepth (_network : FFTNetwork K k) : Nat := k

/-- One multiplication and two addition/subtraction gates per butterfly. -/
def FFTNetwork.primitiveGateCount (network : FFTNetwork K k) : Nat :=
  3 * network.butterflyCount

/-- Each butterfly layer expands to a multiplication level followed by an
addition/subtraction level. -/
def FFTNetwork.primitiveDepth (network : FFTNetwork K k) : Nat :=
  2 * network.butterflyDepth

@[simp] theorem fftNetwork_butterflyDepth {K : Type*} {k : Nat} (omega : K) :
    (fftNetwork (k := k) omega).butterflyDepth = k := rfl

theorem fftNetwork_primitiveGateCount {K : Type*} {k : Nat} (omega : K) :
    (fftNetwork (k := k) omega).primitiveGateCount =
      3 * k * 2 ^ (k - 1) := by
  rw [FFTNetwork.primitiveGateCount, fftNetwork_butterflyCount]
  simp [Nat.mul_assoc]

@[simp] theorem fftNetwork_primitiveDepth {K : Type*} {k : Nat} (omega : K) :
    (fftNetwork (k := k) omega).primitiveDepth = 2 * k := rfl

end Chapter30
end CLRS
