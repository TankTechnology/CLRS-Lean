import CLRSLean.FourthEdition.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Costs
import Mathlib.Tactic

/-! # Chapter 30.3: Layered parallel FFT network

The network exposes one typed layer per iterative stage.  Each layer stores a
recursive stage circuit whose leaves are actual butterfly gates with fixed
twiddle constants; evaluation, butterfly count, and depth all interpret that
same syntax.  Bit-reversal is wiring rather than an arithmetic gate.
-/

namespace CLRS
namespace Chapter30

/-- One logical radix-2 butterfly with a fixed twiddle constant. -/
structure FFTButterflyGate (K : Type*) where
  twiddle : K

/-- Evaluate one logical butterfly on its lower and upper inputs. -/
def FFTButterflyGate.eval [Ring K] (gate : FFTButterflyGate K)
    (u v : K) : K × K :=
  let product := gate.twiddle * v
  (u + product, u - product)

/-- A complete local butterfly layer, with one actual gate at every offset. -/
structure ButterflyLayerCircuit (K : Type*) (k : Nat) where
  gates : Fin (2 ^ k) → FFTButterflyGate K

/-- Evaluate every stored gate in a local butterfly layer in parallel. -/
def ButterflyLayerCircuit.eval [Ring K] (layer : ButterflyLayerCircuit K k)
    (u v : PowTwoVec K k) : PowTwoVec K (k + 1) :=
  joinHalves
    (fun j => (layer.gates j).eval (u j) (v j) |>.1)
    (fun j => (layer.gates j).eval (u j) (v j) |>.2)

/-- The canonical local layer stores twiddle `omega ^ j` at gate `j`. -/
def canonicalButterflyLayerCircuit [Monoid K] (omega : K) (k : Nat) :
    ButterflyLayerCircuit K k :=
  ⟨fun j => ⟨omega ^ j.1⟩⟩

/-- Joining the two extracted halves reconstructs the original vector. -/
private theorem joinHalves_lowerHalf_upperHalf {K : Type*} {k : Nat}
    (a : PowTwoVec K (k + 1)) :
    joinHalves (lowerHalf a) (upperHalf a) = a := by
  funext i
  have h : ∀ t : Fin (2 ^ k + 2 ^ k),
      joinHalves (lowerHalf a) (upperHalf a) ((powTwoSuccEquiv k).symm t) =
        a ((powTwoSuccEquiv k).symm t) := by
    intro t
    refine Fin.addCases ?_ ?_ t
    · intro j
      exact joinHalves_lower (lowerHalf a) (upperHalf a) j
    · intro j
      exact joinHalves_upper (lowerHalf a) (upperHalf a) j
  simpa using h (powTwoSuccEquiv k i)

/-- Equality of both contiguous halves determines a successor-size vector. -/
private theorem powTwoVec_eq_of_halves {K : Type*} {k : Nat}
    {a b : PowTwoVec K (k + 1)}
    (hlower : lowerHalf a = lowerHalf b)
    (hupper : upperHalf a = upperHalf b) : a = b := by
  rw [← joinHalves_lowerHalf_upperHalf a,
    ← joinHalves_lowerHalf_upperHalf b, hlower, hupper]

/-- Evaluating the canonical stored gates is exactly the verified butterfly
layer from the recursive FFT. -/
theorem canonicalButterflyLayerCircuit_eval [Ring K] {k : Nat} (omega : K)
    (u v : PowTwoVec K k) :
    (canonicalButterflyLayerCircuit omega k).eval u v =
      butterflyLayer omega u v := by
  apply powTwoVec_eq_of_halves
  · funext j
    simp [ButterflyLayerCircuit.eval, canonicalButterflyLayerCircuit,
      FFTButterflyGate.eval]
  · funext j
    simp [ButterflyLayerCircuit.eval, canonicalButterflyLayerCircuit,
      FFTButterflyGate.eval]

/-- Syntax for one global FFT stage: either one complete local butterfly layer,
or two equal-depth stage circuits evaluated independently on the two halves. -/
inductive FFTStageCircuit (K : Type*) : Nat → Type _
  | butterfly {k : Nat} (layer : ButterflyLayerCircuit K k) :
      FFTStageCircuit K (k + 1)
  | parallel {k : Nat} (lower upper : FFTStageCircuit K k) :
      FFTStageCircuit K (k + 1)

/-- Evaluate the stored syntax of one global FFT stage. -/
def FFTStageCircuit.eval [Ring K] :
    {k : Nat} → FFTStageCircuit K k → PowTwoVec K k → PowTwoVec K k
  | _, .butterfly layer, a => layer.eval (lowerHalf a) (upperHalf a)
  | _, .parallel lower upper, a =>
      joinHalves (lower.eval (lowerHalf a)) (upper.eval (upperHalf a))

/-- Number of actual logical butterflies stored in a local gate family. -/
def ButterflyLayerCircuit.butterflyCount
    (_layer : ButterflyLayerCircuit K k) : Nat :=
  Fintype.card (Fin (2 ^ k))

/-- Structural butterfly count of one stage circuit. -/
def FFTStageCircuit.butterflyCount : {k : Nat} → FFTStageCircuit K k → Nat
  | _, .butterfly layer => layer.butterflyCount
  | _, .parallel lower upper => lower.butterflyCount + upper.butterflyCount

/-- Structural butterfly depth of one stage circuit. -/
def FFTStageCircuit.butterflyDepth : {k : Nat} → FFTStageCircuit K k → Nat
  | _, .butterfly _ => 1
  | _, .parallel lower upper => max lower.butterflyDepth upper.butterflyDepth

/-- Construct the canonical stored circuit for one globally indexed stage. -/
def fftStageCircuit [Monoid K] :
    {k : Nat} → K → Fin k → FFTStageCircuit K k
  | 0, _, s => Fin.elim0 s
  | k + 1, omega, s =>
      if hfinal : s.1 = k then
        .butterfly (canonicalButterflyLayerCircuit omega k)
      else
        let childStage : Fin k := ⟨s.1, by omega⟩
        .parallel (fftStageCircuit (omega ^ 2) childStage)
          (fftStageCircuit (omega ^ 2) childStage)

/-- The canonical stored stage circuit evaluates to the verified iterative
stage semantics. -/
theorem fftStageCircuit_eval [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K k) (s : Fin k) :
    (fftStageCircuit omega s).eval a = fftStage omega a s := by
  induction k generalizing omega with
  | zero => exact Fin.elim0 s
  | succ k ih =>
      by_cases hfinal : s.1 = k
      · have hs : s = Fin.last k := Fin.ext hfinal
        subst s
        simp [fftStageCircuit, FFTStageCircuit.eval,
          canonicalButterflyLayerCircuit_eval]
      · let childStage : Fin k := Fin.castLT s (by omega)
        have hs : childStage.castSucc = s := Fin.ext rfl
        rw [← hs]
        simp [fftStageCircuit, FFTStageCircuit.eval, ih,
          Nat.ne_of_lt childStage.2]

/-- Every canonical global stage stores exactly `2^(k-1)` butterflies. -/
theorem fftStageCircuit_butterflyCount {K : Type*} [Monoid K] {k : Nat}
    (omega : K) (s : Fin k) :
    (fftStageCircuit omega s).butterflyCount = 2 ^ (k - 1) := by
  induction k generalizing omega with
  | zero => exact Fin.elim0 s
  | succ k ih =>
      by_cases hfinal : s.1 = k
      · simp [fftStageCircuit, hfinal, FFTStageCircuit.butterflyCount,
          ButterflyLayerCircuit.butterflyCount]
      · have hk : 0 < k := by omega
        let childStage : Fin k := Fin.castLT s (by omega)
        have hs : childStage.castSucc = s := Fin.ext rfl
        rw [← hs]
        simp [fftStageCircuit, FFTStageCircuit.butterflyCount, ih,
          Nat.ne_of_lt childStage.2]
        have hk1 : 1 ≤ k := hk
        calc
          2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ (k - 1) * 2 := by omega
          _ = 2 ^ ((k - 1) + 1) := by rw [pow_succ]
          _ = 2 ^ k := by rw [Nat.sub_add_cancel hk1]

/-- Every canonical global stage has one butterfly layer of structural depth. -/
theorem fftStageCircuit_butterflyDepth {K : Type*} [Monoid K] {k : Nat}
    (omega : K) (s : Fin k) :
    (fftStageCircuit omega s).butterflyDepth = 1 := by
  induction k generalizing omega with
  | zero => exact Fin.elim0 s
  | succ k ih =>
      by_cases hfinal : s.1 = k
      · simp [fftStageCircuit, hfinal, FFTStageCircuit.butterflyDepth]
      · let childStage : Fin k := Fin.castLT s (by omega)
        have hs : childStage.castSucc = s := Fin.ext rfl
        rw [← hs]
        simp [fftStageCircuit, FFTStageCircuit.butterflyDepth, ih,
          Nat.ne_of_lt childStage.2]

/-- A butterfly is identified by its contiguous block and its within-half
offset at one stage. -/
abbrev FFTButterflyPosition (k : Nat) (s : Fin k) :=
  Fin (2 ^ (k - s.1 - 1)) × Fin (2 ^ s.1)

/-- One logical butterfly layer of the canonical network. -/
structure FFTLayer (K : Type*) (k : Nat) where
  omega : K
  stage : Fin k
  circuit : FFTStageCircuit K k

/-- Construct the canonical stored layer for one stage. -/
def fftLayer [Monoid K] (omega : K) {k : Nat} (s : Fin k) : FFTLayer K k :=
  ⟨omega, s, fftStageCircuit omega s⟩

/-- Evaluate the actual stage circuit stored by a layer. -/
def FFTLayer.eval [Ring K] (layer : FFTLayer K k)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  layer.circuit.eval a

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
def fftNetwork {K : Type*} [Monoid K] {k : Nat} (omega : K) : FFTNetwork K k :=
  ⟨fun s => fftLayer omega s⟩

/-- Evaluate the requested prefix of a typed network. -/
def FFTNetwork.evalPrefix [Ring K] (network : FFTNetwork K k)
    (a : PowTwoVec K k) : (m : Nat) → m ≤ k → PowTwoVec K k
  | 0, _ => a
  | m + 1, hm =>
      let previous := network.evalPrefix a m (by omega)
      let layer := network.layers ⟨m, by omega⟩
      layer.eval previous

/-- Evaluate all arithmetic layers, without bit-reversal wiring. -/
def FFTNetwork.evalLayers [Ring K] (network : FFTNetwork K k)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  network.evalPrefix a k le_rfl

/-- Evaluate bit-reversal wiring followed by all arithmetic layers. -/
def FFTNetwork.eval [Ring K] (network : FFTNetwork K k)
    (a : PowTwoVec K k) : PowTwoVec K k :=
  network.evalLayers (bitReverseCopy a)

/-- Every canonical circuit prefix agrees with the functional stage prefix. -/
private theorem fftNetwork_evalPrefix [Ring K] {k m : Nat} (omega : K)
    (a : PowTwoVec K k) (hm : m ≤ k) :
    (fftNetwork omega).evalPrefix a m hm =
      runFFTStagePrefix omega a m hm := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change (fftStageCircuit omega ⟨m, by omega⟩).eval
          ((fftNetwork omega).evalPrefix a m (by omega)) =
        fftStage omega
          (runFFTStagePrefix omega a m (by omega)) ⟨m, by omega⟩
      rw [fftStageCircuit_eval, ih]

/-- Evaluating all canonical arithmetic layers agrees with all FFT stages. -/
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
  layer.circuit.butterflyCount

/-- Sum of butterfly positions across all layers. -/
def FFTNetwork.butterflyCount (network : FFTNetwork K k) : Nat :=
  ∑ s : Fin k, (network.layers s).butterflyCount

/-- Every canonical layer stores the exact per-stage butterfly count. -/
theorem fftLayer_butterflyCount {K : Type*} [Monoid K] {k : Nat}
    (omega : K) (s : Fin k) :
    (fftLayer omega s).butterflyCount = 2 ^ (k - 1) := by
  exact fftStageCircuit_butterflyCount omega s

/-- A length-`2^k` FFT network has `k * 2^(k-1)` butterflies. -/
theorem fftNetwork_butterflyCount {K : Type*} [Monoid K] {k : Nat} (omega : K) :
    (fftNetwork omega : FFTNetwork K k).butterflyCount =
      k * 2 ^ (k - 1) := by
  change (∑ s : Fin k, (fftLayer omega s).butterflyCount) =
    k * 2 ^ (k - 1)
  simp [fftLayer_butterflyCount]

/-- Logical depth of one stored stage circuit. -/
def FFTLayer.butterflyDepth (layer : FFTLayer K k) : Nat :=
  layer.circuit.butterflyDepth

/-- Logical depth obtained by composing the stored layer circuits. -/
def FFTNetwork.butterflyDepth (network : FFTNetwork K k) : Nat :=
  ∑ s : Fin k, (network.layers s).butterflyDepth

/-- One multiplication and two addition/subtraction gates per butterfly. -/
def FFTNetwork.primitiveGateCount (network : FFTNetwork K k) : Nat :=
  3 * network.butterflyCount

/-- Each butterfly layer expands to a multiplication level followed by an
addition/subtraction level. -/
def FFTNetwork.primitiveDepth (network : FFTNetwork K k) : Nat :=
  2 * network.butterflyDepth

/-- A canonical `k`-layer network has butterfly depth exactly `k`. -/
@[simp] theorem fftNetwork_butterflyDepth {K : Type*} [Monoid K]
    {k : Nat} (omega : K) :
    (fftNetwork (k := k) omega).butterflyDepth = k := by
  change (∑ s : Fin k, (fftLayer omega s).butterflyDepth) = k
  simp [FFTLayer.butterflyDepth, fftLayer,
    fftStageCircuit_butterflyDepth]

/-- Expanding canonical butterflies gives the exact primitive-gate count. -/
theorem fftNetwork_primitiveGateCount {K : Type*} [Monoid K]
    {k : Nat} (omega : K) :
    (fftNetwork (k := k) omega).primitiveGateCount =
      3 * k * 2 ^ (k - 1) := by
  rw [FFTNetwork.primitiveGateCount, fftNetwork_butterflyCount]
  simp [Nat.mul_assoc]

/-- Expanding each butterfly to two primitive levels gives depth `2 * k`. -/
@[simp] theorem fftNetwork_primitiveDepth {K : Type*} [Monoid K]
    {k : Nat} (omega : K) :
    (fftNetwork (k := k) omega).primitiveDepth = 2 * k := by
  simp [FFTNetwork.primitiveDepth]

end Chapter30
end CLRS
