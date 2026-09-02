import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorEqFinRowProgressionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBoundaryStarts
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource

/-!
# Concrete exact-polynomial source for the symbolic initial boundary

The initial tableau row is emitted in four structural pieces: fixed control
bits, the symbolic input stack (which is compared with itself), empty height
bits for every other stack, and repeated blank cell blocks.  Every runtime
coordinate is an exact polynomial of the raw input length; only finite
machine data remains in finite control.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fixed number of non-stack coordinates in one configuration row. -/
def initialControlWidth (tm : _root_.Turing.FinTM2) : Nat :=
  1 + (labelCount tm + 1) + stateCount tm

/-- Exact affine width polynomial of one fixed machine stack. -/
def verifierInitialStackWidthPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) : Polynomial Nat :=
  1 + Polynomial.C ((reachableAlphabet W.machine.tm k).card + 2) *
    verifierHeight W

@[simp] theorem verifierInitialStackWidthPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (n : Nat) :
    (verifierInitialStackWidthPolynomial W k).eval n =
      cfgStackBitWidth W.machine.tm ((verifierHeight W).eval n) k := by
  simp [verifierInitialStackWidthPolynomial, cfgStackBitWidth,
    Polynomial.eval_add, Polynomial.eval_mul]
  ring

/-- First in-row coordinate of one fixed stack. -/
noncomputable def verifierInitialStackOffsetPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) : Polynomial Nat :=
  Polynomial.C
      (initialControlWidth W.machine.tm + arithmeticStackOrdinal W.machine.tm k) +
    Polynomial.C (cfgStackBitOffsetHeightCoeff W.machine.tm k) *
      verifierHeight W

@[simp] theorem verifierInitialStackOffsetPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (n : Nat) :
    (verifierInitialStackOffsetPolynomial W k).eval n =
      initialControlWidth W.machine.tm +
        cfgStackBitOffset W.machine.tm ((verifierHeight W).eval n) k := by
  rw [cfgStackBitOffset_eq_affine]
  simp [verifierInitialStackOffsetPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul]
  ring

/-- Equality carry immediately before one in-row coordinate. -/
def verifierInitialPreviousPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (coordinate : Polynomial Nat) : Polynomial Nat :=
  verifierTransitionEndPolynomial W + Polynomial.C 6 * coordinate

/-- False-pool wire; the true-pool wire is its successor. -/
def verifierInitialFalseWirePolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  verifierTableauInputPolynomial W

/-- Select the false or true pool wire from the auxiliary seed coordinate. -/
def initialPoolTargetForm : Bool → AffineUnaryTripleForm
  | false => { constant := 0, first := 0, second := 0, third := 1 }
  | true => { constant := 1, first := 0, second := 0, third := 1 }

/-- Canonical non-stack bits of an initial machine configuration. -/
noncomputable def initialControlBits
    (tm : _root_.Turing.FinTM2) : List Bool :=
  [false] ++
    List.ofFn (encodeOneHot (encodeLabel tm (some tm.main))) ++
    List.ofFn (encodeOneHot (stateEquivFin tm tm.initialState))

/-- Fixed affine right-target table for the non-stack prefix. -/
noncomputable def initialControlTargetForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (initialControlBits tm).map initialPoolTargetForm

/-- Fixed blank one-hot target table of a physical cell. -/
noncomputable def initialBlankCellTargetForms
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List AffineUnaryTripleForm :=
  List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
    initialPoolTargetForm (decide (symbol.val = (reachableAlphabet tm k).card))

/-- Exact encoded equality frames for the fixed control prefix. -/
def verifierInitialControlInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineEqFinRowInput
    (initialControlTargetForms W.machine.tm)
    (verifierTransitionEndPolynomial W) 0
    (verifierInitialFalseWirePolynomial W)
    0 0 0 1 input

/-- Exact encoded equality frames for the symbolic input stack.  Its target
is the same first-row stack, so left and right progress together. -/
def verifierInitialInputStackInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  let coordinate := verifierInitialStackOffsetPolynomial W W.machine.tm.k₀
  exactPolynomialAffineEqFinInput
    (verifierInitialPreviousPolynomial W coordinate)
    coordinate coordinate
    6 1 1
    (verifierInitialStackWidthPolynomial W W.machine.tm.k₀) input

/-- Equality input for the selected-zero height coordinate of an empty stack. -/
def verifierInitialEmptyStackHeightZeroInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  let coordinate := verifierInitialStackOffsetPolynomial W k
  exactPolynomialAffineEqFinInput
    (verifierInitialPreviousPolynomial W coordinate)
    coordinate (verifierInitialFalseWirePolynomial W + 1)
    0 0 0 1 input

/-- Equality input for all unselected positive height coordinates of an empty
stack. -/
def verifierInitialEmptyStackHeightTailInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  let coordinate := verifierInitialStackOffsetPolynomial W k + 1
  exactPolynomialAffineEqFinInput
    (verifierInitialPreviousPolynomial W coordinate)
    coordinate (verifierInitialFalseWirePolynomial W)
    6 1 0 (verifierHeight W) input

/-- Equality input for all physical cells of an empty stack.  Each runtime
cell expands to the fixed false/.../false/blank-true symbol row. -/
def verifierInitialEmptyStackCellsInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  let width := (reachableAlphabet W.machine.tm k).card + 1
  let coordinate := verifierInitialStackOffsetPolynomial W k +
    verifierHeight W + 1
  exactPolynomialAffineEqFinRowInput
    (initialBlankCellTargetForms W.machine.tm k)
    (verifierInitialPreviousPolynomial W coordinate)
    coordinate (verifierInitialFalseWirePolynomial W)
    (Polynomial.C (6 * width)) (Polynomial.C width) 0
    (verifierHeight W) input

/-- Complete equality input for one fixed stack. -/
def verifierInitialStackInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  if _hk : k = W.machine.tm.k₀ then
    verifierInitialInputStackInput W input
  else
    verifierInitialEmptyStackHeightZeroInput W k input ++
      verifierInitialEmptyStackHeightTailInput W k input ++
      verifierInitialEmptyStackCellsInput W k input

/-- Stack blocks in the canonical fixed-machine enumeration. -/
def verifierInitialStackFamilyInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (arithmeticRuntimeStackSourceIndices W.machine.tm).flatMap fun index =>
    verifierInitialStackInput W
      ((arithmeticStackEquiv W.machine.tm).symm index) input

/-- Complete exact-polynomial input for the established initial-boundary
equality controller. -/
def verifierInitialBoundaryInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierInitialControlInput W input ++
    verifierInitialStackFamilyInput W input

/-- The fixed control-prefix equality input is polynomial-time computable. -/
noncomputable def verifierInitialControlInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInitialControlInput W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialAffineEqFinRowInput_computableInPolyTime
    (initialControlTargetForms W.machine.tm)
    (verifierTransitionEndPolynomial W) 0
    (verifierInitialFalseWirePolynomial W)
    0 0 0 1

/-- The symbolic input-stack equality input is polynomial-time computable. -/
noncomputable def verifierInitialInputStackInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInitialInputStackInput W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact exactPolynomialAffineEqFinInput_computableInPolyTime
    (verifierInitialPreviousPolynomial W
      (verifierInitialStackOffsetPolynomial W W.machine.tm.k₀))
    (verifierInitialStackOffsetPolynomial W W.machine.tm.k₀)
    (verifierInitialStackOffsetPolynomial W W.machine.tm.k₀)
    6 1 1 (verifierInitialStackWidthPolynomial W W.machine.tm.k₀)

/-- The complete empty-stack equality input is polynomial-time computable. -/
noncomputable def verifierInitialEmptyStackInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ =>
        verifierInitialEmptyStackHeightZeroInput W k input ++
          verifierInitialEmptyStackHeightTailInput W k input ++
          verifierInitialEmptyStackCellsInput W k input) := by
  letI : Fintype Γ := W.alphabetFintype
  let coordinate := verifierInitialStackOffsetPolynomial W k
  let zeroSource := exactPolynomialAffineEqFinInput_computableInPolyTime
    (Γ := Γ)
    (verifierInitialPreviousPolynomial W coordinate)
    coordinate (verifierInitialFalseWirePolynomial W + 1)
    0 0 0 1
  let tailCoordinate := coordinate + 1
  let tailSource := exactPolynomialAffineEqFinInput_computableInPolyTime
    (Γ := Γ)
    (verifierInitialPreviousPolynomial W tailCoordinate)
    tailCoordinate (verifierInitialFalseWirePolynomial W)
    6 1 0 (verifierHeight W)
  let width := (reachableAlphabet W.machine.tm k).card + 1
  let cellCoordinate := coordinate + verifierHeight W + 1
  let cellSource := exactPolynomialAffineEqFinRowInput_computableInPolyTime
    (Γ := Γ) (initialBlankCellTargetForms W.machine.tm k)
    (verifierInitialPreviousPolynomial W cellCoordinate)
    cellCoordinate (verifierInitialFalseWirePolynomial W)
    (Polynomial.C (6 * width)) (Polynomial.C width) 0
    (verifierHeight W)
  let first := unaryFrameSameInputConcat_computableInPolyTime
    zeroSource tailSource
  let result := unaryFrameSameInputConcat_computableInPolyTime first cellSource
  simpa [coordinate, tailCoordinate, cellCoordinate,
    verifierInitialEmptyStackHeightZeroInput,
    verifierInitialEmptyStackHeightTailInput,
    verifierInitialEmptyStackCellsInput, width, List.append_assoc] using result

/-- One fixed stack block has a concrete polynomial-time source. -/
noncomputable def verifierInitialStackInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInitialStackInput W k) := by
  letI : Fintype Γ := W.alphabetFintype
  by_cases hk : k = W.machine.tm.k₀
  · let source := verifierInitialInputStackInput_computableInPolyTime W
    exact
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          have run := source.outputsFun input
          simpa [verifierInitialStackInput, hk] using run }
  · let source := verifierInitialEmptyStackInput_computableInPolyTime W k
    exact
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          have run := source.outputsFun input
          simpa [verifierInitialStackInput, hk, List.append_assoc] using run }

/-- The fixed finite family of all stack blocks is polynomial-time
computable. -/
noncomputable def verifierInitialStackFamilyInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInitialStackFamilyInput W) := by
  letI : Fintype Γ := W.alphabetFintype
  let indices := arithmeticRuntimeStackSourceIndices W.machine.tm
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ => indices.flatMap fun index =>
      verifierInitialStackInput W
        ((arithmeticStackEquiv W.machine.tm).symm index) input)
  induction indices with
  | nil =>
      let empty := exactPolynomialAffineEqFinInput_computableInPolyTime
        (Γ := Γ) 0 0 0 0 0 0 0
      exact
        { tm := empty.tm
          inputAlphabet := empty.inputAlphabet
          outputAlphabet := empty.outputAlphabet
          time := empty.time
          outputsFun := fun input => by
            have run := empty.outputsFun input
            simpa [exactPolynomialAffineEqFinInput,
              exactPolynomialAffineEqFinFrames, eqFinProgressionFrames,
              eqFinProgressionSeeds,
              exactPolynomialAffineUnaryTripleProgression,
              affineUnaryTripleProgressionRows,
              affineUnaryTripleProgressionRowsFrom,
              encodeAffineEqFinFrames] using run }
  | cons index rest ih =>
      let head := verifierInitialStackInput_computableInPolyTime W
        ((arithmeticStackEquiv W.machine.tm).symm index)
      let combined := unaryFrameSameInputConcat_computableInPolyTime head ih
      simpa only [List.flatMap_cons] using combined

/-- A single fixed polynomial-time TM2 compiles every canonical equality
frame of the symbolic initial boundary from the raw verifier word. -/
noncomputable def verifierInitialBoundaryInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInitialBoundaryInputTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact unaryFrameSameInputConcat_computableInPolyTime
    (verifierInitialControlInput_computableInPolyTime W)
    (verifierInitialStackFamilyInput_computableInPolyTime W)

end CLRS.Chapter34.Turing.CookLevin
