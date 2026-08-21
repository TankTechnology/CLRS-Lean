import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryStaticFit
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorDynamicEqFinProgressionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInitialBoundarySource

/-!
# Concrete source for the accepting-row equality

In the representable branch, the accepting row is the canonical halted
configuration with output `[true]`.  Its equality start is dynamic, but every
in-row coordinate, segment length, and Boolean-pool target is polynomial in
the raw input length.  This module compiles those segments with the reusable
dynamic-first equality progression source.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First public wire of the last tableau row. -/
def verifierLastRowStartPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  verifierHorizon W * verifierCfgBitCountPolynomial W

@[simp] theorem verifierLastRowStartPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierLastRowStartPolynomial W).eval n =
      (verifierHorizon W).eval n *
        cfgBitCount W.machine.tm ((verifierHeight W).eval n) := by
  simp [verifierLastRowStartPolynomial, Polynomial.eval_mul]

/-- Exact polynomial `verifierHeight - 1`, exposed without truncated
subtraction. -/
def verifierAcceptingHeightTailPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  W.certificateBound + Polynomial.X +
    verifierHorizon W * Polynomial.C (maxPushesPerStep W.machine.tm) +
    Polynomial.C (2 * maxStackActionsPerStep W.machine.tm)

@[simp] theorem verifierAcceptingHeightTailPolynomial_eval_add_one
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierAcceptingHeightTailPolynomial W).eval n + 1 =
      (verifierHeight W).eval n := by
  rw [verifierHeight_eval, verifierInputBound_eval]
  simp [verifierAcceptingHeightTailPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul]
  omega

/-- Equality carry immediately before an accepting-row coordinate. -/
def verifierAcceptingPrevious
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (coordinate : Polynomial Nat) (input : List Γ) : Nat :=
  verifierInputBoundaryEnd W input +
    (Polynomial.C 6 * coordinate).eval input.length

/-- Dynamic unary source for the equality carry at a polynomial coordinate. -/
def verifierAcceptingPreviousFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (coordinate : Polynomial Nat) (input : List Γ) : List UnaryFrameSym :=
  unaryFrameSameInputAddPolynomial
    (verifierInputBoundaryEnd W) (Polynomial.C 6 * coordinate) input

@[simp] theorem verifierAcceptingPreviousFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (coordinate : Polynomial Nat) (input : List Γ) :
    verifierAcceptingPreviousFrame W coordinate input =
      encodeUnaryFrameBlock
        (verifierAcceptingPrevious W coordinate input) := by
  rw [show encodeUnaryFrameBlock
      (verifierAcceptingPrevious W coordinate input) =
      encodeUnaryFrame [verifierAcceptingPrevious W coordinate input] by
        simp [encodeUnaryFrame]]
  simp [verifierAcceptingPreviousFrame, verifierAcceptingPrevious]

noncomputable def verifierAcceptingPreviousFrame_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (coordinate : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingPreviousFrame W coordinate) := by
  letI : Fintype Γ := W.alphabetFintype
  let raw := verifierInputBoundaryEndFrame_computableInPolyTime W
  let base : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrame
        [verifierInputBoundaryEnd W input]) :=
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        rw [verifierInputBoundaryEndFrame_eq] at run
        simpa only [id_eq] using run }
  change _root_.Turing.TM2ComputableInPolyTime id id
    (unaryFrameSameInputAddPolynomial
      (verifierInputBoundaryEnd W) (Polynomial.C 6 * coordinate))
  exact unaryFrameSameInputAddPolynomial_computableInPolyTime
    (verifierInputBoundaryEnd W) (Polynomial.C 6 * coordinate) base

/-- Fixed halted/label/state bits of the canonical accepting configuration. -/
noncomputable def acceptingControlBits
    (tm : _root_.Turing.FinTM2) : List Bool :=
  [true] ++
    List.ofFn (encodeOneHot (encodeLabel tm none)) ++
    List.ofFn (encodeOneHot (stateEquivFin tm tm.initialState))

/-- Affine Boolean-pool table for the accepting control prefix. -/
noncomputable def acceptingControlTargetForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (acceptingControlBits tm).map initialPoolTargetForm

/-- One-hot target table for the fixed accepting output symbol. -/
noncomputable def acceptingOutputCellTargetForms
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁) :
    List AffineUnaryTripleForm :=
  let code := encodeAlphabetSymbol W.machine.tm W.machine.tm.k₁
    (verifierAcceptingSymbol W) hmember
  List.ofFn fun symbol : Fin
      ((reachableAlphabet W.machine.tm W.machine.tm.k₁).card + 1) =>
    initialPoolTargetForm (decide (symbol = code))

/-- Dynamic-first equality segment at one polynomial in-row coordinate. -/
def verifierAcceptingSegmentInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (coordinate right stepRight count : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  dynamicFirstAffineEqFinInput
    (verifierAcceptingPrevious W coordinate)
    (verifierLastRowStartPolynomial W + coordinate)
    right 6 1 stepRight count input

/-- Dynamic-first row-block equality segment. -/
def verifierAcceptingRowSegmentInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm)
    (coordinate aux stepPrevious stepLeft stepAux count : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  dynamicFirstAffineEqFinRowInput forms
    (verifierAcceptingPrevious W coordinate)
    (verifierLastRowStartPolynomial W + coordinate)
    aux stepPrevious stepLeft stepAux count input

/-- Fixed accepting control prefix. -/
def verifierAcceptingControlInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierAcceptingRowSegmentInput W
    (acceptingControlTargetForms W.machine.tm)
    0 (verifierInitialFalseWirePolynomial W) 0 0 0 1 input

/-- Equality input for one empty non-output stack. -/
def verifierAcceptingEmptyStackInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  let coordinate := verifierInitialStackOffsetPolynomial W k
  let cells := coordinate + verifierHeight W + 1
  verifierAcceptingSegmentInput W coordinate
      (verifierInitialFalseWirePolynomial W + 1) 0 1 input ++
    verifierAcceptingSegmentInput W (coordinate + 1)
      (verifierInitialFalseWirePolynomial W) 0 (verifierHeight W) input ++
    verifierAcceptingRowSegmentInput W
      (initialBlankCellTargetForms W.machine.tm k)
      cells (verifierInitialFalseWirePolynomial W)
      (Polynomial.C
        (6 * ((reachableAlphabet W.machine.tm k).card + 1)))
      (Polynomial.C ((reachableAlphabet W.machine.tm k).card + 1))
      0 (verifierHeight W) input

/-- Complete one-symbol output-stack equality input. -/
def verifierAcceptingOutputStackInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) : List UnaryFrameSym :=
  let k := W.machine.tm.k₁
  let width := (reachableAlphabet W.machine.tm k).card + 1
  let coordinate := verifierInitialStackOffsetPolynomial W k
  let cells := coordinate + verifierHeight W + 1
  verifierAcceptingSegmentInput W coordinate
      (verifierInitialFalseWirePolynomial W) 0 1 input ++
    verifierAcceptingSegmentInput W (coordinate + 1)
      (verifierInitialFalseWirePolynomial W + 1) 0 1 input ++
    verifierAcceptingSegmentInput W (coordinate + 2)
      (verifierInitialFalseWirePolynomial W) 0
      (verifierAcceptingHeightTailPolynomial W) input ++
    verifierAcceptingRowSegmentInput W
      (acceptingOutputCellTargetForms W hmember)
      cells (verifierInitialFalseWirePolynomial W) 0 0 0 1 input ++
    verifierAcceptingRowSegmentInput W
      (initialBlankCellTargetForms W.machine.tm k)
      (cells + Polynomial.C width)
      (verifierInitialFalseWirePolynomial W)
      (Polynomial.C (6 * width)) (Polynomial.C width) 0
      (verifierAcceptingHeightTailPolynomial W) input

/-- One stack block, selected statically by equality with the output stack. -/
def verifierAcceptingStackInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  if _hk : k = W.machine.tm.k₁ then
    verifierAcceptingOutputStackInput W hmember input
  else
    verifierAcceptingEmptyStackInput W k input

/-- Canonically ordered fixed family of accepting stack blocks. -/
def verifierAcceptingStackFamilyInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) : List UnaryFrameSym :=
  (arithmeticRuntimeStackSourceIndices W.machine.tm).flatMap fun index =>
    verifierAcceptingStackInput W hmember
      ((arithmeticStackEquiv W.machine.tm).symm index) input

/-- Complete positive-branch accepting equality operand. -/
def verifierAcceptingBoundaryInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) : List UnaryFrameSym :=
  verifierAcceptingControlInput W input ++
    verifierAcceptingStackFamilyInput W hmember input

private noncomputable def verifierAcceptingSegmentInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (coordinate right stepRight count : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingSegmentInput W coordinate right stepRight count) := by
  letI : Fintype Γ := W.alphabetFintype
  let first := verifierAcceptingPreviousFrame_computableInPolyTime W coordinate
  let first' : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrameBlock
        (verifierAcceptingPrevious W coordinate input)) :=
    { tm := first.tm
      inputAlphabet := first.inputAlphabet
      outputAlphabet := first.outputAlphabet
      time := first.time
      outputsFun := fun input => by
        have run := first.outputsFun input
        rw [verifierAcceptingPreviousFrame_eq] at run
        simpa only [id_eq] using run }
  exact dynamicFirstAffineEqFinInput_computableInPolyTime
    (verifierAcceptingPrevious W coordinate)
    (verifierLastRowStartPolynomial W + coordinate)
    right 6 1 stepRight count first'

private noncomputable def
    verifierAcceptingRowSegmentInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm)
    (coordinate aux stepPrevious stepLeft stepAux count : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingRowSegmentInput W forms coordinate aux
        stepPrevious stepLeft stepAux count) := by
  letI : Fintype Γ := W.alphabetFintype
  let first := verifierAcceptingPreviousFrame_computableInPolyTime W coordinate
  let first' : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrameBlock
        (verifierAcceptingPrevious W coordinate input)) :=
    { tm := first.tm
      inputAlphabet := first.inputAlphabet
      outputAlphabet := first.outputAlphabet
      time := first.time
      outputsFun := fun input => by
        have run := first.outputsFun input
        rw [verifierAcceptingPreviousFrame_eq] at run
        simpa only [id_eq] using run }
  exact dynamicFirstAffineEqFinRowInput_computableInPolyTime forms
    (verifierAcceptingPrevious W coordinate)
    (verifierLastRowStartPolynomial W + coordinate)
    aux stepPrevious stepLeft stepAux count first'

noncomputable def verifierAcceptingControlInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingControlInput W) :=
  verifierAcceptingRowSegmentInput_computableInPolyTime W
    (acceptingControlTargetForms W.machine.tm)
    0 (verifierInitialFalseWirePolynomial W) 0 0 0 1

noncomputable def verifierAcceptingEmptyStackInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingEmptyStackInput W k) := by
  letI : Fintype Γ := W.alphabetFintype
  let coordinate := verifierInitialStackOffsetPolynomial W k
  let cells := coordinate + verifierHeight W + 1
  let zero := verifierAcceptingSegmentInput_computableInPolyTime W coordinate
    (verifierInitialFalseWirePolynomial W + 1) 0 1
  let tail := verifierAcceptingSegmentInput_computableInPolyTime W
    (coordinate + 1) (verifierInitialFalseWirePolynomial W) 0
    (verifierHeight W)
  let cellRows := verifierAcceptingRowSegmentInput_computableInPolyTime W
    (initialBlankCellTargetForms W.machine.tm k) cells
    (verifierInitialFalseWirePolynomial W)
    (Polynomial.C (6 * ((reachableAlphabet W.machine.tm k).card + 1)))
    (Polynomial.C ((reachableAlphabet W.machine.tm k).card + 1))
    0 (verifierHeight W)
  let joinedZeroTail := unaryFrameSameInputConcat_computableInPolyTime zero tail
  let result := unaryFrameSameInputConcat_computableInPolyTime
    joinedZeroTail cellRows
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      verifierAcceptingSegmentInput W coordinate
          (verifierInitialFalseWirePolynomial W + 1) 0 1 input ++
        verifierAcceptingSegmentInput W (coordinate + 1)
          (verifierInitialFalseWirePolynomial W) 0 (verifierHeight W) input ++
        verifierAcceptingRowSegmentInput W
          (initialBlankCellTargetForms W.machine.tm k) cells
          (verifierInitialFalseWirePolynomial W)
          (Polynomial.C
            (6 * ((reachableAlphabet W.machine.tm k).card + 1)))
          (Polynomial.C ((reachableAlphabet W.machine.tm k).card + 1))
          0 (verifierHeight W) input)
  simpa only [List.append_assoc] using result

noncomputable def verifierAcceptingOutputStackInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingOutputStackInput W hmember) := by
  letI : Fintype Γ := W.alphabetFintype
  let k := W.machine.tm.k₁
  let width := (reachableAlphabet W.machine.tm k).card + 1
  let coordinate := verifierInitialStackOffsetPolynomial W k
  let cells := coordinate + verifierHeight W + 1
  let zero := verifierAcceptingSegmentInput_computableInPolyTime W coordinate
    (verifierInitialFalseWirePolynomial W) 0 1
  let one := verifierAcceptingSegmentInput_computableInPolyTime W
    (coordinate + 1) (verifierInitialFalseWirePolynomial W + 1) 0 1
  let heightTail := verifierAcceptingSegmentInput_computableInPolyTime W
    (coordinate + 2) (verifierInitialFalseWirePolynomial W) 0
    (verifierAcceptingHeightTailPolynomial W)
  let outputCell := verifierAcceptingRowSegmentInput_computableInPolyTime W
    (acceptingOutputCellTargetForms W hmember) cells
    (verifierInitialFalseWirePolynomial W) 0 0 0 1
  let blankCells := verifierAcceptingRowSegmentInput_computableInPolyTime W
    (initialBlankCellTargetForms W.machine.tm k)
    (cells + Polynomial.C width) (verifierInitialFalseWirePolynomial W)
    (Polynomial.C (6 * width)) (Polynomial.C width) 0
    (verifierAcceptingHeightTailPolynomial W)
  let first := unaryFrameSameInputConcat_computableInPolyTime zero one
  let second := unaryFrameSameInputConcat_computableInPolyTime first heightTail
  let third := unaryFrameSameInputConcat_computableInPolyTime second outputCell
  let result := unaryFrameSameInputConcat_computableInPolyTime third blankCells
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      verifierAcceptingSegmentInput W coordinate
          (verifierInitialFalseWirePolynomial W) 0 1 input ++
        verifierAcceptingSegmentInput W (coordinate + 1)
          (verifierInitialFalseWirePolynomial W + 1) 0 1 input ++
        verifierAcceptingSegmentInput W (coordinate + 2)
          (verifierInitialFalseWirePolynomial W) 0
          (verifierAcceptingHeightTailPolynomial W) input ++
        verifierAcceptingRowSegmentInput W
          (acceptingOutputCellTargetForms W hmember) cells
          (verifierInitialFalseWirePolynomial W) 0 0 0 1 input ++
        verifierAcceptingRowSegmentInput W
          (initialBlankCellTargetForms W.machine.tm k)
          (cells + Polynomial.C width)
          (verifierInitialFalseWirePolynomial W)
          (Polynomial.C (6 * width)) (Polynomial.C width) 0
          (verifierAcceptingHeightTailPolynomial W) input)
  simpa only [List.append_assoc] using result

noncomputable def verifierAcceptingStackInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingStackInput W hmember k) := by
  by_cases hk : k = W.machine.tm.k₁
  · subst k
    let source :=
      verifierAcceptingOutputStackInput_computableInPolyTime W hmember
    exact
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          have run := source.outputsFun input
          simpa [verifierAcceptingStackInput] using run }
  · let source := verifierAcceptingEmptyStackInput_computableInPolyTime W k
    exact
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          have run := source.outputsFun input
          simpa [verifierAcceptingStackInput, hk] using run }

noncomputable def verifierAcceptingStackFamilyInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingStackFamilyInput W hmember) := by
  letI : Fintype Γ := W.alphabetFintype
  let indices := arithmeticRuntimeStackSourceIndices W.machine.tm
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ => indices.flatMap fun index =>
      verifierAcceptingStackInput W hmember
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
      let head := verifierAcceptingStackInput_computableInPolyTime W hmember
        ((arithmeticStackEquiv W.machine.tm).symm index)
      let combined := unaryFrameSameInputConcat_computableInPolyTime head ih
      simpa only [List.flatMap_cons] using combined

/-- One fixed polynomial-time TM2 emits the complete positive accepting
equality operand directly from the raw verifier word. -/
noncomputable def verifierAcceptingBoundaryInputTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierAcceptingBoundaryInputTarget W hmember) := by
  letI : Fintype Γ := W.alphabetFintype
  exact unaryFrameSameInputConcat_computableInPolyTime
    (verifierAcceptingControlInput_computableInPolyTime W)
    (verifierAcceptingStackFamilyInput_computableInPolyTime W hmember)

end CLRS.Chapter34.Turing.CookLevin
