import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryCanonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInitialBoundaryAlignment
import Mathlib.Tactic

/-!
# Alignment of the concrete accepting source

The positive accepting source is organized by control, height, and cell
segments.  This module identifies its fixed Boolean target tables with the
canonical encoding of `haltList [true]`, before closing the complete frame
family against the semantic optional operand.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Arithmetic Boolean-pool target of one accepting-row slot. -/
def verifierAcceptingSlotRightWire
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) : Nat :=
  let tm := W.machine.tm
  let falseWire := (verifierInitialFalseWirePolynomial W).eval input.length
  let trueWire := falseWire + 1
  let outputCode := encodeAlphabetSymbol tm tm.k₁
    (verifierAcceptingSymbol W) hmember
  match slot with
  | .inl _ => trueWire
  | .inr (.inl label) =>
      if label = encodeLabel tm none then trueWire else falseWire
  | .inr (.inr (.inl state)) =>
      if state = stateEquivFin tm tm.initialState then trueWire else falseWire
  | .inr (.inr (.inr ⟨k, .inl height⟩)) =>
      if _ : k = tm.k₁ then
        if height.val = 1 then trueWire else falseWire
      else if height.val = 0 then trueWire else falseWire
  | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
      if _ : k = tm.k₁ then
        if cell.val = 0 then
          if symbol.val = outputCode.val then trueWire else falseWire
        else if symbol.val = (reachableAlphabet tm k).card then
          trueWire
        else falseWire
      else if symbol.val = (reachableAlphabet tm k).card then
        trueWire
      else falseWire

/-- The arithmetic target is the proof-carrying static halt target wire. -/
theorem verifierAcceptingSlotRightWire_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) :
    verifierAcceptingSlotRightWire W hmember input slot =
      verifierAcceptingTargetWires W input
        (verifierAcceptingOutputFitsOfSymbol W input hmember) slot := by
  rcases slot with (_ | label | state | ⟨k, height | cell⟩)
  · simp [verifierAcceptingSlotRightWire, CfgSlot.halted,
      verifierAcceptingTargetWires, staticBoundedCfgWires,
      staticCfgWires, encodeRawCfgBits, encodeCfg,
      _root_.Turing.haltList, labelHalted]
  · by_cases hlabel :
      label = encodeLabel W.machine.tm none
    <;> simp [verifierAcceptingSlotRightWire, CfgSlot.label,
      verifierAcceptingTargetWires, staticBoundedCfgWires,
      staticCfgWires, encodeRawCfgBits, encodeCfg,
      _root_.Turing.haltList, encodeOneHot, hlabel]
  · by_cases hstate :
      state = stateEquivFin W.machine.tm W.machine.tm.initialState
    <;> simp [verifierAcceptingSlotRightWire, CfgSlot.state,
      verifierAcceptingTargetWires, staticBoundedCfgWires,
      staticCfgWires, encodeRawCfgBits, encodeCfg,
      _root_.Turing.haltList, encodeOneHot, hstate]
  · by_cases hk : k = W.machine.tm.k₁
    · subst k
      by_cases hheight : height.val = 1
      <;> simp [verifierAcceptingSlotRightWire, CfgSlot.stackHeight,
        verifierAcceptingTargetWires, staticBoundedCfgWires,
        staticCfgWires, encodeRawCfgBits, encodeCfg,
        _root_.Turing.haltList, encodeBoundedStack, encodeOneHot,
        hheight, Fin.ext_iff]
    · by_cases hheight : height.val = 0
      · have hfin : height = 0 := Fin.ext hheight
        simp [verifierAcceptingSlotRightWire, CfgSlot.stackHeight,
          verifierAcceptingTargetWires, staticBoundedCfgWires,
          staticCfgWires, encodeRawCfgBits, encodeCfg,
          _root_.Turing.haltList, encodeBoundedStack, encodeOneHot,
          hk, hheight, hfin]
      · have hfin : height ≠ 0 := fun heq =>
          hheight (congrArg Fin.val heq)
        simp [verifierAcceptingSlotRightWire, CfgSlot.stackHeight,
          verifierAcceptingTargetWires, staticBoundedCfgWires,
          staticCfgWires, encodeRawCfgBits, encodeCfg,
          _root_.Turing.haltList, encodeBoundedStack, encodeOneHot,
          hk, hheight, hfin]
  · rcases cell with ⟨cell, symbol⟩
    by_cases hk : k = W.machine.tm.k₁
    · subst k
      by_cases hcell : cell.val = 0
      · by_cases hsymbol : symbol.val =
            (encodeAlphabetSymbol W.machine.tm W.machine.tm.k₁
              (verifierAcceptingSymbol W) hmember).val
        <;> simp [verifierAcceptingSlotRightWire, CfgSlot.stackCell,
          verifierAcceptingTargetWires, staticBoundedCfgWires,
          staticCfgWires, encodeRawCfgBits, encodeCfg,
          _root_.Turing.haltList, encodeBoundedStack, encodeOneHot,
          hcell, hsymbol, Fin.ext_iff]
      · by_cases hsymbol : symbol.val =
          (reachableAlphabet W.machine.tm W.machine.tm.k₁).card
        <;> simp [verifierAcceptingSlotRightWire, CfgSlot.stackCell,
          verifierAcceptingTargetWires, staticBoundedCfgWires,
          staticCfgWires, encodeRawCfgBits, encodeCfg,
          _root_.Turing.haltList, encodeBoundedStack, encodeOneHot,
          hcell, hsymbol, Fin.ext_iff]
    · by_cases hsymbol :
        symbol.val = (reachableAlphabet W.machine.tm k).card
      <;> simp [verifierAcceptingSlotRightWire, CfgSlot.stackCell,
        verifierAcceptingTargetWires, staticBoundedCfgWires,
        staticCfgWires, encodeRawCfgBits, encodeCfg,
        _root_.Turing.haltList, encodeBoundedStack, encodeOneHot,
        hk, hsymbol, Fin.ext_iff]

/-! ## Frames denoted by the concrete source -/

/-- Arithmetic accepting frame at one in-row coordinate. -/
def verifierAcceptingFrameAtCoordinate
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (coordinate right : Nat) : AffineEqFinPairFrame :=
  let previous := verifierInputBoundaryEnd W input + 6 * coordinate
  { eqStart := previous + 1
    left := (verifierLastRowStartPolynomial W).eval input.length + coordinate
    right := right
    matched := previous + 5
    previous := previous }

/-- The explicit public-slot frame is the arithmetic coordinate frame with
the corresponding arithmetic Boolean-pool target. -/
theorem verifierAcceptingSlotFrame_eq_arithmetic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) :
    verifierAcceptingSlotFrame W hmember input slot =
      verifierAcceptingFrameAtCoordinate W input
        (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length) slot).val
        (verifierAcceptingSlotRightWire W hmember input slot) := by
  unfold verifierAcceptingSlotFrame verifierAcceptingFrameAtCoordinate
  rw [verifierAcceptingSlotRightWire_eq_semantic]

/-- Frames denoted by an ordinary accepting progression segment. -/
def verifierAcceptingSegmentFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (coordinate right stepRight count : Polynomial Nat)
    (input : List Γ) : List AffineEqFinPairFrame :=
  dynamicFirstAffineEqFinFrames
    (verifierAcceptingPrevious W coordinate)
    (verifierLastRowStartPolynomial W + coordinate)
    right 6 1 stepRight count input

/-- Frames denoted by an accepting row-block segment. -/
def verifierAcceptingRowSegmentFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm)
    (coordinate aux stepPrevious stepLeft stepAux count : Polynomial Nat)
    (input : List Γ) : List AffineEqFinPairFrame :=
  dynamicFirstAffineEqFinRowFrames forms
    (verifierAcceptingPrevious W coordinate)
    (verifierLastRowStartPolynomial W + coordinate)
    aux stepPrevious stepLeft stepAux count input

def verifierAcceptingControlCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineEqFinPairFrame :=
  verifierAcceptingRowSegmentFrames W
    (acceptingControlTargetForms W.machine.tm)
    0 (verifierInitialFalseWirePolynomial W) 0 0 0 1 input

def verifierAcceptingEmptyStackCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List AffineEqFinPairFrame :=
  let coordinate := verifierInitialStackOffsetPolynomial W k
  let cells := coordinate + verifierHeight W + 1
  verifierAcceptingSegmentFrames W coordinate
      (verifierInitialFalseWirePolynomial W + 1) 0 1 input ++
    verifierAcceptingSegmentFrames W (coordinate + 1)
      (verifierInitialFalseWirePolynomial W) 0 (verifierHeight W) input ++
    verifierAcceptingRowSegmentFrames W
      (initialBlankCellTargetForms W.machine.tm k)
      cells (verifierInitialFalseWirePolynomial W)
      (Polynomial.C
        (6 * ((reachableAlphabet W.machine.tm k).card + 1)))
      (Polynomial.C ((reachableAlphabet W.machine.tm k).card + 1))
      0 (verifierHeight W) input

def verifierAcceptingOutputStackCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) : List AffineEqFinPairFrame :=
  let k := W.machine.tm.k₁
  let width := (reachableAlphabet W.machine.tm k).card + 1
  let coordinate := verifierInitialStackOffsetPolynomial W k
  let cells := coordinate + verifierHeight W + 1
  verifierAcceptingSegmentFrames W coordinate
      (verifierInitialFalseWirePolynomial W) 0 1 input ++
    verifierAcceptingSegmentFrames W (coordinate + 1)
      (verifierInitialFalseWirePolynomial W + 1) 0 1 input ++
    verifierAcceptingSegmentFrames W (coordinate + 2)
      (verifierInitialFalseWirePolynomial W) 0
      (verifierAcceptingHeightTailPolynomial W) input ++
    verifierAcceptingRowSegmentFrames W
      (acceptingOutputCellTargetForms W hmember)
      cells (verifierInitialFalseWirePolynomial W) 0 0 0 1 input ++
    verifierAcceptingRowSegmentFrames W
      (initialBlankCellTargetForms W.machine.tm k)
      (cells + Polynomial.C width)
      (verifierInitialFalseWirePolynomial W)
      (Polynomial.C (6 * width)) (Polynomial.C width) 0
      (verifierAcceptingHeightTailPolynomial W) input

def verifierAcceptingStackCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (k : W.machine.tm.K) (input : List Γ) : List AffineEqFinPairFrame :=
  if _hk : k = W.machine.tm.k₁ then
    verifierAcceptingOutputStackCompiledFrames W hmember input
  else
    verifierAcceptingEmptyStackCompiledFrames W k input

def verifierAcceptingStackFamilyCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) : List AffineEqFinPairFrame :=
  (arithmeticRuntimeStackSourceIndices W.machine.tm).flatMap fun index =>
    verifierAcceptingStackCompiledFrames W hmember
      ((arithmeticStackEquiv W.machine.tm).symm index) input

def verifierAcceptingBoundaryCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) : List AffineEqFinPairFrame :=
  verifierAcceptingControlCompiledFrames W input ++
    verifierAcceptingStackFamilyCompiledFrames W hmember input

private theorem accepting_encodeAffineEqFinFrames_flatMap {α : Type}
    (items : List α) (frames : α → List AffineEqFinPairFrame) :
    encodeAffineEqFinFrames (items.flatMap frames) =
      items.flatMap fun item => encodeAffineEqFinFrames (frames item) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.flatMap_cons]
      unfold encodeAffineEqFinFrames at ih ⊢
      rw [List.flatMap_append, ih]

/-- The concrete positive source target is the serialization of its explicit
compiled frame family. -/
theorem verifierAcceptingBoundaryInputTarget_eq_compiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingBoundaryInputTarget W hmember input =
      encodeAffineEqFinFrames
        (verifierAcceptingBoundaryCompiledFrames W hmember input) := by
  unfold verifierAcceptingBoundaryInputTarget
    verifierAcceptingControlInput verifierAcceptingStackFamilyInput
    verifierAcceptingBoundaryCompiledFrames
    verifierAcceptingControlCompiledFrames
    verifierAcceptingStackFamilyCompiledFrames
    verifierAcceptingRowSegmentInput verifierAcceptingRowSegmentFrames
  rw [show encodeAffineEqFinFrames
      (dynamicFirstAffineEqFinRowFrames
          (acceptingControlTargetForms W.machine.tm)
          (verifierAcceptingPrevious W 0)
          (verifierLastRowStartPolynomial W + 0)
          (verifierInitialFalseWirePolynomial W) 0 0 0 1 input ++
        (arithmeticRuntimeStackSourceIndices W.machine.tm).flatMap fun index =>
          verifierAcceptingStackCompiledFrames W hmember
            ((arithmeticStackEquiv W.machine.tm).symm index) input) =
      encodeAffineEqFinFrames
          (dynamicFirstAffineEqFinRowFrames
            (acceptingControlTargetForms W.machine.tm)
            (verifierAcceptingPrevious W 0)
            (verifierLastRowStartPolynomial W + 0)
            (verifierInitialFalseWirePolynomial W) 0 0 0 1 input) ++
        encodeAffineEqFinFrames
          ((arithmeticRuntimeStackSourceIndices W.machine.tm).flatMap
            fun index => verifierAcceptingStackCompiledFrames W hmember
              ((arithmeticStackEquiv W.machine.tm).symm index) input) by
        simp [encodeAffineEqFinFrames]]
  rw [accepting_encodeAffineEqFinFrames_flatMap]
  congr 1
  apply List.flatMap_congr
  intro index hindex
  let k := (arithmeticStackEquiv W.machine.tm).symm index
  change verifierAcceptingStackInput W hmember k input =
    encodeAffineEqFinFrames
      (verifierAcceptingStackCompiledFrames W hmember k input)
  by_cases hk : k = W.machine.tm.k₁
  · simp [verifierAcceptingStackInput,
      verifierAcceptingStackCompiledFrames, hk,
      verifierAcceptingOutputStackInput,
      verifierAcceptingOutputStackCompiledFrames,
      verifierAcceptingSegmentInput, verifierAcceptingSegmentFrames,
      verifierAcceptingRowSegmentInput,
      verifierAcceptingRowSegmentFrames,
      dynamicFirstAffineEqFinInput,
      dynamicFirstAffineEqFinRowInput,
      encodeAffineEqFinFrames, List.append_assoc]
  · simp [verifierAcceptingStackInput,
      verifierAcceptingStackCompiledFrames, hk,
      verifierAcceptingEmptyStackInput,
      verifierAcceptingEmptyStackCompiledFrames,
      verifierAcceptingSegmentInput, verifierAcceptingSegmentFrames,
      verifierAcceptingRowSegmentInput,
      verifierAcceptingRowSegmentFrames,
      dynamicFirstAffineEqFinInput,
      dynamicFirstAffineEqFinRowInput,
      encodeAffineEqFinFrames, List.append_assoc]

end CLRS.Chapter34.Turing.CookLevin
