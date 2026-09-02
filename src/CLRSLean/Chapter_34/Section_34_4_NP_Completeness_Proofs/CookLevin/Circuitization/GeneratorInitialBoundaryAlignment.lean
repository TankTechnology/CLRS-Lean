import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInitialBoundarySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSlotEnumeration
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmCoordinates
import Mathlib.Tactic

/-!
# Canonical-slot alignment of the symbolic initial boundary

This module states the generated initial equality in the existing explicit
public-slot order.  It first removes all proof-carrying builder coordinates
from the semantic boundary.  The remaining source-to-slot alignment is then
pure list arithmetic.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Arithmetic right target of one initial-row slot. -/
def verifierInitialSlotRightWire
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) : Nat :=
  let tm := W.machine.tm
  let H := (verifierHeight W).eval input.length
  let falseWire := (verifierInitialFalseWirePolynomial W).eval input.length
  let trueWire := falseWire + 1
  match slot with
  | .inl _ => falseWire
  | .inr (.inl label) =>
      if label = encodeLabel tm (some tm.main) then trueWire else falseWire
  | .inr (.inr (.inl state)) =>
      if state = stateEquivFin tm tm.initialState then trueWire else falseWire
  | .inr (.inr (.inr ⟨k, .inl height⟩)) =>
      if hk : k = tm.k₀ then
        (cfgSlotEquivFin tm H (CfgSlot.stackHeight k height)).val
      else if height.val = 0 then trueWire else falseWire
  | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
      if hk : k = tm.k₀ then
        (cfgSlotEquivFin tm H (CfgSlot.stackCell k cell symbol)).val
      else if symbol.val = (reachableAlphabet tm k).card then
        trueWire
      else falseWire

@[simp] theorem verifierInitialFalseWirePolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierInitialFalseWirePolynomial W).eval n =
      tableauInputCount W.machine.tm
        ((verifierHeight W).eval n) ((verifierHorizon W).eval n) := by
  exact verifierTableauInputPolynomial_eval W n

@[simp] theorem verifierPool_falseWire_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierPool W input).pool.falseWire =
      tableauInputCount W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length) := by
  simp [verifierPool, verifierRows,
    CircuitBuilder.allocateBoolWirePool_falseWire,
    allocateTableauRows_gate_delta]

@[simp] theorem verifierPool_trueWire_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierPool W input).pool.trueWire =
      tableauInputCount W.machine.tm
          ((verifierHeight W).eval input.length)
          ((verifierHorizon W).eval input.length) + 1 := by
  simp [verifierPool, verifierRows,
    CircuitBuilder.allocateBoolWirePool_trueWire,
    allocateTableauRows_gate_delta]

/-- The arithmetic target is literally the symbolic target wire already used
by the semantic initial boundary. -/
theorem verifierInitialSlotRightWire_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) :
    verifierInitialSlotRightWire W input slot =
      let rows := verifierRows W input
      let pool := verifierPool W input
      let validity := verifierValidity W input
      let transitions := verifierTransitions W input
      let row := rows.rows (verifierFirstRow _)
      symbolicInitialCfgWires W.machine.tm
        ((verifierHeight W).eval input.length)
        (pool.pool.mono (validity.extension.trans transitions.extension))
        (row.stack W.machine.tm.k₀) slot := by
  rcases slot with (_ | label | state | ⟨k, height | cell⟩)
  · simp [verifierInitialSlotRightWire, CfgSlot.halted,
      symbolicInitialCfgWires, CfgBundle.replaceStack,
      staticBoundedCfgWires, staticCfgWires, encodeRawCfgBits,
      emptyInitialCode, encodeCfg, _root_.Turing.initList, labelHalted]
  · by_cases hlabel :
      label = encodeLabel W.machine.tm (some W.machine.tm.main)
    <;> simp [verifierInitialSlotRightWire, CfgSlot.label,
      symbolicInitialCfgWires, CfgBundle.replaceStack,
      staticBoundedCfgWires, staticCfgWires, encodeRawCfgBits,
      emptyInitialCode, encodeCfg, _root_.Turing.initList,
      encodeOneHot, hlabel]
  · by_cases hstate :
      state = stateEquivFin W.machine.tm W.machine.tm.initialState
    <;> simp [verifierInitialSlotRightWire, CfgSlot.state,
      symbolicInitialCfgWires, CfgBundle.replaceStack,
      staticBoundedCfgWires, staticCfgWires, encodeRawCfgBits,
      emptyInitialCode, encodeCfg, _root_.Turing.initList,
      encodeOneHot, hstate]
  · by_cases hk : k = W.machine.tm.k₀
    · subst k
      simp only [verifierInitialSlotRightWire, CfgSlot.stackHeight,
        dite_true, symbolicInitialCfgWires,
        CfgBundle.replaceStack, CfgBundle.stack, CfgBundle.stackHeight]
      rw [verifierRowWire_eq]
      simp [verifierFirstRow]
    · by_cases hheight : height.val = 0
      · have hfin : height = 0 := Fin.ext hheight
        simp [verifierInitialSlotRightWire, CfgSlot.stackHeight, hk,
          hheight, hfin, symbolicInitialCfgWires, CfgBundle.replaceStack,
          staticBoundedCfgWires, staticCfgWires, encodeRawCfgBits,
          emptyInitialCode, encodeCfg, _root_.Turing.initList,
          encodeOneHot, encodeBoundedStack]
      · have hfin : height ≠ 0 := fun heq =>
          hheight (congrArg Fin.val heq)
        simp [verifierInitialSlotRightWire, CfgSlot.stackHeight, hk,
          hheight, hfin, symbolicInitialCfgWires, CfgBundle.replaceStack,
          staticBoundedCfgWires, staticCfgWires, encodeRawCfgBits,
          emptyInitialCode, encodeCfg, _root_.Turing.initList,
          encodeOneHot, encodeBoundedStack]
  · rcases cell with ⟨cell, symbol⟩
    by_cases hk : k = W.machine.tm.k₀
    · subst k
      simp only [verifierInitialSlotRightWire, CfgSlot.stackCell,
        dite_true, symbolicInitialCfgWires,
        CfgBundle.replaceStack, CfgBundle.stack, CfgBundle.stackCell]
      rw [verifierRowWire_eq]
      simp [verifierFirstRow]
    · by_cases hsymbol :
        symbol.val = (reachableAlphabet W.machine.tm k).card
      <;> simp [verifierInitialSlotRightWire, CfgSlot.stackCell, hk,
        hsymbol, symbolicInitialCfgWires, CfgBundle.replaceStack,
        staticBoundedCfgWires, staticCfgWires, encodeRawCfgBits,
        emptyInitialCode, encodeCfg, _root_.Turing.initList,
        encodeOneHot, encodeBoundedStack, Fin.ext_iff]

/-- Canonical initial equality frame at one numeric row coordinate. -/
def verifierInitialFrameAtCoordinate
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (coordinate right : Nat) : AffineEqFinPairFrame :=
  let start := (verifierTransitionEndPolynomial W).eval input.length
  { eqStart := start + 1 + 6 * coordinate
    left := coordinate
    right := right
    matched := start + 5 + 6 * coordinate
    previous := start + 6 * coordinate }

/-- Canonical equality frame attached to one explicit public slot. -/
def verifierInitialSlotFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) :
    AffineEqFinPairFrame :=
  let coordinate :=
    (cfgSlotEquivFin W.machine.tm
      ((verifierHeight W).eval input.length) slot).val
  verifierInitialFrameAtCoordinate W input coordinate
    (verifierInitialSlotRightWire W input slot)

/-- The old proof-carrying semantic frame family is exactly the explicit
canonical public-slot map. -/
theorem compileVerifierInitialBoundaryFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    compileVerifierInitialBoundaryFrames W input =
      (transitionEqPublicSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierInitialSlotFrame W input) := by
  unfold compileVerifierInitialBoundaryFrames
  rw [affineEqFinCanonicalFrames_eq_ofFn]
  calc
    (List.ofFn fun coordinate =>
        { eqStart := (verifierTransitions W input).builder.gates.length +
              1 + 6 * coordinate.val
          left := (verifierRows W input).rows (verifierFirstRow _)
            ((cfgSlotEquivFin W.machine.tm
              ((verifierHeight W).eval input.length)).symm coordinate)
          right := symbolicInitialCfgWires W.machine.tm
            ((verifierHeight W).eval input.length)
            ((verifierPool W input).pool.mono
              ((verifierValidity W input).extension.trans
                (verifierTransitions W input).extension))
            (((verifierRows W input).rows (verifierFirstRow _)).stack
              W.machine.tm.k₀)
            ((cfgSlotEquivFin W.machine.tm
              ((verifierHeight W).eval input.length)).symm coordinate)
          matched := (verifierTransitions W input).builder.gates.length +
            5 + 6 * coordinate.val
          previous := (verifierTransitions W input).builder.gates.length +
            6 * coordinate.val }) =
        List.ofFn (fun coordinate : Fin
            (cfgBitCount W.machine.tm
              ((verifierHeight W).eval input.length)) =>
          verifierInitialSlotFrame W input
            ((cfgSlotEquivFin W.machine.tm
              ((verifierHeight W).eval input.length)).symm coordinate)) := by
      apply List.ofFn_inj.mpr
      funext coordinate
      unfold verifierInitialSlotFrame verifierInitialFrameAtCoordinate
      rw [verifierTransitionEndPolynomial_eval_eq_builder]
      rw [verifierInitialSlotRightWire_eq_semantic]
      rw [verifierRowWire_eq]
      simp [verifierFirstRow]
    _ = _ := by
      rw [transitionEqPublicSlots_eq_canonical, List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext coordinate
      rfl

/-! ## Frames denoted by the concrete polynomial sources -/

def verifierInitialControlCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineEqFinPairFrame :=
  exactPolynomialAffineEqFinRowFrames
    (initialControlTargetForms W.machine.tm)
    (verifierTransitionEndPolynomial W) 0
    (verifierInitialFalseWirePolynomial W)
    0 0 0 1 input

def verifierInitialInputStackCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineEqFinPairFrame :=
  let coordinate := verifierInitialStackOffsetPolynomial W W.machine.tm.k₀
  exactPolynomialAffineEqFinFrames
    (verifierInitialPreviousPolynomial W coordinate)
    coordinate coordinate
    6 1 1
    (verifierInitialStackWidthPolynomial W W.machine.tm.k₀) input

def verifierInitialEmptyStackCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    List AffineEqFinPairFrame :=
  let coordinate := verifierInitialStackOffsetPolynomial W k
  exactPolynomialAffineEqFinFrames
      (verifierInitialPreviousPolynomial W coordinate)
      coordinate (verifierInitialFalseWirePolynomial W + 1)
      0 0 0 1 input ++
    exactPolynomialAffineEqFinFrames
      (verifierInitialPreviousPolynomial W (coordinate + 1))
      (coordinate + 1) (verifierInitialFalseWirePolynomial W)
      6 1 0 (verifierHeight W) input ++
    exactPolynomialAffineEqFinRowFrames
      (initialBlankCellTargetForms W.machine.tm k)
      (verifierInitialPreviousPolynomial W
        (coordinate + verifierHeight W + 1))
      (coordinate + verifierHeight W + 1)
      (verifierInitialFalseWirePolynomial W)
      (Polynomial.C
        (6 * ((reachableAlphabet W.machine.tm k).card + 1)))
      (Polynomial.C ((reachableAlphabet W.machine.tm k).card + 1))
      0 (verifierHeight W) input

def verifierInitialStackCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    List AffineEqFinPairFrame :=
  if _hk : k = W.machine.tm.k₀ then
    verifierInitialInputStackCompiledFrames W input
  else
    verifierInitialEmptyStackCompiledFrames W k input

def verifierInitialStackFamilyCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineEqFinPairFrame :=
  (arithmeticRuntimeStackSourceIndices W.machine.tm).flatMap fun index =>
    verifierInitialStackCompiledFrames W
      ((arithmeticStackEquiv W.machine.tm).symm index) input

def verifierInitialBoundaryCompiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineEqFinPairFrame :=
  verifierInitialControlCompiledFrames W input ++
    verifierInitialStackFamilyCompiledFrames W input

private theorem encodeAffineEqFinFrames_flatMap {α : Type}
    (items : List α) (frames : α → List AffineEqFinPairFrame) :
    encodeAffineEqFinFrames (items.flatMap frames) =
      items.flatMap fun item => encodeAffineEqFinFrames (frames item) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.flatMap_cons]
      unfold encodeAffineEqFinFrames at ih ⊢
      rw [List.flatMap_append]
      rw [ih]

/-- The concrete source target is the canonical serialization of its
explicit compiled frame family. -/
theorem verifierInitialBoundaryInputTarget_eq_compiledFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialBoundaryInputTarget W input =
      encodeAffineEqFinFrames
        (verifierInitialBoundaryCompiledFrames W input) := by
  unfold verifierInitialBoundaryInputTarget
    verifierInitialControlInput verifierInitialStackFamilyInput
    verifierInitialBoundaryCompiledFrames
    verifierInitialControlCompiledFrames
    verifierInitialStackFamilyCompiledFrames
    exactPolynomialAffineEqFinRowInput
  rw [show encodeAffineEqFinFrames
      (exactPolynomialAffineEqFinRowFrames
          (initialControlTargetForms W.machine.tm)
          (verifierTransitionEndPolynomial W) 0
          (verifierInitialFalseWirePolynomial W) 0 0 0 1 input ++
        (arithmeticRuntimeStackSourceIndices W.machine.tm).flatMap fun index =>
          verifierInitialStackCompiledFrames W
            ((arithmeticStackEquiv W.machine.tm).symm index) input) =
      encodeAffineEqFinFrames
          (exactPolynomialAffineEqFinRowFrames
            (initialControlTargetForms W.machine.tm)
            (verifierTransitionEndPolynomial W) 0
            (verifierInitialFalseWirePolynomial W) 0 0 0 1 input) ++
        encodeAffineEqFinFrames
          ((arithmeticRuntimeStackSourceIndices W.machine.tm).flatMap
            fun index => verifierInitialStackCompiledFrames W
              ((arithmeticStackEquiv W.machine.tm).symm index) input) by
        simp [encodeAffineEqFinFrames]]
  rw [encodeAffineEqFinFrames_flatMap]
  congr 1
  apply List.flatMap_congr
  intro index hindex
  let k := (arithmeticStackEquiv W.machine.tm).symm index
  change verifierInitialStackInput W k input =
    encodeAffineEqFinFrames (verifierInitialStackCompiledFrames W k input)
  by_cases hk : k = W.machine.tm.k₀
  · simp [verifierInitialStackInput, verifierInitialStackCompiledFrames,
      hk, verifierInitialInputStackInput,
      verifierInitialInputStackCompiledFrames,
      exactPolynomialAffineEqFinInput]
  · simp [verifierInitialStackInput, verifierInitialStackCompiledFrames,
      hk, verifierInitialEmptyStackHeightZeroInput,
      verifierInitialEmptyStackHeightTailInput,
      verifierInitialEmptyStackCellsInput,
      verifierInitialEmptyStackCompiledFrames,
      exactPolynomialAffineEqFinInput,
      exactPolynomialAffineEqFinRowInput, encodeAffineEqFinFrames,
      List.append_assoc]

/-! ## Segment alignment -/

private theorem flatMap_ofFn_apply
    {α β : Type} {count : Nat} (items : Fin count → α)
    (emit : α → List β) :
    (List.ofFn items).flatMap emit =
      (List.ofFn fun index => emit (items index)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [List.flatMap_cons, List.flatten_cons]
      congr 1
      exact ih (fun index => items index.succ)

/-- The symbolic input-stack source is the consecutive coordinate block in
which both equality operands are the public first-row wires. -/
theorem verifierInitialInputStackCompiledFrames_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialInputStackCompiledFrames W input =
      let offset := initialControlWidth W.machine.tm +
        cfgStackBitOffset W.machine.tm
          ((verifierHeight W).eval input.length) W.machine.tm.k₀
      List.ofFn fun index : Fin
          (cfgStackBitWidth W.machine.tm
            ((verifierHeight W).eval input.length) W.machine.tm.k₀) =>
        verifierInitialFrameAtCoordinate W input
          (offset + index.val) (offset + index.val) := by
  unfold verifierInitialInputStackCompiledFrames
  rw [exactPolynomialAffineEqFinFrames_eq_ofFn]
  dsimp only
  simp only [verifierInitialStackWidthPolynomial_eval]
  apply List.ofFn_inj.mpr
  funext index
  simp only [verifierInitialStackOffsetPolynomial_eval,
    verifierInitialPreviousPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C,
    verifierInitialFrameAtCoordinate]
  congr 1 <;> simp <;> ring

/-- On the designated input stack, the slot right target is its own public
wire coordinate. -/
theorem verifierInitialInputStackSlotFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length))
    (hslot : slot ∈ transitionEqStackSlots W.machine.tm
      ((verifierHeight W).eval input.length) W.machine.tm.k₀) :
    verifierInitialSlotFrame W input slot =
      verifierInitialFrameAtCoordinate W input
        (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length) slot).val
        (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length) slot).val := by
  unfold verifierInitialSlotFrame
  unfold transitionEqStackSlots at hslot
  simp only [List.mem_append, List.mem_ofFn, List.mem_flatten] at hslot
  rcases hslot with ⟨height, rfl⟩ | ⟨cellRow, hcellRow, hcell⟩
  · simp [verifierInitialSlotRightWire, CfgSlot.stackHeight]
  · rcases hcellRow with ⟨cell, rfl⟩
    simp only [List.mem_ofFn] at hcell
    rcases hcell with ⟨symbol, rfl⟩
    simp [verifierInitialSlotRightWire, CfgSlot.stackCell]

/-- The compiled designated-stack block is exactly its canonical slot map. -/
theorem verifierInitialInputStackCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialInputStackCompiledFrames W input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) W.machine.tm.k₀).map
          (verifierInitialSlotFrame W input) := by
  rw [verifierInitialInputStackCompiledFrames_eq_ofFn]
  let slots := transitionEqStackSlots W.machine.tm
    ((verifierHeight W).eval input.length) W.machine.tm.k₀
  have hvalues := transitionEqStackSlots_values W.machine.tm
    ((verifierHeight W).eval input.length) W.machine.tm.k₀
  have hframes : slots.map (verifierInitialSlotFrame W input) =
      slots.map (fun slot => verifierInitialFrameAtCoordinate W input
        (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length) slot).val
        (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length) slot).val) := by
    apply List.map_congr_left
    intro slot hslot
    exact verifierInitialInputStackSlotFrame_eq W input slot hslot
  rw [hframes]
  let coordinate : CfgSlot W.machine.tm
      ((verifierHeight W).eval input.length) → Nat := fun slot =>
    (cfgSlotEquivFin W.machine.tm
      ((verifierHeight W).eval input.length) slot).val
  let frame : Nat → AffineEqFinPairFrame := fun value =>
    verifierInitialFrameAtCoordinate W input value value
  change _ = slots.map (fun slot => frame (coordinate slot))
  rw [show slots.map (fun slot => frame (coordinate slot)) =
      (slots.map coordinate).map frame by simp [List.map_map]]
  change slots.map coordinate = _ at hvalues
  rw [hvalues]
  apply List.ext_getElem
  · simp [initialControlWidth, transitionEqPrefixWidth]
  · intro index hleft hright
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
    unfold frame
    congr 1 <;>
      simp [initialControlWidth, transitionEqPrefixWidth] <;> ring

/-- Closed explicit frame list of one empty non-input stack. -/
def verifierInitialEmptyStackExpectedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    List AffineEqFinPairFrame :=
  let tm := W.machine.tm
  let H := (verifierHeight W).eval input.length
  let offset := initialControlWidth tm + cfgStackBitOffset tm H k
  let falseWire := (verifierInitialFalseWirePolynomial W).eval input.length
  [verifierInitialFrameAtCoordinate W input offset (falseWire + 1)] ++
    (List.ofFn fun index : Fin H =>
      verifierInitialFrameAtCoordinate W input
        (offset + 1 + index.val) falseWire) ++
    (List.ofFn fun cell : Fin H =>
      List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
        verifierInitialFrameAtCoordinate W input
          (offset + (H + 1) +
            ((reachableAlphabet tm k).card + 1) * cell.val + symbol.val)
          (if symbol.val = (reachableAlphabet tm k).card then
            falseWire + 1
          else falseWire)).flatten

/-- The three exact-polynomial empty-stack segments expand to their closed
height/cell frame list. -/
theorem verifierInitialEmptyStackCompiledFrames_eq_expected
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierInitialEmptyStackCompiledFrames W k input =
      verifierInitialEmptyStackExpectedFrames W k input := by
  unfold verifierInitialEmptyStackCompiledFrames
    verifierInitialEmptyStackExpectedFrames
  dsimp only
  rw [exactPolynomialAffineEqFinFrames_eq_ofFn,
    exactPolynomialAffineEqFinFrames_eq_ofFn,
    exactPolynomialAffineEqFinRowFrames_eq_flatMap_ofFn]
  apply congrArg₂ (· ++ ·)
  · apply congrArg₂ (· ++ ·)
    · simp only [Polynomial.eval_one]
      rw [List.ofFn_succ, List.ofFn_zero]
      congr 1 <;>
        simp [verifierInitialStackOffsetPolynomial_eval,
          verifierInitialPreviousPolynomial,
          verifierInitialFrameAtCoordinate] <;> ring <;> simp
    · apply List.ofFn_inj.mpr
      funext index
      simp [verifierInitialStackOffsetPolynomial_eval,
        verifierInitialPreviousPolynomial,
        verifierInitialFrameAtCoordinate] <;> ring <;> simp
  · rw [flatMap_ofFn_apply]
    apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext cell
    rw [show initialBlankCellTargetForms W.machine.tm k =
        List.ofFn (fun symbol : Fin
          ((reachableAlphabet W.machine.tm k).card + 1) =>
            initialPoolTargetForm
              (decide (symbol.val =
                (reachableAlphabet W.machine.tm k).card))) by rfl]
    rw [affineEqFinRowFrames_ofFn]
    apply List.ofFn_inj.mpr
    funext symbol
    by_cases hsymbol :
        symbol.val = (reachableAlphabet W.machine.tm k).card
    <;> simp [verifierInitialStackOffsetPolynomial_eval,
      verifierInitialPreviousPolynomial, verifierInitialFrameAtCoordinate,
      affineUnaryTripleFormValue, initialPoolTargetForm, hsymbol]
    <;> ring <;> simp

/-- For a non-input stack, the arithmetic slot map is the same closed empty
height/cell frame list. -/
theorem verifierInitialEmptyStackExpectedFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (hk : k ≠ W.machine.tm.k₀)
    (input : List Γ) :
    verifierInitialEmptyStackExpectedFrames W k input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) k).map
          (verifierInitialSlotFrame W input) := by
  have hheightCoordinate
      (height : Fin ((verifierHeight W).eval input.length + 1)) :
      (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length)
          (CfgSlot.stackHeight k height)).val =
        initialControlWidth W.machine.tm +
          cfgStackBitOffset W.machine.tm
            ((verifierHeight W).eval input.length) k + height.val := by
    rw [cfgSlotEquivFin_stackHeight_val]
    unfold initialControlWidth
    ring
  have hcellCoordinate
      (cell : Fin ((verifierHeight W).eval input.length))
      (symbol : Fin ((reachableAlphabet W.machine.tm k).card + 1)) :
      (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length)
          (CfgSlot.stackCell k cell symbol)).val =
        initialControlWidth W.machine.tm +
          cfgStackBitOffset W.machine.tm
            ((verifierHeight W).eval input.length) k +
          (((verifierHeight W).eval input.length) + 1) +
          ((reachableAlphabet W.machine.tm k).card + 1) * cell.val +
          symbol.val := by
    rw [cfgSlotEquivFin_stackCell_val]
    unfold initialControlWidth
    ring
  unfold verifierInitialEmptyStackExpectedFrames transitionEqStackSlots
  rw [List.map_append, List.map_flatten, List.map_ofFn]
  simp_rw [List.map_ofFn]
  apply congrArg₂ (· ++ ·)
  · rw [List.ofFn_succ]
    apply congrArg₂ List.cons
    · simp only [Function.comp_apply]
      unfold verifierInitialSlotFrame
      rw [hheightCoordinate]
      simp [verifierInitialSlotRightWire, CfgSlot.stackHeight, hk,
        verifierInitialFalseWirePolynomial_eval,
        verifierInitialFrameAtCoordinate] <;> ring <;> try simp
    · apply List.ofFn_inj.mpr
      funext height
      simp only [Function.comp_apply]
      unfold verifierInitialSlotFrame
      rw [hheightCoordinate]
      simp [verifierInitialSlotRightWire, CfgSlot.stackHeight, hk,
        verifierInitialFalseWirePolynomial_eval,
        verifierInitialFrameAtCoordinate] <;> ring <;> try simp
  · apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext cell
    simp only [Function.comp_apply, List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext symbol
    simp only [Function.comp_apply]
    unfold verifierInitialSlotFrame
    rw [hcellCoordinate]
    by_cases hsymbol :
        symbol.val = (reachableAlphabet W.machine.tm k).card
    <;> simp [verifierInitialSlotRightWire, CfgSlot.stackCell, hk,
      hsymbol, verifierInitialFalseWirePolynomial_eval,
      verifierInitialFrameAtCoordinate]
    <;> ring <;> try simp

/-- Every non-input stack source is exactly its canonical public-slot map. -/
theorem verifierInitialEmptyStackCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (hk : k ≠ W.machine.tm.k₀)
    (input : List Γ) :
    verifierInitialEmptyStackCompiledFrames W k input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) k).map
          (verifierInitialSlotFrame W input) := by
  rw [verifierInitialEmptyStackCompiledFrames_eq_expected,
    verifierInitialEmptyStackExpectedFrames_eq_slotFrames W k hk]

/-! ## Fixed control-prefix alignment -/

/-- Boolean pool selection used by the fixed initial control prefix. -/
def initialPoolWire (falseWire : Nat) : Bool → Nat
  | false => falseWire
  | true => falseWire + 1

@[simp] theorem initialControlBits_length
    (tm : _root_.Turing.FinTM2) :
    (initialControlBits tm).length = initialControlWidth tm := by
  simp [initialControlBits, initialControlWidth]
  ring

theorem initialControlWidth_eq_transitionEqPrefixWidth
    (tm : _root_.Turing.FinTM2) :
    initialControlWidth tm = transitionEqPrefixWidth tm := by
  unfold initialControlWidth transitionEqPrefixWidth
  ring

/-- Reading the semantic initial target on the explicit prefix slots gives
exactly the fixed halted/label/state bit table. -/
theorem transitionEqPrefixSlots_initialRightWires
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (transitionEqPrefixSlots W.machine.tm
      ((verifierHeight W).eval input.length)).map
        (verifierInitialSlotRightWire W input) =
      (initialControlBits W.machine.tm).map
        (initialPoolWire
          ((verifierInitialFalseWirePolynomial W).eval input.length)) := by
  unfold transitionEqPrefixSlots initialControlBits
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_ofFn]
  apply congrArg₂ List.cons
  · simp [verifierInitialSlotRightWire, CfgSlot.halted, initialPoolWire]
  · change
      (List.ofFn fun label : Fin (labelCount W.machine.tm + 1) =>
        verifierInitialSlotRightWire W input (CfgSlot.label label)) ++
        (List.ofFn fun state : Fin (stateCount W.machine.tm) =>
          verifierInitialSlotRightWire W input (CfgSlot.state state)) =
      (List.ofFn fun label : Fin (labelCount W.machine.tm + 1) =>
        initialPoolWire
          ((verifierInitialFalseWirePolynomial W).eval input.length)
          (encodeOneHot (encodeLabel W.machine.tm
            (some W.machine.tm.main)) label)) ++
        (List.ofFn fun state : Fin (stateCount W.machine.tm) =>
          initialPoolWire
            ((verifierInitialFalseWirePolynomial W).eval input.length)
            (encodeOneHot
              (stateEquivFin W.machine.tm W.machine.tm.initialState) state))
    apply congrArg₂ (· ++ ·)
    · apply List.ofFn_inj.mpr
      funext label
      by_cases hlabel :
          label = encodeLabel W.machine.tm (some W.machine.tm.main)
      <;> simp [verifierInitialSlotRightWire, CfgSlot.label,
        encodeOneHot, initialPoolWire, hlabel]
    · apply List.ofFn_inj.mpr
      funext state
      by_cases hstate :
          state = stateEquivFin W.machine.tm W.machine.tm.initialState
      <;> simp [verifierInitialSlotRightWire, CfgSlot.state,
        encodeOneHot, initialPoolWire, hstate]

/-- The fixed row source expands to one canonical frame for every control
bit, in the bit table's own order. -/
theorem verifierInitialControlCompiledFrames_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialControlCompiledFrames W input =
      List.ofFn fun index : Fin (initialControlBits W.machine.tm).length =>
        verifierInitialFrameAtCoordinate W input index.val
          (initialPoolWire
            ((verifierInitialFalseWirePolynomial W).eval input.length)
            ((initialControlBits W.machine.tm).get index)) := by
  unfold verifierInitialControlCompiledFrames
  rw [exactPolynomialAffineEqFinRowFrames_eq_flatMap_ofFn]
  simp only [Polynomial.eval_one]
  rw [List.ofFn_succ, List.ofFn_zero]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show initialControlTargetForms W.machine.tm =
      List.ofFn (fun index : Fin (initialControlBits W.machine.tm).length =>
        initialPoolTargetForm
          ((initialControlBits W.machine.tm).get index)) by
      unfold initialControlTargetForms
      symm
      have h := congrArg (List.map initialPoolTargetForm)
        (List.ofFn_get (initialControlBits W.machine.tm))
      rw [List.map_ofFn] at h
      change (List.ofFn fun index :
          Fin (initialControlBits W.machine.tm).length =>
            initialPoolTargetForm
              ((initialControlBits W.machine.tm).get index)) =
        (initialControlBits W.machine.tm).map initialPoolTargetForm at h
      exact h]
  rw [affineEqFinRowFrames_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  cases hbit : (initialControlBits W.machine.tm).get index
  <;> simp [affineUnaryTripleFormValue, initialPoolTargetForm,
    initialPoolWire, verifierInitialFrameAtCoordinate, hbit]
  <;> ring <;> simp

private theorem mapValue_at_of_eq
    {α β : Type} (items : List α) (value : α → β) (values : List β)
    (hvalues : items.map value = values)
    (index : Nat) (hitems : index < items.length)
    (hvaluesIndex : index < values.length) :
    value items[index] = values[index] := by
  have hget := congrArg (fun entries : List β => entries[index]?) hvalues
  simp only [List.getElem?_map] at hget
  rw [List.getElem?_eq_getElem hitems,
    List.getElem?_eq_getElem hvaluesIndex] at hget
  simpa using hget

private theorem mapNatValue_at_of_eq_range
    {α : Type} (items : List α) (value : α → Nat)
    (base count : Nat)
    (hvalues : items.map value = List.range' base count)
    (index : Nat) (hitems : index < items.length) :
    value items[index] = base + index := by
  have hcount : items.length = count := by
    simpa using congrArg List.length hvalues
  have hindex : index < count := by omega
  have hget := mapValue_at_of_eq items value (List.range' base count)
    hvalues index hitems (by simp [hindex])
  simpa using hget

/-- The concrete fixed-prefix source is exactly the canonical prefix-slot
map used by the semantic initial boundary. -/
theorem verifierInitialControlCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialControlCompiledFrames W input =
      (transitionEqPrefixSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierInitialSlotFrame W input) := by
  rw [verifierInitialControlCompiledFrames_eq_ofFn]
  let slots := transitionEqPrefixSlots W.machine.tm
    ((verifierHeight W).eval input.length)
  let bits := initialControlBits W.machine.tm
  let falseWire :=
    (verifierInitialFalseWirePolynomial W).eval input.length
  have hcoordinates : slots.map (fun slot =>
      (cfgSlotEquivFin W.machine.tm
        ((verifierHeight W).eval input.length) slot).val) =
      List.range' 0 (transitionEqPrefixWidth W.machine.tm) :=
    transitionEqPrefixSlots_values W.machine.tm
      ((verifierHeight W).eval input.length)
  have hrights : slots.map (verifierInitialSlotRightWire W input) =
      bits.map (initialPoolWire falseWire) :=
    transitionEqPrefixSlots_initialRightWires W input
  have hslotsLength : slots.length = transitionEqPrefixWidth W.machine.tm := by
    simpa using congrArg List.length hcoordinates
  have hbitsLength : bits.length = transitionEqPrefixWidth W.machine.tm := by
    simp [bits, initialControlWidth_eq_transitionEqPrefixWidth]
  apply List.ext_getElem
  · simp [slots, bits, hslotsLength, hbitsLength]
  · intro index hleft hright
    simp only [List.getElem_ofFn, List.getElem_map]
    have hslotIndex : index < slots.length := by simpa [slots] using hright
    have hbitIndex : index < bits.length := by simpa [bits] using hleft
    have hcoordinate := mapNatValue_at_of_eq_range slots
      (fun slot => (cfgSlotEquivFin W.machine.tm
        ((verifierHeight W).eval input.length) slot).val)
      0 (transitionEqPrefixWidth W.machine.tm) hcoordinates
      index hslotIndex
    have hprefixIndex :
        index < transitionEqPrefixWidth W.machine.tm := by
      simpa [hslotsLength] using hslotIndex
    have hrightValue := mapValue_at_of_eq slots
      (verifierInitialSlotRightWire W input)
      (bits.map (initialPoolWire falseWire)) hrights
      index hslotIndex (by simpa [hbitsLength] using hprefixIndex)
    simp only [List.getElem_map] at hrightValue
    unfold verifierInitialSlotFrame
    rw [hcoordinate, hrightValue]
    simp only [Nat.zero_add]
    rfl

/-! ## Complete initial-boundary closure -/

/-- Either stack source, including the symbolic designated stack, agrees
with the corresponding canonical public-slot block. -/
theorem verifierInitialStackCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierInitialStackCompiledFrames W k input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) k).map
          (verifierInitialSlotFrame W input) := by
  by_cases hk : k = W.machine.tm.k₀
  · subst k
    simpa [verifierInitialStackCompiledFrames] using
      verifierInitialInputStackCompiledFrames_eq_slotFrames W input
  · simpa [verifierInitialStackCompiledFrames, hk] using
      verifierInitialEmptyStackCompiledFrames_eq_slotFrames W k hk input

/-- The finite compiled stack family is the semantic stack-slot family in
the fixed machine-stack order. -/
theorem verifierInitialStackFamilyCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialStackFamilyCompiledFrames W input =
      (((arithmeticRuntimeStackSourceIndices W.machine.tm).map fun position =>
        transitionEqStackSlots W.machine.tm
          ((verifierHeight W).eval input.length)
          ((arithmeticStackEquiv W.machine.tm).symm position)).flatten).map
        (verifierInitialSlotFrame W input) := by
  unfold verifierInitialStackFamilyCompiledFrames
  rw [List.map_flatten, List.map_map, List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro position hposition
  change verifierInitialStackCompiledFrames W
      ((arithmeticStackEquiv W.machine.tm).symm position) input =
    (transitionEqStackSlots W.machine.tm
      ((verifierHeight W).eval input.length)
      ((arithmeticStackEquiv W.machine.tm).symm position)).map
        (verifierInitialSlotFrame W input)
  exact verifierInitialStackCompiledFrames_eq_slotFrames W _ input

/-- All explicit source frames, prefix and stacks, are exactly the public
slot map used by the semantic initial-boundary proof. -/
theorem verifierInitialBoundaryCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialBoundaryCompiledFrames W input =
      (transitionEqPublicSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierInitialSlotFrame W input) := by
  unfold verifierInitialBoundaryCompiledFrames transitionEqPublicSlots
  rw [List.map_append,
    verifierInitialControlCompiledFrames_eq_slotFrames,
    verifierInitialStackFamilyCompiledFrames_eq_slotFrames]

/-- The raw-input source target is the old proof-carrying semantic initial
boundary serialization, not merely an arithmetically similar candidate. -/
theorem verifierInitialBoundaryInputTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInitialBoundaryInputTarget W input =
      encodeAffineEqFinFrames
        (compileVerifierInitialBoundaryFrames W input) := by
  rw [verifierInitialBoundaryInputTarget_eq_compiledFrames,
    verifierInitialBoundaryCompiledFrames_eq_slotFrames,
    compileVerifierInitialBoundaryFrames_eq_slotFrames]

/-- A single fixed polynomial-time TM2 computes the canonical semantic
initial-boundary equality input directly from the raw verifier word. -/
noncomputable def verifierInitialBoundaryInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ =>
        encodeAffineEqFinFrames
          (compileVerifierInitialBoundaryFrames W input)) := by
  let source := verifierInitialBoundaryInputTarget_computableInPolyTime W
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have run := source.outputsFun input
        simpa only [verifierInitialBoundaryInputTarget_eq_canonical] using run }

end CLRS.Chapter34.Turing.CookLevin
