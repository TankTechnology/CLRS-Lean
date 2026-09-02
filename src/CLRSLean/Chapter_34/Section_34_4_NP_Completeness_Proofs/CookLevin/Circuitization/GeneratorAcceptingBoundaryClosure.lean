import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryOutputStackAlignment
import Mathlib.Tactic

/-!
# Complete closure of the accepting-boundary source

This module aligns the fixed halted/label/state prefix, joins all finite stack
blocks, and identifies the raw-input source with the semantic optional
accepting operand used by the continuous verifier-body controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

@[simp] theorem acceptingControlBits_length
    (tm : _root_.Turing.FinTM2) :
    (acceptingControlBits tm).length = initialControlWidth tm := by
  simp [acceptingControlBits, initialControlWidth]
  ring

/-- Reading the arithmetic accepting target on prefix slots gives the fixed
halted/label/state table. -/
theorem transitionEqPrefixSlots_acceptingRightWires
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    (transitionEqPrefixSlots W.machine.tm
      ((verifierHeight W).eval input.length)).map
        (verifierAcceptingSlotRightWire W hmember input) =
      (acceptingControlBits W.machine.tm).map
        (initialPoolWire
          ((verifierInitialFalseWirePolynomial W).eval input.length)) := by
  unfold transitionEqPrefixSlots acceptingControlBits
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_ofFn]
  apply congrArg₂ List.cons
  · simp [verifierAcceptingSlotRightWire, CfgSlot.halted, initialPoolWire]
  · change
      (List.ofFn fun label : Fin (labelCount W.machine.tm + 1) =>
        verifierAcceptingSlotRightWire W hmember input
          (CfgSlot.label label)) ++
        (List.ofFn fun state : Fin (stateCount W.machine.tm) =>
          verifierAcceptingSlotRightWire W hmember input
            (CfgSlot.state state)) =
      (List.ofFn fun label : Fin (labelCount W.machine.tm + 1) =>
        initialPoolWire
          ((verifierInitialFalseWirePolynomial W).eval input.length)
          (encodeOneHot (encodeLabel W.machine.tm none) label)) ++
        (List.ofFn fun state : Fin (stateCount W.machine.tm) =>
          initialPoolWire
            ((verifierInitialFalseWirePolynomial W).eval input.length)
            (encodeOneHot
              (stateEquivFin W.machine.tm W.machine.tm.initialState) state))
    apply congrArg₂ (· ++ ·)
    · apply List.ofFn_inj.mpr
      funext label
      by_cases hlabel : label = encodeLabel W.machine.tm none
      <;> simp [verifierAcceptingSlotRightWire, CfgSlot.label,
        encodeOneHot, initialPoolWire, hlabel]
    · apply List.ofFn_inj.mpr
      funext state
      by_cases hstate :
          state = stateEquivFin W.machine.tm W.machine.tm.initialState
      <;> simp [verifierAcceptingSlotRightWire, CfgSlot.state,
        encodeOneHot, initialPoolWire, hstate]

/-- The generated accepting control row expands in its Boolean-table order. -/
theorem verifierAcceptingControlCompiledFrames_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierAcceptingControlCompiledFrames W input =
      List.ofFn fun index : Fin (acceptingControlBits W.machine.tm).length =>
        verifierAcceptingFrameAtCoordinate W input index.val
          (initialPoolWire
            ((verifierInitialFalseWirePolynomial W).eval input.length)
            ((acceptingControlBits W.machine.tm).get index)) := by
  unfold verifierAcceptingControlCompiledFrames
    verifierAcceptingRowSegmentFrames
  rw [dynamicFirstAffineEqFinRowFrames_eq_flatMap_ofFn]
  simp only [Polynomial.eval_one]
  conv_lhs => rw [List.ofFn_succ, List.ofFn_zero]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show acceptingControlTargetForms W.machine.tm =
      List.ofFn (fun index : Fin (acceptingControlBits W.machine.tm).length =>
        initialPoolTargetForm
          ((acceptingControlBits W.machine.tm).get index)) by
      unfold acceptingControlTargetForms
      symm
      have h := congrArg (List.map initialPoolTargetForm)
        (List.ofFn_get (acceptingControlBits W.machine.tm))
      rw [List.map_ofFn] at h
      change (List.ofFn fun index :
          Fin (acceptingControlBits W.machine.tm).length =>
            initialPoolTargetForm
              ((acceptingControlBits W.machine.tm).get index)) =
        (acceptingControlBits W.machine.tm).map initialPoolTargetForm at h
      exact h]
  rw [affineEqFinRowFrames_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  cases hbit : (acceptingControlBits W.machine.tm).get index
  <;> simp [verifierAcceptingPrevious, affineUnaryTripleFormValue,
    initialPoolTargetForm, initialPoolWire,
    verifierAcceptingFrameAtCoordinate, hbit]
  <;> ring <;> simp

private theorem accepting_mapValue_at_of_eq
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

private theorem accepting_mapNatValue_at_of_eq_range
    {α : Type} (items : List α) (value : α → Nat)
    (base count : Nat)
    (hvalues : items.map value = List.range' base count)
    (index : Nat) (hitems : index < items.length) :
    value items[index] = base + index := by
  have hcount : items.length = count := by
    simpa using congrArg List.length hvalues
  have hindex : index < count := by omega
  have hget := accepting_mapValue_at_of_eq items value
    (List.range' base count) hvalues index hitems (by simp [hindex])
  simpa using hget

/-- The fixed accepting control source is exactly the canonical prefix map. -/
theorem verifierAcceptingControlCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingControlCompiledFrames W input =
      (transitionEqPrefixSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierAcceptingSlotFrame W hmember input) := by
  rw [verifierAcceptingControlCompiledFrames_eq_ofFn]
  let slots := transitionEqPrefixSlots W.machine.tm
    ((verifierHeight W).eval input.length)
  let bits := acceptingControlBits W.machine.tm
  let falseWire :=
    (verifierInitialFalseWirePolynomial W).eval input.length
  have hcoordinates : slots.map (fun slot =>
      (cfgSlotEquivFin W.machine.tm
        ((verifierHeight W).eval input.length) slot).val) =
      List.range' 0 (transitionEqPrefixWidth W.machine.tm) :=
    transitionEqPrefixSlots_values W.machine.tm
      ((verifierHeight W).eval input.length)
  have hrights : slots.map
      (verifierAcceptingSlotRightWire W hmember input) =
      bits.map (initialPoolWire falseWire) :=
    transitionEqPrefixSlots_acceptingRightWires W hmember input
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
    have hcoordinate := accepting_mapNatValue_at_of_eq_range slots
      (fun slot => (cfgSlotEquivFin W.machine.tm
        ((verifierHeight W).eval input.length) slot).val)
      0 (transitionEqPrefixWidth W.machine.tm) hcoordinates
      index hslotIndex
    have hprefixIndex : index < transitionEqPrefixWidth W.machine.tm := by
      simpa [hslotsLength] using hslotIndex
    have hrightValue := accepting_mapValue_at_of_eq slots
      (verifierAcceptingSlotRightWire W hmember input)
      (bits.map (initialPoolWire falseWire)) hrights
      index hslotIndex (by simpa [hbitsLength] using hprefixIndex)
    simp only [List.getElem_map] at hrightValue
    rw [verifierAcceptingSlotFrame_eq_arithmetic]
    rw [hcoordinate, hrightValue]
    simp only [Nat.zero_add]
    rfl

/-- Either accepting stack source agrees with its canonical stack-slot
block. -/
theorem verifierAcceptingStackCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierAcceptingStackCompiledFrames W hmember k input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) k).map
          (verifierAcceptingSlotFrame W hmember input) := by
  by_cases hk : k = W.machine.tm.k₁
  · subst k
    simpa [verifierAcceptingStackCompiledFrames] using
      verifierAcceptingOutputStackCompiledFrames_eq_slotFrames
        W hmember input
  · simpa [verifierAcceptingStackCompiledFrames, hk] using
      verifierAcceptingEmptyStackCompiledFrames_eq_slotFrames
        W hmember k hk input

/-- The finite accepting stack family is the semantic stack-slot family in
the fixed machine-stack order. -/
theorem verifierAcceptingStackFamilyCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingStackFamilyCompiledFrames W hmember input =
      (((arithmeticRuntimeStackSourceIndices W.machine.tm).map fun position =>
        transitionEqStackSlots W.machine.tm
          ((verifierHeight W).eval input.length)
          ((arithmeticStackEquiv W.machine.tm).symm position)).flatten).map
        (verifierAcceptingSlotFrame W hmember input) := by
  unfold verifierAcceptingStackFamilyCompiledFrames
  rw [List.map_flatten, List.map_map, List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro position hposition
  change verifierAcceptingStackCompiledFrames W hmember
      ((arithmeticStackEquiv W.machine.tm).symm position) input =
    (transitionEqStackSlots W.machine.tm
      ((verifierHeight W).eval input.length)
      ((arithmeticStackEquiv W.machine.tm).symm position)).map
        (verifierAcceptingSlotFrame W hmember input)
  exact verifierAcceptingStackCompiledFrames_eq_slotFrames W hmember _ input

/-- All accepting source frames are exactly the canonical public-slot map. -/
theorem verifierAcceptingBoundaryCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingBoundaryCompiledFrames W hmember input =
      (transitionEqPublicSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierAcceptingSlotFrame W hmember input) := by
  unfold verifierAcceptingBoundaryCompiledFrames transitionEqPublicSlots
  rw [List.map_append,
    verifierAcceptingControlCompiledFrames_eq_slotFrames,
    verifierAcceptingStackFamilyCompiledFrames_eq_slotFrames]

/-- In the static positive case, the raw source serializes the exact semantic
accepting-boundary frame family. -/
theorem verifierAcceptingBoundaryInputTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingBoundaryInputTarget W hmember input =
      encodeAffineEqFinFrames
        ((transitionEqPublicSlots W.machine.tm
          ((verifierHeight W).eval input.length)).map
            (verifierAcceptingSlotFrame W hmember input)) := by
  rw [verifierAcceptingBoundaryInputTarget_eq_compiledFrames,
    verifierAcceptingBoundaryCompiledFrames_eq_slotFrames]

end CLRS.Chapter34.Turing.CookLevin
