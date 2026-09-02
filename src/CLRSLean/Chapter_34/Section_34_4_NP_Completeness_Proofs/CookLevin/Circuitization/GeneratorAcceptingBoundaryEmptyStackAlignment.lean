import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryAlignment
import Mathlib.Tactic

/-!
# Accepting-boundary alignment for empty stacks

This module isolates the repeated empty-stack block of the concrete
accepting source.  It expands the three generated progressions and identifies
them with the canonical height/cell slots of a non-output stack.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem accepting_flatMap_ofFn_apply
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

/-- Closed explicit frame list for an empty stack in the accepting row. -/
def verifierAcceptingEmptyStackExpectedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    List AffineEqFinPairFrame :=
  let tm := W.machine.tm
  let H := (verifierHeight W).eval input.length
  let offset := initialControlWidth tm + cfgStackBitOffset tm H k
  let falseWire := (verifierInitialFalseWirePolynomial W).eval input.length
  [verifierAcceptingFrameAtCoordinate W input offset (falseWire + 1)] ++
    (List.ofFn fun index : Fin H =>
      verifierAcceptingFrameAtCoordinate W input
        (offset + 1 + index.val) falseWire) ++
    (List.ofFn fun cell : Fin H =>
      List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
        verifierAcceptingFrameAtCoordinate W input
          (offset + (H + 1) +
            ((reachableAlphabet tm k).card + 1) * cell.val + symbol.val)
          (if symbol.val = (reachableAlphabet tm k).card then
            falseWire + 1
          else falseWire)).flatten

/-- The dynamic-first source for an empty stack expands to its closed
height/cell frame list. -/
theorem verifierAcceptingEmptyStackCompiledFrames_eq_expected
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierAcceptingEmptyStackCompiledFrames W k input =
      verifierAcceptingEmptyStackExpectedFrames W k input := by
  unfold verifierAcceptingEmptyStackCompiledFrames
    verifierAcceptingEmptyStackExpectedFrames
    verifierAcceptingSegmentFrames verifierAcceptingRowSegmentFrames
  dsimp only
  rw [dynamicFirstAffineEqFinFrames_eq_ofFn,
    dynamicFirstAffineEqFinFrames_eq_ofFn,
    dynamicFirstAffineEqFinRowFrames_eq_flatMap_ofFn]
  apply congrArg₂ (· ++ ·)
  · apply congrArg₂ (· ++ ·)
    · simp only [Polynomial.eval_one]
      rw [List.ofFn_succ, List.ofFn_zero]
      congr 1 <;>
        simp [verifierInitialStackOffsetPolynomial_eval,
          verifierAcceptingPrevious,
          verifierAcceptingFrameAtCoordinate] <;> ring <;> simp
    · apply List.ofFn_inj.mpr
      funext index
      simp [verifierInitialStackOffsetPolynomial_eval,
        verifierAcceptingPrevious,
        verifierAcceptingFrameAtCoordinate] <;> ring <;> simp
  · rw [accepting_flatMap_ofFn_apply]
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
      verifierAcceptingPrevious, verifierAcceptingFrameAtCoordinate,
      affineUnaryTripleFormValue, initialPoolTargetForm, hsymbol]
    <;> ring <;> simp

/-- For a non-output stack, the arithmetic accepting slot map is the same
closed empty height/cell frame list. -/
theorem verifierAcceptingEmptyStackExpectedFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (k : W.machine.tm.K) (hk : k ≠ W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingEmptyStackExpectedFrames W k input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) k).map
          (verifierAcceptingSlotFrame W hmember input) := by
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
  unfold verifierAcceptingEmptyStackExpectedFrames transitionEqStackSlots
  rw [List.map_append, List.map_flatten, List.map_ofFn]
  simp_rw [List.map_ofFn]
  apply congrArg₂ (· ++ ·)
  · rw [List.ofFn_succ]
    apply congrArg₂ List.cons
    · simp only [Function.comp_apply]
      rw [verifierAcceptingSlotFrame_eq_arithmetic, hheightCoordinate]
      simp [verifierAcceptingSlotRightWire, CfgSlot.stackHeight, hk,
        verifierAcceptingFrameAtCoordinate] <;> ring <;> try simp
    · apply List.ofFn_inj.mpr
      funext height
      simp only [Function.comp_apply]
      rw [verifierAcceptingSlotFrame_eq_arithmetic, hheightCoordinate]
      simp [verifierAcceptingSlotRightWire, CfgSlot.stackHeight, hk,
        verifierAcceptingFrameAtCoordinate] <;> ring <;> try simp
  · apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext cell
    simp only [Function.comp_apply, List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext symbol
    simp only [Function.comp_apply]
    rw [verifierAcceptingSlotFrame_eq_arithmetic, hcellCoordinate]
    by_cases hsymbol :
        symbol.val = (reachableAlphabet W.machine.tm k).card
    <;> simp [verifierAcceptingSlotRightWire, CfgSlot.stackCell, hk,
      hsymbol, verifierAcceptingFrameAtCoordinate]
    <;> ring <;> try simp

/-- Every non-output stack source is exactly its canonical public-slot map. -/
theorem verifierAcceptingEmptyStackCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (k : W.machine.tm.K) (hk : k ≠ W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingEmptyStackCompiledFrames W k input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) k).map
          (verifierAcceptingSlotFrame W hmember input) := by
  rw [verifierAcceptingEmptyStackCompiledFrames_eq_expected,
    verifierAcceptingEmptyStackExpectedFrames_eq_slotFrames W hmember k hk]

end CLRS.Chapter34.Turing.CookLevin
