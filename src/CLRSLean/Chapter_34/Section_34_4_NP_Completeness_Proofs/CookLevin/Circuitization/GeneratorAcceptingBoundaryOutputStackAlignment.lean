import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryEmptyStackAlignment
import Mathlib.Tactic

/-!
# Accepting-boundary alignment for the output stack

The distinguished output stack has height one, contains the accepting symbol
in cell zero, and is blank thereafter.  This module expands exactly those five
source segments before aligning them with the canonical stack slots.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem acceptingOutput_flatMap_ofFn_apply
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

private theorem acceptingOutput_ofFn_eq_cons_of_add_one_eq
    {α : Type} {tail H : Nat} (hsize : tail + 1 = H)
    (items : Fin H → α) :
    List.ofFn items =
      items ⟨0, by omega⟩ ::
        List.ofFn (fun index : Fin tail =>
          items ⟨index.val + 1, by omega⟩) := by
  subst H
  rw [List.ofFn_succ]
  congr 1

/-- Closed segmented frame list for the distinguished accepting output
stack. -/
def verifierAcceptingOutputStackExpectedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) : List AffineEqFinPairFrame :=
  let tm := W.machine.tm
  let k := tm.k₁
  let width := (reachableAlphabet tm k).card + 1
  let tail := (verifierAcceptingHeightTailPolynomial W).eval input.length
  let H := (verifierHeight W).eval input.length
  let offset := initialControlWidth tm + cfgStackBitOffset tm H k
  let cells := offset + H + 1
  let falseWire := (verifierInitialFalseWirePolynomial W).eval input.length
  let outputCode := encodeAlphabetSymbol tm k
    (verifierAcceptingSymbol W) hmember
  [verifierAcceptingFrameAtCoordinate W input offset falseWire] ++
    [verifierAcceptingFrameAtCoordinate W input (offset + 1)
      (falseWire + 1)] ++
    (List.ofFn fun index : Fin tail =>
      verifierAcceptingFrameAtCoordinate W input
        (offset + 2 + index.val) falseWire) ++
    (List.ofFn fun symbol : Fin width =>
      verifierAcceptingFrameAtCoordinate W input
        (cells + symbol.val)
        (if symbol = outputCode then falseWire + 1 else falseWire)) ++
    (List.ofFn fun cell : Fin tail =>
      List.ofFn fun symbol : Fin width =>
        verifierAcceptingFrameAtCoordinate W input
          (cells + width + width * cell.val + symbol.val)
          (if symbol.val = (reachableAlphabet tm k).card then
            falseWire + 1
          else falseWire)).flatten

/-- The five generated output-stack segments expand to the closed accepting
height/output/blank-cell list. -/
theorem verifierAcceptingOutputStackCompiledFrames_eq_expected
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingOutputStackCompiledFrames W hmember input =
      verifierAcceptingOutputStackExpectedFrames W hmember input := by
  unfold verifierAcceptingOutputStackCompiledFrames
    verifierAcceptingOutputStackExpectedFrames
    verifierAcceptingSegmentFrames verifierAcceptingRowSegmentFrames
  dsimp only
  rw [dynamicFirstAffineEqFinFrames_eq_ofFn,
    dynamicFirstAffineEqFinFrames_eq_ofFn,
    dynamicFirstAffineEqFinFrames_eq_ofFn,
    dynamicFirstAffineEqFinRowFrames_eq_flatMap_ofFn,
    dynamicFirstAffineEqFinRowFrames_eq_flatMap_ofFn]
  apply congrArg₂ (· ++ ·)
  · apply congrArg₂ (· ++ ·)
    · apply congrArg₂ (· ++ ·)
      · apply congrArg₂ (· ++ ·)
        · simp only [Polynomial.eval_one]
          rw [List.ofFn_succ, List.ofFn_zero]
          congr 1
          simp [verifierInitialStackOffsetPolynomial_eval,
            verifierAcceptingPrevious,
            verifierAcceptingFrameAtCoordinate]
        · simp only [Polynomial.eval_one]
          rw [List.ofFn_succ, List.ofFn_zero]
          congr 1
          simp [verifierInitialStackOffsetPolynomial_eval,
            verifierAcceptingPrevious,
            verifierAcceptingFrameAtCoordinate] <;> ring
      · apply List.ofFn_inj.mpr
        funext index
        simp [verifierInitialStackOffsetPolynomial_eval,
          verifierAcceptingPrevious,
          verifierAcceptingFrameAtCoordinate] <;> ring <;> simp
    · simp only [Polynomial.eval_one]
      conv_lhs => rw [List.ofFn_succ, List.ofFn_zero]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [show acceptingOutputCellTargetForms W hmember =
          List.ofFn (fun symbol : Fin
            ((reachableAlphabet W.machine.tm W.machine.tm.k₁).card + 1) =>
              initialPoolTargetForm
                (decide (symbol = encodeAlphabetSymbol W.machine.tm
                  W.machine.tm.k₁ (verifierAcceptingSymbol W)
                    hmember))) by rfl]
      rw [affineEqFinRowFrames_ofFn]
      apply List.ofFn_inj.mpr
      funext symbol
      by_cases hsymbol : symbol = encodeAlphabetSymbol W.machine.tm
          W.machine.tm.k₁ (verifierAcceptingSymbol W) hmember
      <;> simp [verifierInitialStackOffsetPolynomial_eval,
        verifierAcceptingPrevious, verifierAcceptingFrameAtCoordinate,
        affineUnaryTripleFormValue, initialPoolTargetForm, hsymbol]
      <;> ring <;> simp
  · rw [acceptingOutput_flatMap_ofFn_apply]
    apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext cell
    rw [show initialBlankCellTargetForms W.machine.tm W.machine.tm.k₁ =
        List.ofFn (fun symbol : Fin
          ((reachableAlphabet W.machine.tm W.machine.tm.k₁).card + 1) =>
            initialPoolTargetForm
              (decide (symbol.val =
                (reachableAlphabet W.machine.tm W.machine.tm.k₁).card))) by
          rfl]
    rw [affineEqFinRowFrames_ofFn]
    apply List.ofFn_inj.mpr
    funext symbol
    by_cases hsymbol : symbol.val =
        (reachableAlphabet W.machine.tm W.machine.tm.k₁).card
    <;> simp [verifierInitialStackOffsetPolynomial_eval,
      verifierAcceptingHeightTailPolynomial_eval_add_one,
      verifierAcceptingPrevious, verifierAcceptingFrameAtCoordinate,
      affineUnaryTripleFormValue, initialPoolTargetForm, hsymbol]
    <;> ring <;> simp

/-- The closed output-stack source is precisely the canonical height and
cell slot map for the distinguished stack. -/
theorem verifierAcceptingOutputStackExpectedFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingOutputStackExpectedFrames W hmember input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) W.machine.tm.k₁).map
          (verifierAcceptingSlotFrame W hmember input) := by
  have htail := verifierAcceptingHeightTailPolynomial_eval_add_one W
    input.length
  have hheightCoordinate
      (height : Fin ((verifierHeight W).eval input.length + 1)) :
      (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length)
          (CfgSlot.stackHeight W.machine.tm.k₁ height)).val =
        initialControlWidth W.machine.tm +
          cfgStackBitOffset W.machine.tm
            ((verifierHeight W).eval input.length) W.machine.tm.k₁ +
          height.val := by
    rw [cfgSlotEquivFin_stackHeight_val]
    unfold initialControlWidth
    ring
  have hcellCoordinate
      (cell : Fin ((verifierHeight W).eval input.length))
      (symbol : Fin
        ((reachableAlphabet W.machine.tm W.machine.tm.k₁).card + 1)) :
      (cfgSlotEquivFin W.machine.tm
          ((verifierHeight W).eval input.length)
          (CfgSlot.stackCell W.machine.tm.k₁ cell symbol)).val =
        initialControlWidth W.machine.tm +
          cfgStackBitOffset W.machine.tm
            ((verifierHeight W).eval input.length) W.machine.tm.k₁ +
          (((verifierHeight W).eval input.length) + 1) +
          ((reachableAlphabet W.machine.tm W.machine.tm.k₁).card + 1) *
            cell.val + symbol.val := by
    rw [cfgSlotEquivFin_stackCell_val]
    unfold initialControlWidth
    ring
  unfold verifierAcceptingOutputStackExpectedFrames transitionEqStackSlots
  dsimp only
  rw [List.map_append, List.map_flatten, List.map_ofFn]
  simp_rw [List.map_ofFn]
  simp only [List.singleton_append, List.nil_append, List.append_assoc]
  conv_rhs => rw [List.ofFn_succ]
  simp only [List.cons_append, List.nil_append]
  apply congrArg₂ List.cons
  · simp only [Function.comp_apply]
    rw [verifierAcceptingSlotFrame_eq_arithmetic, hheightCoordinate]
    simp [verifierAcceptingSlotRightWire, CfgSlot.stackHeight,
      verifierAcceptingFrameAtCoordinate]
  · rw [acceptingOutput_ofFn_eq_cons_of_add_one_eq htail]
    simp only [List.cons_append, List.nil_append]
    apply congrArg₂ List.cons
    · simp only [Function.comp_apply]
      rw [verifierAcceptingSlotFrame_eq_arithmetic, hheightCoordinate]
      simp [verifierAcceptingSlotRightWire, CfgSlot.stackHeight,
        verifierAcceptingFrameAtCoordinate] <;> ring
    · apply congrArg₂ (· ++ ·)
      · apply List.ofFn_inj.mpr
        funext height
        simp only [Function.comp_apply]
        rw [verifierAcceptingSlotFrame_eq_arithmetic, hheightCoordinate]
        have hne : ((⟨height.val + 1, by omega⟩ : Fin
            ((verifierHeight W).eval input.length)).succ : Fin
              ((verifierHeight W).eval input.length + 1)).val ≠ 1 := by
          simp
        simp [verifierAcceptingSlotRightWire, CfgSlot.stackHeight,
          verifierAcceptingFrameAtCoordinate, hne]
        ring
      · conv_rhs =>
          rw [acceptingOutput_ofFn_eq_cons_of_add_one_eq htail,
            List.flatten_cons]
        apply congrArg₂ (· ++ ·)
        · simp only [Function.comp_apply, List.map_ofFn]
          apply List.ofFn_inj.mpr
          funext symbol
          simp only [Function.comp_apply]
          rw [verifierAcceptingSlotFrame_eq_arithmetic, hcellCoordinate]
          by_cases hsymbol : symbol = encodeAlphabetSymbol W.machine.tm
              W.machine.tm.k₁ (verifierAcceptingSymbol W) hmember
          · subst symbol
            simp [verifierAcceptingSlotRightWire, CfgSlot.stackCell,
              verifierAcceptingFrameAtCoordinate]
            ring
          · have hsymbolVal : symbol.val ≠
                (encodeAlphabetSymbol W.machine.tm W.machine.tm.k₁
                  (verifierAcceptingSymbol W) hmember).val := by
              intro heq
              exact hsymbol (Fin.ext heq)
            simp [verifierAcceptingSlotRightWire, CfgSlot.stackCell,
              verifierAcceptingFrameAtCoordinate, hsymbol, hsymbolVal]
            ring
        · apply congrArg List.flatten
          apply List.ofFn_inj.mpr
          funext cell
          simp only [Function.comp_apply, List.map_ofFn]
          apply List.ofFn_inj.mpr
          funext symbol
          simp only [Function.comp_apply]
          rw [verifierAcceptingSlotFrame_eq_arithmetic, hcellCoordinate]
          have hcell : (⟨cell.val + 1, by omega⟩ : Fin
              ((verifierHeight W).eval input.length)).val ≠ 0 := by simp
          by_cases hsymbol : symbol.val =
              (reachableAlphabet W.machine.tm W.machine.tm.k₁).card
          <;> simp [verifierAcceptingSlotRightWire, CfgSlot.stackCell,
            verifierAcceptingFrameAtCoordinate, hcell, hsymbol]
          <;> ring

/-- The generated distinguished output stack agrees with its canonical
public-slot block. -/
theorem verifierAcceptingOutputStackCompiledFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    verifierAcceptingOutputStackCompiledFrames W hmember input =
      (transitionEqStackSlots W.machine.tm
        ((verifierHeight W).eval input.length) W.machine.tm.k₁).map
          (verifierAcceptingSlotFrame W hmember input) := by
  rw [verifierAcceptingOutputStackCompiledFrames_eq_expected,
    verifierAcceptingOutputStackExpectedFrames_eq_slotFrames]

end CLRS.Chapter34.Turing.CookLevin
