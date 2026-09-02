import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveOutput

/-!
# End-to-end output finalization for parallel marked-row interleaving

Starting from the embedded halted configurations of two row-family
transducers, the combined machine alternates their aligned rows, restores the
forward output, and reaches its standard halted configuration.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- For aligned row lists, the encoded interleaving contains exactly all
symbols (including boundaries) from both inputs. -/
theorem encodeUnaryFrameMarkedRows_interleave_length
    (left right : List (List UnaryFrameSym))
    (haligned : left.length = right.length) :
    (encodeUnaryFrameMarkedRows
      (interleaveUnaryFrameMarkedRows left right)).length =
      (encodeUnaryFrameMarkedRows left).length +
        (encodeUnaryFrameMarkedRows right).length := by
  induction left generalizing right with
  | nil =>
      have hright : right = [] :=
        List.eq_nil_of_length_eq_zero haligned.symm
      subst right
      rfl
  | cons leftRow leftRows ih =>
      cases right with
      | nil => simp at haligned
      | cons rightRow rightRows =>
          have htail : leftRows.length = rightRows.length := by
            simpa using Nat.succ.inj haligned
          rw [show interleaveUnaryFrameMarkedRows
              (leftRow :: leftRows) (rightRow :: rightRows) =
              leftRow :: rightRow ::
                interleaveUnaryFrameMarkedRows leftRows rightRows by rfl,
            encodeUnaryFrameMarkedRows_cons,
            encodeUnaryFrameMarkedRows_cons,
            encodeUnaryFrameMarkedRows_cons,
            encodeUnaryFrameMarkedRows_cons]
          simp only [List.length_append, List.length_cons]
          rw [ih rightRows htail]
          omega

namespace UnaryFrameMarkedRowParallelInterleave

variable {α Γ : Type} [Fintype Γ]
variable {encode : α → List Γ}
variable {leftFamily rightFamily : α → UnaryFrameMarkedRowFamily}
variable
  (M₁ : _root_.Turing.TM2ComputableInPolyTime encode
    encodeUnaryFrameMarkedRowFamily leftFamily)
  (M₂ : _root_.Turing.TM2ComputableInPolyTime encode
    encodeUnaryFrameMarkedRowFamily rightFamily)

/-- Exact combined finalization cost after both embedded transducers halt. -/
def finalizeAlignedRowsSteps
    (left right : List (List UnaryFrameSym)) : Nat :=
  2 * (encodeUnaryFrameMarkedRows
    (interleaveUnaryFrameMarkedRows left right)).length + 2

/-- The complete physical output phase, from two embedded halted row-family
outputs to the standard halted configuration containing their interleaving. -/
def finalize_aligned_rows_run
    (left right : UnaryFrameMarkedRowFamily)
    (haligned : left.rows.length = right.rows.length) :
    EvalsToInTime (machine M₁ M₂).step
      (mapCfg₂ M₁ M₂
        (_root_.Turing.haltList M₂.tm
          (List.map M₂.outputAlphabet.invFun
            (encodeUnaryFrameMarkedRowFamily right)))
        (_root_.Turing.haltList M₁.tm
          (List.map M₁.outputAlphabet.invFun
            (encodeUnaryFrameMarkedRowFamily left))).stk)
      (some (_root_.Turing.haltList (machine M₁ M₂)
        (List.map M₂.outputAlphabet.invFun
          (encodeUnaryFrameMarkedRowFamily
            (UnaryFrameAlignedMarkedRowPair.interleaved
              { left := left
                right := right
                rowAligned := haligned })))))
      (finalizeAlignedRowsSteps left.rows right.rows) := by
  let leftStream := encodeUnaryFrameMarkedRows left.rows
  let rightStream := encodeUnaryFrameMarkedRows right.rows
  let interleaved := encodeUnaryFrameMarkedRows
    (interleaveUnaryFrameMarkedRows left.rows right.rows)
  let firstHalt := _root_.Turing.haltList M₁.tm
    (List.map M₁.outputAlphabet.invFun leftStream)
  let secondHalt := _root_.Turing.haltList M₂.tm
    (List.map M₂.outputAlphabet.invFun rightStream)
  let values := combinedStacks M₁ M₂ firstHalt.stk secondHalt.stk
  let mergedValues := Function.update
    (Function.update
      (Function.update values (firstOutputK M₁ M₂) [])
      (outputK M₁ M₂) [])
    (outputTempK M₁ M₂) interleaved.reverse
  let restoredValues := Function.update
    (Function.update mergedValues (outputTempK M₁ M₂) [])
    (outputK M₁ M₂)
      ((List.map M₂.outputAlphabet.invFun interleaved.reverse).reverse ++ [])
  let mergeStart := mergeCfg M₁ M₂ ExtraΛ.mergeLeft
    ExtraState.initial values
  let afterMerge := mergeCfg M₁ M₂ ExtraΛ.mergeLeft
    (mergeRowsFinalState (Γ := Γ) ExtraState.initial left.rows)
    mergedValues
  let restoreStart := mergeCfg M₁ M₂ ExtraΛ.outputRestore
    ExtraState.mergeDone mergedValues
  let haltCombined := _root_.Turing.haltList (machine M₁ M₂)
    (List.map M₂.outputAlphabet.invFun interleaved)
  have hleft : values (firstOutputK M₁ M₂) =
      List.map M₁.outputAlphabet.invFun leftStream := by
    simp [values, firstHalt, combinedStacks]
  have hright : values (outputK M₁ M₂) =
      List.map M₂.outputAlphabet.invFun rightStream := by
    simp [values, secondHalt, combinedStacks]
  have htemp : values (outputTempK M₁ M₂) = [] := by
    simp [values, combinedStacks]
  have hmerge : EvalsToInTime (machine M₁ M₂).step mergeStart
      (some afterMerge) (mergeAlignedRowsSteps left.rows right.rows) := by
    simpa [mergeStart, afterMerge, mergedValues, interleaved,
      leftStream, rightStream] using
      merge_aligned_rows_run M₁ M₂ left.rows right.rows haligned
        left.frameEnd_free right.frameEnd_free ExtraState.initial
        hleft hright htemp
  have hempty : mergedValues (firstOutputK M₁ M₂) = [] := by
    simp [mergedValues]
  have hfinish : EvalsToInTime (machine M₁ M₂).step afterMerge
      (some restoreStart) 1 :=
    ⟨⟨1, by
      simpa [afterMerge, restoreStart] using
        merge_finish_step M₁ M₂
          (mergeRowsFinalState (Γ := Γ) ExtraState.initial left.rows)
          hempty⟩, le_rfl⟩
  have hmergedTemp : mergedValues (outputTempK M₁ M₂) =
      interleaved.reverse := by
    simp [mergedValues]
  have hmergedOutput : mergedValues (outputK M₁ M₂) = [] := by
    simp [mergedValues]
  have hrestore : EvalsToInTime (machine M₁ M₂).step restoreStart
      (some (restoredCfg M₁ M₂ restoredValues))
      (interleaved.reverse.length + 1) :=
    ⟨⟨interleaved.reverse.length + 1, by
      simpa [restoreStart, restoredValues] using
        output_restore_phase M₁ M₂ ExtraState.mergeDone
          hmergedTemp hmergedOutput⟩, le_rfl⟩
  have hrestored : restoredCfg M₁ M₂ restoredValues = haltCombined := by
    apply _root_.Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext key
      cases key with
      | inl bank =>
          cases bank with
          | inl firstIndex =>
              by_cases h : firstIndex = M₁.tm.k₁
              · subst firstIndex
                simp [restoredCfg, restoredValues, mergedValues, values,
                  firstHalt, secondHalt, haltCombined,
                  _root_.Turing.haltList]
              · simp [restoredCfg, restoredValues, mergedValues, values,
                  combinedStacks, firstHalt, secondHalt, haltCombined,
                  _root_.Turing.haltList, h]
          | inr secondIndex =>
              by_cases h : secondIndex = M₂.tm.k₁
              · subst secondIndex
                simp [restoredCfg, restoredValues, mergedValues, values,
                  firstHalt, secondHalt, haltCombined,
                  _root_.Turing.haltList, List.map_reverse]
              · simp [restoredCfg, restoredValues, mergedValues, values,
                  combinedStacks, firstHalt, secondHalt, haltCombined,
                  _root_.Turing.haltList, h]
      | inr extra =>
          cases extra <;>
            simp [restoredCfg, restoredValues, mergedValues, values,
              combinedStacks, firstHalt, secondHalt, haltCombined,
              _root_.Turing.haltList]
  rw [hrestored] at hrestore
  let firstTwo := EvalsToInTime.trans (machine M₁ M₂).step
    (mergeAlignedRowsSteps left.rows right.rows) 1
    mergeStart afterMerge (some restoreStart) hmerge hfinish
  let full := EvalsToInTime.trans (machine M₁ M₂).step
    (1 + mergeAlignedRowsSteps left.rows right.rows)
    (interleaved.reverse.length + 1)
    mergeStart restoreStart (some haltCombined) firstTwo hrestore
  have hstart :
      mapCfg₂ M₁ M₂
          (_root_.Turing.haltList M₂.tm
            (List.map M₂.outputAlphabet.invFun
              (encodeUnaryFrameMarkedRowFamily right)))
          (_root_.Turing.haltList M₁.tm
            (List.map M₁.outputAlphabet.invFun
              (encodeUnaryFrameMarkedRowFamily left))).stk =
        mergeStart := by
    simp [mapCfg₂, mergeStart, values, firstHalt, secondHalt,
      leftStream, rightStream, encodeUnaryFrameMarkedRowFamily]
    rfl
  have hhalt : haltCombined =
      _root_.Turing.haltList (machine M₁ M₂)
        (List.map M₂.outputAlphabet.invFun
          (encodeUnaryFrameMarkedRowFamily
            (UnaryFrameAlignedMarkedRowPair.interleaved
              { left := left
                right := right
                rowAligned := haligned }))) := by
    rfl
  have hsteps : interleaved.length + 1 +
        (1 + mergeAlignedRowsSteps left.rows right.rows) =
      finalizeAlignedRowsSteps left.rows right.rows := by
    have hlen := encodeUnaryFrameMarkedRows_interleave_length
      left.rows right.rows haligned
    simp [interleaved, mergeAlignedRowsSteps, finalizeAlignedRowsSteps] at *
    omega
  rw [hstart, ← hhalt]
  have full' : EvalsToInTime (machine M₁ M₂).step mergeStart
      (some haltCombined)
      (interleaved.length + 1 +
        (1 + mergeAlignedRowsSteps left.rows right.rows)) := by
    simpa only [List.length_reverse] using full
  rw [hsteps] at full'
  exact full'

end UnaryFrameMarkedRowParallelInterleave

end CLRS.Chapter34.Turing.PolyBuilder
