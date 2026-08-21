import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitSimulation

/-!
# Selector phase of the length-prefixed four-way splitter

This file proves the first output phase separately from the dynamic-width
loader.  The controller copies one unary selector block and appends the row
boundary consumed by the downstream mux pipeline.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev splitStep :=
  step unaryFrameLengthPrefixedFourWaySplitRevProgram

/-- The selector scanner copies one unary block and then emits its row marker.
The output stack is reversed, as required by the builder compiler. -/
def unaryFrameLengthPrefixedFourWaySplit_selector
    (selector coordinateFields trueFields falseFields : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitCfg .selectorScan buffer₁ buffer₂
        test (encodeUnaryFrameBlock selector ++ tail) output
        coordinateFields trueFields falseFields)
      (some (unaryFrameLengthPrefixedFourWaySplitCfg
        (.sectionCheck .coordinates) (some .separator) buffer₂ test tail
        ((encodeUnaryFrameBlock selector ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        coordinateFields trueFields falseFields))
      (2 * selector + 3) := by
  induction selector generalizing buffer₁ output with
  | zero =>
      exact ⟨⟨3, rfl⟩, le_rfl⟩
  | succ selector ih =>
      let afterPop := unaryFrameLengthPrefixedFourWaySplitCfg .selectorTick
        (some UnaryFrameSym.tick) buffer₂ test
        (encodeUnaryFrameBlock selector ++ tail) output
        coordinateFields trueFields falseFields
      let afterPush := unaryFrameLengthPrefixedFourWaySplitCfg .selectorScan
        (some UnaryFrameSym.tick) buffer₂ test
        (encodeUnaryFrameBlock selector ++ tail) (.tick :: output)
        coordinateFields trueFields falseFields
      have hpop : EvalsToInTime splitStep
          (unaryFrameLengthPrefixedFourWaySplitCfg .selectorScan buffer₁ buffer₂
            test (encodeUnaryFrameBlock (selector + 1) ++ tail) output
            coordinateFields trueFields falseFields)
          (some afterPop) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hpush : EvalsToInTime splitStep afterPop (some afterPush) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have hfirst := EvalsToInTime.trans splitStep 1 1 _ afterPop _ hpop hpush
      have hrest := ih (some UnaryFrameSym.tick) (.tick :: output)
      let full := EvalsToInTime.trans splitStep 2 (2 * selector + 3)
        _ afterPush _ hfirst hrest
      simpa [afterPop, afterPush, encodeUnaryFrameBlock,
        List.replicate_succ, List.reverse_append, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.PolyBuilder
