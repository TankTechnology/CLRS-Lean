import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitSelectorSimulation

/-!
# One payload block of the length-prefixed four-way splitter

All three variable-width payload channels share the same unary-block scanner.
This file proves that reusable scanner before reasoning about the three
different counters.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev splitStep :=
  step unaryFrameLengthPrefixedFourWaySplitRevProgram

/-- Scanning one payload field copies its complete unary block and returns to
the counter check for the same channel. -/
def unaryFrameLengthPrefixedFourWaySplit_sectionBlock
    (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
    (value coordinateFields trueFields falseFields : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitCfg (.sectionScan channel)
        buffer₁ buffer₂ test (encodeUnaryFrameBlock value ++ tail) output
        coordinateFields trueFields falseFields)
      (some (unaryFrameLengthPrefixedFourWaySplitCfg (.sectionCheck channel)
        (some .separator) buffer₂ test tail
        ((encodeUnaryFrameBlock value).reverse ++ output)
        coordinateFields trueFields falseFields))
      (2 * (value + 1)) := by
  induction value generalizing buffer₁ output with
  | zero =>
      exact ⟨⟨2, rfl⟩, le_rfl⟩
  | succ value ih =>
      let afterPop := unaryFrameLengthPrefixedFourWaySplitCfg
        (.sectionTick channel) (some UnaryFrameSym.tick) buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output
        coordinateFields trueFields falseFields
      let afterPush := unaryFrameLengthPrefixedFourWaySplitCfg
        (.sectionScan channel) (some UnaryFrameSym.tick) buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) (.tick :: output)
        coordinateFields trueFields falseFields
      have hpop : EvalsToInTime splitStep
          (unaryFrameLengthPrefixedFourWaySplitCfg (.sectionScan channel)
            buffer₁ buffer₂ test
            (encodeUnaryFrameBlock (value + 1) ++ tail) output
            coordinateFields trueFields falseFields)
          (some afterPop) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hpush : EvalsToInTime splitStep afterPop (some afterPush) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have hfirst := EvalsToInTime.trans splitStep 1 1 _ afterPop _ hpop hpush
      have hrest := ih (some UnaryFrameSym.tick) (.tick :: output)
      let full := EvalsToInTime.trans splitStep 2 (2 * (value + 1))
        _ afterPush _ hfirst hrest
      convert full using 1
      · simp [encodeUnaryFrameBlock,
          List.replicate_succ, List.reverse_append, List.append_assoc]
      · omega

end CLRS.Chapter34.Turing.PolyBuilder
