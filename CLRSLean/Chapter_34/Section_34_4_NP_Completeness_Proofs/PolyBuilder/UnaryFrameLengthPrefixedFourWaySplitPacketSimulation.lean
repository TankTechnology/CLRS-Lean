import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitSectionSimulation

/-!
# Complete packet simulation for the dynamic four-way splitter

The phase lemmas are composed here for one well-sized packet.  This is the
first end-to-end theorem connecting the self-described width to four concrete
row frames.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev splitStep :=
  step unaryFrameLengthPrefixedFourWaySplitRevProgram

/-- Exact builder-step count for one complete four-channel packet. -/
def unaryFrameLengthPrefixedFourWaySplitPacketSteps
    (width selector : Nat)
    (coordinates whenTrue whenFalse : List Nat) : Nat :=
  (6 * width + 1) + (2 * selector + 3) +
    unaryFrameLengthPrefixedFourWaySplitSectionSteps coordinates +
    unaryFrameLengthPrefixedFourWaySplitSectionSteps whenTrue +
    unaryFrameLengthPrefixedFourWaySplitSectionSteps whenFalse + 1

/-- One length-prefixed packet is split into selector, coordinate, true-arm,
and false-arm rows.  The width is checked operationally by the three counters,
not by finite control. -/
def unaryFrameLengthPrefixedFourWaySplit_packet
    (width selector : Nat)
    (coordinates whenTrue whenFalse : List Nat)
    (hcoordinates : coordinates.length = 3 * width)
    (htrue : whenTrue.length = width)
    (hfalse : whenFalse.length = width)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth buffer₁ buffer₂
        false
        (encodeUnaryFrameLengthPrefixedFourWaySplitInput width selector
          coordinates whenTrue whenFalse ++ tail)
        output 0 0 0)
      (some (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth
        (some .frameEnd) buffer₂ false tail
        ((encodeUnaryFrameLengthPrefixedFourWaySplitOutput selector coordinates
          whenTrue whenFalse).reverse ++ output)
        0 0 0))
      (unaryFrameLengthPrefixedFourWaySplitPacketSteps width selector
        coordinates whenTrue whenFalse) := by
  let selectorInput := encodeUnaryFrameBlock selector ++
    encodeUnaryFrame coordinates ++ encodeUnaryFrame whenTrue ++
      encodeUnaryFrame whenFalse ++ UnaryFrameSym.frameEnd :: tail
  let selectorOutput :=
    (encodeUnaryFrameBlock selector ++ [UnaryFrameSym.frameEnd]).reverse ++ output
  let coordinateOutput :=
    (encodeUnaryFrame coordinates ++ [UnaryFrameSym.frameEnd]).reverse ++
      selectorOutput
  let trueOutput :=
    (encodeUnaryFrame whenTrue ++ [UnaryFrameSym.frameEnd]).reverse ++
      coordinateOutput
  let finalOutput :=
    (encodeUnaryFrame whenFalse ++ [UnaryFrameSym.frameEnd]).reverse ++ trueOutput
  let afterWidth := unaryFrameLengthPrefixedFourWaySplitCfg .selectorScan
    (some UnaryFrameSym.separator) buffer₂ false selectorInput output
    (3 * width) width width
  let afterSelector := unaryFrameLengthPrefixedFourWaySplitCfg
    (.sectionCheck .coordinates) (some UnaryFrameSym.separator) buffer₂ false
    (encodeUnaryFrame coordinates ++ encodeUnaryFrame whenTrue ++
      encodeUnaryFrame whenFalse ++ UnaryFrameSym.frameEnd :: tail)
    selectorOutput (3 * width) width width
  let afterCoordinates := unaryFrameLengthPrefixedFourWaySplitCfg
    (.sectionCheck .trueArm) (some UnaryFrameSym.separator) buffer₂ false
    (encodeUnaryFrame whenTrue ++ encodeUnaryFrame whenFalse ++
      UnaryFrameSym.frameEnd :: tail)
    coordinateOutput 0 width width
  let afterTrue := unaryFrameLengthPrefixedFourWaySplitCfg
    (.sectionCheck .falseArm) (some UnaryFrameSym.separator) buffer₂ false
    (encodeUnaryFrame whenFalse ++ UnaryFrameSym.frameEnd :: tail)
    trueOutput 0 0 width
  let afterFalse := unaryFrameLengthPrefixedFourWaySplitCfg .consumeBoundary
    (some UnaryFrameSym.separator) buffer₂ false
    (UnaryFrameSym.frameEnd :: tail) finalOutput 0 0 0
  have hload : EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth buffer₁ buffer₂
        false
        (encodeUnaryFrameLengthPrefixedFourWaySplitInput width selector
          coordinates whenTrue whenFalse ++ tail)
        output 0 0 0)
      (some afterWidth) (6 * width + 1) := by
    simpa [afterWidth, selectorInput,
      encodeUnaryFrameLengthPrefixedFourWaySplitInput, encodeUnaryFrame,
      encodeUnaryFrameBlock, List.append_assoc] using
      (unaryFrameLengthPrefixedFourWaySplit_loadWidth width 0 0 0
        buffer₁ buffer₂ selectorInput output)
  have hselectorRun : EvalsToInTime splitStep afterWidth
      (some afterSelector) (2 * selector + 3) := by
    simpa [afterWidth, afterSelector, selectorInput, selectorOutput,
      List.append_assoc] using
      (unaryFrameLengthPrefixedFourWaySplit_selector selector
        (3 * width) width width (some UnaryFrameSym.separator) buffer₂ false
        (encodeUnaryFrame coordinates ++ encodeUnaryFrame whenTrue ++
          encodeUnaryFrame whenFalse ++ UnaryFrameSym.frameEnd :: tail)
        output)
  have hcoordinatesRun : EvalsToInTime splitStep afterSelector
      (some afterCoordinates)
      (unaryFrameLengthPrefixedFourWaySplitSectionSteps coordinates) := by
    simpa [afterSelector, afterCoordinates, coordinateOutput, selectorOutput,
      unaryFrameLengthPrefixedFourWaySplitSectionCfg,
      unaryFrameLengthPrefixedFourWaySplitNext, hcoordinates,
      List.append_assoc] using
      (unaryFrameLengthPrefixedFourWaySplit_section .coordinates coordinates
        width width (some UnaryFrameSym.separator) buffer₂ false
        (encodeUnaryFrame whenTrue ++ encodeUnaryFrame whenFalse ++
          UnaryFrameSym.frameEnd :: tail)
        selectorOutput)
  have htrueRun : EvalsToInTime splitStep afterCoordinates
      (some afterTrue)
      (unaryFrameLengthPrefixedFourWaySplitSectionSteps whenTrue) := by
    simpa [afterCoordinates, afterTrue, trueOutput, coordinateOutput,
      unaryFrameLengthPrefixedFourWaySplitSectionCfg,
      unaryFrameLengthPrefixedFourWaySplitNext, htrue,
      List.append_assoc] using
      (unaryFrameLengthPrefixedFourWaySplit_section .trueArm whenTrue
        0 width (some UnaryFrameSym.separator) buffer₂ false
        (encodeUnaryFrame whenFalse ++ UnaryFrameSym.frameEnd :: tail)
        coordinateOutput)
  have hfalseRun : EvalsToInTime splitStep afterTrue
      (some afterFalse)
      (unaryFrameLengthPrefixedFourWaySplitSectionSteps whenFalse) := by
    simpa [afterTrue, afterFalse, finalOutput, trueOutput,
      unaryFrameLengthPrefixedFourWaySplitSectionCfg,
      unaryFrameLengthPrefixedFourWaySplitNext, hfalse,
      List.append_assoc] using
      (unaryFrameLengthPrefixedFourWaySplit_section .falseArm whenFalse
        0 0 (some UnaryFrameSym.separator) buffer₂ false
        (UnaryFrameSym.frameEnd :: tail) trueOutput)
  have hboundary : EvalsToInTime splitStep afterFalse
      (some (unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth
        (some .frameEnd) buffer₂ false tail finalOutput 0 0 0)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans splitStep (6 * width + 1)
    (2 * selector + 3) _ afterWidth _ hload hselectorRun
  let h₂ := EvalsToInTime.trans splitStep _
    (unaryFrameLengthPrefixedFourWaySplitSectionSteps coordinates)
    _ afterSelector _ h₁ hcoordinatesRun
  let h₃ := EvalsToInTime.trans splitStep _
    (unaryFrameLengthPrefixedFourWaySplitSectionSteps whenTrue)
    _ afterCoordinates _ h₂ htrueRun
  let h₄ := EvalsToInTime.trans splitStep _
    (unaryFrameLengthPrefixedFourWaySplitSectionSteps whenFalse)
    _ afterTrue _ h₃ hfalseRun
  let full := EvalsToInTime.trans splitStep _ 1 _ afterFalse _ h₄ hboundary
  convert full using 1
  · simp [finalOutput, trueOutput, coordinateOutput, selectorOutput,
      encodeUnaryFrameLengthPrefixedFourWaySplitOutput,
      encodeUnaryFrame,
      List.reverse_append, List.append_assoc]
  · simp [unaryFrameLengthPrefixedFourWaySplitPacketSteps]
    omega

end CLRS.Chapter34.Turing.PolyBuilder
