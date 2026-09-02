import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineMuxInvocationProgressionControllerFamily
import Mathlib.Tactic

/-!
# Complete segment execution for affine mux invocations

One segment contains selector metadata, an optional invocation header, an
arbitrary affine row family, and a final marker.  This file composes the small
execution lemmas into one exact clean-boundary theorem.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Stable boundary used between complete invocation segments. -/
def affineMuxInvocationProgressionControllerBoundaryCfg
    (buffer₁ : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg affineMuxInvocationProgressionControllerRevProgram :=
  affineMuxInvocationProgressionControllerCfg .loadSelector buffer₁ none
    false input output [] [] [] [] []

/-- The header flag is retained only in finite control. -/
def affineMuxInvocationProgressionControllerHeaderBuffer
    (emitsHeader : Bool) : Option UnaryFrameSym :=
  if emitsHeader then none else some .separator

/-- Exact flag-dispatch and optional-header cost. -/
def affineMuxInvocationProgressionControllerHeaderSteps
    (selector : Nat) (emitsHeader : Bool) : Nat :=
  if emitsHeader then (5 * selector + 6) + 2 else 1

/-- Exact runtime of one complete segment. -/
def affineMuxInvocationProgressionControllerSegmentSteps
    (segment : AffineMuxInvocationProgression) : Nat :=
  (2 * segment.selector + 1) +
    (2 * segment.selectorNot + 1) +
    affineMuxInvocationProgressionControllerHeaderSteps
      segment.selector segment.emitsHeader +
    affineMuxInvocationProgressionControllerRowsSteps
      segment.selector segment.selectorNot segment.dataRows +
    (segment.selector + segment.selectorNot + 3)

@[simp] theorem affineMuxInvocationProgression_dataSource_eq
    (segment : AffineMuxInvocationProgression) :
    affineMuxInvocationRowsSource segment.dataRows =
      affineUnaryTripleProgressionFrameStream segment.dataProgression := rfl

theorem affineMuxInvocationProgression_rowsFrames_eq
    (segment : AffineMuxInvocationProgression) :
    affineMuxInvocationRowsFrames segment.selector segment.selectorNot
        segment.dataRows =
      segment.frames.flatMap encodeAffineMuxFinPairFrame := by
  simp [affineMuxInvocationRowsFrames,
    AffineMuxInvocationProgression.frames,
    AffineMuxInvocationProgression.frameOfRow,
    affineMuxInvocationFrameOfRow, List.flatMap_map]

/-- The unary Boolean flag either emits no bytes or the exact existing mux
header, then reaches the common row-loop boundary. -/
def affineMuxInvocationProgressionController_headerStage
    (selector selectorNot : Nat) (emitsHeader : Bool)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .loadHeaderFlag
        buffer₁ buffer₂ false
        (encodeUnaryFrameBlock (if emitsHeader then 1 else 0) ++ tail)
        output [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])
      (some (affineMuxInvocationProgressionControllerCfg .dataCheck
        (affineMuxInvocationProgressionControllerHeaderBuffer emitsHeader)
        buffer₂ false tail
        ((if emitsHeader then encodeAffineMuxFinHeader selector else []).reverse ++
          output)
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []))
      (affineMuxInvocationProgressionControllerHeaderSteps
        selector emitsHeader) := by
  cases emitsHeader with
  | false =>
      exact ⟨⟨1, by
        simpa [affineMuxInvocationProgressionControllerHeaderBuffer,
          affineMuxInvocationProgressionControllerHeaderSteps,
          encodeUnaryFrameBlock] using
          muxInvocation_headerFlag_false_eval selector selectorNot buffer₁
            buffer₂ false tail output⟩, le_rfl⟩
  | true =>
      let afterFlag :=
        affineMuxInvocationProgressionControllerCfg .headerSeparator₁
          (some .separator) buffer₂ false tail output [] []
          (List.replicate selector ()) (List.replicate selectorNot ()) []
      have hflag : EvalsToInTime
          (step affineMuxInvocationProgressionControllerRevProgram)
          (affineMuxInvocationProgressionControllerCfg .loadHeaderFlag
            buffer₁ buffer₂ false
            (encodeUnaryFrameBlock 1 ++ tail) output [] []
            (List.replicate selector ()) (List.replicate selectorNot ()) [])
          (some afterFlag) 2 :=
        ⟨⟨2, by
          simpa [afterFlag, encodeUnaryFrameBlock] using
            muxInvocation_headerFlag_true_eval selector selectorNot buffer₁
              buffer₂ false tail output⟩, le_rfl⟩
      have hheader : EvalsToInTime
          (step affineMuxInvocationProgressionControllerRevProgram)
          afterFlag
          (some (affineMuxInvocationProgressionControllerCfg .dataCheck none
            buffer₂ false tail
            ((encodeAffineMuxFinHeader selector).reverse ++ output) [] []
            (List.replicate selector ()) (List.replicate selectorNot ()) []))
          (5 * selector + 6) := by
        simpa [afterFlag] using
          muxInvocation_header_emit selector selectorNot (some .separator)
            buffer₂ false tail output
      let full := EvalsToInTime.trans
        (step affineMuxInvocationProgressionControllerRevProgram)
        2 (5 * selector + 6) _ _ _ hflag hheader
      simpa [affineMuxInvocationProgressionControllerHeaderBuffer,
        affineMuxInvocationProgressionControllerHeaderSteps] using full

/-- One complete source segment emits exactly its denoted mux invocation
bytes and returns with all work stacks and counters empty. -/
def affineMuxInvocationProgressionController_segment_emit
    (segment : AffineMuxInvocationProgression)
    (buffer₁ : Option UnaryFrameSym) (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerBoundaryCfg buffer₁
        (segment.sourceFrames ++ tail) output)
      (some (affineMuxInvocationProgressionControllerBoundaryCfg
        (some .frameEnd) tail
        ((segment.invocationFrames).reverse ++ output)))
      (affineMuxInvocationProgressionControllerSegmentSteps segment) := by
  let rowsInput :=
    affineMuxInvocationRowsSource segment.dataRows ++ .frameEnd :: tail
  let afterSelector :=
    affineMuxInvocationProgressionControllerCfg .loadSelectorNot
      (some .separator) none false
      (encodeUnaryFrameBlock segment.selectorNot ++
        encodeUnaryFrameBlock (if segment.emitsHeader then 1 else 0) ++
        rowsInput)
      output [] [] (List.replicate segment.selector ()) [] []
  have hselector : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerBoundaryCfg buffer₁
        (segment.sourceFrames ++ tail) output)
      (some afterSelector) (2 * segment.selector + 1) :=
    ⟨⟨2 * segment.selector + 1, by
      simpa [affineMuxInvocationProgressionControllerBoundaryCfg,
        afterSelector, rowsInput, AffineMuxInvocationProgression.sourceFrames,
        AffineMuxInvocationProgression.headerProgression_frameStream,
        encodeUnaryFrame, List.append_assoc] using
        muxInvocation_loadSelector_eval segment.selector buffer₁ none false
          (encodeUnaryFrameBlock segment.selectorNot ++
            encodeUnaryFrameBlock (if segment.emitsHeader then 1 else 0) ++
            rowsInput)
          output [] [] [] [] []⟩, le_rfl⟩
  let afterSelectorNot :=
    affineMuxInvocationProgressionControllerCfg .loadHeaderFlag
      (some .separator) none false
      (encodeUnaryFrameBlock (if segment.emitsHeader then 1 else 0) ++
        rowsInput)
      output [] [] (List.replicate segment.selector ())
      (List.replicate segment.selectorNot ()) []
  have hselectorNot : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterSelector (some afterSelectorNot)
      (2 * segment.selectorNot + 1) :=
    ⟨⟨2 * segment.selectorNot + 1, by
      simpa [afterSelector, afterSelectorNot] using
        muxInvocation_loadSelectorNot_eval segment.selector
          segment.selectorNot (some .separator) none false
          (encodeUnaryFrameBlock
            (if segment.emitsHeader then 1 else 0) ++ rowsInput)
          output [] [] [] []⟩, le_rfl⟩
  let headerOutput :=
    (segment.headerFrames).reverse ++ output
  let afterHeader :=
    affineMuxInvocationProgressionControllerCfg .dataCheck
      (affineMuxInvocationProgressionControllerHeaderBuffer
        segment.emitsHeader)
      none false rowsInput headerOutput [] []
      (List.replicate segment.selector ())
      (List.replicate segment.selectorNot ()) []
  have hheader : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterSelectorNot (some afterHeader)
      (affineMuxInvocationProgressionControllerHeaderSteps
        segment.selector segment.emitsHeader) := by
    simpa [afterSelectorNot, afterHeader, headerOutput,
      AffineMuxInvocationProgression.headerFrames] using
      affineMuxInvocationProgressionController_headerStage
        segment.selector segment.selectorNot segment.emitsHeader
        (some .separator) none rowsInput output
  let rowsOutput :=
    (affineMuxInvocationRowsFrames segment.selector segment.selectorNot
      segment.dataRows).reverse ++ headerOutput
  let afterRows :=
    affineMuxInvocationProgressionControllerCfg .dataCheck
      (affineMuxInvocationRowsFinalBuffer segment.dataRows
        (affineMuxInvocationProgressionControllerHeaderBuffer
          segment.emitsHeader))
      none (affineMuxInvocationRowsFinalTest segment.dataRows false)
      (.frameEnd :: tail) rowsOutput [] []
      (List.replicate segment.selector ())
      (List.replicate segment.selectorNot ()) []
  have hrows : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterHeader (some afterRows)
      (affineMuxInvocationProgressionControllerRowsSteps
        segment.selector segment.selectorNot segment.dataRows) := by
    simpa [afterHeader, afterRows, rowsOutput, rowsInput] using
      affineMuxInvocationProgressionController_rows_emit
        segment.selector segment.selectorNot segment.dataRows
        (affineMuxInvocationProgressionControllerHeaderBuffer
          segment.emitsHeader)
        none false (.frameEnd :: tail) headerOutput
  have hclear : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterRows
      (some (affineMuxInvocationProgressionControllerBoundaryCfg
        (some .frameEnd) tail rowsOutput))
      (segment.selector + segment.selectorNot + 3) := by
    simpa [afterRows,
      affineMuxInvocationProgressionControllerBoundaryCfg] using
      affineMuxInvocationProgressionController_clearSegment
        segment.selector segment.selectorNot
        (affineMuxInvocationRowsFinalBuffer segment.dataRows
          (affineMuxInvocationProgressionControllerHeaderBuffer
            segment.emitsHeader))
        none (affineMuxInvocationRowsFinalTest segment.dataRows false)
        tail rowsOutput
  let first := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    (2 * segment.selector + 1) (2 * segment.selectorNot + 1)
    _ _ _ hselector hselectorNot
  let second := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (affineMuxInvocationProgressionControllerHeaderSteps
      segment.selector segment.emitsHeader) _ _ _ first hheader
  let third := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (affineMuxInvocationProgressionControllerRowsSteps
      segment.selector segment.selectorNot segment.dataRows)
    _ _ _ second hrows
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (segment.selector + segment.selectorNot + 3) _ _ _ third hclear
  convert full using 1
  · simp [affineMuxInvocationProgressionControllerBoundaryCfg,
      rowsOutput, headerOutput, AffineMuxInvocationProgression.invocationFrames,
      affineMuxInvocationProgression_rowsFrames_eq, List.reverse_append,
      List.append_assoc]
  · simp [affineMuxInvocationProgressionControllerSegmentSteps]
    omega

end CLRS.Chapter34.Turing.PolyBuilder
