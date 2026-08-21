import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionMuxQuotedRowParserCore
import Mathlib.Tactic

/-!
# Exact simulation of the transition-mux quoted-row parser

The proof is split at the grammar boundaries of the public mux encoding:
unary triples, coordinate frames, complete invocations, and invocation
families.  This keeps the runtime argument independent of semantic circuit
reasoning.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private def parserEmit
    (state : TransitionMuxQuotedRowState) (symbol : UnaryFrameSym)
    (buffer : Option UnaryFrameSym) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserCfg (.emitFirst state symbol) buffer tail
        output)
      (some (transitionMuxQuotedRowParserScanCfg state buffer tail
        ((quoteUnaryFrameSym symbol).reverse ++ output))) 2 := by
  cases symbol <;> exact ⟨⟨2, rfl⟩, le_rfl⟩

private def parserTick
    (phase : TransitionMuxQuotedRowPhase) (separators : Fin 4)
    (buffer : Option UnaryFrameSym) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
        (.tick :: tail) output)
      (some (transitionMuxQuotedRowParserScanCfg (.triple phase separators)
        (some .tick) tail
        ((quoteUnaryFrameSym .tick).reverse ++ output))) 3 := by
  exact ⟨⟨3, rfl⟩, le_rfl⟩

private def parserSeparator
    (phase : TransitionMuxQuotedRowPhase) (separators : Fin 4)
    (hroom : separators.val < 3) (buffer : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
        (.separator :: tail) output)
      (some (transitionMuxQuotedRowParserScanCfg
        (.triple phase
          (transitionMuxQuotedRowIncrement separators hroom))
        (some .separator) tail
        ((quoteUnaryFrameSym .separator).reverse ++ output))) 3 := by
  let afterPop := transitionMuxQuotedRowParserCfg
    (.emitFirst
      (.triple phase (transitionMuxQuotedRowIncrement separators hroom))
      .separator) (some .separator) tail output
  have hpop : EvalsToInTime
      (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
        (.separator :: tail) output)
      (some afterPop) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step transitionMuxQuotedRowParserRevProgram
      (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
        (.separator :: tail) output) = some afterPop
    simp only [step, transitionMuxQuotedRowParserScanCfg,
      transitionMuxQuotedRowParserCfg,
      transitionMuxQuotedRowParserRevProgram, Option.map_some]
    rw [dif_pos hroom]
    rfl
  have hemit := parserEmit
    (.triple phase (transitionMuxQuotedRowIncrement separators hroom))
    .separator (some .separator) tail output
  let full := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) 1 2 _ _ _ hpop hemit
  simpa [afterPop, Nat.add_comm] using full

private def parserTripleFrameEnd
    (phase : TransitionMuxQuotedRowPhase) (separators : Fin 4)
    (hfull : separators.val = 3) (buffer : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
        (.frameEnd :: tail) output)
      (some (transitionMuxQuotedRowParserScanCfg
        (transitionMuxQuotedRowAfterTriple phase) (some .frameEnd) tail
        ((quoteUnaryFrameSym .frameEnd).reverse ++ output))) 3 := by
  let afterPop := transitionMuxQuotedRowParserCfg
    (.emitFirst (transitionMuxQuotedRowAfterTriple phase) .frameEnd)
    (some .frameEnd) tail output
  have hpop : EvalsToInTime
      (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
        (.frameEnd :: tail) output)
      (some afterPop) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step transitionMuxQuotedRowParserRevProgram
      (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
        (.frameEnd :: tail) output) = some afterPop
    simp only [step, transitionMuxQuotedRowParserScanCfg,
      transitionMuxQuotedRowParserCfg,
      transitionMuxQuotedRowParserRevProgram, Option.map_some]
    rw [if_pos hfull]
    rfl
  have hemit := parserEmit (transitionMuxQuotedRowAfterTriple phase)
    .frameEnd (some .frameEnd) tail output
  let full := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) 1 2 _ _ _ hpop hemit
  simpa [afterPop, Nat.add_comm] using full

/-- A unary run leaves the separator counter unchanged and quotes every tick.
-/
private def parserTicks
    (phase : TransitionMuxQuotedRowPhase) (separators : Fin 4)
    (count : Nat) (buffer : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
        (List.replicate count .tick ++ tail) output)
      (some (transitionMuxQuotedRowParserScanCfg (.triple phase separators)
        (if count = 0 then buffer else some .tick) tail
        ((quoteUnaryFrameStream (List.replicate count .tick)).reverse ++
          output))) (3 * count) := by
  induction count generalizing buffer output with
  | zero =>
      simpa using EvalsToInTime.refl
        (step transitionMuxQuotedRowParserRevProgram)
        (transitionMuxQuotedRowParserScanCfg (.triple phase separators) buffer
          tail output)
  | succ count ih =>
      let first := parserTick phase separators buffer
        (List.replicate count .tick ++ tail) output
      let rest := ih (some .tick)
        ((quoteUnaryFrameSym .tick).reverse ++ output)
      let full := EvalsToInTime.trans
        (step transitionMuxQuotedRowParserRevProgram) 3 (3 * count)
        _ _ _ first rest
      convert full using 1
      · rfl
      · have hrep : List.replicate (count + 1) UnaryFrameSym.tick =
            .tick :: List.replicate count .tick := by
          rw [show count + 1 = Nat.succ count by omega,
            List.replicate_succ]
        rw [hrep, quoteUnaryFrameStream_cons, List.reverse_append]
        simp [List.append_assoc]
      · rw [Nat.mul_add]

private def parserTripleSteps (first second third : Nat) : Nat :=
  3 * (encodeUnaryFrame [first, second, third] ++
    [UnaryFrameSym.frameEnd]).length

/-- Every delimiter-terminated unary triple is quoted exactly and moves to
the grammar successor of its phase. -/
def transitionMuxQuotedRowParser_triple
    (phase : TransitionMuxQuotedRowPhase) (first second third : Nat)
    (buffer : Option UnaryFrameSym) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg (.triple phase ⟨0, by omega⟩)
        buffer
        (encodeUnaryFrame [first, second, third] ++ .frameEnd :: tail)
        output)
      (some (transitionMuxQuotedRowParserScanCfg
        (transitionMuxQuotedRowAfterTriple phase) (some .frameEnd) tail
        ((quoteUnaryFrameStream
          (encodeUnaryFrame [first, second, third] ++ [.frameEnd])).reverse ++
            output)))
      (parserTripleSteps first second third) := by
  let afterFirstTicks :=
    (quoteUnaryFrameStream (List.replicate first .tick)).reverse ++ output
  let afterFirstSeparator :=
    (quoteUnaryFrameSym .separator).reverse ++ afterFirstTicks
  let afterSecondTicks :=
    (quoteUnaryFrameStream (List.replicate second .tick)).reverse ++
      afterFirstSeparator
  let afterSecondSeparator :=
    (quoteUnaryFrameSym .separator).reverse ++ afterSecondTicks
  let afterThirdTicks :=
    (quoteUnaryFrameStream (List.replicate third .tick)).reverse ++
      afterSecondSeparator
  let afterThirdSeparator :=
    (quoteUnaryFrameSym .separator).reverse ++ afterThirdTicks
  let thirdTail :=
    List.replicate third .tick ++ .separator :: .frameEnd :: tail
  let secondTail :=
    List.replicate second .tick ++ .separator :: thirdTail
  have hfirst := parserTicks phase (⟨0, by decide⟩ : Fin 4) first buffer
    (.separator :: secondTail) output
  have hsep₁ : EvalsToInTime
      (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg
        (.triple phase ⟨0, by decide⟩)
        (if first = 0 then buffer else some .tick)
        (.separator :: secondTail)
        afterFirstTicks)
      (some (transitionMuxQuotedRowParserScanCfg
        (.triple phase ⟨1, by decide⟩) (some .separator)
        secondTail
        afterFirstSeparator)) 3 := by
    simpa [transitionMuxQuotedRowIncrement, afterFirstSeparator,
      quoteUnaryFrameSym, quoteUnaryFrameFirst, quoteUnaryFrameSecond] using
      parserSeparator phase (⟨0, by decide⟩ : Fin 4) (by decide)
        (if first = 0 then buffer else some .tick)
        secondTail afterFirstTicks
  have hsecond := parserTicks phase (⟨1, by decide⟩ : Fin 4) second
    (some .separator) (.separator :: thirdTail) afterFirstSeparator
  have hsep₂ : EvalsToInTime
      (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg
        (.triple phase ⟨1, by decide⟩)
        (if second = 0 then some .separator else some .tick)
        (.separator :: thirdTail) afterSecondTicks)
      (some (transitionMuxQuotedRowParserScanCfg
        (.triple phase ⟨2, by decide⟩) (some .separator)
        thirdTail
        afterSecondSeparator)) 3 := by
    simpa [transitionMuxQuotedRowIncrement, afterSecondSeparator,
      quoteUnaryFrameSym, quoteUnaryFrameFirst, quoteUnaryFrameSecond] using
      parserSeparator phase (⟨1, by decide⟩ : Fin 4) (by decide)
        (if second = 0 then some .separator else some .tick)
        thirdTail afterSecondTicks
  have hthird := parserTicks phase (⟨2, by decide⟩ : Fin 4) third
    (some .separator) (.separator :: .frameEnd :: tail)
    afterSecondSeparator
  have hsep₃ : EvalsToInTime
      (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg
        (.triple phase ⟨2, by decide⟩)
        (if third = 0 then some .separator else some .tick)
        (.separator :: .frameEnd :: tail) afterThirdTicks)
      (some (transitionMuxQuotedRowParserScanCfg
        (.triple phase ⟨3, by decide⟩) (some .separator)
        (.frameEnd :: tail) afterThirdSeparator)) 3 := by
    simpa [transitionMuxQuotedRowIncrement, afterThirdSeparator,
      quoteUnaryFrameSym, quoteUnaryFrameFirst, quoteUnaryFrameSecond] using
      parserSeparator phase (⟨2, by decide⟩ : Fin 4) (by decide)
        (if third = 0 then some .separator else some .tick)
        (.frameEnd :: tail) afterThirdTicks
  have hend := parserTripleFrameEnd phase (⟨3, by decide⟩ : Fin 4)
    (by decide) (some .separator) tail afterThirdSeparator
  let h₁ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) (3 * first) 3
    _ _ _ hfirst hsep₁
  let h₂ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _ (3 * second)
    _ _ _ h₁ hsecond
  let h₃ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _ 3
    _ _ _ h₂ hsep₂
  let h₄ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _ (3 * third)
    _ _ _ h₃ hthird
  let h₅ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _ 3
    _ _ _ h₄ hsep₃
  let full := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _ 3
    _ _ _ h₅ hend
  convert full using 1
  · simp [encodeUnaryFrame, encodeUnaryFrameBlock, afterFirstTicks,
      afterFirstSeparator, afterSecondTicks, afterSecondSeparator,
      afterThirdTicks, afterThirdSeparator, thirdTail, secondTail,
      quoteUnaryFrameStream, List.reverse_append, List.append_assoc]
  · simp [encodeUnaryFrame, encodeUnaryFrameBlock, afterFirstTicks,
      afterFirstSeparator, afterSecondTicks, afterSecondSeparator,
      afterThirdTicks, afterThirdSeparator, thirdTail, secondTail,
      quoteUnaryFrameStream, List.reverse_append, List.append_assoc]
  · simp [parserTripleSteps, encodeUnaryFrame, encodeUnaryFrameBlock]
    omega

private def parserCoordinateLead
    (buffer : Option UnaryFrameSym) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer
        (.frameEnd :: tail) output)
      (some (transitionMuxQuotedRowParserScanCfg
        transitionMuxQuotedRowFirstCoordinateState (some .frameEnd) tail
        ((quoteUnaryFrameSym .frameEnd).reverse ++ output))) 3 := by
  exact ⟨⟨3, rfl⟩, le_rfl⟩

/-- One coordinate's leading marker and its three unary triples are quoted
without introducing an outer boundary. -/
def transitionMuxQuotedRowParser_coordinate
    (frame : AffineMuxFinPairFrame) (buffer : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer
        (encodeAffineMuxFinPairFrame frame ++ tail) output)
      (some (transitionMuxQuotedRowParserScanCfg .afterInvocation
        (some .frameEnd) tail
        ((quoteUnaryFrameStream
          (encodeAffineMuxFinPairFrame frame)).reverse ++ output)))
      (3 * (encodeAffineMuxFinPairFrame frame).length) := by
  let afterLead :=
    (quoteUnaryFrameSym .frameEnd).reverse ++ output
  let firstChunk := encodeUnaryFrame
    [frame.whenTrue, 0, frame.selector] ++ [.frameEnd]
  let afterFirst :=
    (quoteUnaryFrameStream firstChunk).reverse ++ afterLead
  let secondChunk := encodeUnaryFrame
    [frame.whenFalse, 0, frame.selectorNot] ++ [.frameEnd]
  let afterSecond :=
    (quoteUnaryFrameStream secondChunk).reverse ++ afterFirst
  let thirdChunk := encodeUnaryFrame
    [frame.trueArm, 0, frame.falseArm + 1] ++ [.frameEnd]
  have hlead : EvalsToInTime
      (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer
        (.frameEnd :: (firstChunk ++ (secondChunk ++ (thirdChunk ++ tail))))
        output)
      (some (transitionMuxQuotedRowParserScanCfg
        (.triple (.coordinate ⟨0, by decide⟩) ⟨0, by decide⟩)
        (some .frameEnd) (firstChunk ++ (secondChunk ++ (thirdChunk ++ tail)))
        afterLead)) 3 := by
    simpa [transitionMuxQuotedRowFirstCoordinateState, afterLead] using
      parserCoordinateLead buffer
        (firstChunk ++ (secondChunk ++ (thirdChunk ++ tail))) output
  have hfirst := transitionMuxQuotedRowParser_triple
    (.coordinate ⟨0, by decide⟩) frame.whenTrue 0 frame.selector
    (some .frameEnd) (secondChunk ++ thirdChunk ++ tail) afterLead
  have hsecond := transitionMuxQuotedRowParser_triple
    (.coordinate ⟨1, by decide⟩) frame.whenFalse 0 frame.selectorNot
    (some .frameEnd) (thirdChunk ++ tail) afterFirst
  have hthird := transitionMuxQuotedRowParser_triple
    (.coordinate ⟨2, by decide⟩) frame.trueArm 0 (frame.falseArm + 1)
    (some .frameEnd) tail afterSecond
  simp [transitionMuxQuotedRowAfterTriple] at hfirst hsecond hthird
  dsimp [firstChunk, secondChunk, thirdChunk] at hlead hfirst hsecond hthird
  simp only [List.singleton_append, List.append_assoc] at hlead hfirst hsecond hthird
  let h₁ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) 3
    (parserTripleSteps frame.whenTrue 0 frame.selector)
    _ _ _ hlead hfirst
  let h₂ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _
    (parserTripleSteps frame.whenFalse 0 frame.selectorNot)
    _ _ _ h₁ hsecond
  let full := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _
    (parserTripleSteps frame.trueArm 0 (frame.falseArm + 1))
    _ _ _ h₂ hthird
  convert full using 1
  · simp [encodeAffineMuxFinPairFrame, firstChunk, secondChunk, thirdChunk,
      List.append_assoc]
  · simp [encodeAffineMuxFinPairFrame, firstChunk, secondChunk, thirdChunk,
      afterLead, afterFirst, afterSecond, quoteUnaryFrameStream,
      List.reverse_append, List.append_assoc]
  · simp [encodeAffineMuxFinPairFrame, parserTripleSteps, firstChunk,
      secondChunk, thirdChunk, encodeUnaryFrame, encodeUnaryFrameBlock]
    omega

/-- A complete coordinate list preserves the invocation-boundary scan state.
-/
def transitionMuxQuotedRowParser_coordinates
    (frames : List AffineMuxFinPairFrame) (buffer : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer
        (frames.flatMap encodeAffineMuxFinPairFrame ++ tail) output)
      (some (transitionMuxQuotedRowParserScanCfg .afterInvocation
        (match frames with | [] => buffer | _ :: _ => some .frameEnd)
        tail
        ((quoteUnaryFrameStream
          (frames.flatMap encodeAffineMuxFinPairFrame)).reverse ++ output)))
      (3 * (frames.flatMap encodeAffineMuxFinPairFrame).length) := by
  induction frames generalizing buffer output with
  | nil =>
      simpa using EvalsToInTime.refl
        (step transitionMuxQuotedRowParserRevProgram)
        (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer tail
          output)
  | cons frame rest ih =>
      let restInput := rest.flatMap encodeAffineMuxFinPairFrame ++ tail
      let frameOutput :=
        (quoteUnaryFrameStream (encodeAffineMuxFinPairFrame frame)).reverse ++
          output
      have hframe := transitionMuxQuotedRowParser_coordinate frame buffer
        restInput output
      have hrest := ih (some .frameEnd) frameOutput
      let full := EvalsToInTime.trans
        (step transitionMuxQuotedRowParserRevProgram)
        (3 * (encodeAffineMuxFinPairFrame frame).length)
        (3 * (rest.flatMap encodeAffineMuxFinPairFrame).length)
        _ _ _ hframe hrest
      convert full using 1
      · simp [restInput, List.append_assoc]
      · simp [frameOutput, quoteUnaryFrameStream, List.flatMap_cons,
          List.reverse_append, List.append_assoc]
        cases rest <;> rfl
      · simp only [List.flatMap_cons, List.length_append, Nat.mul_add]
        omega

private def transitionMuxQuotedRowParser_header
    (selector : Nat) (buffer : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg
        transitionMuxQuotedRowInitialState buffer
        (encodeAffineMuxFinHeader selector ++ tail) output)
      (some (transitionMuxQuotedRowParserScanCfg .afterInvocation
        (some .frameEnd) tail
        ((quoteUnaryFrameStream
          (encodeAffineMuxFinHeader selector)).reverse ++ output)))
      (3 * (encodeAffineMuxFinHeader selector).length) := by
  simpa [encodeAffineMuxFinHeader, transitionMuxQuotedRowInitialState,
    transitionMuxQuotedRowAfterTriple, parserTripleSteps] using
      transitionMuxQuotedRowParser_triple .header 0 0 selector buffer tail
        output

/-- One view is parsed without a leading outer marker.  This is the entry
case for the first invocation in a family. -/
def transitionMuxQuotedRowParser_view
    (view : TransitionDispatchMuxInvocationView)
    (buffer : Option UnaryFrameSym) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg
        transitionMuxQuotedRowInitialState buffer (view.encode ++ tail) output)
      (some (transitionMuxQuotedRowParserScanCfg .afterInvocation
        (some .frameEnd)
        tail ((quoteUnaryFrameStream view.encode).reverse ++ output)))
      (3 * view.encode.length) := by
  let coordinateInput :=
    view.frames.flatMap encodeAffineMuxFinPairFrame ++ tail
  let headerOutput :=
    (quoteUnaryFrameStream (encodeAffineMuxFinHeader view.selector)).reverse ++
      output
  have hheader := transitionMuxQuotedRowParser_header view.selector buffer
    (view.frames.flatMap encodeAffineMuxFinPairFrame ++ tail) output
  have hcoordinates := transitionMuxQuotedRowParser_coordinates view.frames
    (some .frameEnd) tail headerOutput
  let full := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram)
    (3 * (encodeAffineMuxFinHeader view.selector).length)
    (3 * (view.frames.flatMap encodeAffineMuxFinPairFrame).length)
    _ _ _ hheader hcoordinates
  convert full using 1
  · simp [TransitionDispatchMuxInvocationView.encode,
      encodeAffineMuxFinFrames, coordinateInput, List.append_assoc]
  · simp [TransitionDispatchMuxInvocationView.encode,
      encodeAffineMuxFinFrames, headerOutput, quoteUnaryFrameStream,
      List.reverse_append, List.append_assoc]
    cases view.frames <;> rfl
  · simp only [TransitionDispatchMuxInvocationView.encode,
      encodeAffineMuxFinFrames, List.length_append, Nat.mul_add]
    omega

private def transitionMuxQuotedRowHeaderTail (selector : Nat) :
    List UnaryFrameSym :=
  .separator :: List.replicate selector .tick ++
    .separator :: .frameEnd :: []

private def parserBoundaryThenHeaderFirst
    (buffer : Option UnaryFrameSym) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer
        (.separator :: tail) output)
      (some (transitionMuxQuotedRowParserScanCfg
        transitionMuxQuotedRowFirstHeaderState (some .separator) tail
        ((quoteUnaryFrameSym .separator).reverse ++ .frameEnd :: output))) 4 := by
  exact ⟨⟨4, rfl⟩, le_rfl⟩

/-- Once the first zero-field separator has been consumed at a row boundary,
the rest of a mux header reaches the ordinary post-header state. -/
private def transitionMuxQuotedRowParser_headerTail
    (selector : Nat) (buffer : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg
        transitionMuxQuotedRowFirstHeaderState buffer
        (transitionMuxQuotedRowHeaderTail selector ++ tail) output)
      (some (transitionMuxQuotedRowParserScanCfg .afterInvocation
        (some .frameEnd) tail
        ((quoteUnaryFrameStream
          (transitionMuxQuotedRowHeaderTail selector)).reverse ++ output)))
      (3 * (transitionMuxQuotedRowHeaderTail selector).length) := by
  let afterSecondSeparator :=
    (quoteUnaryFrameSym .separator).reverse ++ output
  let afterTicks :=
    (quoteUnaryFrameStream (List.replicate selector .tick)).reverse ++
      afterSecondSeparator
  let afterThirdSeparator :=
    (quoteUnaryFrameSym .separator).reverse ++ afterTicks
  have hsep₂ : EvalsToInTime
      (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg
        (.triple .header ⟨1, by decide⟩) buffer
        (.separator :: List.replicate selector .tick ++
          .separator :: .frameEnd :: tail) output)
      (some (transitionMuxQuotedRowParserScanCfg
        (.triple .header ⟨2, by decide⟩) (some .separator)
        (List.replicate selector .tick ++ .separator :: .frameEnd :: tail)
        afterSecondSeparator)) 3 := by
    simpa [transitionMuxQuotedRowIncrement, afterSecondSeparator,
      quoteUnaryFrameSym, quoteUnaryFrameFirst, quoteUnaryFrameSecond] using
      parserSeparator .header (⟨1, by decide⟩ : Fin 4) (by decide) buffer
        (List.replicate selector .tick ++ .separator :: .frameEnd :: tail)
        output
  have hticks := parserTicks .header (⟨2, by decide⟩ : Fin 4) selector
    (some .separator) (.separator :: .frameEnd :: tail)
    afterSecondSeparator
  have hsep₃ : EvalsToInTime
      (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg
        (.triple .header ⟨2, by decide⟩)
        (if selector = 0 then some .separator else some .tick)
        (.separator :: .frameEnd :: tail) afterTicks)
      (some (transitionMuxQuotedRowParserScanCfg
        (.triple .header ⟨3, by decide⟩) (some .separator)
        (.frameEnd :: tail) afterThirdSeparator)) 3 := by
    simpa [transitionMuxQuotedRowIncrement, afterThirdSeparator,
      quoteUnaryFrameSym, quoteUnaryFrameFirst, quoteUnaryFrameSecond] using
      parserSeparator .header (⟨2, by decide⟩ : Fin 4) (by decide)
        (if selector = 0 then some .separator else some .tick)
        (.frameEnd :: tail) afterTicks
  have hend := parserTripleFrameEnd .header (⟨3, by decide⟩ : Fin 4)
    (by decide) (some .separator) tail afterThirdSeparator
  simp [transitionMuxQuotedRowAfterTriple] at hend
  let h₁ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) 3 (3 * selector)
    _ _ _ hsep₂ hticks
  let h₂ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _ 3
    _ _ _ h₁ hsep₃
  let full := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _ 3
    _ _ _ h₂ hend
  convert full using 1
  · simp [transitionMuxQuotedRowFirstHeaderState,
      transitionMuxQuotedRowHeaderTail, List.append_assoc]
  · simp [transitionMuxQuotedRowHeaderTail, afterSecondSeparator,
      afterTicks, afterThirdSeparator, quoteUnaryFrameStream,
      List.reverse_append, List.append_assoc]
  · simp [transitionMuxQuotedRowHeaderTail]
    omega

/-- A later view emits the boundary of its predecessor before quoting its
own header and coordinates. -/
private def transitionMuxQuotedRowParser_viewAfterBoundary
    (view : TransitionDispatchMuxInvocationView)
    (buffer : Option UnaryFrameSym) (tail output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer
        (view.encode ++ tail) output)
      (some (transitionMuxQuotedRowParserScanCfg .afterInvocation
        (some .frameEnd) tail
        ((quoteUnaryFrameStream view.encode).reverse ++ .frameEnd :: output)))
      (3 * view.encode.length + 1) := by
  let headerTail := transitionMuxQuotedRowHeaderTail view.selector
  let coordinateFrames := view.frames.flatMap encodeAffineMuxFinPairFrame
  let afterBoundary :=
    (quoteUnaryFrameSym .separator).reverse ++ .frameEnd :: output
  let afterHeader :=
    (quoteUnaryFrameStream headerTail).reverse ++ afterBoundary
  have hboundary := parserBoundaryThenHeaderFirst buffer
    (headerTail ++ (coordinateFrames ++ tail)) output
  have hheader := transitionMuxQuotedRowParser_headerTail view.selector
    (some .separator) (coordinateFrames ++ tail) afterBoundary
  have hcoordinates := transitionMuxQuotedRowParser_coordinates view.frames
    (some .frameEnd) tail afterHeader
  have hheaderEncoding : encodeAffineMuxFinHeader view.selector =
      .separator :: headerTail := by
    simp [encodeAffineMuxFinHeader, headerTail,
      transitionMuxQuotedRowHeaderTail, encodeUnaryFrame,
      encodeUnaryFrameBlock, List.append_assoc]
  have hviewEncoding : view.encode =
      .separator :: (headerTail ++ coordinateFrames) := by
    simp [TransitionDispatchMuxInvocationView.encode,
      encodeAffineMuxFinFrames, hheaderEncoding, coordinateFrames,
      List.append_assoc]
  let h₁ := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) 4
    (3 * headerTail.length) _ _ _ hboundary hheader
  let full := EvalsToInTime.trans
    (step transitionMuxQuotedRowParserRevProgram) _
    (3 * coordinateFrames.length) _ _ _ h₁ hcoordinates
  convert full using 1
  · rw [hviewEncoding]
    simp [List.append_assoc]
  · rw [hviewEncoding, quoteUnaryFrameStream_cons, List.reverse_append]
    simp [afterBoundary, afterHeader, quoteUnaryFrameStream,
      List.reverse_append, List.append_assoc]
    simp [coordinateFrames]
    cases view.frames <;> rfl
  · rw [hviewEncoding]
    simp only [List.length_cons, List.length_append]
    omega

private def transitionMuxQuotedRowParser_finish
    (buffer : Option UnaryFrameSym) (output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer [] output)
      (some (haltCfg transitionMuxQuotedRowParserRevProgram
        (.frameEnd :: output))) 3 := by
  exact ⟨⟨3, rfl⟩, le_rfl⟩

private def transitionMuxQuotedRowParserTailSteps
    (views : List TransitionDispatchMuxInvocationView) : Nat :=
  3 * (transitionMuxInvocationViewFamilyFrames views).length +
    views.length + 3

/-- Exact execution for all invocations after an already completed first
view.  The base case emits that first view's trailing boundary. -/
private def transitionMuxQuotedRowParser_viewsTail
    (views : List TransitionDispatchMuxInvocationView)
    (buffer : Option UnaryFrameSym) (output : List UnaryFrameSym) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (transitionMuxQuotedRowParserScanCfg .afterInvocation buffer
        (transitionMuxInvocationViewFamilyFrames views) output)
      (some (haltCfg transitionMuxQuotedRowParserRevProgram
        ((views.flatMap fun view =>
          quoteUnaryFrameStream view.encode ++ [.frameEnd]).reverse ++
            .frameEnd :: output)))
      (transitionMuxQuotedRowParserTailSteps views) := by
  induction views generalizing buffer output with
  | nil =>
      simpa [transitionMuxInvocationViewFamilyFrames,
        transitionMuxQuotedRowParserTailSteps] using
        transitionMuxQuotedRowParser_finish buffer output
  | cons view rest ih =>
      let restInput := transitionMuxInvocationViewFamilyFrames rest
      let viewOutput :=
        (quoteUnaryFrameStream view.encode).reverse ++ .frameEnd :: output
      have hview := transitionMuxQuotedRowParser_viewAfterBoundary view buffer
        restInput output
      have hrest := ih (some .frameEnd) viewOutput
      let full := EvalsToInTime.trans
        (step transitionMuxQuotedRowParserRevProgram)
        (3 * view.encode.length + 1)
        (transitionMuxQuotedRowParserTailSteps rest)
        _ _ _ hview hrest
      convert full using 1
      · simp [transitionMuxInvocationViewFamilyFrames, restInput]
      · simp [viewOutput, List.reverse_append, List.append_assoc]
      · simp [transitionMuxQuotedRowParserTailSteps,
          transitionMuxInvocationViewFamilyFrames, Nat.mul_add]
        omega

/-- Exact total cost of the closed parser. -/
def transitionMuxQuotedRowParserSteps
    (views : List TransitionDispatchMuxInvocationView) : Nat :=
  match views with
  | [] => 2
  | _ :: _ =>
      3 * (transitionMuxInvocationViewFamilyFrames views).length +
        views.length + 2

/-- Complete prepend-output run on a typed family of mux invocations. -/
def transitionMuxQuotedRowParserRev_run
    (views : List TransitionDispatchMuxInvocationView) :
    EvalsToInTime (step transitionMuxQuotedRowParserRevProgram)
      (initialCfg transitionMuxQuotedRowParserRevProgram
        (transitionMuxInvocationViewFamilyFrames views))
      (some (haltCfg transitionMuxQuotedRowParserRevProgram
        (encodeUnaryFrameMarkedRowFamily
          (transitionMuxInvocationQuotedRowFamily views)).reverse))
      (transitionMuxQuotedRowParserSteps views) := by
  cases views with
  | nil => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | cons view rest =>
      let restInput := transitionMuxInvocationViewFamilyFrames rest
      let viewOutput := (quoteUnaryFrameStream view.encode).reverse ++ []
      have hview := transitionMuxQuotedRowParser_view view none restInput []
      have hrest := transitionMuxQuotedRowParser_viewsTail rest
        (some .frameEnd) viewOutput
      let full := EvalsToInTime.trans
        (step transitionMuxQuotedRowParserRevProgram)
        (3 * view.encode.length)
        (transitionMuxQuotedRowParserTailSteps rest)
        _ _ _ hview hrest
      convert full using 1
      · simp [initialCfg, transitionMuxQuotedRowParserRevProgram,
          transitionMuxQuotedRowParserScanCfg,
          transitionMuxQuotedRowParserCfg,
          transitionMuxInvocationViewFamilyFrames, restInput]
      · rw [transitionMuxInvocationQuotedRowFamily_encoding]
        simp [viewOutput, List.reverse_append, List.append_assoc]
      · simp [transitionMuxQuotedRowParserSteps,
          transitionMuxQuotedRowParserTailSteps,
          transitionMuxInvocationViewFamilyFrames, Nat.mul_add]
        omega

end CLRS.Chapter34.Turing.CookLevin
