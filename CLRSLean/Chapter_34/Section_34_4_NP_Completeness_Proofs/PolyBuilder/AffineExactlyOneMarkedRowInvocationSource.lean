import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneSeedCarrierSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneOutputFamilySource
import Mathlib.Tactic

/-!
# Projecting reversed marked one-hot rows to output-source invocations

The structured one-hot source can expose the reverse of a row-delimited
compact stream.  In that representation rows occur in reverse order, and the
compact frames inside each row also occur in reverse order.  This fixed
controller uses exactly that layout: it drops each unused `sourceBase`, emits
the compact `(start, count, 0)` invocation, buffers one row, and flushes the
row as a unit.  Prepend output reverses the row order a second time, yielding
the forward row family required by the validity final-conjunction source.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Final-conjunction invocation block for one structured validity row. -/
def encodeAffineExactlyOneStructuredRowOutputInvocation
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : List UnaryFrameSym :=
  encodeAffineExactlyOneOutputSourceInvocationFamily
      (affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
        seed.height seed.start seed.rowBase).reverse ++
    [.frameEnd]

/-- Row-major family of final-conjunction one-hot invocations. -/
def encodeAffineExactlyOneStructuredRowOutputInvocationFamily
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    List AffineExactlyOneStructuredRowSeed → List UnaryFrameSym
  | [] => []
  | seed :: rest =>
      encodeAffineExactlyOneStructuredRowOutputInvocation
          labelWidth stateWidth cellCounts seed ++
        encodeAffineExactlyOneStructuredRowOutputInvocationFamily
          labelWidth stateWidth cellCounts rest

/-- Input block seen by the projector for one compact frame after its leading
separator has already been consumed. -/
def encodeAffineExactlyOneReversedCompactBody
  (frame : AffineExactlyOneFrame) : List UnaryFrameSym :=
  List.replicate frame.count .tick ++ [.separator] ++
    List.replicate frame.rowBase .tick ++ [.separator] ++
    List.replicate frame.start .tick

/-- Reversed compact frames in the exact order seen after a row marker. -/
def encodeAffineExactlyOneReversedCompactFrameStream
    (frames : List AffineExactlyOneFrame) : List UnaryFrameSym :=
  frames.flatMap (fun frame =>
    .separator :: encodeAffineExactlyOneReversedCompactBody frame)

/-- Reversed marked seed stream, indexed in the order in which the projector
will process rows. -/
def encodeAffineExactlyOneReversedMarkedSeedStream
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    List AffineExactlyOneStructuredRowSeed → List UnaryFrameSym
  | [] => []
  | seed :: rest =>
      .frameEnd ::
        encodeAffineExactlyOneReversedCompactFrameStream
          (affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
            seed.height seed.start seed.rowBase).reverse ++
        encodeAffineExactlyOneReversedMarkedSeedStream
          labelWidth stateWidth cellCounts rest

theorem encodeAffineExactlyOneCompact_reverse
    (frame : AffineExactlyOneFrame) :
    (encodeAffineExactlyOneCompactFrame frame).reverse =
      .separator :: encodeAffineExactlyOneReversedCompactBody frame := by
  simp [encodeAffineExactlyOneCompactFrame,
    encodeAffineExactlyOneReversedCompactBody, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.reverse_append, List.append_assoc]

/-- Reversing the ordinary compact family exposes exactly the marked-row
projector's frame stream, in reverse frame order. -/
theorem encodeAffineExactlyOneCompactFamily_reverse
    (frames : List AffineExactlyOneFrame) :
    (encodeAffineExactlyOneCompactFamily frames).reverse =
      encodeAffineExactlyOneReversedCompactFrameStream frames.reverse := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      simp [encodeAffineExactlyOneCompactFamily, List.reverse_append, ih,
        encodeAffineExactlyOneReversedCompactFrameStream,
        encodeAffineExactlyOneCompact_reverse]

private theorem encodeAffineExactlyOneReversedMarkedSeedStream_append
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (left right : List AffineExactlyOneStructuredRowSeed) :
    encodeAffineExactlyOneReversedMarkedSeedStream
        labelWidth stateWidth cellCounts (left ++ right) =
      encodeAffineExactlyOneReversedMarkedSeedStream
          labelWidth stateWidth cellCounts left ++
        encodeAffineExactlyOneReversedMarkedSeedStream
          labelWidth stateWidth cellCounts right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineExactlyOneReversedMarkedSeedStream, ih,
        List.append_assoc]

/-- The marked row source's prepend output is exactly the projector stream
for the seeds in reverse order. -/
theorem encodeAffineExactlyOneStructuredRowMarkedFamily_reverse
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    (encodeAffineExactlyOneStructuredRowMarkedFamily
      labelWidth stateWidth cellCounts seeds).reverse =
      encodeAffineExactlyOneReversedMarkedSeedStream
        labelWidth stateWidth cellCounts seeds.reverse := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineExactlyOneStructuredRowMarkedFamily,
        encodeAffineExactlyOneReversedMarkedSeedStream,
        encodeAffineExactlyOneCompactFamily_reverse,
        encodeAffineExactlyOneReversedMarkedSeedStream_append,
        List.reverse_append, ih, List.append_assoc]

/-- Whether the current compact frame is followed by another frame in the
same row or is the final frame of that row. -/
inductive AffineExactlyOneMarkedRowAfterFrame
  | nextFrame | endRow
deriving DecidableEq, Fintype

/-- Finite control for the reversed-row projector. -/
inductive AffineExactlyOneMarkedRowInvocationLabel
  | rowStart
  | expectFrame
  | loadCount
  | incCount
  | loadBase
  | loadStart
  | incStart
  | restoreMarker
  | restoreMarkerInput
  | emitStart (after : AffineExactlyOneMarkedRowAfterFrame)
  | emitStartTick (after : AffineExactlyOneMarkedRowAfterFrame)
  | emitStartSeparator (after : AffineExactlyOneMarkedRowAfterFrame)
  | emitCount (after : AffineExactlyOneMarkedRowAfterFrame)
  | emitCountTick (after : AffineExactlyOneMarkedRowAfterFrame)
  | emitCountSeparator₁ (after : AffineExactlyOneMarkedRowAfterFrame)
  | emitCountSeparator₂ (after : AffineExactlyOneMarkedRowAfterFrame)
  | markRow
  | flushRow
  | flushSymbol (symbol : UnaryFrameSym)
  | finish
  | invalid
deriving DecidableEq, Fintype

/-- Fixed projector from a reversed marked compact stream to row-major
`(start, count, 0)` invocations.  `sourceBase` ticks are consumed without
entering a counter. -/
def affineExactlyOneMarkedRowInvocationProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneMarkedRowInvocationLabel
  main := .rowStart
  op
    | .rowStart =>
        .popInput .finish (fun symbol =>
          if symbol = .frameEnd then .expectFrame else .invalid)
    | .expectFrame =>
        .popInput .invalid (fun symbol =>
          if symbol = .separator then .loadCount else .invalid)
    | .loadCount =>
        .popInput (.emitStart .endRow) (fun symbol =>
          match symbol with
          | .tick => .incCount
          | .separator => .loadBase
          | .frameEnd => .invalid)
    | .incCount => .inc₂ .loadCount
    | .loadBase =>
        .popInput .invalid (fun symbol =>
          match symbol with
          | .tick => .loadBase
          | .separator => .loadStart
          | .frameEnd => .invalid)
    | .loadStart =>
        .popInput (.emitStart .endRow) (fun symbol =>
          match symbol with
          | .tick => .incStart
          | .separator => .emitStart .nextFrame
          | .frameEnd => .restoreMarker)
    | .incStart => .inc₁ .loadStart
    | .restoreMarker => .pushWork₂ .frameEnd .restoreMarkerInput
    | .restoreMarkerInput =>
        .moveWork₂Input (.emitStart .endRow)
          (fun _ => .emitStart .endRow)
    | .emitStart after =>
        .dec₁ (.emitStartSeparator after) (.emitStartTick after)
    | .emitStartTick after => .pushWork₁ .tick (.emitStart after)
    | .emitStartSeparator after =>
        .pushWork₁ .separator (.emitCount after)
    | .emitCount after =>
        .dec₂ (.emitCountSeparator₁ after) (.emitCountTick after)
    | .emitCountTick after => .pushWork₁ .tick (.emitCount after)
    | .emitCountSeparator₁ after =>
        .pushWork₁ .separator (.emitCountSeparator₂ after)
    | .emitCountSeparator₂ .nextFrame =>
        .pushWork₁ .separator .loadCount
    | .emitCountSeparator₂ .endRow =>
        .pushWork₁ .separator .markRow
    | .markRow => .pushWork₁ .frameEnd .flushRow
    | .flushRow => .popWork₁ .rowStart .flushSymbol
    | .flushSymbol symbol => .pushOutput symbol .flushRow
    | .finish => .halt
    | .invalid => .halt

private def affineExactlyOneMarkedRowInvocationCfg
    (label : AffineExactlyOneMarkedRowInvocationLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (start count : List Unit) :
    BuilderCfg affineExactlyOneMarkedRowInvocationProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := start
  counter₂ := count
  counter₃ := []

private def affineExactlyOneMarkedRowInvocationLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneMarkedRowInvocationProgram :=
  affineExactlyOneMarkedRowInvocationCfg .rowStart none none false
    input output [] [] [] []

private theorem markedRowInvocation_scanCount_eval
    (base value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym) :
    (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
      2 * value + 1]
      (some (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (List.replicate value .tick ++ .separator :: tail)
        output work₁ work₂ [] (List.replicate base ()))) =
      some (affineExactlyOneMarkedRowInvocationCfg .loadBase
        (some .separator) buffer₂ test tail output work₁ work₂ []
        (List.replicate (base + value) ())) := by
  induction value generalizing base buffer₁ test with
  | zero =>
      change step affineExactlyOneMarkedRowInvocationProgram
        (affineExactlyOneMarkedRowInvocationCfg .loadCount
          buffer₁ buffer₂ test (.separator :: tail)
          output work₁ work₂ [] (List.replicate base ())) = _
      rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
          2 * value + 1]
          (some (affineExactlyOneMarkedRowInvocationCfg .loadCount
            (some .tick) buffer₂ test
            (List.replicate value .tick ++ .separator :: tail)
            output work₁ work₂ []
            (() :: List.replicate base ()))) = _
      have hcounter : (() :: List.replicate base ()) =
          List.replicate (base + 1) () := by
        rw [List.replicate_succ]
      rw [hcounter]
      simpa only [Nat.add_assoc, Nat.add_comm 1 value] using
        ih (base + 1) (some .tick) test

private theorem markedRowInvocation_scanBase_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (start count : List Unit) :
    (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
      value + 1]
      (some (affineExactlyOneMarkedRowInvocationCfg .loadBase
        buffer₁ buffer₂ test
        (List.replicate value .tick ++ .separator :: tail)
        output work₁ work₂ start count)) =
      some (affineExactlyOneMarkedRowInvocationCfg .loadStart
        (some .separator) buffer₂ test tail output work₁ work₂
        start count) := by
  induction value generalizing buffer₁ with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
          value + 1]
          (some (affineExactlyOneMarkedRowInvocationCfg .loadBase
            (some .tick) buffer₂ test
            (List.replicate value .tick ++ .separator :: tail)
            output work₁ work₂ start count)) = _
      exact ih (some .tick)

private theorem markedRowInvocation_scanStartNext_eval
    (base value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (count : List Unit) :
    (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
      2 * value + 1]
      (some (affineExactlyOneMarkedRowInvocationCfg .loadStart
        buffer₁ buffer₂ test
        (List.replicate value .tick ++ .separator :: tail)
        output work₁ work₂ (List.replicate base ()) count)) =
      some (affineExactlyOneMarkedRowInvocationCfg
        (.emitStart .nextFrame) (some .separator) buffer₂ test tail output
        work₁ work₂ (List.replicate (base + value) ()) count) := by
  induction value generalizing base buffer₁ test with
  | zero =>
      change step affineExactlyOneMarkedRowInvocationProgram
        (affineExactlyOneMarkedRowInvocationCfg .loadStart
          buffer₁ buffer₂ test (.separator :: tail)
          output work₁ work₂ (List.replicate base ()) count) = _
      rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
          2 * value + 1]
          (some (affineExactlyOneMarkedRowInvocationCfg .loadStart
            (some .tick) buffer₂ test
            (List.replicate value .tick ++ .separator :: tail)
            output work₁ work₂
            (() :: List.replicate base ()) count)) = _
      have hcounter : (() :: List.replicate base ()) =
          List.replicate (base + 1) () := by
        rw [List.replicate_succ]
      rw [hcounter]
      simpa only [Nat.add_assoc, Nat.add_comm 1 value] using
        ih (base + 1) (some .tick) test

private theorem markedRowInvocation_scanStartEnd_eval
    (base value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ : List UnaryFrameSym)
    (count : List Unit) :
    (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
      2 * value + 3]
      (some (affineExactlyOneMarkedRowInvocationCfg .loadStart
        buffer₁ buffer₂ test
        (List.replicate value .tick ++ .frameEnd :: tail)
        output work₁ [] (List.replicate base ()) count)) =
      some (affineExactlyOneMarkedRowInvocationCfg
        (.emitStart .endRow) (some .frameEnd) (some .frameEnd) test
        (.frameEnd :: tail) output work₁ []
        (List.replicate (base + value) ()) count) := by
  induction value generalizing base buffer₁ test with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 3 = (2 * value + 3) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
          2 * value + 3]
          (some (affineExactlyOneMarkedRowInvocationCfg .loadStart
            (some .tick) buffer₂ test
            (List.replicate value .tick ++ .frameEnd :: tail)
            output work₁ [] (() :: List.replicate base ()) count)) = _
      have hcounter : (() :: List.replicate base ()) =
          List.replicate (base + 1) () := by
        rw [List.replicate_succ]
      rw [hcounter]
      simpa only [Nat.add_assoc, Nat.add_comm 1 value] using
        ih (base + 1) (some .tick) test

private theorem markedRowInvocation_scanStartEOF_eval
    (base value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (output work₁ : List UnaryFrameSym) (count : List Unit) :
    (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
      2 * value + 1]
      (some (affineExactlyOneMarkedRowInvocationCfg .loadStart
        buffer₁ buffer₂ test (List.replicate value .tick)
        output work₁ [] (List.replicate base ()) count)) =
      some (affineExactlyOneMarkedRowInvocationCfg
        (.emitStart .endRow) none buffer₂ test [] output work₁ []
        (List.replicate (base + value) ()) count) := by
  induction value generalizing base buffer₁ test with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
          2 * value + 1]
          (some (affineExactlyOneMarkedRowInvocationCfg .loadStart
            (some .tick) buffer₂ test (List.replicate value .tick)
            output work₁ [] (() :: List.replicate base ()) count)) = _
      have hcounter : (() :: List.replicate base ()) =
          List.replicate (base + 1) () := by
        rw [List.replicate_succ]
      rw [hcounter]
      simpa only [Nat.add_assoc, Nat.add_comm 1 value] using
        ih (base + 1) (some .tick) test

private theorem markedRowInvocation_replicate_append_cons
    {alpha : Type} (item : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count item ++ item :: tail =
      item :: (List.replicate count item ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons item) ih

private theorem markedRowInvocation_emitStart_eval
    (after : AffineExactlyOneMarkedRowAfterFrame)
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (count : List Unit) :
    (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
      2 * value + 1]
      (some (affineExactlyOneMarkedRowInvocationCfg (.emitStart after)
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate value ()) count)) =
      some (affineExactlyOneMarkedRowInvocationCfg
        (.emitStartSeparator after) buffer₁ buffer₂ false input output
        (List.replicate value .tick ++ work₁) work₂ [] count) := by
  induction value generalizing test work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
          2 * value + 1]
          (some (affineExactlyOneMarkedRowInvocationCfg (.emitStart after)
            buffer₁ buffer₂ true input output (.tick :: work₁) work₂
            (List.replicate value ()) count)) = _
      simpa only [List.replicate_succ, List.cons_append,
        markedRowInvocation_replicate_append_cons] using
        ih true (.tick :: work₁)

private theorem markedRowInvocation_emitCount_eval
    (after : AffineExactlyOneMarkedRowAfterFrame)
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym) :
    (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
      2 * value + 1]
      (some (affineExactlyOneMarkedRowInvocationCfg (.emitCount after)
        buffer₁ buffer₂ test input output work₁ work₂ []
        (List.replicate value ()))) =
      some (affineExactlyOneMarkedRowInvocationCfg
        (.emitCountSeparator₁ after) buffer₁ buffer₂ false input output
        (List.replicate value .tick ++ work₁) work₂ [] []) := by
  induction value generalizing test work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
          2 * value + 1]
          (some (affineExactlyOneMarkedRowInvocationCfg (.emitCount after)
            buffer₁ buffer₂ true input output (.tick :: work₁) work₂
            [] (List.replicate value ()))) = _
      simpa only [List.replicate_succ, List.cons_append,
        markedRowInvocation_replicate_append_cons] using
        ih true (.tick :: work₁)

/-- Exact emission cost for one projected `(start, count, 0)` invocation. -/
def affineExactlyOneMarkedRowEmitSteps (start count : Nat) : Nat :=
  2 * start + 2 * count + 5

private theorem markedRowInvocation_projected_reverse
    (start count : Nat) (work : List UnaryFrameSym) :
    (encodeUnaryFrame [start, count, 0]).reverse ++ work =
      .separator :: .separator ::
        (List.replicate count .tick ++
          (.separator :: (List.replicate start .tick ++ work))) := by
  simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.reverse_append,
    List.append_assoc]

private def affineExactlyOneMarkedRow_emit_run
    (after : AffineExactlyOneMarkedRowAfterFrame)
    (start count : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg (.emitStart after)
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate start ()) (List.replicate count ()))
      (some (affineExactlyOneMarkedRowInvocationCfg
        (match after with
          | .nextFrame => .loadCount
          | .endRow => .markRow)
        buffer₁ buffer₂ false input output
        ((encodeUnaryFrame [start, count, 0]).reverse ++ work₁)
        work₂ [] []))
      (affineExactlyOneMarkedRowEmitSteps start count) := by
  let afterStart := affineExactlyOneMarkedRowInvocationCfg
    (.emitStartSeparator after) buffer₁ buffer₂ false input output
    (List.replicate start .tick ++ work₁) work₂ []
    (List.replicate count ())
  let beforeCount := affineExactlyOneMarkedRowInvocationCfg
    (.emitCount after) buffer₁ buffer₂ false input output
    (.separator :: List.replicate start .tick ++ work₁) work₂ []
    (List.replicate count ())
  let afterCount := affineExactlyOneMarkedRowInvocationCfg
    (.emitCountSeparator₁ after) buffer₁ buffer₂ false input output
    (List.replicate count .tick ++
      (.separator :: (List.replicate start .tick ++ work₁))) work₂ [] []
  let beforeLast := affineExactlyOneMarkedRowInvocationCfg
    (.emitCountSeparator₂ after) buffer₁ buffer₂ false input output
    (.separator :: (List.replicate count .tick ++
      (.separator :: (List.replicate start .tick ++ work₁)))) work₂ [] []
  let finalWork := .separator :: .separator ::
    (List.replicate count .tick ++
      (.separator :: (List.replicate start .tick ++ work₁)))
  have hstart : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg (.emitStart after)
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate start ()) (List.replicate count ()))
      (some afterStart) (2 * start + 1) :=
    ⟨⟨2 * start + 1, by
      simpa [afterStart] using markedRowInvocation_emitStart_eval after start
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate count ())⟩, le_rfl⟩
  have hstartSep : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterStart (some beforeCount) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hcount : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      beforeCount (some afterCount) (2 * count + 1) :=
    ⟨⟨2 * count + 1, by
      simpa [beforeCount, afterCount, List.cons_append,
        List.append_assoc] using
        markedRowInvocation_emitCount_eval after count buffer₁ buffer₂
          false input output
          (.separator :: (List.replicate start .tick ++ work₁)) work₂⟩,
      le_rfl⟩
  have hcountSep : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterCount (some beforeLast) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hlast : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      beforeLast
      (some (affineExactlyOneMarkedRowInvocationCfg
        (match after with
          | .nextFrame => .loadCount
          | .endRow => .markRow)
        buffer₁ buffer₂ false input output
        finalWork work₂ [] [])) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step affineExactlyOneMarkedRowInvocationProgram beforeLast = _
    cases after <;> rfl
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    (2 * start + 1) 1 _ afterStart _ hstart hstartSep
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ (2 * count + 1) _ beforeCount _ h₁ hcount
  let h₃ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ 1 _ afterCount _ h₂ hcountSep
  let full := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ 1 _ beforeLast _ h₃ hlast
  convert full using 1
  · rw [markedRowInvocation_projected_reverse]
    cases after <;> rfl
  · simp [affineExactlyOneMarkedRowEmitSteps]
    omega

/-- Cost of parsing and projecting a frame whose following row delimiter does
not need to be restored. -/
def affineExactlyOneMarkedRowFrameSteps
    (frame : AffineExactlyOneFrame) : Nat :=
  4 * frame.start + 4 * frame.count + frame.rowBase + 8

private def affineExactlyOneMarkedRow_frameNext_run
    (frame : AffineExactlyOneFrame)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (encodeAffineExactlyOneReversedCompactBody frame ++
          .separator :: tail)
        output work₁ work₂ [] [])
      (some (affineExactlyOneMarkedRowInvocationCfg .loadCount
        (some .separator) buffer₂ false tail output
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ work₁)
        work₂ [] []))
      (affineExactlyOneMarkedRowFrameSteps frame) := by
  let afterCount := affineExactlyOneMarkedRowInvocationCfg .loadBase
    (some .separator) buffer₂ test
    (List.replicate frame.rowBase .tick ++ .separator ::
      List.replicate frame.start .tick ++ .separator :: tail)
    output work₁ work₂ [] (List.replicate frame.count ())
  let afterBase := affineExactlyOneMarkedRowInvocationCfg .loadStart
    (some .separator) buffer₂ test
    (List.replicate frame.start .tick ++ .separator :: tail)
    output work₁ work₂ [] (List.replicate frame.count ())
  let afterStart := affineExactlyOneMarkedRowInvocationCfg
    (.emitStart .nextFrame) (some .separator) buffer₂ test tail output
    work₁ work₂ (List.replicate frame.start ())
    (List.replicate frame.count ())
  have hcount : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (encodeAffineExactlyOneReversedCompactBody frame ++
          .separator :: tail)
        output work₁ work₂ [] [])
      (some afterCount) (2 * frame.count + 1) :=
    ⟨⟨2 * frame.count + 1, by
      simpa [afterCount, encodeAffineExactlyOneReversedCompactBody,
        List.cons_append, List.append_assoc] using
        markedRowInvocation_scanCount_eval 0 frame.count buffer₁ buffer₂
          test
          (List.replicate frame.rowBase .tick ++
            (.separator :: (List.replicate frame.start .tick ++
              (.separator :: tail))))
          output work₁ work₂⟩, le_rfl⟩
  have hbase : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterCount (some afterBase) (frame.rowBase + 1) :=
    ⟨⟨frame.rowBase + 1, by
      simpa [afterCount, afterBase, List.append_assoc] using
        markedRowInvocation_scanBase_eval frame.rowBase (some .separator)
          buffer₂ test
          (List.replicate frame.start .tick ++ .separator :: tail)
          output work₁ work₂ [] (List.replicate frame.count ())⟩,
      le_rfl⟩
  have hstart : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterBase (some afterStart) (2 * frame.start + 1) :=
    ⟨⟨2 * frame.start + 1, by
      simpa [afterBase, afterStart] using
        markedRowInvocation_scanStartNext_eval 0 frame.start
          (some .separator) buffer₂ test tail output work₁ work₂
          (List.replicate frame.count ())⟩, le_rfl⟩
  have hemit := affineExactlyOneMarkedRow_emit_run .nextFrame
    frame.start frame.count (some .separator) buffer₂ test
    tail output work₁ work₂
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    (2 * frame.count + 1) (frame.rowBase + 1) _ afterCount _ hcount hbase
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ (2 * frame.start + 1) _ afterBase _ h₁ hstart
  let full := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ (affineExactlyOneMarkedRowEmitSteps frame.start frame.count)
    _ afterStart _ h₂ hemit
  convert full using 1
  all_goals simp [encodeAffineExactlyOneOutputSourceInvocation,
      affineExactlyOneMarkedRowFrameSteps,
      affineExactlyOneMarkedRowEmitSteps]
  all_goals omega

private def affineExactlyOneMarkedRow_frameEnd_run
    (frame : AffineExactlyOneFrame)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (encodeAffineExactlyOneReversedCompactBody frame ++
          .frameEnd :: tail)
        output work₁ [] [] [])
      (some (affineExactlyOneMarkedRowInvocationCfg .markRow
        (some .frameEnd) (some .frameEnd) false (.frameEnd :: tail) output
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ work₁)
        [] [] []))
      (affineExactlyOneMarkedRowFrameSteps frame + 2) := by
  let afterCount := affineExactlyOneMarkedRowInvocationCfg .loadBase
    (some .separator) buffer₂ test
    (List.replicate frame.rowBase .tick ++ .separator ::
      List.replicate frame.start .tick ++ .frameEnd :: tail)
    output work₁ [] [] (List.replicate frame.count ())
  let afterBase := affineExactlyOneMarkedRowInvocationCfg .loadStart
    (some .separator) buffer₂ test
    (List.replicate frame.start .tick ++ .frameEnd :: tail)
    output work₁ [] [] (List.replicate frame.count ())
  let afterStart := affineExactlyOneMarkedRowInvocationCfg
    (.emitStart .endRow) (some .frameEnd) (some .frameEnd) test
    (.frameEnd :: tail) output work₁ []
    (List.replicate frame.start ()) (List.replicate frame.count ())
  have hcount : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (encodeAffineExactlyOneReversedCompactBody frame ++
          .frameEnd :: tail)
        output work₁ [] [] [])
      (some afterCount) (2 * frame.count + 1) :=
    ⟨⟨2 * frame.count + 1, by
      simpa [afterCount, encodeAffineExactlyOneReversedCompactBody,
        List.cons_append, List.append_assoc] using
        markedRowInvocation_scanCount_eval 0 frame.count buffer₁ buffer₂
          test
          (List.replicate frame.rowBase .tick ++
            (.separator :: (List.replicate frame.start .tick ++
              (.frameEnd :: tail))))
          output work₁ []⟩, le_rfl⟩
  have hbase : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterCount (some afterBase) (frame.rowBase + 1) :=
    ⟨⟨frame.rowBase + 1, by
      simpa [afterCount, afterBase, List.append_assoc] using
        markedRowInvocation_scanBase_eval frame.rowBase (some .separator)
          buffer₂ test
          (List.replicate frame.start .tick ++ .frameEnd :: tail)
          output work₁ [] [] (List.replicate frame.count ())⟩,
      le_rfl⟩
  have hstart : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterBase (some afterStart) (2 * frame.start + 3) :=
    ⟨⟨2 * frame.start + 3, by
      simpa [afterBase, afterStart] using
        markedRowInvocation_scanStartEnd_eval 0 frame.start
          (some .separator) buffer₂ test tail output work₁
          (List.replicate frame.count ())⟩, le_rfl⟩
  have hemit := affineExactlyOneMarkedRow_emit_run .endRow
    frame.start frame.count (some .frameEnd) (some .frameEnd) test
    (.frameEnd :: tail) output work₁ []
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    (2 * frame.count + 1) (frame.rowBase + 1) _ afterCount _ hcount hbase
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ (2 * frame.start + 3) _ afterBase _ h₁ hstart
  let full := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ (affineExactlyOneMarkedRowEmitSteps frame.start frame.count)
    _ afterStart _ h₂ hemit
  convert full using 1
  all_goals simp [encodeAffineExactlyOneOutputSourceInvocation,
      affineExactlyOneMarkedRowFrameSteps,
      affineExactlyOneMarkedRowEmitSteps]
  all_goals omega

private def affineExactlyOneMarkedRow_frameEOF_run
    (frame : AffineExactlyOneFrame)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (output work₁ : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (encodeAffineExactlyOneReversedCompactBody frame)
        output work₁ [] [] [])
      (some (affineExactlyOneMarkedRowInvocationCfg .markRow
        none buffer₂ false [] output
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ work₁)
        [] [] []))
      (affineExactlyOneMarkedRowFrameSteps frame) := by
  let afterCount := affineExactlyOneMarkedRowInvocationCfg .loadBase
    (some .separator) buffer₂ test
    (List.replicate frame.rowBase .tick ++ .separator ::
      List.replicate frame.start .tick)
    output work₁ [] [] (List.replicate frame.count ())
  let afterBase := affineExactlyOneMarkedRowInvocationCfg .loadStart
    (some .separator) buffer₂ test
    (List.replicate frame.start .tick)
    output work₁ [] [] (List.replicate frame.count ())
  let afterStart := affineExactlyOneMarkedRowInvocationCfg
    (.emitStart .endRow) none buffer₂ test [] output work₁ []
    (List.replicate frame.start ()) (List.replicate frame.count ())
  have hcount : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (encodeAffineExactlyOneReversedCompactBody frame)
        output work₁ [] [] [])
      (some afterCount) (2 * frame.count + 1) :=
    ⟨⟨2 * frame.count + 1, by
      simpa [afterCount, encodeAffineExactlyOneReversedCompactBody,
        List.cons_append, List.append_assoc] using
        markedRowInvocation_scanCount_eval 0 frame.count buffer₁ buffer₂
          test
          (List.replicate frame.rowBase .tick ++
            (.separator :: List.replicate frame.start .tick))
          output work₁ []⟩, le_rfl⟩
  have hbase : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterCount (some afterBase) (frame.rowBase + 1) :=
    ⟨⟨frame.rowBase + 1, by
      simpa [afterCount, afterBase, List.append_assoc] using
        markedRowInvocation_scanBase_eval frame.rowBase (some .separator)
          buffer₂ test (List.replicate frame.start .tick)
          output work₁ [] [] (List.replicate frame.count ())⟩,
      le_rfl⟩
  have hstart : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterBase (some afterStart) (2 * frame.start + 1) :=
    ⟨⟨2 * frame.start + 1, by
      simpa [afterBase, afterStart] using
        markedRowInvocation_scanStartEOF_eval 0 frame.start
          (some .separator) buffer₂ test output work₁
          (List.replicate frame.count ())⟩, le_rfl⟩
  have hemit := affineExactlyOneMarkedRow_emit_run .endRow
    frame.start frame.count none buffer₂ test [] output work₁ []
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    (2 * frame.count + 1) (frame.rowBase + 1) _ afterCount _ hcount hbase
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ (2 * frame.start + 1) _ afterBase _ h₁ hstart
  let full := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    _ (affineExactlyOneMarkedRowEmitSteps frame.start frame.count)
    _ afterStart _ h₂ hemit
  convert full using 1
  all_goals simp [encodeAffineExactlyOneOutputSourceInvocation,
      affineExactlyOneMarkedRowFrameSteps,
      affineExactlyOneMarkedRowEmitSteps]
  all_goals omega

/-- Parse cost for a nonempty reversed compact-frame stream.  Restoring a
following row marker costs two additional steps only once, at the final
frame. -/
def affineExactlyOneMarkedRowFramesSteps
    (frames : List AffineExactlyOneFrame) : Nat :=
  (frames.map affineExactlyOneMarkedRowFrameSteps).sum

private def affineExactlyOneMarkedRow_framesEnd_run
    (frame : AffineExactlyOneFrame) (rest : List AffineExactlyOneFrame)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (encodeAffineExactlyOneReversedCompactBody frame ++
          encodeAffineExactlyOneReversedCompactFrameStream rest ++
          .frameEnd :: tail)
        output work₁ [] [] [])
      (some (affineExactlyOneMarkedRowInvocationCfg .markRow
        (some .frameEnd) (some .frameEnd) false (.frameEnd :: tail) output
        ((encodeAffineExactlyOneOutputSourceInvocationFamily
          (frame :: rest)).reverse ++ work₁) [] [] []))
      (affineExactlyOneMarkedRowFramesSteps (frame :: rest) + 2) := by
  induction rest generalizing frame buffer₁ buffer₂ test work₁ with
  | nil =>
      simpa [encodeAffineExactlyOneReversedCompactFrameStream,
        affineExactlyOneMarkedRowFramesSteps,
        encodeAffineExactlyOneOutputSourceInvocationFamily] using
        affineExactlyOneMarkedRow_frameEnd_run frame buffer₁ buffer₂ test
          tail output work₁
  | cons next rest ih =>
      let nextInput := encodeAffineExactlyOneReversedCompactBody next ++
        encodeAffineExactlyOneReversedCompactFrameStream rest ++
        .frameEnd :: tail
      let afterFrame := affineExactlyOneMarkedRowInvocationCfg .loadCount
        (some .separator) buffer₂ false nextInput output
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ work₁)
        [] [] []
      have hfirst : EvalsToInTime
          (step affineExactlyOneMarkedRowInvocationProgram)
          (affineExactlyOneMarkedRowInvocationCfg .loadCount
            buffer₁ buffer₂ test
            (encodeAffineExactlyOneReversedCompactBody frame ++
              encodeAffineExactlyOneReversedCompactFrameStream (next :: rest) ++
              .frameEnd :: tail)
            output work₁ [] [] [])
          (some afterFrame) (affineExactlyOneMarkedRowFrameSteps frame) := by
        simpa [afterFrame, nextInput,
          encodeAffineExactlyOneReversedCompactFrameStream,
          List.append_assoc] using
          affineExactlyOneMarkedRow_frameNext_run frame buffer₁ buffer₂
            test nextInput output work₁ []
      have hrest := ih next (some .separator) buffer₂ false
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ work₁)
      let full := EvalsToInTime.trans
        (step affineExactlyOneMarkedRowInvocationProgram)
        (affineExactlyOneMarkedRowFrameSteps frame)
        (affineExactlyOneMarkedRowFramesSteps (next :: rest) + 2)
        _ afterFrame _ hfirst (by simpa [afterFrame, nextInput] using hrest)
      convert full using 1
      · simp [encodeAffineExactlyOneOutputSourceInvocationFamily,
          List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneMarkedRowFramesSteps]
        omega

private def affineExactlyOneMarkedRow_framesEOF_run
    (frame : AffineExactlyOneFrame) (rest : List AffineExactlyOneFrame)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (output work₁ : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .loadCount
        buffer₁ buffer₂ test
        (encodeAffineExactlyOneReversedCompactBody frame ++
          encodeAffineExactlyOneReversedCompactFrameStream rest)
        output work₁ [] [] [])
      (some (affineExactlyOneMarkedRowInvocationCfg .markRow
        none buffer₂ false [] output
        ((encodeAffineExactlyOneOutputSourceInvocationFamily
          (frame :: rest)).reverse ++ work₁) [] [] []))
      (affineExactlyOneMarkedRowFramesSteps (frame :: rest)) := by
  induction rest generalizing frame buffer₁ buffer₂ test work₁ with
  | nil =>
      simpa [encodeAffineExactlyOneReversedCompactFrameStream,
        affineExactlyOneMarkedRowFramesSteps,
        encodeAffineExactlyOneOutputSourceInvocationFamily] using
        affineExactlyOneMarkedRow_frameEOF_run frame buffer₁ buffer₂ test
          output work₁
  | cons next rest ih =>
      let nextInput := encodeAffineExactlyOneReversedCompactBody next ++
        encodeAffineExactlyOneReversedCompactFrameStream rest
      let afterFrame := affineExactlyOneMarkedRowInvocationCfg .loadCount
        (some .separator) buffer₂ false nextInput output
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ work₁)
        [] [] []
      have hfirst : EvalsToInTime
          (step affineExactlyOneMarkedRowInvocationProgram)
          (affineExactlyOneMarkedRowInvocationCfg .loadCount
            buffer₁ buffer₂ test
            (encodeAffineExactlyOneReversedCompactBody frame ++
              encodeAffineExactlyOneReversedCompactFrameStream (next :: rest))
            output work₁ [] [] [])
          (some afterFrame) (affineExactlyOneMarkedRowFrameSteps frame) := by
        simpa [afterFrame, nextInput,
          encodeAffineExactlyOneReversedCompactFrameStream,
          List.append_assoc] using
          affineExactlyOneMarkedRow_frameNext_run frame buffer₁ buffer₂
            test nextInput output work₁ []
      have hrest := ih next (some .separator) buffer₂ false
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ work₁)
      let full := EvalsToInTime.trans
        (step affineExactlyOneMarkedRowInvocationProgram)
        (affineExactlyOneMarkedRowFrameSteps frame)
        (affineExactlyOneMarkedRowFramesSteps (next :: rest))
        _ afterFrame _ hfirst (by simpa [afterFrame, nextInput] using hrest)
      convert full using 1
      · simp [encodeAffineExactlyOneOutputSourceInvocationFamily,
          List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneMarkedRowFramesSteps]
        omega

private theorem affineExactlyOneMarkedRow_flush_eval
    (work : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym) :
    (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
      2 * work.length + 1]
      (some (affineExactlyOneMarkedRowInvocationCfg .flushRow
        buffer₁ buffer₂ test input output work work₂ [] [])) =
      some (affineExactlyOneMarkedRowInvocationCfg .rowStart
        none buffer₂ test input (work.reverse ++ output) [] work₂ [] []) := by
  induction work generalizing buffer₁ output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneMarkedRowInvocationProgram))^[
          2 * rest.length + 1]
          (some (affineExactlyOneMarkedRowInvocationCfg .flushRow
            (some symbol) buffer₂ test input (symbol :: output) rest work₂
            [] [])) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: output)

/-- Uniform row bound; the final row uses two fewer steps because no following
input marker has to be restored. -/
def affineExactlyOneMarkedRowSteps
    (frames : List AffineExactlyOneFrame) : Nat :=
  affineExactlyOneMarkedRowFramesSteps frames +
    2 * (encodeAffineExactlyOneOutputSourceInvocationFamily frames).length + 8

private def affineExactlyOneMarkedRow_rowEnd_run
    (frame : AffineExactlyOneFrame) (rest : List AffineExactlyOneFrame)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .rowStart
        buffer₁ buffer₂ test
        (.frameEnd ::
          encodeAffineExactlyOneReversedCompactFrameStream (frame :: rest) ++
          .frameEnd :: tail)
        output [] [] [] [])
      (some (affineExactlyOneMarkedRowInvocationCfg .rowStart
        none (some .frameEnd) false (.frameEnd :: tail)
        (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest) ++
          [.frameEnd] ++ output) [] [] [] []))
      (affineExactlyOneMarkedRowSteps (frame :: rest)) := by
  let afterMarker := affineExactlyOneMarkedRowInvocationCfg .expectFrame
    (some .frameEnd) buffer₂ test
    (encodeAffineExactlyOneReversedCompactFrameStream (frame :: rest) ++
      .frameEnd :: tail)
    output [] [] [] []
  let frameStart := affineExactlyOneMarkedRowInvocationCfg .loadCount
    (some .separator) buffer₂ test
    (encodeAffineExactlyOneReversedCompactBody frame ++
      encodeAffineExactlyOneReversedCompactFrameStream rest ++
      .frameEnd :: tail)
    output [] [] [] []
  let beforeMark := affineExactlyOneMarkedRowInvocationCfg .markRow
    (some .frameEnd) (some .frameEnd) false (.frameEnd :: tail) output
    (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).reverse
    [] [] []
  let beforeFlush := affineExactlyOneMarkedRowInvocationCfg .flushRow
    (some .frameEnd) (some .frameEnd) false (.frameEnd :: tail) output
    (.frameEnd ::
      (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).reverse)
    [] [] []
  have hmarker : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .rowStart
        buffer₁ buffer₂ test
        (.frameEnd ::
          encodeAffineExactlyOneReversedCompactFrameStream (frame :: rest) ++
          .frameEnd :: tail)
        output [] [] [] [])
      (some afterMarker) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hfirst : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterMarker (some frameStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hframes : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      frameStart (some beforeMark)
      (affineExactlyOneMarkedRowFramesSteps (frame :: rest) + 2) := by
    simpa [frameStart, beforeMark] using
      affineExactlyOneMarkedRow_framesEnd_run frame rest
        (some .separator) buffer₂ test tail output []
  have hmark : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      beforeMark (some beforeFlush) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hflush : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      beforeFlush
      (some (affineExactlyOneMarkedRowInvocationCfg .rowStart
        none (some .frameEnd) false (.frameEnd :: tail)
        (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest) ++
          [.frameEnd] ++ output) [] [] [] []))
      (2 * (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).length +
        3) := by
    let work := .frameEnd ::
      (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).reverse
    have source := affineExactlyOneMarkedRow_flush_eval work
      (some .frameEnd) (some .frameEnd) false (.frameEnd :: tail) output []
    refine ⟨⟨2 *
      (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).length +
      3, ?_⟩, le_rfl⟩
    have hsteps : 2 *
        ((encodeAffineExactlyOneOutputSourceInvocationFamily
          (frame :: rest)).length + 1) + 1 =
        2 * (encodeAffineExactlyOneOutputSourceInvocationFamily
          (frame :: rest)).length + 3 := by omega
    rw [← hsteps]
    simpa [beforeFlush, work, List.reverse_cons, List.append_assoc] using source
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram) 1 1 _ afterMarker _
    hmarker hfirst
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram) _
    (affineExactlyOneMarkedRowFramesSteps (frame :: rest) + 2)
    _ frameStart _ h₁ hframes
  let h₃ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram) _ 1 _ beforeMark _
    h₂ hmark
  let full := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram) _
    (2 * (encodeAffineExactlyOneOutputSourceInvocationFamily
      (frame :: rest)).length + 3) _ beforeFlush _ h₃ hflush
  convert full using 1
  all_goals simp [affineExactlyOneMarkedRowSteps]
  all_goals omega

private def affineExactlyOneMarkedRow_rowEOF_run
    (frame : AffineExactlyOneFrame) (rest : List AffineExactlyOneFrame)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .rowStart
        buffer₁ buffer₂ test
        (.frameEnd ::
          encodeAffineExactlyOneReversedCompactFrameStream (frame :: rest))
        output [] [] [] [])
      (some (affineExactlyOneMarkedRowInvocationCfg .rowStart
        none buffer₂ false []
        (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest) ++
          [.frameEnd] ++ output) [] [] [] []))
      (affineExactlyOneMarkedRowSteps (frame :: rest)) := by
  let afterMarker := affineExactlyOneMarkedRowInvocationCfg .expectFrame
    (some .frameEnd) buffer₂ test
    (encodeAffineExactlyOneReversedCompactFrameStream (frame :: rest))
    output [] [] [] []
  let frameStart := affineExactlyOneMarkedRowInvocationCfg .loadCount
    (some .separator) buffer₂ test
    (encodeAffineExactlyOneReversedCompactBody frame ++
      encodeAffineExactlyOneReversedCompactFrameStream rest)
    output [] [] [] []
  let beforeMark := affineExactlyOneMarkedRowInvocationCfg .markRow
    none buffer₂ false [] output
    (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).reverse
    [] [] []
  let beforeFlush := affineExactlyOneMarkedRowInvocationCfg .flushRow
    none buffer₂ false [] output
    (.frameEnd ::
      (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).reverse)
    [] [] []
  have hmarker : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      (affineExactlyOneMarkedRowInvocationCfg .rowStart
        buffer₁ buffer₂ test
        (.frameEnd ::
          encodeAffineExactlyOneReversedCompactFrameStream (frame :: rest))
        output [] [] [] [])
      (some afterMarker) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hfirst : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      afterMarker (some frameStart) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hframes : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      frameStart (some beforeMark)
      (affineExactlyOneMarkedRowFramesSteps (frame :: rest)) := by
    simpa [frameStart, beforeMark] using
      affineExactlyOneMarkedRow_framesEOF_run frame rest
        (some .separator) buffer₂ test output []
  have hmark : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      beforeMark (some beforeFlush) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  have hflush : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      beforeFlush
      (some (affineExactlyOneMarkedRowInvocationCfg .rowStart
        none buffer₂ false []
        (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest) ++
          [.frameEnd] ++ output) [] [] [] []))
      (2 * (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).length +
        3) := by
    let work := .frameEnd ::
      (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).reverse
    have source := affineExactlyOneMarkedRow_flush_eval work
      none buffer₂ false [] output []
    refine ⟨⟨2 *
      (encodeAffineExactlyOneOutputSourceInvocationFamily (frame :: rest)).length +
      3, ?_⟩, le_rfl⟩
    have hsteps : 2 *
        ((encodeAffineExactlyOneOutputSourceInvocationFamily
          (frame :: rest)).length + 1) + 1 =
        2 * (encodeAffineExactlyOneOutputSourceInvocationFamily
          (frame :: rest)).length + 3 := by omega
    rw [← hsteps]
    simpa [beforeFlush, work, List.reverse_cons, List.append_assoc] using source
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram) 1 1 _ afterMarker _
    hmarker hfirst
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram) _
    (affineExactlyOneMarkedRowFramesSteps (frame :: rest))
    _ frameStart _ h₁ hframes
  let h₃ := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram) _ 1 _ beforeMark _
    h₂ hmark
  let exactRun := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram) _
    (2 * (encodeAffineExactlyOneOutputSourceInvocationFamily
      (frame :: rest)).length + 3) _ beforeFlush _ h₃ hflush
  have hbound :
      2 * (encodeAffineExactlyOneOutputSourceInvocationFamily
          (frame :: rest)).length + 3 +
        (1 + (affineExactlyOneMarkedRowFramesSteps (frame :: rest) +
          (1 + 1))) ≤
      affineExactlyOneMarkedRowSteps (frame :: rest) := by
    simp [affineExactlyOneMarkedRowSteps]
    omega
  exact ⟨exactRun.toEvalsTo, exactRun.steps_le_m.trans hbound⟩

private theorem encodeAffineExactlyOneStructuredRowOutputInvocationFamily_append
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (left right : List AffineExactlyOneStructuredRowSeed) :
    encodeAffineExactlyOneStructuredRowOutputInvocationFamily
        labelWidth stateWidth cellCounts (left ++ right) =
      encodeAffineExactlyOneStructuredRowOutputInvocationFamily
          labelWidth stateWidth cellCounts left ++
        encodeAffineExactlyOneStructuredRowOutputInvocationFamily
          labelWidth stateWidth cellCounts right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineExactlyOneStructuredRowOutputInvocationFamily, ih,
        List.append_assoc]

private theorem affineExactlyOneStructuredRowFrames_ne_nil
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
      seed.height seed.start seed.rowBase ≠ [] := by
  simp [affineExactlyOneStructuredRowFrames, affineExactlyOnePrefixFrames]

/-- Per-seed cost of projecting its complete structured row. -/
def affineExactlyOneMarkedRowSeedSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : Nat :=
  affineExactlyOneMarkedRowSteps
    (affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
      seed.height seed.start seed.rowBase).reverse

/-- Total row-processing cost before the final empty-input halt. -/
def affineExactlyOneMarkedRowSeedFamilySteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) : Nat :=
  (seeds.map
    (affineExactlyOneMarkedRowSeedSteps
      labelWidth stateWidth cellCounts)).sum

private noncomputable def affineExactlyOneMarkedRow_rows_runFrom
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed)
    (buffer₂ : Option UnaryFrameSym) (output : List UnaryFrameSym) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
        (affineExactlyOneMarkedRowInvocationCfg .rowStart
          none buffer₂ false
          (encodeAffineExactlyOneReversedMarkedSeedStream
            labelWidth stateWidth cellCounts seeds)
          output [] [] [] [])
        (some (affineExactlyOneMarkedRowInvocationCfg .rowStart
          none finalBuffer₂ false []
          (encodeAffineExactlyOneStructuredRowOutputInvocationFamily
            labelWidth stateWidth cellCounts seeds.reverse ++ output)
          [] [] [] []))
        (affineExactlyOneMarkedRowSeedFamilySteps
          labelWidth stateWidth cellCounts seeds) := by
  induction seeds generalizing buffer₂ output with
  | nil =>
      refine ⟨buffer₂, ⟨⟨0, ?_⟩, le_rfl⟩⟩
      rfl
  | cons seed rest ih =>
      let rawFrames := affineExactlyOneStructuredRowFrames
        labelWidth stateWidth cellCounts seed.height seed.start seed.rowBase
      have hraw : rawFrames ≠ [] := by
        exact affineExactlyOneStructuredRowFrames_ne_nil
          labelWidth stateWidth cellCounts seed
      have hrev : rawFrames.reverse ≠ [] := by
        simpa using hraw
      cases hframes : rawFrames.reverse with
      | nil => contradiction
      | cons frame frames =>
          let rowOutput :=
            encodeAffineExactlyOneStructuredRowOutputInvocation
              labelWidth stateWidth cellCounts seed ++ output
          cases rest with
          | nil =>
              refine ⟨buffer₂, ?_⟩
              have hrow := affineExactlyOneMarkedRow_rowEOF_run
                frame frames none buffer₂ false output
              simpa [encodeAffineExactlyOneReversedMarkedSeedStream,
                encodeAffineExactlyOneStructuredRowOutputInvocationFamily,
                encodeAffineExactlyOneStructuredRowOutputInvocation,
                affineExactlyOneMarkedRowSeedFamilySteps,
                affineExactlyOneMarkedRowSeedSteps, rawFrames, hframes,
                List.append_assoc] using hrow
          | cons next rest =>
              let remainingSeeds := next :: rest
              let remainingInput :=
                encodeAffineExactlyOneReversedMarkedSeedStream
                  labelWidth stateWidth cellCounts remainingSeeds
              let remainingTail :=
                encodeAffineExactlyOneReversedCompactFrameStream
                    (affineExactlyOneStructuredRowFrames
                      labelWidth stateWidth cellCounts next.height next.start
                      next.rowBase).reverse ++
                  encodeAffineExactlyOneReversedMarkedSeedStream
                    labelWidth stateWidth cellCounts rest
              have hrow := affineExactlyOneMarkedRow_rowEnd_run
                frame frames none buffer₂ false remainingTail output
              rcases ih (some .frameEnd) rowOutput with
                ⟨finalBuffer₂, hrest⟩
              let full := EvalsToInTime.trans
                (step affineExactlyOneMarkedRowInvocationProgram)
                (affineExactlyOneMarkedRowSeedSteps
                  labelWidth stateWidth cellCounts seed)
                (affineExactlyOneMarkedRowSeedFamilySteps
                  labelWidth stateWidth cellCounts remainingSeeds)
                _ (affineExactlyOneMarkedRowInvocationCfg .rowStart
                  none (some .frameEnd) false remainingInput rowOutput
                  [] [] [] []) _
                (by
                  simpa [encodeAffineExactlyOneReversedMarkedSeedStream,
                    encodeAffineExactlyOneStructuredRowOutputInvocation,
                    affineExactlyOneMarkedRowSeedSteps, rawFrames, hframes,
                    remainingSeeds, remainingInput, remainingTail, rowOutput,
                    List.append_assoc] using hrow)
                (by simpa [remainingInput, rowOutput] using hrest)
              refine ⟨finalBuffer₂, ?_⟩
              convert full using 1
              · simp [encodeAffineExactlyOneReversedMarkedSeedStream,
                  rawFrames, hframes]
              · have hout :
                    encodeAffineExactlyOneStructuredRowOutputInvocationFamily
                        labelWidth stateWidth cellCounts
                        (rest.reverse ++ [next, seed]) ++ output =
                      encodeAffineExactlyOneStructuredRowOutputInvocationFamily
                          labelWidth stateWidth cellCounts
                          (rest.reverse ++ [next]) ++
                        (encodeAffineExactlyOneStructuredRowOutputInvocation
                          labelWidth stateWidth cellCounts seed ++ output) := by
                    rw [show rest.reverse ++ [next, seed] =
                        (rest.reverse ++ [next]) ++ [seed] by simp]
                    rw [
                      encodeAffineExactlyOneStructuredRowOutputInvocationFamily_append]
                    simp [
                      encodeAffineExactlyOneStructuredRowOutputInvocationFamily,
                      List.append_assoc]
                rw [show (seed :: next :: rest).reverse =
                  rest.reverse ++ [next, seed] by simp]
                simp only [hout]
              · change
                  affineExactlyOneMarkedRowSeedSteps
                      labelWidth stateWidth cellCounts seed +
                    affineExactlyOneMarkedRowSeedFamilySteps
                      labelWidth stateWidth cellCounts (next :: rest) =
                  affineExactlyOneMarkedRowSeedFamilySteps
                      labelWidth stateWidth cellCounts (next :: rest) +
                    affineExactlyOneMarkedRowSeedSteps
                      labelWidth stateWidth cellCounts seed
                omega

/-- Exact family runtime, including the final empty-input transition and
halt instruction. -/
def affineExactlyOneMarkedRowInvocationSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) : Nat :=
  2 + affineExactlyOneMarkedRowSeedFamilySteps
    labelWidth stateWidth cellCounts seeds.reverse

/-- The fixed projector consumes the reversed marked compact stream and emits
the row-major final-conjunction invocation family. -/
def affineExactlyOneMarkedRowInvocation_run
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (initialCfg affineExactlyOneMarkedRowInvocationProgram
        (encodeAffineExactlyOneStructuredRowMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse)
      (some (haltCfg affineExactlyOneMarkedRowInvocationProgram
        (encodeAffineExactlyOneStructuredRowOutputInvocationFamily
          labelWidth stateWidth cellCounts seeds)))
      (affineExactlyOneMarkedRowInvocationSteps
        labelWidth stateWidth cellCounts seeds) := by
  rcases affineExactlyOneMarkedRow_rows_runFrom
      labelWidth stateWidth cellCounts seeds.reverse none [] with
    ⟨finalBuffer₂, hrows⟩
  let output := encodeAffineExactlyOneStructuredRowOutputInvocationFamily
    labelWidth stateWidth cellCounts seeds
  let beforeHalt := affineExactlyOneMarkedRowInvocationCfg .rowStart
    none finalBuffer₂ false [] output [] [] [] []
  have hsource : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      (initialCfg affineExactlyOneMarkedRowInvocationProgram
        (encodeAffineExactlyOneStructuredRowMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse)
      (some beforeHalt)
      (affineExactlyOneMarkedRowSeedFamilySteps
        labelWidth stateWidth cellCounts seeds.reverse) := by
    simpa [initialCfg, affineExactlyOneMarkedRowInvocationProgram,
      affineExactlyOneMarkedRowInvocationCfg, beforeHalt, output,
      encodeAffineExactlyOneStructuredRowMarkedFamily_reverse] using
      hrows
  have hhalt : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      beforeHalt
      (some (haltCfg affineExactlyOneMarkedRowInvocationProgram output)) 2 := by
    refine ⟨⟨2, ?_⟩, le_rfl⟩
    rfl
  let full := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    (affineExactlyOneMarkedRowSeedFamilySteps
      labelWidth stateWidth cellCounts seeds.reverse) 2
    _ beforeHalt _ hsource hhalt
  simpa [affineExactlyOneMarkedRowInvocationSteps, output] using full

@[simp] theorem encodeAffineExactlyOneOutputSourceInvocation_length
    (frame : AffineExactlyOneFrame) :
    (encodeAffineExactlyOneOutputSourceInvocation frame).length =
      frame.start + frame.count + 3 := by
  simp [encodeAffineExactlyOneOutputSourceInvocation,
    encodeUnaryFrame_length]
  omega

/-- Reversing the field order changes neither the byte cost of an individual
compact frame nor the cost of a frame family. -/
theorem encodeAffineExactlyOneReversedCompactFrameStream_length
    (frames : List AffineExactlyOneFrame) :
    (encodeAffineExactlyOneReversedCompactFrameStream frames).length =
      (encodeAffineExactlyOneCompactFamily frames).length := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      have ih' :
          (List.flatMap (fun next => .separator ::
            encodeAffineExactlyOneReversedCompactBody next) rest).length =
            (encodeAffineExactlyOneCompactFamily rest).length := by
        simpa only [encodeAffineExactlyOneReversedCompactFrameStream] using ih
      rw [encodeAffineExactlyOneReversedCompactFrameStream,
        encodeAffineExactlyOneCompactFamily]
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [ih']
      simp [encodeAffineExactlyOneReversedCompactBody]
      omega

theorem affineExactlyOneMarkedRowFrameSteps_le
    (frame : AffineExactlyOneFrame) :
    affineExactlyOneMarkedRowFrameSteps frame ≤
      4 * (encodeAffineExactlyOneCompactFrame frame).length := by
  simp [affineExactlyOneMarkedRowFrameSteps]
  omega

theorem affineExactlyOneMarkedRowFramesSteps_le
    (frames : List AffineExactlyOneFrame) :
    affineExactlyOneMarkedRowFramesSteps frames ≤
      4 * (encodeAffineExactlyOneCompactFamily frames).length := by
  induction frames with
  | nil => simp [affineExactlyOneMarkedRowFramesSteps,
      encodeAffineExactlyOneCompactFamily]
  | cons frame rest ih =>
      have hframe := affineExactlyOneMarkedRowFrameSteps_le frame
      have ih' :
          (rest.map affineExactlyOneMarkedRowFrameSteps).sum ≤
            4 * (encodeAffineExactlyOneCompactFamily rest).length := by
        simpa only [affineExactlyOneMarkedRowFramesSteps] using ih
      rw [affineExactlyOneMarkedRowFramesSteps,
        encodeAffineExactlyOneCompactFamily]
      simp only [List.map_cons, List.sum_cons, List.length_append]
      omega

theorem encodeAffineExactlyOneOutputSourceInvocationFamily_length_le
    (frames : List AffineExactlyOneFrame) :
    (encodeAffineExactlyOneOutputSourceInvocationFamily frames).length ≤
      (encodeAffineExactlyOneCompactFamily frames).length := by
  induction frames with
  | nil => simp [encodeAffineExactlyOneOutputSourceInvocationFamily,
      encodeAffineExactlyOneCompactFamily]
  | cons frame rest ih =>
      have ih' :
          (rest.flatMap encodeAffineExactlyOneOutputSourceInvocation).length ≤
            (encodeAffineExactlyOneCompactFamily rest).length := by
        simpa only [encodeAffineExactlyOneOutputSourceInvocationFamily] using ih
      rw [encodeAffineExactlyOneOutputSourceInvocationFamily,
        encodeAffineExactlyOneCompactFamily]
      simp only [List.flatMap_cons, List.length_append]
      simp only [encodeAffineExactlyOneOutputSourceInvocation_length,
        encodeAffineExactlyOneCompactFrame_length]
      omega

theorem affineExactlyOneMarkedRowSteps_le
    (frames : List AffineExactlyOneFrame) :
    affineExactlyOneMarkedRowSteps frames ≤
      6 * (encodeAffineExactlyOneCompactFamily frames).length + 8 := by
  have hframes := affineExactlyOneMarkedRowFramesSteps_le frames
  have houtput :=
    encodeAffineExactlyOneOutputSourceInvocationFamily_length_le frames
  simp only [affineExactlyOneMarkedRowSteps]
  omega

theorem affineExactlyOneMarkedRowSeedSteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneMarkedRowSeedSteps labelWidth stateWidth cellCounts seed ≤
      14 * (1 +
        (encodeAffineExactlyOneReversedCompactFrameStream
          (affineExactlyOneStructuredRowFrames
            labelWidth stateWidth cellCounts seed.height seed.start
            seed.rowBase).reverse).length) := by
  have hrow := affineExactlyOneMarkedRowSteps_le
    (affineExactlyOneStructuredRowFrames
      labelWidth stateWidth cellCounts seed.height seed.start
      seed.rowBase).reverse
  rw [encodeAffineExactlyOneReversedCompactFrameStream_length]
  simp only [affineExactlyOneMarkedRowSeedSteps]
  omega

theorem affineExactlyOneMarkedRowSeedFamilySteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneMarkedRowSeedFamilySteps
        labelWidth stateWidth cellCounts seeds ≤
      14 * (encodeAffineExactlyOneReversedMarkedSeedStream
        labelWidth stateWidth cellCounts seeds).length := by
  induction seeds with
  | nil => simp [affineExactlyOneMarkedRowSeedFamilySteps,
      encodeAffineExactlyOneReversedMarkedSeedStream]
  | cons seed rest ih =>
      have hseed := affineExactlyOneMarkedRowSeedSteps_le
        labelWidth stateWidth cellCounts seed
      have ih' :
          (rest.map (affineExactlyOneMarkedRowSeedSteps
            labelWidth stateWidth cellCounts)).sum ≤
            14 * (encodeAffineExactlyOneReversedMarkedSeedStream
              labelWidth stateWidth cellCounts rest).length := by
        simpa only [affineExactlyOneMarkedRowSeedFamilySteps] using ih
      rw [affineExactlyOneMarkedRowSeedFamilySteps,
        encodeAffineExactlyOneReversedMarkedSeedStream]
      simp only [List.map_cons, List.sum_cons, List.length_append,
        List.length_cons]
      omega

/-- The complete projector is linear in its marked-stream input. -/
theorem affineExactlyOneMarkedRowInvocationSteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneMarkedRowInvocationSteps
        labelWidth stateWidth cellCounts seeds ≤
      14 * (encodeAffineExactlyOneStructuredRowMarkedFamily
        labelWidth stateWidth cellCounts seeds).reverse.length + 2 := by
  have hfamily := affineExactlyOneMarkedRowSeedFamilySteps_le
    labelWidth stateWidth cellCounts seeds.reverse
  have hencoding := congrArg List.length
    (encodeAffineExactlyOneStructuredRowMarkedFamily_reverse
      labelWidth stateWidth cellCounts seeds)
  simp only [affineExactlyOneMarkedRowInvocationSteps]
  rw [hencoding]
  omega

/-- The fixed controller is a concrete TM2 computing row-major output-source
invocations from the reverse marked compact-row representation. -/
noncomputable def
    affineExactlyOneMarkedRowInvocation_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      (fun seeds : List AffineExactlyOneStructuredRowSeed =>
        (encodeAffineExactlyOneStructuredRowMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse)
      id
      (encodeAffineExactlyOneStructuredRowOutputInvocationFamily
        labelWidth stateWidth cellCounts) where
  tm := compile affineExactlyOneMarkedRowInvocationProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 14 * Polynomial.X + 2
  outputsFun := fun seeds => by
    have builderRun := affineExactlyOneMarkedRowInvocation_run
      labelWidth stateWidth cellCounts seeds
    have compiledRun := compile_evalsToInTime
      affineExactlyOneMarkedRowInvocationProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneMarkedRowInvocationProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneMarkedRowInvocationProgram)
          (encodeAffineExactlyOneStructuredRowMarkedFamily
            labelWidth stateWidth cellCounts seeds).reverse)
        (some (_root_.Turing.haltList
          (compile affineExactlyOneMarkedRowInvocationProgram)
          (encodeAffineExactlyOneStructuredRowOutputInvocationFamily
            labelWidth stateWidth cellCounts seeds)))
        (affineExactlyOneMarkedRowInvocationSteps
          labelWidth stateWidth cellCounts seeds) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : affineExactlyOneMarkedRowInvocationSteps
        labelWidth stateWidth cellCounts seeds ≤
        (Polynomial.C 14 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneStructuredRowMarkedFamily
            labelWidth stateWidth cellCounts seeds).reverse.length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat] using
        affineExactlyOneMarkedRowInvocationSteps_le
          labelWidth stateWidth cellCounts seeds
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneMarkedRowInvocationProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneMarkedRowInvocationProgram)
          (encodeAffineExactlyOneStructuredRowMarkedFamily
            labelWidth stateWidth cellCounts seeds).reverse)
        (some (_root_.Turing.haltList
          (compile affineExactlyOneMarkedRowInvocationProgram)
          (encodeAffineExactlyOneStructuredRowOutputInvocationFamily
            labelWidth stateWidth cellCounts seeds)))
        ((Polynomial.C 14 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneStructuredRowMarkedFamily
            labelWidth stateWidth cellCounts seeds).reverse.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Repackage the established marked-row source so that its semantic output
remains the seed family while its byte representation changes to the marked
compact stream.  This is the typed interface used for honest TM2
composition. -/
noncomputable def
    affineExactlyOneStructuredRowMarkedSeeds_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneStructuredRowSeedFamily
      (fun seeds : List AffineExactlyOneStructuredRowSeed =>
        (encodeAffineExactlyOneStructuredRowMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse)
      id := by
  let source :=
    affineExactlyOneStructuredRowMarkedFamilyRev_computableInPolyTime
      labelWidth stateWidth cellCounts
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun seeds => by
        simpa only [id_eq] using source.outputsFun seeds }

/-- End-to-end polynomial-time compilation from structured row seeds to the
row-major invocation stream consumed by the final exactly-one conjunction
source. -/
noncomputable def
    affineExactlyOneStructuredRowOutputInvocationFamily_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneStructuredRowSeedFamily id
      (encodeAffineExactlyOneStructuredRowOutputInvocationFamily
        labelWidth stateWidth cellCounts) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineExactlyOneStructuredRowMarkedSeeds_computableInPolyTime
        labelWidth stateWidth cellCounts)
      (affineExactlyOneMarkedRowInvocation_computableInPolyTime
        labelWidth stateWidth cellCounts)
  simpa [Function.comp_def] using Classical.choice composed

/-! ## Seed-carrier rows -/

/-- The complete compact row seen by the projector: two synthetic frames
retaining the row seed, followed by the genuine structured one-hot frames. -/
def affineExactlyOneSeedCarrierRowFrames
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : List AffineExactlyOneFrame :=
  affineExactlyOneStructuredRowSeedCarrierFrames seed ++
    affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
      seed.height seed.start seed.rowBase

/-- Projected carrier row.  Its two synthetic invocations retain all three
seed values alongside the ordinary one-hot output-source invocation row. -/
def encodeAffineExactlyOneSeedCarrierOutputInvocation
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : List UnaryFrameSym :=
  encodeAffineExactlyOneOutputSourceInvocationFamily
      (affineExactlyOneSeedCarrierRowFrames
        labelWidth stateWidth cellCounts seed).reverse ++
    [.frameEnd]

/-- Projection follows reverse compact-frame order: the canonical one-hot
output invocations come first, followed by carrier two `(rowBase,0,0)`,
carrier one `(height,start,0)`, and the row terminator. -/
theorem encodeAffineExactlyOneSeedCarrierOutputInvocation_eq
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) :
    encodeAffineExactlyOneSeedCarrierOutputInvocation
        labelWidth stateWidth cellCounts seed =
      encodeAffineExactlyOneOutputSourceInvocationFamily
          (affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
            seed.height seed.start seed.rowBase).reverse ++
        encodeUnaryFrame [seed.rowBase, 0, 0] ++
        encodeUnaryFrame [seed.height, seed.start, 0] ++ [.frameEnd] := by
  simp [encodeAffineExactlyOneSeedCarrierOutputInvocation,
    affineExactlyOneSeedCarrierRowFrames,
    affineExactlyOneStructuredRowSeedCarrierFrames,
    encodeAffineExactlyOneOutputSourceInvocationFamily,
    encodeAffineExactlyOneOutputSourceInvocation,
    List.append_assoc]

/-- Row-major projected carrier family. -/
def encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    List AffineExactlyOneStructuredRowSeed → List UnaryFrameSym
  | [] => []
  | seed :: rest =>
      encodeAffineExactlyOneSeedCarrierOutputInvocation
          labelWidth stateWidth cellCounts seed ++
        encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
          labelWidth stateWidth cellCounts rest

private theorem encodeAffineExactlyOneSeedCarrierOutputInvocationFamily_append
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (left right : List AffineExactlyOneStructuredRowSeed) :
    encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
        labelWidth stateWidth cellCounts (left ++ right) =
      encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
          labelWidth stateWidth cellCounts left ++
        encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
          labelWidth stateWidth cellCounts right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineExactlyOneSeedCarrierOutputInvocationFamily, ih,
        List.append_assoc]

/-- Reversed marked carrier rows in projector processing order. -/
def encodeAffineExactlyOneReversedSeedCarrierStream
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    List AffineExactlyOneStructuredRowSeed → List UnaryFrameSym
  | [] => []
  | seed :: rest =>
      .frameEnd ::
        encodeAffineExactlyOneReversedCompactFrameStream
          (affineExactlyOneSeedCarrierRowFrames
            labelWidth stateWidth cellCounts seed).reverse ++
        encodeAffineExactlyOneReversedSeedCarrierStream
          labelWidth stateWidth cellCounts rest

private theorem encodeAffineExactlyOneReversedSeedCarrierStream_append
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (left right : List AffineExactlyOneStructuredRowSeed) :
    encodeAffineExactlyOneReversedSeedCarrierStream
        labelWidth stateWidth cellCounts (left ++ right) =
      encodeAffineExactlyOneReversedSeedCarrierStream
          labelWidth stateWidth cellCounts left ++
        encodeAffineExactlyOneReversedSeedCarrierStream
          labelWidth stateWidth cellCounts right := by
  induction left with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineExactlyOneReversedSeedCarrierStream, ih,
        List.append_assoc]

/-- The carrier source's prepend result exposes exactly the row projector's
reverse marked input stream. -/
theorem encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily_reverse
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
      labelWidth stateWidth cellCounts seeds).reverse =
      encodeAffineExactlyOneReversedSeedCarrierStream
        labelWidth stateWidth cellCounts seeds.reverse := by
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily,
        affineExactlyOneSeedCarrierRowFrames,
        encodeAffineExactlyOneCompactFamily_reverse,
        encodeAffineExactlyOneReversedSeedCarrierStream,
        encodeAffineExactlyOneReversedSeedCarrierStream_append,
        List.reverse_append, ih, List.append_assoc]

/-- Cost of projecting one carrier row. -/
def affineExactlyOneSeedCarrierProjectionSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : Nat :=
  affineExactlyOneMarkedRowSteps
    (affineExactlyOneSeedCarrierRowFrames
      labelWidth stateWidth cellCounts seed).reverse

/-- Total carrier-row projection cost before the final empty-input halt. -/
def affineExactlyOneSeedCarrierProjectionFamilySteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) : Nat :=
  (seeds.map (affineExactlyOneSeedCarrierProjectionSteps
    labelWidth stateWidth cellCounts)).sum

private noncomputable def affineExactlyOneSeedCarrierProjection_rows_runFrom
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed)
    (buffer₂ : Option UnaryFrameSym) (output : List UnaryFrameSym) :
    Σ finalBuffer₂ : Option UnaryFrameSym,
      EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
        (affineExactlyOneMarkedRowInvocationCfg .rowStart
          none buffer₂ false
          (encodeAffineExactlyOneReversedSeedCarrierStream
            labelWidth stateWidth cellCounts seeds)
          output [] [] [] [])
        (some (affineExactlyOneMarkedRowInvocationCfg .rowStart
          none finalBuffer₂ false []
          (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
            labelWidth stateWidth cellCounts seeds.reverse ++ output)
          [] [] [] []))
        (affineExactlyOneSeedCarrierProjectionFamilySteps
          labelWidth stateWidth cellCounts seeds) := by
  induction seeds generalizing buffer₂ output with
  | nil =>
      refine ⟨buffer₂, ⟨⟨0, ?_⟩, le_rfl⟩⟩
      rfl
  | cons seed rest ih =>
      let rawFrames := affineExactlyOneSeedCarrierRowFrames
        labelWidth stateWidth cellCounts seed
      have hraw : rawFrames ≠ [] := by
        simp [rawFrames, affineExactlyOneSeedCarrierRowFrames,
          affineExactlyOneStructuredRowSeedCarrierFrames]
      have hrev : rawFrames.reverse ≠ [] := by simpa using hraw
      cases hframes : rawFrames.reverse with
      | nil => contradiction
      | cons frame frames =>
          let rowOutput :=
            encodeAffineExactlyOneSeedCarrierOutputInvocation
              labelWidth stateWidth cellCounts seed ++ output
          cases rest with
          | nil =>
              refine ⟨buffer₂, ?_⟩
              have hrow := affineExactlyOneMarkedRow_rowEOF_run
                frame frames none buffer₂ false output
              simpa [encodeAffineExactlyOneReversedSeedCarrierStream,
                encodeAffineExactlyOneSeedCarrierOutputInvocationFamily,
                encodeAffineExactlyOneSeedCarrierOutputInvocation,
                affineExactlyOneSeedCarrierProjectionFamilySteps,
                affineExactlyOneSeedCarrierProjectionSteps,
                rawFrames, hframes, List.append_assoc] using hrow
          | cons next rest =>
              let remainingSeeds := next :: rest
              let remainingInput :=
                encodeAffineExactlyOneReversedSeedCarrierStream
                  labelWidth stateWidth cellCounts remainingSeeds
              let remainingTail :=
                encodeAffineExactlyOneReversedCompactFrameStream
                    (affineExactlyOneSeedCarrierRowFrames
                      labelWidth stateWidth cellCounts next).reverse ++
                  encodeAffineExactlyOneReversedSeedCarrierStream
                    labelWidth stateWidth cellCounts rest
              have hrow := affineExactlyOneMarkedRow_rowEnd_run
                frame frames none buffer₂ false remainingTail output
              rcases ih (some .frameEnd) rowOutput with
                ⟨finalBuffer₂, hrest⟩
              let full := EvalsToInTime.trans
                (step affineExactlyOneMarkedRowInvocationProgram)
                (affineExactlyOneSeedCarrierProjectionSteps
                  labelWidth stateWidth cellCounts seed)
                (affineExactlyOneSeedCarrierProjectionFamilySteps
                  labelWidth stateWidth cellCounts remainingSeeds)
                _ (affineExactlyOneMarkedRowInvocationCfg .rowStart
                  none (some .frameEnd) false remainingInput rowOutput
                  [] [] [] []) _
                (by
                  simpa [encodeAffineExactlyOneReversedSeedCarrierStream,
                    encodeAffineExactlyOneSeedCarrierOutputInvocation,
                    affineExactlyOneSeedCarrierProjectionSteps,
                    rawFrames, hframes, remainingSeeds, remainingInput,
                    remainingTail, rowOutput, List.append_assoc] using hrow)
                (by simpa [remainingInput, rowOutput] using hrest)
              refine ⟨finalBuffer₂, ?_⟩
              convert full using 1
              · simp [encodeAffineExactlyOneReversedSeedCarrierStream,
                  rawFrames, hframes]
              · have hout :
                    encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
                        labelWidth stateWidth cellCounts
                        (rest.reverse ++ [next, seed]) ++ output =
                      encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
                          labelWidth stateWidth cellCounts
                          (rest.reverse ++ [next]) ++
                        (encodeAffineExactlyOneSeedCarrierOutputInvocation
                          labelWidth stateWidth cellCounts seed ++ output) := by
                    rw [show rest.reverse ++ [next, seed] =
                        (rest.reverse ++ [next]) ++ [seed] by simp]
                    rw [
                      encodeAffineExactlyOneSeedCarrierOutputInvocationFamily_append]
                    simp [
                      encodeAffineExactlyOneSeedCarrierOutputInvocationFamily,
                      List.append_assoc]
                rw [show (seed :: next :: rest).reverse =
                  rest.reverse ++ [next, seed] by simp]
                simp only [hout]
              · change
                  affineExactlyOneSeedCarrierProjectionSteps
                      labelWidth stateWidth cellCounts seed +
                    affineExactlyOneSeedCarrierProjectionFamilySteps
                      labelWidth stateWidth cellCounts (next :: rest) =
                  affineExactlyOneSeedCarrierProjectionFamilySteps
                      labelWidth stateWidth cellCounts (next :: rest) +
                    affineExactlyOneSeedCarrierProjectionSteps
                      labelWidth stateWidth cellCounts seed
                omega

/-- Exact runtime, including final empty-input transition and halt. -/
def affineExactlyOneSeedCarrierProjectionRunSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) : Nat :=
  2 + affineExactlyOneSeedCarrierProjectionFamilySteps
    labelWidth stateWidth cellCounts seeds.reverse

/-- The existing marked-row projector consumes the carrier stream and emits
the seed carriers plus genuine one-hot output invocations in row-major order. -/
def affineExactlyOneSeedCarrierProjection_run
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    EvalsToInTime (step affineExactlyOneMarkedRowInvocationProgram)
      (initialCfg affineExactlyOneMarkedRowInvocationProgram
        (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse)
      (some (haltCfg affineExactlyOneMarkedRowInvocationProgram
        (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
          labelWidth stateWidth cellCounts seeds)))
      (affineExactlyOneSeedCarrierProjectionRunSteps
        labelWidth stateWidth cellCounts seeds) := by
  rcases affineExactlyOneSeedCarrierProjection_rows_runFrom
      labelWidth stateWidth cellCounts seeds.reverse none [] with
    ⟨finalBuffer₂, hrows⟩
  let output := encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
    labelWidth stateWidth cellCounts seeds
  let beforeHalt := affineExactlyOneMarkedRowInvocationCfg .rowStart
    none finalBuffer₂ false [] output [] [] [] []
  have hsource : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      (initialCfg affineExactlyOneMarkedRowInvocationProgram
        (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse)
      (some beforeHalt)
      (affineExactlyOneSeedCarrierProjectionFamilySteps
        labelWidth stateWidth cellCounts seeds.reverse) := by
    simpa [initialCfg, affineExactlyOneMarkedRowInvocationProgram,
      affineExactlyOneMarkedRowInvocationCfg, beforeHalt, output,
      encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily_reverse]
      using hrows
  have hhalt : EvalsToInTime
      (step affineExactlyOneMarkedRowInvocationProgram)
      beforeHalt
      (some (haltCfg affineExactlyOneMarkedRowInvocationProgram output)) 2 := by
    refine ⟨⟨2, ?_⟩, le_rfl⟩
    rfl
  let full := EvalsToInTime.trans
    (step affineExactlyOneMarkedRowInvocationProgram)
    (affineExactlyOneSeedCarrierProjectionFamilySteps
      labelWidth stateWidth cellCounts seeds.reverse) 2
    _ beforeHalt _ hsource hhalt
  simpa [affineExactlyOneSeedCarrierProjectionRunSteps, output] using full

theorem affineExactlyOneSeedCarrierProjectionSteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneSeedCarrierProjectionSteps
        labelWidth stateWidth cellCounts seed ≤
      14 * (1 +
        (encodeAffineExactlyOneReversedCompactFrameStream
          (affineExactlyOneSeedCarrierRowFrames
            labelWidth stateWidth cellCounts seed).reverse).length) := by
  have hrow := affineExactlyOneMarkedRowSteps_le
    (affineExactlyOneSeedCarrierRowFrames
      labelWidth stateWidth cellCounts seed).reverse
  rw [encodeAffineExactlyOneReversedCompactFrameStream_length]
  simp only [affineExactlyOneSeedCarrierProjectionSteps]
  omega

theorem affineExactlyOneSeedCarrierProjectionFamilySteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneSeedCarrierProjectionFamilySteps
        labelWidth stateWidth cellCounts seeds ≤
      14 * (encodeAffineExactlyOneReversedSeedCarrierStream
        labelWidth stateWidth cellCounts seeds).length := by
  induction seeds with
  | nil =>
      simp [affineExactlyOneSeedCarrierProjectionFamilySteps,
        encodeAffineExactlyOneReversedSeedCarrierStream]
  | cons seed rest ih =>
      have hseed := affineExactlyOneSeedCarrierProjectionSteps_le
        labelWidth stateWidth cellCounts seed
      have ih' :
          (rest.map (affineExactlyOneSeedCarrierProjectionSteps
            labelWidth stateWidth cellCounts)).sum ≤
            14 * (encodeAffineExactlyOneReversedSeedCarrierStream
              labelWidth stateWidth cellCounts rest).length := by
        simpa only [affineExactlyOneSeedCarrierProjectionFamilySteps] using ih
      rw [affineExactlyOneSeedCarrierProjectionFamilySteps,
        encodeAffineExactlyOneReversedSeedCarrierStream]
      simp only [List.map_cons, List.sum_cons, List.length_append,
        List.length_cons]
      omega

theorem affineExactlyOneSeedCarrierProjectionRunSteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneSeedCarrierProjectionRunSteps
        labelWidth stateWidth cellCounts seeds ≤
      14 * (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
        labelWidth stateWidth cellCounts seeds).reverse.length + 2 := by
  have hfamily := affineExactlyOneSeedCarrierProjectionFamilySteps_le
    labelWidth stateWidth cellCounts seeds.reverse
  have hencoding := congrArg List.length
    (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily_reverse
      labelWidth stateWidth cellCounts seeds)
  simp only [affineExactlyOneSeedCarrierProjectionRunSteps]
  rw [hencoding]
  omega

/-- Concrete linear-time projection of seed-carrier rows. -/
noncomputable def
    affineExactlyOneSeedCarrierProjection_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      (fun seeds : List AffineExactlyOneStructuredRowSeed =>
        (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse)
      id
      (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
        labelWidth stateWidth cellCounts) := by
  exact
    { tm := compile affineExactlyOneMarkedRowInvocationProgram
      inputAlphabet := Equiv.refl _
      outputAlphabet := Equiv.refl _
      time := Polynomial.C 14 * Polynomial.X + 2
      outputsFun := fun seeds => by
        have builderRun := affineExactlyOneSeedCarrierProjection_run
          labelWidth stateWidth cellCounts seeds
        have compiledRun := compile_evalsToInTime
          affineExactlyOneMarkedRowInvocationProgram builderRun
        have machineRun : _root_.StateTransition.EvalsToInTime
            (compile affineExactlyOneMarkedRowInvocationProgram).step
            (_root_.Turing.initList
              (compile affineExactlyOneMarkedRowInvocationProgram)
              (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
                labelWidth stateWidth cellCounts seeds).reverse)
            (some (_root_.Turing.haltList
              (compile affineExactlyOneMarkedRowInvocationProgram)
              (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
                labelWidth stateWidth cellCounts seeds)))
            (affineExactlyOneSeedCarrierProjectionRunSteps
              labelWidth stateWidth cellCounts seeds) := by
          simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
        have htime : affineExactlyOneSeedCarrierProjectionRunSteps
            labelWidth stateWidth cellCounts seeds ≤
            (Polynomial.C 14 * Polynomial.X + 2).eval
              (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
                labelWidth stateWidth cellCounts seeds).reverse.length := by
          simpa only [Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X, Polynomial.eval_C,
            Polynomial.eval_ofNat] using
            affineExactlyOneSeedCarrierProjectionRunSteps_le
              labelWidth stateWidth cellCounts seeds
        have boundedRun : _root_.StateTransition.EvalsToInTime
            (compile affineExactlyOneMarkedRowInvocationProgram).step
            (_root_.Turing.initList
              (compile affineExactlyOneMarkedRowInvocationProgram)
              (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
                labelWidth stateWidth cellCounts seeds).reverse)
            (some (_root_.Turing.haltList
              (compile affineExactlyOneMarkedRowInvocationProgram)
              (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
                labelWidth stateWidth cellCounts seeds)))
            ((Polynomial.C 14 * Polynomial.X + 2).eval
              (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
                labelWidth stateWidth cellCounts seeds).reverse.length) :=
          ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
        simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun }

/-- Typed view of the carrier re-encoder: the semantic seed family is kept
while its physical representation changes to the reversed carrier stream. -/
noncomputable def affineExactlyOneSeedCarrierRevSeeds_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
        labelWidth stateWidth cellCounts)
      (fun seeds : List AffineExactlyOneStructuredRowSeed =>
        (encodeAffineExactlyOneStructuredRowSeedCarrierMarkedFamily
          labelWidth stateWidth cellCounts seeds).reverse)
      id := by
  let source := affineExactlyOneSeedCarrierRev_computableInPolyTime
    labelWidth stateWidth cellCounts
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun seeds => by
        simpa only [id_eq] using source.outputsFun seeds }

/-- End-to-end from ordinary seed-preserving packets to the projected carrier
row stream. -/
noncomputable def
    affineExactlyOneSeedMarkedToCarrierOutput_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      (encodeAffineExactlyOneStructuredRowSeedMarkedFamily
        labelWidth stateWidth cellCounts)
      id
      (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
        labelWidth stateWidth cellCounts) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineExactlyOneSeedCarrierRevSeeds_computableInPolyTime
        labelWidth stateWidth cellCounts)
      (affineExactlyOneSeedCarrierProjection_computableInPolyTime
        labelWidth stateWidth cellCounts)
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
