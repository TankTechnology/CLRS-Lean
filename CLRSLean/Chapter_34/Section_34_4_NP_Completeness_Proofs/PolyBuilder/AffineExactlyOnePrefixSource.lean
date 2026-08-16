import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource
import Mathlib.Tactic

/-!
# Fixed prefix source for affine exactly-one rows

The Cook--Levin row source begins with two fixed-width groups: label and
state.  This module implements the concrete, embeddable controller for that
prefix.  It enters with `(H, start, rowBase)` already loaded in the three unary
counters, emits the two compact `(start, sourceBase, count)` frames, preserves
`H`, advances the other counters to the first stack group, and stops at a
public continuation label.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Width selected by the two finite prefix phases (`false` is label, `true`
is state). -/
def affineExactlyOnePrefixWidth
    (labelWidth stateWidth : Nat) (phase : Bool) : Nat :=
  if phase then stateWidth else labelWidth

/-- Finite control of the loaded-prefix component.  The bounded cursor counts
down a fixed width stored entirely in finite control. -/
inductive AffineExactlyOnePrefixLabel (labelWidth stateWidth : Nat)
  | initialBase
  | emitStart (phase : Bool)
  | saveStart (phase : Bool)
  | pushStartTick (phase : Bool)
  | pushStartSeparator (phase : Bool)
  | restoreStart (phase : Bool)
  | restoreStartInc (phase : Bool)
  | emitBase (phase : Bool)
  | saveBase (phase : Bool)
  | pushBaseTick (phase : Bool)
  | pushBaseSeparator (phase : Bool)
  | restoreBase (phase : Bool)
  | restoreBaseInc (phase : Bool)
  | count (phase : Bool) (remaining : Fin (max labelWidth stateWidth + 1))
  | countInc₁ (phase : Bool) (remaining : Fin (max labelWidth stateWidth + 1))
  | countInc₂ (phase : Bool) (remaining : Fin (max labelWidth stateWidth + 1))
  | countInc₃ (phase : Bool) (remaining : Fin (max labelWidth stateWidth + 1))
  | countIncBase (phase : Bool)
      (remaining : Fin (max labelWidth stateWidth + 1))
  | addOffset₁ (phase : Bool)
  | addOffset₂ (phase : Bool)
  | addOffset₃ (phase : Bool)
  | addOffset₄ (phase : Bool)
  | finishGroup (phase : Bool)
  | finish
deriving DecidableEq, Fintype

/-- Initial bounded cursor for either fixed prefix width. -/
def affineExactlyOnePrefixCursor
    (labelWidth stateWidth : Nat) (phase : Bool) :
  Fin (max labelWidth stateWidth + 1) :=
  ⟨affineExactlyOnePrefixWidth labelWidth stateWidth phase, by
    cases phase <;> simp [affineExactlyOnePrefixWidth]⟩

private def affineExactlyOnePrefixPred
    {labelWidth stateWidth : Nat}
    (remaining : Fin (max labelWidth stateWidth + 1))
    (_hpositive : remaining.val ≠ 0) :
    Fin (max labelWidth stateWidth + 1) :=
  ⟨remaining.val - 1, by omega⟩

/-- Concrete loaded-prefix controller.  The public `finish` halt is replaced
by the stack continuation when this component is embedded in the row source. -/
def affineExactlyOnePrefixRevProgram (labelWidth stateWidth : Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOnePrefixLabel labelWidth stateWidth
  main := .initialBase
  op
    | .initialBase => .inc₃ (.emitStart false)
    | .emitStart phase =>
        .dec₂ (.pushStartSeparator phase) (.saveStart phase)
    | .saveStart phase => .pushWork₁ .tick (.pushStartTick phase)
    | .pushStartTick phase => .pushOutput .tick (.emitStart phase)
    | .pushStartSeparator phase =>
        .pushOutput .separator (.restoreStart phase)
    | .restoreStart phase => .popWork₁ (.emitBase phase) fun
        | .tick => .restoreStartInc phase
        | _ => .emitBase phase
    | .restoreStartInc phase => .inc₂ (.restoreStart phase)
    | .emitBase phase =>
        .dec₃ (.pushBaseSeparator phase) (.saveBase phase)
    | .saveBase phase => .pushWork₁ .tick (.pushBaseTick phase)
    | .pushBaseTick phase => .pushOutput .tick (.emitBase phase)
    | .pushBaseSeparator phase =>
        .pushOutput .separator (.restoreBase phase)
    | .restoreBase phase => .popWork₁
        (.count phase (affineExactlyOnePrefixCursor
          labelWidth stateWidth phase)) fun
        | .tick => .restoreBaseInc phase
        | _ => .count phase (affineExactlyOnePrefixCursor
            labelWidth stateWidth phase)
    | .restoreBaseInc phase => .inc₃ (.restoreBase phase)
    | .count phase remaining =>
        if _h : remaining.val = 0 then
          .pushOutput .separator (.addOffset₁ phase)
        else .pushOutput .tick (.countInc₁ phase remaining)
    | .countInc₁ phase remaining => .inc₂ (.countInc₂ phase remaining)
    | .countInc₂ phase remaining => .inc₂ (.countInc₃ phase remaining)
    | .countInc₃ phase remaining => .inc₂ (.countIncBase phase remaining)
    | .countIncBase phase remaining =>
        if h : remaining.val = 0 then
          .jump (.addOffset₁ phase)
        else .inc₃ (.count phase
          (affineExactlyOnePrefixPred remaining h))
    | .addOffset₁ phase => .inc₂ (.addOffset₂ phase)
    | .addOffset₂ phase => .inc₂ (.addOffset₃ phase)
    | .addOffset₃ phase => .inc₂ (.addOffset₄ phase)
    | .addOffset₄ phase => .inc₂ (.finishGroup phase)
    | .finishGroup false => .jump (.emitStart true)
    | .finishGroup true => .jump .finish
    | .finish => .halt

private def affineExactlyOnePrefixCfg
    {labelWidth stateWidth : Nat}
    (label : AffineExactlyOnePrefixLabel labelWidth stateWidth)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg (affineExactlyOnePrefixRevProgram labelWidth stateWidth) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := []
  counter₁ := height
  counter₂ := start
  counter₃ := rowBase

/-- Public loaded entry.  The source-base counter is incremented once before
the label frame because the halted bit precedes the label interval. -/
def affineExactlyOnePrefixLoadedCfg
    (labelWidth stateWidth height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOnePrefixRevProgram labelWidth stateWidth) :=
  affineExactlyOnePrefixCfg .initialBase none false input output []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())

/-- Public continuation after both fixed groups. -/
def affineExactlyOnePrefixFinishCfg
    (labelWidth stateWidth height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOnePrefixRevProgram labelWidth stateWidth) :=
  affineExactlyOnePrefixCfg .finish none false input output []
    (List.replicate height ())
    (List.replicate
      (start + (3 * labelWidth + 4) + (3 * stateWidth + 4)) ())
    (List.replicate (rowBase + 1 + labelWidth + stateWidth) ())

/-- The two compact frames emitted by the loaded component. -/
def affineExactlyOnePrefixFrames
    (labelWidth stateWidth start rowBase : Nat) :
    List AffineExactlyOneFrame :=
  [ { start := start
      rowBase := rowBase + 1
      count := labelWidth }
  , { start := start + (3 * labelWidth + 4)
      rowBase := rowBase + 1 + labelWidth
      count := stateWidth } ]

private theorem prefix_replicate_append_cons {alpha : Type}
    (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem emitStart_eval
    {labelWidth stateWidth : Nat} (phase : Bool) (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (height rowBase : List Unit) :
    (flip Option.bind
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[3 * value + 1]
        (some (affineExactlyOnePrefixCfg (.emitStart phase) buffer₁ test
          input output work₁ height (List.replicate value ()) rowBase)) =
      some (affineExactlyOnePrefixCfg (.pushStartSeparator phase) buffer₁
        false input (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) height [] rowBase) := by
  induction value generalizing test output work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[3 * value + 1]
          (some (affineExactlyOnePrefixCfg (.emitStart phase) buffer₁ true
            input (.tick :: output) (.tick :: work₁) height
            (List.replicate value ()) rowBase)) = _
      simpa only [List.replicate_succ, prefix_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₁)

private theorem restoreStart_eval
    {labelWidth stateWidth : Nat} (phase : Bool) (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (height current rowBase : List Unit) :
    (flip Option.bind
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[2 * value + 1]
        (some (affineExactlyOnePrefixCfg (.restoreStart phase) buffer₁ test
          input output (List.replicate value .tick) height current rowBase)) =
      some (affineExactlyOnePrefixCfg (.emitBase phase) none test input output []
        height (List.replicate value () ++ current) rowBase) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[2 * value + 1]
          (some (affineExactlyOnePrefixCfg (.restoreStart phase) (some .tick)
            test input output (List.replicate value .tick) height (() :: current)
            rowBase)) = _
      simpa only [List.replicate_succ, prefix_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem emitBase_eval
    {labelWidth stateWidth : Nat} (phase : Bool) (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (height start : List Unit) :
    (flip Option.bind
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[3 * value + 1]
        (some (affineExactlyOnePrefixCfg (.emitBase phase) buffer₁ test
          input output work₁ height start (List.replicate value ()))) =
      some (affineExactlyOnePrefixCfg (.pushBaseSeparator phase) buffer₁
        false input (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) height start []) := by
  induction value generalizing test output work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[3 * value + 1]
          (some (affineExactlyOnePrefixCfg (.emitBase phase) buffer₁ true
            input (.tick :: output) (.tick :: work₁) height start
            (List.replicate value ()))) = _
      simpa only [List.replicate_succ, prefix_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₁)

private theorem restoreBase_eval
    {labelWidth stateWidth : Nat} (phase : Bool) (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (height start current : List Unit) :
    (flip Option.bind
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[2 * value + 1]
        (some (affineExactlyOnePrefixCfg (.restoreBase phase) buffer₁ test
          input output (List.replicate value .tick) height start current)) =
      some (affineExactlyOnePrefixCfg
          (.count phase (affineExactlyOnePrefixCursor
          labelWidth stateWidth phase)) none test input output [] height start
        (List.replicate value () ++ current)) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[2 * value + 1]
          (some (affineExactlyOnePrefixCfg (.restoreBase phase) (some .tick)
            test input output (List.replicate value .tick) height start
            (() :: current))) = _
      simpa only [List.replicate_succ, prefix_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem fixedCount_eval
    {labelWidth stateWidth : Nat} (phase : Bool) (value : Nat)
    (hvalue : value < max labelWidth stateWidth + 1)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    (flip Option.bind
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[5 * value + 1]
        (some (affineExactlyOnePrefixCfg (.count phase ⟨value, hvalue⟩)
          buffer₁ test input output [] height start rowBase)) =
      some (affineExactlyOnePrefixCfg (.addOffset₁ phase) buffer₁ test
        input (.separator :: (List.replicate value .tick ++ output)) [] height
        (List.replicate (3 * value) () ++ start)
        (List.replicate value () ++ rowBase)) := by
  induction value generalizing output start rowBase with
  | zero => rfl
  | succ value ih =>
      rw [show 5 * (value + 1) + 1 = (5 * value + 1) + 1 + 1 + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)))^[5 * value + 1]
          (some (affineExactlyOnePrefixCfg (.count phase ⟨value, by omega⟩)
            buffer₁ test input (.tick :: output) [] height
            (() :: () :: () :: start) (() :: rowBase))) = _
      simpa only [List.replicate_succ, prefix_replicate_append_cons,
        List.cons_append, show 3 * (value + 1) = 3 * value + 3 by omega,
        List.replicate_add] using
          ih (by omega) (.tick :: output)
            (() :: () :: () :: start) (() :: rowBase)

/-- Exact cost of one compact fixed-width group from loaded counters. -/
def affineExactlyOnePrefixGroupSteps (start rowBase count : Nat) : Nat :=
  5 * (start + rowBase + count) + 12

private def affineExactlyOnePrefix_runGroup
    (labelWidth stateWidth : Nat) (phase : Bool)
    (height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    EvalsToInTime (step (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth))
      (affineExactlyOnePrefixCfg (.emitStart phase) none false input output []
        (List.replicate height ()) (List.replicate start ())
        (List.replicate rowBase ()))
      (some (affineExactlyOnePrefixCfg
        (if phase then .finish else .emitStart true) none false input
        ((encodeAffineExactlyOneCompactFrame
          { start := start, rowBase := rowBase,
            count := affineExactlyOnePrefixWidth
              labelWidth stateWidth phase }).reverse ++ output) []
        (List.replicate height ())
        (List.replicate (start +
          (3 * affineExactlyOnePrefixWidth labelWidth stateWidth phase + 4)) ())
        (List.replicate (rowBase +
          affineExactlyOnePrefixWidth labelWidth stateWidth phase) ())))
      (affineExactlyOnePrefixGroupSteps start rowBase
        (affineExactlyOnePrefixWidth labelWidth stateWidth phase)) := by
  let count := affineExactlyOnePrefixWidth labelWidth stateWidth phase
  let afterStart : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.pushStartSeparator phase) none
    false input (List.replicate start .tick ++ output)
    (List.replicate start .tick) (List.replicate height ()) []
    (List.replicate rowBase ())
  let beforeRestoreStart : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.restoreStart phase) none
    false input (.separator :: (List.replicate start .tick ++ output))
    (List.replicate start .tick) (List.replicate height ()) []
    (List.replicate rowBase ())
  let beforeBase : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.emitBase phase) none false input
    (.separator :: (List.replicate start .tick ++ output)) []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())
  let afterBase : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.pushBaseSeparator phase) none
    false input
    (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output))
    (List.replicate rowBase .tick) (List.replicate height ())
    (List.replicate start ()) []
  let beforeRestoreBase : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.restoreBase phase) none
    false input
    (.separator :: (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output)))
    (List.replicate rowBase .tick) (List.replicate height ())
    (List.replicate start ()) []
  let beforeCount : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) := affineExactlyOnePrefixCfg
    (.count phase (affineExactlyOnePrefixCursor labelWidth stateWidth phase))
    none false input
    (.separator :: (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output))) []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())
  let beforeOffsets : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.addOffset₁ phase) none false
    input
    (.separator :: (List.replicate count .tick ++
      .separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output)))) []
    (List.replicate height ())
    (List.replicate (3 * count) () ++ List.replicate start ())
    (List.replicate count () ++ List.replicate rowBase ())
  let beforeFinish : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.finishGroup phase) none false
    input
    (.separator :: (List.replicate count .tick ++
      .separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output)))) []
    (List.replicate height ())
    (List.replicate 4 () ++
      (List.replicate (3 * count) () ++ List.replicate start ()))
    (List.replicate count () ++ List.replicate rowBase ())
  have hstart : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
      (affineExactlyOnePrefixCfg (.emitStart phase) none false input output []
        (List.replicate height ()) (List.replicate start ())
        (List.replicate rowBase ()))
      (some afterStart) (3 * start + 1) := by
    refine ⟨⟨3 * start + 1, ?_⟩, le_rfl⟩
    simpa [afterStart] using emitStart_eval (labelWidth := labelWidth)
      (stateWidth := stateWidth) phase start none false input output
      [] (List.replicate height ()) (List.replicate rowBase ())
  have hstartSep : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)) afterStart
      (some beforeRestoreStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestoreStart : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
      beforeRestoreStart
      (some beforeBase) (2 * start + 1) := by
    refine ⟨⟨2 * start + 1, ?_⟩, le_rfl⟩
    simpa [beforeRestoreStart, beforeBase] using restoreStart_eval
      (labelWidth := labelWidth) (stateWidth := stateWidth) phase start none
      false input (.separator :: (List.replicate start .tick ++ output))
      (List.replicate height ()) [] (List.replicate rowBase ())
  have hbase : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)) beforeBase
      (some afterBase) (3 * rowBase + 1) := by
    refine ⟨⟨3 * rowBase + 1, ?_⟩, le_rfl⟩
    simpa [beforeBase, afterBase] using emitBase_eval
      (labelWidth := labelWidth) (stateWidth := stateWidth) phase rowBase none
      false input (.separator :: (List.replicate start .tick ++ output))
      [] (List.replicate height ()) (List.replicate start ())
  have hbaseSep : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)) afterBase
      (some beforeRestoreBase) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestoreBase : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
      beforeRestoreBase
      (some beforeCount) (2 * rowBase + 1) := by
    refine ⟨⟨2 * rowBase + 1, ?_⟩, le_rfl⟩
    simpa [beforeRestoreBase, beforeCount] using restoreBase_eval
      (labelWidth := labelWidth) (stateWidth := stateWidth) phase rowBase none
      false input
      (.separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output)))
      (List.replicate height ()) (List.replicate start ()) []
  have hcount : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)) beforeCount
      (some beforeOffsets) (5 * count + 1) := by
    refine ⟨⟨5 * count + 1, ?_⟩, le_rfl⟩
    have hbound : count < max labelWidth stateWidth + 1 := by
      cases phase <;> simp [count, affineExactlyOnePrefixWidth]
    have hcursor : affineExactlyOnePrefixCursor labelWidth stateWidth phase =
        ⟨count, hbound⟩ := by
      apply Fin.ext
      rfl
    simpa [beforeCount, beforeOffsets, hcursor] using fixedCount_eval
      (labelWidth := labelWidth) (stateWidth := stateWidth) phase count hbound
      none false input
      (.separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output)))
      (List.replicate height ()) (List.replicate start ())
      (List.replicate rowBase ())
  have hoffsets : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
      beforeOffsets
      (some beforeFinish) 4 := ⟨⟨4, rfl⟩, le_rfl⟩
  have hfinish : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
      beforeFinish
      (some (affineExactlyOnePrefixCfg
        (if phase then .finish else .emitStart true) none false input
        (.separator :: (List.replicate count .tick ++
          .separator :: (List.replicate rowBase .tick ++
            .separator :: (List.replicate start .tick ++ output)))) []
        (List.replicate height ())
        (List.replicate (start + (3 * count + 4)) ())
      (List.replicate (rowBase + count) ()))) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    have hstartCounter :
        List.replicate 4 () ++
            (List.replicate (3 * count) () ++ List.replicate start ()) =
          List.replicate (start + (3 * count + 4)) () := by
      simpa only [List.replicate_append_replicate] using congrArg
        (fun n => List.replicate n ())
        (show 4 + (3 * count + start) = start + (3 * count + 4) by omega)
    have hbaseCounter :
        List.replicate count () ++ List.replicate rowBase () =
          List.replicate (rowBase + count) () := by
      simpa only [List.replicate_append_replicate] using congrArg
        (fun n => List.replicate n ())
        (show count + rowBase = rowBase + count by omega)
    change step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)
      beforeFinish = _
    unfold beforeFinish
    rw [hstartCounter, hbaseCounter]
    cases phase <;> rfl
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ afterStart _ hstart hstartSep
  let h₂ := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ beforeRestoreStart _ h₁
    hrestoreStart
  let h₃ := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ beforeBase _ h₂ hbase
  let h₄ := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ afterBase _ h₃ hbaseSep
  let h₅ := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ beforeRestoreBase _ h₄
    hrestoreBase
  let h₆ := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ beforeCount _ h₅ hcount
  let h₇ := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ beforeOffsets _ h₆ hoffsets
  let full := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ beforeFinish _ h₇ hfinish
  convert full using 1
  · simp [encodeAffineExactlyOneCompactFrame, encodeUnaryFrame,
      encodeUnaryFrameBlock, count, List.reverse_append, List.append_assoc]
  · simp [affineExactlyOnePrefixGroupSteps]
    omega

/-- Exact runtime of the loaded two-group prefix. -/
def affineExactlyOnePrefixSteps
    (labelWidth stateWidth start rowBase : Nat) : Nat :=
  1 +
    affineExactlyOnePrefixGroupSteps start (rowBase + 1) labelWidth +
    affineExactlyOnePrefixGroupSteps
      (start + (3 * labelWidth + 4))
      (rowBase + 1 + labelWidth) stateWidth

/-- The fixed label/state prefix is linear in its two runtime offsets. -/
theorem affineExactlyOnePrefixSteps_le
    (labelWidth stateWidth start rowBase : Nat) :
    affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase ≤
      30 * (labelWidth + stateWidth + 2) * (start + rowBase + 1) := by
  simp [affineExactlyOnePrefixSteps, affineExactlyOnePrefixGroupSteps]
  nlinarith

/-- The fixed loaded component emits the exact compact prefix continuously
and reaches its public continuation with the height counter intact. -/
def affineExactlyOnePrefix_runToFinish
    (labelWidth stateWidth height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    EvalsToInTime (step (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth))
      (affineExactlyOnePrefixLoadedCfg labelWidth stateWidth height start
        rowBase input output)
      (some (affineExactlyOnePrefixFinishCfg labelWidth stateWidth height
        start rowBase input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOnePrefixFrames labelWidth stateWidth start rowBase)
          ).reverse ++ output)))
      (affineExactlyOnePrefixSteps labelWidth stateWidth start rowBase) := by
  let afterInitial : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.emitStart false) none false
    input output [] (List.replicate height ()) (List.replicate start ())
    (List.replicate (rowBase + 1) ())
  let afterLabelOutput :=
    (encodeAffineExactlyOneCompactFrame
      { start := start, rowBase := rowBase + 1, count := labelWidth }).reverse ++
      output
  let afterLabel : BuilderCfg (affineExactlyOnePrefixRevProgram
      labelWidth stateWidth) :=
    affineExactlyOnePrefixCfg (.emitStart true) none false
    input afterLabelOutput [] (List.replicate height ())
    (List.replicate (start + (3 * labelWidth + 4)) ())
    (List.replicate (rowBase + 1 + labelWidth) ())
  have hinitial : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
      (affineExactlyOnePrefixLoadedCfg labelWidth stateWidth height start
        rowBase input output) (some afterInitial) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step (affineExactlyOnePrefixRevProgram labelWidth stateWidth)
      (affineExactlyOnePrefixLoadedCfg labelWidth stateWidth height start
        rowBase input output) = some afterInitial
    unfold affineExactlyOnePrefixLoadedCfg afterInitial
    rw [show rowBase + 1 = Nat.succ rowBase by omega,
      List.replicate_succ]
    rfl
  have hlabel := affineExactlyOnePrefix_runGroup labelWidth stateWidth false
    height start (rowBase + 1) input output
  have hstate := affineExactlyOnePrefix_runGroup labelWidth stateWidth true
    height (start + (3 * labelWidth + 4))
      (rowBase + 1 + labelWidth) input afterLabelOutput
  have hlabel' : EvalsToInTime
      (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
      afterInitial (some afterLabel)
      (affineExactlyOnePrefixGroupSteps start (rowBase + 1) labelWidth) := by
    simpa [afterInitial, afterLabel, afterLabelOutput,
      affineExactlyOnePrefixWidth] using hlabel
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    1 _ _ afterInitial _ hinitial hlabel'
  let full := EvalsToInTime.trans
    (step (affineExactlyOnePrefixRevProgram labelWidth stateWidth))
    _ _ _ afterLabel _ h₁ hstate
  convert full using 1
  · simp [affineExactlyOnePrefixFinishCfg, affineExactlyOnePrefixCfg,
      affineExactlyOnePrefixWidth, affineExactlyOnePrefixFrames,
      encodeAffineExactlyOneCompactFamily, afterLabelOutput,
      List.reverse_append, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm]
  · simp [affineExactlyOnePrefixSteps, affineExactlyOnePrefixWidth]
    omega

end CLRS.Chapter34.Turing.PolyBuilder
