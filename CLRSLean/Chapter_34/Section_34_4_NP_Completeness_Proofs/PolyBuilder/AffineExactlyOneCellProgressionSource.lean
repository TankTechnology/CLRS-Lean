import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource
import Mathlib.Tactic

/-!
# Runtime-height cell progression source

After a stack-height group, a Cook--Levin stack contributes `H` cell-symbol
groups of one fixed width.  This module implements their compact triple
source directly.  The fixed width is finite-control data; `H`, `start`, and
`rowBase` remain unary runtime counters.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The affine triple progression implemented by the cell source. -/
def affineExactlyOneCellProgression
    (cellCount height start rowBase : Nat) : AffineUnaryTripleProgression :=
  { base₁ := start
    base₂ := rowBase
    base₃ := cellCount
    step₁ := 3 * cellCount + 4
    step₂ := cellCount
    step₃ := 0
    count := height }

/-- Finite control of the loaded cell progression. -/
inductive AffineExactlyOneCellProgressionLabel (cellCount : Nat)
  | loop | saveHeight
  | emitStart | saveStart | pushStartTick | pushStartSeparator
  | restoreStart | restoreStartInc
  | emitBase | saveBase | pushBaseTick | pushBaseSeparator
  | restoreBase | restoreBaseInc
  | count (remaining : Fin (cellCount + 1))
  | countInc₁ (remaining : Fin (cellCount + 1))
  | countInc₂ (remaining : Fin (cellCount + 1))
  | countInc₃ (remaining : Fin (cellCount + 1))
  | countIncBase (remaining : Fin (cellCount + 1))
  | addOffset₁ | addOffset₂ | addOffset₃ | addOffset₄
  | finishGroup
  | restoreHeight | restoreHeightInc
  | finish
deriving DecidableEq, Fintype

private def affineExactlyOneCellProgressionPred {cellCount : Nat}
    (remaining : Fin (cellCount + 1)) (_hpositive : remaining.val ≠ 0) :
    Fin (cellCount + 1) :=
  ⟨remaining.val - 1, by omega⟩

/-- Fixed reverse-output controller for a runtime number of cell groups. -/
def affineExactlyOneCellProgressionRevProgram (cellCount : Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneCellProgressionLabel cellCount
  main := .loop
  op
    | .loop => .dec₁ .restoreHeight .saveHeight
    | .saveHeight => .pushWork₂ .tick .emitStart
    | .emitStart => .dec₂ .pushStartSeparator .saveStart
    | .saveStart => .pushWork₁ .tick .pushStartTick
    | .pushStartTick => .pushOutput .tick .emitStart
    | .pushStartSeparator => .pushOutput .separator .restoreStart
    | .restoreStart => .popWork₁ .emitBase fun
        | .tick => .restoreStartInc
        | _ => .emitBase
    | .restoreStartInc => .inc₂ .restoreStart
    | .emitBase => .dec₃ .pushBaseSeparator .saveBase
    | .saveBase => .pushWork₁ .tick .pushBaseTick
    | .pushBaseTick => .pushOutput .tick .emitBase
    | .pushBaseSeparator => .pushOutput .separator .restoreBase
    | .restoreBase => .popWork₁ (.count ⟨cellCount, by omega⟩) fun
        | .tick => .restoreBaseInc
        | _ => .count ⟨cellCount, by omega⟩
    | .restoreBaseInc => .inc₃ .restoreBase
    | .count remaining =>
        if _h : remaining.val = 0 then
          .pushOutput .separator .addOffset₁
        else .pushOutput .tick (.countInc₁ remaining)
    | .countInc₁ remaining => .inc₂ (.countInc₂ remaining)
    | .countInc₂ remaining => .inc₂ (.countInc₃ remaining)
    | .countInc₃ remaining => .inc₂ (.countIncBase remaining)
    | .countIncBase remaining =>
        if h : remaining.val = 0 then
          .jump .addOffset₁
        else .inc₃ (.count (affineExactlyOneCellProgressionPred remaining h))
    | .addOffset₁ => .inc₂ .addOffset₂
    | .addOffset₂ => .inc₂ .addOffset₃
    | .addOffset₃ => .inc₂ .addOffset₄
    | .addOffset₄ => .inc₂ .finishGroup
    | .finishGroup => .jump .loop
    | .restoreHeight => .popWork₂ .finish fun
        | .tick => .restoreHeightInc
        | _ => .finish
    | .restoreHeightInc => .inc₁ .restoreHeight
    | .finish => .halt

private def affineExactlyOneCellProgressionCfg {cellCount : Nat}
    (label : AffineExactlyOneCellProgressionLabel cellCount)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg (affineExactlyOneCellProgressionRevProgram cellCount) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := height
  counter₂ := start
  counter₃ := rowBase

/-- Restoration configurations expose buffer two, which is the buffer written
by `popWork₂`. -/
private def affineExactlyOneCellRestoreCfg {cellCount : Nat}
    (label : AffineExactlyOneCellProgressionLabel cellCount)
    (buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg (affineExactlyOneCellProgressionRevProgram cellCount) where
  label := some label
  buffer₁ := none
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := work₂
  counter₁ := height
  counter₂ := start
  counter₃ := rowBase

/-- Public loaded entry. -/
def affineExactlyOneCellProgressionLoadedCfg
    (cellCount height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOneCellProgressionRevProgram cellCount) :=
  affineExactlyOneCellProgressionCfg .loop none false input output [] []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())

/-- Public continuation after all `H` cell groups. -/
def affineExactlyOneCellProgressionFinishCfg
    (cellCount height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineExactlyOneCellProgressionRevProgram cellCount) :=
  affineExactlyOneCellProgressionCfg .finish none false input output [] []
    (List.replicate height ())
    (List.replicate (start + height * (3 * cellCount + 4)) ())
    (List.replicate (rowBase + height * cellCount) ())

private theorem cell_replicate_append_cons {alpha : Type}
    (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem cell_emitStart_eval {cellCount : Nat} (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height rowBase : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[3 * value + 1]
      (some (affineExactlyOneCellProgressionCfg .emitStart buffer₁ test
        input output work₁ work₂ height (List.replicate value ())
        rowBase)) =
      some (affineExactlyOneCellProgressionCfg .pushStartSeparator buffer₁
        false input (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) work₂ height [] rowBase) := by
  induction value generalizing test output work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[3 * value + 1]
          (some (affineExactlyOneCellProgressionCfg .emitStart buffer₁ true
            input (.tick :: output) (.tick :: work₁) work₂ height
            (List.replicate value ()) rowBase)) = _
      simpa only [List.replicate_succ, cell_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₁)

private theorem cell_restoreStart_eval {cellCount : Nat} (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (height current rowBase : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[2 * value + 1]
      (some (affineExactlyOneCellProgressionCfg .restoreStart buffer₁ test
        input output (List.replicate value .tick) work₂ height current
        rowBase)) =
      some (affineExactlyOneCellProgressionCfg .emitBase none test input output
        [] work₂ height (List.replicate value () ++ current) rowBase) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[2 * value + 1]
          (some (affineExactlyOneCellProgressionCfg .restoreStart (some .tick)
            test input output (List.replicate value .tick) work₂ height
            (() :: current) rowBase)) = _
      simpa only [List.replicate_succ, cell_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem cell_emitBase_eval {cellCount : Nat} (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[3 * value + 1]
      (some (affineExactlyOneCellProgressionCfg .emitBase buffer₁ test input
        output work₁ work₂ height start (List.replicate value ()))) =
      some (affineExactlyOneCellProgressionCfg .pushBaseSeparator buffer₁
        false input (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) work₂ height start []) := by
  induction value generalizing test output work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[3 * value + 1]
          (some (affineExactlyOneCellProgressionCfg .emitBase buffer₁ true
            input (.tick :: output) (.tick :: work₁) work₂ height start
            (List.replicate value ()))) = _
      simpa only [List.replicate_succ, cell_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₁)

private theorem cell_restoreBase_eval {cellCount : Nat} (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (height start current : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[2 * value + 1]
      (some (affineExactlyOneCellProgressionCfg .restoreBase buffer₁ test input
        output (List.replicate value .tick) work₂ height start current)) =
      some (affineExactlyOneCellProgressionCfg
        (.count ⟨cellCount, by omega⟩) none test input output [] work₂ height
        start (List.replicate value () ++ current)) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[2 * value + 1]
          (some (affineExactlyOneCellProgressionCfg .restoreBase (some .tick)
            test input output (List.replicate value .tick) work₂ height start
            (() :: current))) = _
      simpa only [List.replicate_succ, cell_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem cell_fixedCount_eval {cellCount : Nat} (value : Nat)
    (hvalue : value < cellCount + 1)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[5 * value + 1]
      (some (affineExactlyOneCellProgressionCfg
        (.count ⟨value, hvalue⟩) buffer₁ test input output [] work₂
        height start rowBase)) =
      some (affineExactlyOneCellProgressionCfg .addOffset₁ buffer₁ test
        input (.separator :: (List.replicate value .tick ++ output)) []
        work₂ height (List.replicate (3 * value) () ++ start)
        (List.replicate value () ++ rowBase)) := by
  induction value generalizing output start rowBase with
  | zero => rfl
  | succ value ih =>
      rw [show 5 * (value + 1) + 1 = (5 * value + 1) +
          1 + 1 + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[5 * value + 1]
          (some (affineExactlyOneCellProgressionCfg
            (.count ⟨value, by omega⟩) buffer₁ test input
            (.tick :: output) [] work₂ height (() :: () :: () :: start)
            (() :: rowBase))) = _
      simpa only [List.replicate_succ, cell_replicate_append_cons,
        List.cons_append, show 3 * (value + 1) = 3 * value + 3 by omega,
        List.replicate_add] using
          ih (by omega) (.tick :: output)
            (() :: () :: () :: start) (() :: rowBase)

/-- Exact cost of one fixed-width compact cell group. -/
def affineExactlyOneCellGroupSteps
    (cellCount start rowBase : Nat) : Nat :=
  5 * (start + rowBase + cellCount) + 12

private def affineExactlyOneCell_runGroup
    (cellCount remaining start rowBase : Nat) (test : Bool)
    (input output savedHeight : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      (affineExactlyOneCellProgressionCfg .emitStart none test input output []
        savedHeight (List.replicate remaining ()) (List.replicate start ())
        (List.replicate rowBase ()))
      (some (affineExactlyOneCellProgressionCfg .loop none false input
        ((encodeAffineExactlyOneCompactFrame
          { start := start, rowBase := rowBase, count := cellCount }).reverse ++
          output) [] savedHeight (List.replicate remaining ())
        (List.replicate (start + (3 * cellCount + 4)) ())
        (List.replicate (rowBase + cellCount) ())))
      (affineExactlyOneCellGroupSteps cellCount start rowBase) := by
  let afterStart : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg .pushStartSeparator
    none false input (List.replicate start .tick ++ output)
    (List.replicate start .tick) savedHeight (List.replicate remaining ()) []
    (List.replicate rowBase ())
  let beforeRestoreStart : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg .restoreStart
    none false input (.separator :: (List.replicate start .tick ++ output))
    (List.replicate start .tick) savedHeight (List.replicate remaining ()) []
    (List.replicate rowBase ())
  let beforeBase : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg .emitBase none false
    input (.separator :: (List.replicate start .tick ++ output)) []
    savedHeight (List.replicate remaining ()) (List.replicate start ())
    (List.replicate rowBase ())
  let afterBase : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg .pushBaseSeparator
    none false input
    (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output))
    (List.replicate rowBase .tick) savedHeight
    (List.replicate remaining ()) (List.replicate start ()) []
  let beforeRestoreBase : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg .restoreBase
    none false input
    (.separator :: (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output)))
    (List.replicate rowBase .tick) savedHeight
    (List.replicate remaining ()) (List.replicate start ()) []
  let beforeCount : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg
    (.count ⟨cellCount, by omega⟩) none false input
    (.separator :: (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output))) []
    savedHeight (List.replicate remaining ()) (List.replicate start ())
    (List.replicate rowBase ())
  let beforeOffsets : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg .addOffset₁ none
    false input
    (.separator :: (List.replicate cellCount .tick ++
      .separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output)))) []
    savedHeight (List.replicate remaining ())
    (List.replicate (3 * cellCount) () ++ List.replicate start ())
    (List.replicate cellCount () ++ List.replicate rowBase ())
  let beforeFinish : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg .finishGroup none
    false input
    (.separator :: (List.replicate cellCount .tick ++
      .separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output)))) []
    savedHeight (List.replicate remaining ())
    (List.replicate 4 () ++
      (List.replicate (3 * cellCount) () ++ List.replicate start ()))
    (List.replicate cellCount () ++ List.replicate rowBase ())
  have hstart : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      (affineExactlyOneCellProgressionCfg .emitStart none test input output []
        savedHeight (List.replicate remaining ()) (List.replicate start ())
        (List.replicate rowBase ()))
      (some afterStart) (3 * start + 1) := by
    refine ⟨⟨3 * start + 1, ?_⟩, le_rfl⟩
    simpa [afterStart] using cell_emitStart_eval
      (cellCount := cellCount) start none test input output [] savedHeight
      (List.replicate remaining ()) (List.replicate rowBase ())
  have hstartSep : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount)) afterStart
      (some beforeRestoreStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestoreStart : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      beforeRestoreStart (some beforeBase) (2 * start + 1) := by
    refine ⟨⟨2 * start + 1, ?_⟩, le_rfl⟩
    simpa [beforeRestoreStart, beforeBase] using cell_restoreStart_eval
      (cellCount := cellCount) start none false input
      (.separator :: (List.replicate start .tick ++ output)) savedHeight
      (List.replicate remaining ()) [] (List.replicate rowBase ())
  have hbase : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount)) beforeBase
      (some afterBase) (3 * rowBase + 1) := by
    refine ⟨⟨3 * rowBase + 1, ?_⟩, le_rfl⟩
    simpa [beforeBase, afterBase] using cell_emitBase_eval
      (cellCount := cellCount) rowBase none false input
      (.separator :: (List.replicate start .tick ++ output)) [] savedHeight
      (List.replicate remaining ()) (List.replicate start ())
  have hbaseSep : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount)) afterBase
      (some beforeRestoreBase) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestoreBase : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      beforeRestoreBase (some beforeCount) (2 * rowBase + 1) := by
    refine ⟨⟨2 * rowBase + 1, ?_⟩, le_rfl⟩
    simpa [beforeRestoreBase, beforeCount] using cell_restoreBase_eval
      (cellCount := cellCount) rowBase none false input
      (.separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output))) savedHeight
      (List.replicate remaining ()) (List.replicate start ()) []
  have hcount : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount)) beforeCount
      (some beforeOffsets) (5 * cellCount + 1) := by
    refine ⟨⟨5 * cellCount + 1, ?_⟩, le_rfl⟩
    simpa [beforeCount, beforeOffsets] using cell_fixedCount_eval
      (cellCount := cellCount) cellCount (by omega) none false input
      (.separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output))) savedHeight
      (List.replicate remaining ()) (List.replicate start ())
      (List.replicate rowBase ())
  have hoffsets : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      beforeOffsets (some beforeFinish) 4 := ⟨⟨4, rfl⟩, le_rfl⟩
  have hfinish : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      beforeFinish
      (some (affineExactlyOneCellProgressionCfg .loop none false input
        (.separator :: (List.replicate cellCount .tick ++
          .separator :: (List.replicate rowBase .tick ++
            .separator :: (List.replicate start .tick ++ output)))) []
        savedHeight (List.replicate remaining ())
        (List.replicate (start + (3 * cellCount + 4)) ())
        (List.replicate (rowBase + cellCount) ()))) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    have hstartCounter :
        List.replicate 4 () ++
            (List.replicate (3 * cellCount) () ++ List.replicate start ()) =
          List.replicate (start + (3 * cellCount + 4)) () := by
      simpa only [List.replicate_append_replicate] using congrArg
        (fun n => List.replicate n ())
        (show 4 + (3 * cellCount + start) =
            start + (3 * cellCount + 4) by omega)
    have hbaseCounter :
        List.replicate cellCount () ++ List.replicate rowBase () =
          List.replicate (rowBase + cellCount) () := by
      simpa only [List.replicate_append_replicate] using congrArg
        (fun n => List.replicate n ())
        (show cellCount + rowBase = rowBase + cellCount by omega)
    change step (affineExactlyOneCellProgressionRevProgram cellCount)
      beforeFinish = _
    unfold beforeFinish
    rw [hstartCounter, hbaseCounter]
    rfl
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ 1 _ afterStart _ hstart hstartSep
  let h₂ := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ _ _ beforeRestoreStart _ h₁ hrestoreStart
  let h₃ := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ _ _ beforeBase _ h₂ hbase
  let h₄ := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ 1 _ afterBase _ h₃ hbaseSep
  let h₅ := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ _ _ beforeRestoreBase _ h₄ hrestoreBase
  let h₆ := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ _ _ beforeCount _ h₅ hcount
  let h₇ := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ _ _ beforeOffsets _ h₆ hoffsets
  let full := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ 1 _ beforeFinish _ h₇ hfinish
  convert full using 1
  · simp [encodeAffineExactlyOneCompactFrame, encodeUnaryFrame,
      encodeUnaryFrameBlock, List.reverse_append, List.append_assoc]
  · simp [affineExactlyOneCellGroupSteps]
    omega

/-- Adding one runtime cell exposes the current frame and the same
progression at the advanced affine offsets. -/
theorem affineExactlyOneCellProgression_frames_succ
    (cellCount height start rowBase : Nat) :
    affineExactlyOneFramesOfTripleProgression
        (affineExactlyOneCellProgression cellCount (height + 1) start rowBase) =
      { start := start, rowBase := rowBase, count := cellCount } ::
        affineExactlyOneFramesOfTripleProgression
          (affineExactlyOneCellProgression cellCount height
            (start + (3 * cellCount + 4)) (rowBase + cellCount)) := by
  rfl

/-- Exact cost of all productive cell phases, before the final zero test and
height restoration. -/
def affineExactlyOneCellProgressionPhaseSteps :
    Nat → Nat → Nat → Nat → Nat
  | _, 0, _, _ => 0
  | cellCount, height + 1, start, rowBase =>
      2 + affineExactlyOneCellGroupSteps cellCount start rowBase +
        affineExactlyOneCellProgressionPhaseSteps cellCount height
          (start + (3 * cellCount + 4)) (rowBase + cellCount)

private theorem cell_restoreHeight_eval {cellCount : Nat} (value : Nat)
    (buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (current start rowBase : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[2 * value + 1]
      (some (affineExactlyOneCellRestoreCfg .restoreHeight buffer₂ test
        input output (List.replicate value .tick) current start rowBase)) =
      some (affineExactlyOneCellRestoreCfg .finish none test input output []
        (List.replicate value () ++ current) start rowBase) := by
  induction value generalizing buffer₂ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneCellProgressionRevProgram cellCount)))^[2 * value + 1]
          (some (affineExactlyOneCellRestoreCfg .restoreHeight (some .tick)
            test input output (List.replicate value .tick) (() :: current) start
            rowBase)) = _
      simpa only [List.replicate_succ, cell_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private def affineExactlyOneCellProgression_runPhases
    (cellCount height start rowBase : Nat)
    (input output savedHeight : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      (affineExactlyOneCellProgressionCfg .loop none false input output []
        savedHeight (List.replicate height ()) (List.replicate start ())
        (List.replicate rowBase ()))
      (some (affineExactlyOneCellProgressionCfg .loop none false input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneFramesOfTripleProgression
            (affineExactlyOneCellProgression cellCount height start rowBase))
          ).reverse ++ output) []
        (List.replicate height .tick ++ savedHeight) []
        (List.replicate (start + height * (3 * cellCount + 4)) ())
        (List.replicate (rowBase + height * cellCount) ())))
      (affineExactlyOneCellProgressionPhaseSteps cellCount height start
        rowBase) := by
  induction height generalizing start rowBase output savedHeight with
  | zero =>
      exact ⟨⟨0, by simp [affineExactlyOneCellProgression,
          affineExactlyOneFramesOfTripleProgression,
        affineUnaryTripleProgressionRows,
        affineUnaryTripleProgressionRowsFrom,
        encodeAffineExactlyOneCompactFamily]⟩, le_rfl⟩
  | succ height ih =>
      let afterDec : BuilderCfg
          (affineExactlyOneCellProgressionRevProgram cellCount) :=
        affineExactlyOneCellProgressionCfg .saveHeight none true input output
          [] savedHeight (List.replicate height ()) (List.replicate start ())
          (List.replicate rowBase ())
      let afterSave : BuilderCfg
          (affineExactlyOneCellProgressionRevProgram cellCount) :=
        affineExactlyOneCellProgressionCfg .emitStart none true input output []
          (.tick :: savedHeight) (List.replicate height ())
          (List.replicate start ()) (List.replicate rowBase ())
      let nextStart := start + (3 * cellCount + 4)
      let nextBase := rowBase + cellCount
      let frameOutput :=
        (encodeAffineExactlyOneCompactFrame
          { start := start, rowBase := rowBase, count := cellCount }).reverse ++
          output
      let afterGroup : BuilderCfg
          (affineExactlyOneCellProgressionRevProgram cellCount) :=
        affineExactlyOneCellProgressionCfg .loop none false input frameOutput []
          (.tick :: savedHeight) (List.replicate height ())
          (List.replicate nextStart ()) (List.replicate nextBase ())
      have hdec : EvalsToInTime
          (step (affineExactlyOneCellProgressionRevProgram cellCount))
          (affineExactlyOneCellProgressionCfg .loop none false input output []
            savedHeight (List.replicate (height + 1) ())
            (List.replicate start ()) (List.replicate rowBase ()))
          (some afterDec) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step (affineExactlyOneCellProgressionRevProgram cellCount)
          (affineExactlyOneCellProgressionCfg .loop none false input output []
            savedHeight (List.replicate (height + 1) ())
            (List.replicate start ()) (List.replicate rowBase ())) =
          some afterDec
        unfold afterDec
        rw [List.replicate_succ]
        rfl
      have hsave : EvalsToInTime
          (step (affineExactlyOneCellProgressionRevProgram cellCount))
          afterDec (some afterSave) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hgroup : EvalsToInTime
          (step (affineExactlyOneCellProgressionRevProgram cellCount))
          afterSave (some afterGroup)
          (affineExactlyOneCellGroupSteps cellCount start rowBase) := by
        simpa [afterSave, afterGroup, frameOutput, nextStart, nextBase] using
          affineExactlyOneCell_runGroup cellCount height start rowBase true
            input output (.tick :: savedHeight)
      have hremaining : EvalsToInTime
          (step (affineExactlyOneCellProgressionRevProgram cellCount))
          afterGroup
          (some (affineExactlyOneCellProgressionCfg .loop none false input
            ((encodeAffineExactlyOneCompactFamily
              (affineExactlyOneFramesOfTripleProgression
                (affineExactlyOneCellProgression cellCount height nextStart
                  nextBase))).reverse ++ frameOutput) []
            (List.replicate height .tick ++ (.tick :: savedHeight)) []
            (List.replicate
              (nextStart + height * (3 * cellCount + 4)) ())
            (List.replicate (nextBase + height * cellCount) ())))
          (affineExactlyOneCellProgressionPhaseSteps cellCount height nextStart
            nextBase) := by
        simpa [afterGroup, nextStart, nextBase, frameOutput] using
          ih nextStart nextBase frameOutput (.tick :: savedHeight)
      let h₁ := EvalsToInTime.trans
        (step (affineExactlyOneCellProgressionRevProgram cellCount))
        1 1 _ afterDec _ hdec hsave
      let h₂ := EvalsToInTime.trans
        (step (affineExactlyOneCellProgressionRevProgram cellCount))
        _ (affineExactlyOneCellGroupSteps cellCount start rowBase) _
        afterSave _ h₁ hgroup
      let full := EvalsToInTime.trans
        (step (affineExactlyOneCellProgressionRevProgram cellCount))
        _ _ _ afterGroup _ h₂ hremaining
      convert full using 1
      · simp [affineExactlyOneCellProgression_frames_succ,
          encodeAffineExactlyOneCompactFamily, frameOutput, nextStart,
          nextBase, List.reverse_append, List.append_assoc,
          List.replicate_succ, cell_replicate_append_cons, Nat.add_mul,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [affineExactlyOneCellProgressionPhaseSteps, nextStart, nextBase]
        omega

/-- Exact total runtime, including the final zero test and restoration of the
height counter. -/
def affineExactlyOneCellProgressionSteps
    (cellCount height start rowBase : Nat) : Nat :=
  affineExactlyOneCellProgressionPhaseSteps cellCount height start rowBase +
    2 * height + 2

/-- The fixed cell source emits the exact compact affine progression,
preserves `H`, and reaches its public continuation. -/
def affineExactlyOneCellProgression_runToFinish
    (cellCount height start rowBase : Nat)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      (affineExactlyOneCellProgressionLoadedCfg cellCount height start rowBase
        input output)
      (some (affineExactlyOneCellProgressionFinishCfg cellCount height start
        rowBase input
        ((encodeAffineExactlyOneCompactFamily
          (affineExactlyOneFramesOfTripleProgression
            (affineExactlyOneCellProgression cellCount height start rowBase))
          ).reverse ++ output)))
      (affineExactlyOneCellProgressionSteps cellCount height start rowBase) := by
  let phaseOutput :=
    (encodeAffineExactlyOneCompactFamily
      (affineExactlyOneFramesOfTripleProgression
        (affineExactlyOneCellProgression cellCount height start rowBase))
      ).reverse ++ output
  let afterPhases : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellProgressionCfg .loop none false input phaseOutput []
      (List.replicate height .tick) []
      (List.replicate (start + height * (3 * cellCount + 4)) ())
      (List.replicate (rowBase + height * cellCount) ())
  let beforeRestore : BuilderCfg
      (affineExactlyOneCellProgressionRevProgram cellCount) :=
    affineExactlyOneCellRestoreCfg .restoreHeight none false input
      phaseOutput (List.replicate height .tick) []
      (List.replicate (start + height * (3 * cellCount + 4)) ())
      (List.replicate (rowBase + height * cellCount) ())
  have hphases : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      (affineExactlyOneCellProgressionLoadedCfg cellCount height start rowBase
        input output) (some afterPhases)
      (affineExactlyOneCellProgressionPhaseSteps cellCount height start
        rowBase) := by
    simpa [affineExactlyOneCellProgressionLoadedCfg, afterPhases,
      phaseOutput] using affineExactlyOneCellProgression_runPhases
        cellCount height start rowBase input output []
  have hzero : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount)) afterPhases
      (some beforeRestore) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime
      (step (affineExactlyOneCellProgressionRevProgram cellCount))
      beforeRestore
      (some (affineExactlyOneCellProgressionFinishCfg cellCount height start
        rowBase input phaseOutput)) (2 * height + 1) := by
    refine ⟨⟨2 * height + 1, ?_⟩, le_rfl⟩
    simpa [beforeRestore, affineExactlyOneCellProgressionFinishCfg,
      affineExactlyOneCellRestoreCfg, affineExactlyOneCellProgressionCfg] using
      cell_restoreHeight_eval (cellCount := cellCount) height none false input
        phaseOutput []
        (List.replicate (start + height * (3 * cellCount + 4)) ())
        (List.replicate (rowBase + height * cellCount) ())
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ 1 _ afterPhases _ hphases hzero
  let full := EvalsToInTime.trans
    (step (affineExactlyOneCellProgressionRevProgram cellCount))
    _ _ _ beforeRestore _ h₁ hrestore
  convert full using 1
  · simp [affineExactlyOneCellProgressionSteps]
    omega

end CLRS.Chapter34.Turing.PolyBuilder
