import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource
import Mathlib.Tactic

/-!
# Runtime-height compact exactly-one source

One verifier stack begins with an exactly-one group of width `H + 1`.  This
module implements the fixed loaded controller for that dynamic group.  It
enters with `(H, start, rowBase)` in the three unary counters, emits the exact
compact triple, preserves `H`, advances both affine offsets, and halts at a
public continuation.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite control for one runtime-height compact frame. -/
inductive AffineExactlyOneHeightLabel
  | emitStart | saveStart | pushStartTick | pushStartSeparator
  | restoreStart | restoreStartInc
  | emitBase | saveBase | pushBaseTick | pushBaseSeparator
  | restoreBase | restoreBaseInc
  | count | saveHeight | pushCountTick
  | advanceStart₁ | advanceStart₂ | advanceStart₃ | advanceBase
  | pushExtraTick
  | advanceExtraStart₁ | advanceExtraStart₂ | advanceExtraStart₃
  | advanceExtraBase | pushCountSeparator
  | addOffset₁ | addOffset₂ | addOffset₃ | addOffset₄
  | restoreHeight | restoreHeightInc
  | finish
deriving DecidableEq, Fintype

/-- Fixed reverse-output controller for one dynamic stack-height frame. -/
def affineExactlyOneHeightRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneHeightLabel
  main := .emitStart
  op
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
    | .restoreBase => .popWork₁ .count fun
        | .tick => .restoreBaseInc
        | _ => .count
    | .restoreBaseInc => .inc₃ .restoreBase
    | .count => .dec₁ .pushExtraTick .saveHeight
    | .saveHeight => .pushWork₁ .tick .pushCountTick
    | .pushCountTick => .pushOutput .tick .advanceStart₁
    | .advanceStart₁ => .inc₂ .advanceStart₂
    | .advanceStart₂ => .inc₂ .advanceStart₃
    | .advanceStart₃ => .inc₂ .advanceBase
    | .advanceBase => .inc₃ .count
    | .pushExtraTick => .pushOutput .tick .advanceExtraStart₁
    | .advanceExtraStart₁ => .inc₂ .advanceExtraStart₂
    | .advanceExtraStart₂ => .inc₂ .advanceExtraStart₃
    | .advanceExtraStart₃ => .inc₂ .advanceExtraBase
    | .advanceExtraBase => .inc₃ .pushCountSeparator
    | .pushCountSeparator => .pushOutput .separator .addOffset₁
    | .addOffset₁ => .inc₂ .addOffset₂
    | .addOffset₂ => .inc₂ .addOffset₃
    | .addOffset₃ => .inc₂ .addOffset₄
    | .addOffset₄ => .inc₂ .restoreHeight
    | .restoreHeight => .popWork₁ .finish fun
        | .tick => .restoreHeightInc
        | _ => .finish
    | .restoreHeightInc => .inc₁ .restoreHeight
    | .finish => .halt

private def affineExactlyOneHeightCfg
    (label : AffineExactlyOneHeightLabel)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg affineExactlyOneHeightRevProgram where
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

/-- Public loaded entry. -/
def affineExactlyOneHeightLoadedCfg
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneHeightRevProgram :=
  affineExactlyOneHeightCfg .emitStart none false input output []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())

/-- Public continuation after the dynamic frame. -/
def affineExactlyOneHeightFinishCfg
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneHeightRevProgram :=
  affineExactlyOneHeightCfg .finish none false input output []
    (List.replicate height ())
    (List.replicate (start + (3 * (height + 1) + 4)) ())
    (List.replicate (rowBase + (height + 1)) ())

/-- The compact frame emitted by the loaded controller. -/
def affineExactlyOneHeightFrame
    (height start rowBase : Nat) : AffineExactlyOneFrame :=
  { start := start, rowBase := rowBase, count := height + 1 }

private theorem height_replicate_append_cons {alpha : Type}
    (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem height_emitStart_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (height rowBase : List Unit) :
    (flip Option.bind (step affineExactlyOneHeightRevProgram))^[3 * value + 1]
      (some (affineExactlyOneHeightCfg .emitStart buffer₁ test input output
        work₁ height (List.replicate value ()) rowBase)) =
      some (affineExactlyOneHeightCfg .pushStartSeparator buffer₁ false input
        (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) height [] rowBase) := by
  induction value generalizing test output work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneHeightRevProgram))^[3 * value + 1]
          (some (affineExactlyOneHeightCfg .emitStart buffer₁ true input
            (.tick :: output) (.tick :: work₁) height
            (List.replicate value ()) rowBase)) = _
      simpa only [List.replicate_succ, height_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₁)

private theorem height_restoreStart_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (height current rowBase : List Unit) :
    (flip Option.bind (step affineExactlyOneHeightRevProgram))^[2 * value + 1]
      (some (affineExactlyOneHeightCfg .restoreStart buffer₁ test input
        output (List.replicate value .tick) height current rowBase)) =
      some (affineExactlyOneHeightCfg .emitBase none test input output []
        height (List.replicate value () ++ current) rowBase) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneHeightRevProgram))^[2 * value + 1]
          (some (affineExactlyOneHeightCfg .restoreStart (some .tick) test
            input output (List.replicate value .tick) height (() :: current)
            rowBase)) = _
      simpa only [List.replicate_succ, height_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem height_emitBase_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (height start : List Unit) :
    (flip Option.bind (step affineExactlyOneHeightRevProgram))^[3 * value + 1]
      (some (affineExactlyOneHeightCfg .emitBase buffer₁ test input output
        work₁ height start (List.replicate value ()))) =
      some (affineExactlyOneHeightCfg .pushBaseSeparator buffer₁ false input
        (List.replicate value .tick ++ output)
        (List.replicate value .tick ++ work₁) height start []) := by
  induction value generalizing test output work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneHeightRevProgram))^[3 * value + 1]
          (some (affineExactlyOneHeightCfg .emitBase buffer₁ true input
            (.tick :: output) (.tick :: work₁) height start
            (List.replicate value ()))) = _
      simpa only [List.replicate_succ, height_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (.tick :: work₁)

private theorem height_restoreBase_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (height start current : List Unit) :
    (flip Option.bind (step affineExactlyOneHeightRevProgram))^[2 * value + 1]
      (some (affineExactlyOneHeightCfg .restoreBase buffer₁ test input output
        (List.replicate value .tick) height start current)) =
      some (affineExactlyOneHeightCfg .count none test input output [] height
        start (List.replicate value () ++ current)) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneHeightRevProgram))^[2 * value + 1]
          (some (affineExactlyOneHeightCfg .restoreBase (some .tick) test
            input output (List.replicate value .tick) height start
            (() :: current))) = _
      simpa only [List.replicate_succ, height_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

private theorem height_count_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym)
    (start rowBase : List Unit) :
    (flip Option.bind (step affineExactlyOneHeightRevProgram))^[7 * value + 11]
      (some (affineExactlyOneHeightCfg .count buffer₁ test input output
        work₁ (List.replicate value ()) start rowBase)) =
      some (affineExactlyOneHeightCfg .restoreHeight buffer₁ false input
        (.separator :: (List.replicate (value + 1) .tick ++ output))
        (List.replicate value .tick ++ work₁) []
        (List.replicate (3 * (value + 1) + 4) () ++ start)
        (List.replicate (value + 1) () ++ rowBase)) := by
  induction value generalizing test output work₁ start rowBase with
  | zero => rfl
  | succ value ih =>
      rw [show 7 * (value + 1) + 11 = (7 * value + 11) +
          1 + 1 + 1 + 1 + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneHeightRevProgram))^[7 * value + 11]
          (some (affineExactlyOneHeightCfg .count buffer₁ false input
            (.tick :: output) (.tick :: work₁)
            (List.replicate value ()) (() :: () :: () :: start)
            (() :: rowBase))) = _
      simpa only [List.replicate_succ, height_replicate_append_cons,
        List.cons_append,
        show 3 * (value + 1 + 1) + 4 = (3 * (value + 1) + 4) + 3 by
          omega,
        List.replicate_add, List.append_assoc] using
          ih false (.tick :: output) (.tick :: work₁)
            (() :: () :: () :: start) (() :: rowBase)

private theorem height_restoreHeight_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (current start rowBase : List Unit) :
    (flip Option.bind (step affineExactlyOneHeightRevProgram))^[2 * value + 1]
      (some (affineExactlyOneHeightCfg .restoreHeight buffer₁ test input
        output (List.replicate value .tick) current start rowBase)) =
      some (affineExactlyOneHeightCfg .finish none test input output []
        (List.replicate value () ++ current) start rowBase) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step affineExactlyOneHeightRevProgram))^[2 * value + 1]
          (some (affineExactlyOneHeightCfg .restoreHeight (some .tick) test
            input output (List.replicate value .tick) (() :: current) start
            rowBase)) = _
      simpa only [List.replicate_succ, height_replicate_append_cons,
        List.cons_append] using ih (some .tick) (() :: current)

/-- Exact runtime of the loaded dynamic-height component. -/
def affineExactlyOneHeightSteps (height start rowBase : Nat) : Nat :=
  5 * (start + rowBase) + 9 * height + 18

/-- The fixed component emits the exact compact height frame, preserves the
height counter, and reaches its public continuation in the stated time. -/
def affineExactlyOneHeight_runToFinish
    (height start rowBase : Nat) (input output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneHeightRevProgram)
      (affineExactlyOneHeightLoadedCfg height start rowBase input output)
      (some (affineExactlyOneHeightFinishCfg height start rowBase input
        ((encodeAffineExactlyOneCompactFrame
          (affineExactlyOneHeightFrame height start rowBase)).reverse ++
          output)))
      (affineExactlyOneHeightSteps height start rowBase) := by
  let afterStart := affineExactlyOneHeightCfg .pushStartSeparator none false
    input (List.replicate start .tick ++ output)
    (List.replicate start .tick) (List.replicate height ()) []
    (List.replicate rowBase ())
  let beforeRestoreStart := affineExactlyOneHeightCfg .restoreStart none false
    input (.separator :: (List.replicate start .tick ++ output))
    (List.replicate start .tick) (List.replicate height ()) []
    (List.replicate rowBase ())
  let beforeBase := affineExactlyOneHeightCfg .emitBase none false input
    (.separator :: (List.replicate start .tick ++ output)) []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())
  let afterBase := affineExactlyOneHeightCfg .pushBaseSeparator none false input
    (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output))
    (List.replicate rowBase .tick) (List.replicate height ())
    (List.replicate start ()) []
  let beforeRestoreBase := affineExactlyOneHeightCfg .restoreBase none false
    input
    (.separator :: (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output)))
    (List.replicate rowBase .tick) (List.replicate height ())
    (List.replicate start ()) []
  let beforeCount := affineExactlyOneHeightCfg .count none false input
    (.separator :: (List.replicate rowBase .tick ++
      .separator :: (List.replicate start .tick ++ output))) []
    (List.replicate height ()) (List.replicate start ())
    (List.replicate rowBase ())
  let beforeRestoreHeight := affineExactlyOneHeightCfg .restoreHeight none false
    input
    (.separator :: (List.replicate (height + 1) .tick ++
      .separator :: (List.replicate rowBase .tick ++
        .separator :: (List.replicate start .tick ++ output))))
    (List.replicate height .tick) []
    (List.replicate (start + (3 * (height + 1) + 4)) ())
    (List.replicate (rowBase + (height + 1)) ())
  have hstart : EvalsToInTime (step affineExactlyOneHeightRevProgram)
      (affineExactlyOneHeightLoadedCfg height start rowBase input output)
      (some afterStart) (3 * start + 1) := by
    refine ⟨⟨3 * start + 1, ?_⟩, le_rfl⟩
    simpa [affineExactlyOneHeightLoadedCfg, afterStart] using
      height_emitStart_eval start none false input output []
        (List.replicate height ()) (List.replicate rowBase ())
  have hstartSep : EvalsToInTime (step affineExactlyOneHeightRevProgram)
      afterStart (some beforeRestoreStart) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestoreStart : EvalsToInTime
      (step affineExactlyOneHeightRevProgram) beforeRestoreStart
      (some beforeBase) (2 * start + 1) := by
    refine ⟨⟨2 * start + 1, ?_⟩, le_rfl⟩
    simpa [beforeRestoreStart, beforeBase] using
      height_restoreStart_eval start none false input
        (.separator :: (List.replicate start .tick ++ output))
        (List.replicate height ()) [] (List.replicate rowBase ())
  have hbase : EvalsToInTime (step affineExactlyOneHeightRevProgram)
      beforeBase (some afterBase) (3 * rowBase + 1) := by
    refine ⟨⟨3 * rowBase + 1, ?_⟩, le_rfl⟩
    simpa [beforeBase, afterBase] using
      height_emitBase_eval rowBase none false input
        (.separator :: (List.replicate start .tick ++ output)) []
        (List.replicate height ()) (List.replicate start ())
  have hbaseSep : EvalsToInTime (step affineExactlyOneHeightRevProgram)
      afterBase (some beforeRestoreBase) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestoreBase : EvalsToInTime
      (step affineExactlyOneHeightRevProgram) beforeRestoreBase
      (some beforeCount) (2 * rowBase + 1) := by
    refine ⟨⟨2 * rowBase + 1, ?_⟩, le_rfl⟩
    simpa [beforeRestoreBase, beforeCount] using
      height_restoreBase_eval rowBase none false input
        (.separator :: (List.replicate rowBase .tick ++
          .separator :: (List.replicate start .tick ++ output)))
        (List.replicate height ()) (List.replicate start ()) []
  have hcount : EvalsToInTime (step affineExactlyOneHeightRevProgram)
      beforeCount (some beforeRestoreHeight) (7 * height + 11) := by
    refine ⟨⟨7 * height + 11, ?_⟩, le_rfl⟩
    simpa [beforeCount, beforeRestoreHeight,
      List.replicate_append_replicate, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      height_count_eval height none false input
        (.separator :: (List.replicate rowBase .tick ++
          .separator :: (List.replicate start .tick ++ output))) []
        (List.replicate start ()) (List.replicate rowBase ())
  have hrestoreHeight : EvalsToInTime
      (step affineExactlyOneHeightRevProgram) beforeRestoreHeight
      (some (affineExactlyOneHeightFinishCfg height start rowBase input
        (.separator :: (List.replicate (height + 1) .tick ++
          .separator :: (List.replicate rowBase .tick ++
            .separator :: (List.replicate start .tick ++ output))))))
      (2 * height + 1) := by
    refine ⟨⟨2 * height + 1, ?_⟩, le_rfl⟩
    simpa [beforeRestoreHeight, affineExactlyOneHeightFinishCfg] using
      height_restoreHeight_eval height none false input
        (.separator :: (List.replicate (height + 1) .tick ++
          .separator :: (List.replicate rowBase .tick ++
            .separator :: (List.replicate start .tick ++ output)))) []
        (List.replicate (start + (3 * (height + 1) + 4)) ())
        (List.replicate (rowBase + (height + 1)) ())
  let h₁ := EvalsToInTime.trans (step affineExactlyOneHeightRevProgram)
    _ 1 _ afterStart _ hstart hstartSep
  let h₂ := EvalsToInTime.trans (step affineExactlyOneHeightRevProgram)
    _ _ _ beforeRestoreStart _ h₁ hrestoreStart
  let h₃ := EvalsToInTime.trans (step affineExactlyOneHeightRevProgram)
    _ _ _ beforeBase _ h₂ hbase
  let h₄ := EvalsToInTime.trans (step affineExactlyOneHeightRevProgram)
    _ 1 _ afterBase _ h₃ hbaseSep
  let h₅ := EvalsToInTime.trans (step affineExactlyOneHeightRevProgram)
    _ _ _ beforeRestoreBase _ h₄ hrestoreBase
  let h₆ := EvalsToInTime.trans (step affineExactlyOneHeightRevProgram)
    _ _ _ beforeCount _ h₅ hcount
  let full := EvalsToInTime.trans (step affineExactlyOneHeightRevProgram)
    _ _ _ beforeRestoreHeight _ h₆ hrestoreHeight
  convert full using 1
  · simp [affineExactlyOneHeightFrame, encodeAffineExactlyOneCompactFrame,
      encodeUnaryFrame, encodeUnaryFrameBlock, List.reverse_append,
      List.append_assoc]
  · simp [affineExactlyOneHeightSteps]
    omega

end CLRS.Chapter34.Turing.PolyBuilder
