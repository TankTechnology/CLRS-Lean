import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneMarkedRowInvocationSource
import Mathlib.Tactic

/-!
# Projecting a trailing compact exactly-one family behind fixed row fields

For a fixed number of ordinary unary fields, this controller maps every row

`leading ++ frameEnd ++ encodeUnaryFrame fixed ++ compact ++ frameEnd`

to

`leading ++ frameEnd ++ encodeUnaryFrame fixed ++ invocations.reverse ++ frameEnd`.

The already assembled leading segment and fixed fields are preserved exactly.
Only the trailing compact exactly-one copy is projected to the invocation
stream consumed by the final-conjunction source.  The controller first stacks
that suffix, so it can visit the compact frames in reverse order without any
semantic-side list reversal or row-wise oracle zip.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- One row whose trailing compact family is to be projected. -/
structure AffineExactlyOneLeadingFixedCompactProjectionRow where
  leading : List UnaryFrameSym
  fixed : List Nat
  frames : List AffineExactlyOneFrame
deriving DecidableEq, Repr

/-- Well-formed family for a verifier-fixed number of unary fields. -/
structure AffineExactlyOneLeadingFixedCompactProjectionFamily
    (fixedFieldCount : Nat) where
  rows : List AffineExactlyOneLeadingFixedCompactProjectionRow
  fixed_lengths : ∀ row ∈ rows, row.fixed.length = fixedFieldCount
  leading_frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row.leading,
    symbol ≠ UnaryFrameSym.frameEnd

/-- Physical input encoding. -/
def encodeAffineExactlyOneLeadingFixedCompactProjectionInput
    {fixedFieldCount : Nat}
    (family : AffineExactlyOneLeadingFixedCompactProjectionFamily
      fixedFieldCount) : List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    row.leading ++ [.frameEnd] ++ encodeUnaryFrame row.fixed ++
      encodeAffineExactlyOneCompactFamily row.frames ++ [.frameEnd]

/-- Physical output encoding.  Invocation frames occur in reverse frame order,
as required by the validity final-conjunction source. -/
def encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
    {fixedFieldCount : Nat}
    (family : AffineExactlyOneLeadingFixedCompactProjectionFamily
      fixedFieldCount) : List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    row.leading ++ [.frameEnd] ++ encodeUnaryFrame row.fixed ++
      encodeAffineExactlyOneOutputSourceInvocationFamily row.frames.reverse ++
      [.frameEnd]

/-- Whether another reversed compact frame remains in the current row. -/
inductive AffineExactlyOneLeadingFixedCompactAfterFrame
  | nextFrame | endRow
deriving DecidableEq, Fintype

/-- Finite control for copying the row prefix, stacking the compact suffix,
and projecting the stacked frames. -/
inductive AffineExactlyOneLeadingFixedCompactProjectionLabel
    (fixedFieldCount : Nat)
  | leading
  | emitLeading (symbol : UnaryFrameSym)
  | emitLeadingEnd
  | fixed (position : Fin (fixedFieldCount + 1))
  | emitFixedTick (position : Fin (fixedFieldCount + 1))
  | emitFixedNext (position : Fin (fixedFieldCount + 1))
  | emitFixedLast
  | collect
  | collectSymbol (symbol : UnaryFrameSym)
  | expectFrame
  | loadCount
  | incCount
  | loadBase
  | loadStart
  | incStart
  | emitStart (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
  | emitStartTick (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
  | emitStartSeparator (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
  | emitCount (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
  | emitCountTick (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
  | emitCountSeparator₁ (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
  | emitCountSeparator₂ (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
  | finishRow
  | clearRowEnd
  | finish
  | invalid
deriving DecidableEq, Fintype

/-- Fixed controller.  Its observable output is the reverse of the desired
family stream; one final established list-reversal controller restores the
forward representation. -/
def affineExactlyOneLeadingFixedCompactProjectionRevProgram
    (fixedFieldCount : Nat) : Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneLeadingFixedCompactProjectionLabel fixedFieldCount
  main := .leading
  op
    | .leading => .popInput .finish fun
        | .frameEnd => .emitLeadingEnd
        | symbol => .emitLeading symbol
    | .emitLeading symbol => .pushOutput symbol .leading
    | .emitLeadingEnd => .pushOutput .frameEnd
        (if h : 0 < fixedFieldCount then .fixed ⟨0, by omega⟩ else .collect)
    | .fixed position => .popInput .invalid fun
        | .tick => .emitFixedTick position
        | .separator =>
            if hnext : position.val + 1 < fixedFieldCount then
              .emitFixedNext ⟨position.val + 1, by omega⟩
            else
              .emitFixedLast
        | .frameEnd => .invalid
    | .emitFixedTick position => .pushOutput .tick (.fixed position)
    | .emitFixedNext position => .pushOutput .separator (.fixed position)
    | .emitFixedLast => .pushOutput .separator .collect
    | .collect => .popInput .invalid fun
        | .frameEnd => .expectFrame
        | symbol => .collectSymbol symbol
    | .collectSymbol symbol => .pushWork₂ symbol .collect
    | .expectFrame => .popWork₂ .finishRow fun symbol =>
        if symbol = .separator then .loadCount else .invalid
    | .loadCount => .popWork₂ (.emitStart .endRow) fun
        | .tick => .incCount
        | .separator => .loadBase
        | .frameEnd => .invalid
    | .incCount => .inc₂ .loadCount
    | .loadBase => .popWork₂ .invalid fun
        | .tick => .loadBase
        | .separator => .loadStart
        | .frameEnd => .invalid
    | .loadStart => .popWork₂ (.emitStart .endRow) fun
        | .tick => .incStart
        | .separator => .emitStart .nextFrame
        | .frameEnd => .invalid
    | .incStart => .inc₁ .loadStart
    | .emitStart after =>
        .dec₁ (.emitStartSeparator after) (.emitStartTick after)
    | .emitStartTick after => .pushOutput .tick (.emitStart after)
    | .emitStartSeparator after =>
        .pushOutput .separator (.emitCount after)
    | .emitCount after =>
        .dec₂ (.emitCountSeparator₁ after) (.emitCountTick after)
    | .emitCountTick after => .pushOutput .tick (.emitCount after)
    | .emitCountSeparator₁ after =>
        .pushOutput .separator (.emitCountSeparator₂ after)
    | .emitCountSeparator₂ .nextFrame =>
        .pushOutput .separator .loadCount
    | .emitCountSeparator₂ .endRow =>
        .pushOutput .separator .finishRow
    | .finishRow => .pushOutput .frameEnd .clearRowEnd
    | .clearRowEnd => .popWork₁ .leading (fun _ => .leading)
    | .finish => .halt
    | .invalid => .halt

private def affineExactlyOneLeadingFixedCompactProjectionCfg
    (fixedFieldCount : Nat)
    (label : AffineExactlyOneLeadingFixedCompactProjectionLabel
      fixedFieldCount)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (start count : List Unit) :
    BuilderCfg
      (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount) where
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

private def affineExactlyOneLeadingFixedCompactProjectionLoopCfg
    (fixedFieldCount : Nat) (input output : List UnaryFrameSym) :
    BuilderCfg
      (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount) :=
  affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount .leading
    none none false input output [] [] [] []

private theorem leadingFixedCompact_leading_eval
    (fixedFieldCount : Nat) (leading tail output : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ leading, symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[2 * (leading.length + 1)]
      (some (affineExactlyOneLeadingFixedCompactProjectionLoopCfg
        fixedFieldCount (leading ++ .frameEnd :: tail) output)) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (if h : 0 < fixedFieldCount then .fixed ⟨0, by omega⟩ else .collect)
        (some .frameEnd) none false tail
        ((leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        [] [] [] []) := by
  induction leading generalizing output with
  | nil =>
      simp only [List.length_nil, zero_add, Nat.mul_one,
        Function.iterate_succ_apply, Function.iterate_zero_apply,
        List.nil_append, List.reverse_singleton, List.singleton_append]
      rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      rw [show 2 * ((symbol :: rest).length + 1) =
          2 * (rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases symbol with
      | frameEnd => exact (hsymbol rfl).elim
      | tick =>
          change
            (flip Option.bind
              (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                fixedFieldCount)))^[2 * (rest.length + 1)]
              (some (affineExactlyOneLeadingFixedCompactProjectionLoopCfg
                fixedFieldCount (rest ++ .frameEnd :: tail)
                (.tick :: output))) = _
          simpa [List.reverse_cons, List.append_assoc] using
            ih (.tick :: output) hrest
      | separator =>
          change
            (flip Option.bind
              (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                fixedFieldCount)))^[2 * (rest.length + 1)]
              (some (affineExactlyOneLeadingFixedCompactProjectionLoopCfg
                fixedFieldCount (rest ++ .frameEnd :: tail)
                (.separator :: output))) = _
          simpa [List.reverse_cons, List.append_assoc] using
            ih (.separator :: output) hrest

private theorem leadingFixedCompact_replicate_append_cons
    {alpha : Type} (item : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count item ++ item :: tail =
      item :: (List.replicate count item ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons item) ih

private theorem leadingFixedCompact_fixed_ticks_eval
    (fixedFieldCount : Nat) (position : Fin (fixedFieldCount + 1))
    (count : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[2 * count]
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.fixed position) buffer₁ buffer₂ false
        (List.replicate count .tick ++ tail) output [] [] [] [])) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.fixed position) (if count = 0 then buffer₁ else some .tick)
        buffer₂ false tail (List.replicate count .tick ++ output)
        [] [] [] []) := by
  induction count generalizing buffer₁ output with
  | zero => simp
  | succ count ih =>
      rw [show 2 * (count + 1) = 2 * count + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)))^[2 * count]
          (some (affineExactlyOneLeadingFixedCompactProjectionCfg
            fixedFieldCount (.fixed position) (some .tick) buffer₂ false
            (List.replicate count .tick ++ tail) (.tick :: output)
            [] [] [] [])) = _
      simpa [List.replicate_succ, List.cons_append,
        leadingFixedCompact_replicate_append_cons,
        List.append_assoc] using ih (some .tick) (.tick :: output)

private def leadingFixedCompact_fixed_values_eval
    (fixedFieldCount position : Nat) (values : List Nat)
    (hfit : position + values.length = fixedFieldCount)
    (hposition : position < fixedFieldCount)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.fixed ⟨position, by omega⟩) buffer₁ buffer₂ false
        (encodeUnaryFrame values ++ tail) output [] [] [] [])
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .collect (some .separator) buffer₂ false tail
        ((encodeUnaryFrame values).reverse ++ output) [] [] [] []))
      (2 * (encodeUnaryFrame values).length) := by
  induction values generalizing position buffer₁ output with
  | nil => simp at hfit; omega
  | cons value values ih =>
      have hnextFit : position + 1 + values.length = fixedFieldCount := by
        simp only [List.length_cons] at hfit
        omega
      let afterTicks :=
        affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
          (.fixed ⟨position, by omega⟩)
          (if value = 0 then buffer₁ else some .tick) buffer₂ false
          (.separator :: (encodeUnaryFrame values ++ tail))
          (List.replicate value .tick ++ output) [] [] [] []
      have hticks : EvalsToInTime
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount))
          (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
            (.fixed ⟨position, by omega⟩) buffer₁ buffer₂ false
            (List.replicate value .tick ++
              .separator :: (encodeUnaryFrame values ++ tail))
            output [] [] [] [])
          (some afterTicks) (2 * value) := by
        refine ⟨⟨2 * value, ?_⟩, le_rfl⟩
        simpa [afterTicks] using leadingFixedCompact_fixed_ticks_eval
          fixedFieldCount ⟨position, by omega⟩ value buffer₁ buffer₂
          (.separator :: (encodeUnaryFrame values ++ tail)) output
      by_cases hnext : position + 1 < fixedFieldCount
      · let afterSeparator :=
          affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
            (.fixed ⟨position + 1, by omega⟩) (some .separator) buffer₂
            false (encodeUnaryFrame values ++ tail)
            (.separator :: List.replicate value .tick ++ output)
            [] [] [] []
        have hseparator : EvalsToInTime
            (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
              fixedFieldCount)) afterTicks (some afterSeparator) 2 := by
          let beforeEmit :=
            affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
              (.emitFixedNext ⟨position + 1, by omega⟩)
              (some .separator) buffer₂ false
              (encodeUnaryFrame values ++ tail)
              (List.replicate value .tick ++ output) [] [] [] []
          have hpop : EvalsToInTime
              (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                fixedFieldCount)) afterTicks (some beforeEmit) 1 := by
            refine ⟨⟨1, ?_⟩, le_rfl⟩
            change step
              (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                fixedFieldCount) afterTicks = some beforeEmit
            simp [afterTicks, beforeEmit, step,
              affineExactlyOneLeadingFixedCompactProjectionCfg, stepOp,
              affineExactlyOneLeadingFixedCompactProjectionRevProgram,
              hnext]
          have hemit : EvalsToInTime
              (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                fixedFieldCount)) beforeEmit (some afterSeparator) 1 :=
            ⟨⟨1, rfl⟩, le_rfl⟩
          simpa using EvalsToInTime.trans
            (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
              fixedFieldCount)) 1 1 _ beforeEmit _ hpop hemit
        have hrest := ih (position + 1) hnextFit hnext
          (some .separator) (.separator ::
            List.replicate value .tick ++ output)
        let full := EvalsToInTime.trans
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)) (2 * value) 2 _ afterTicks _ hticks hseparator
        have fullNorm : EvalsToInTime
            (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
              fixedFieldCount))
            (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
              (.fixed ⟨position, by omega⟩) buffer₁ buffer₂ false
              (List.replicate value .tick ++
                .separator :: (encodeUnaryFrame values ++ tail))
              output [] [] [] [])
            (some afterSeparator) (2 * value + 2) := by
          simpa [Nat.add_comm] using full
        let full' := EvalsToInTime.trans
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)) (2 * value + 2)
            (2 * (encodeUnaryFrame values).length)
            _ afterSeparator _ fullNorm hrest
        convert full' using 1
        · simp [encodeUnaryFrame, encodeUnaryFrameBlock,
            List.append_assoc]
        · simp [encodeUnaryFrame, encodeUnaryFrameBlock,
            List.reverse_append, List.append_assoc]
        · simp [encodeUnaryFrame, encodeUnaryFrameBlock]
          omega
      · cases values with
        | nil =>
            have hlast : position + 1 = fixedFieldCount := by omega
            have hseparator : EvalsToInTime
                (step
                  (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                    fixedFieldCount)) afterTicks
                (some
                  (affineExactlyOneLeadingFixedCompactProjectionCfg
                    fixedFieldCount .collect (some .separator) buffer₂ false
                    tail (.separator :: List.replicate value .tick ++ output)
                    [] [] [] [])) 2 := by
              let beforeEmit :=
                affineExactlyOneLeadingFixedCompactProjectionCfg
                  fixedFieldCount .emitFixedLast (some .separator) buffer₂
                  false tail (List.replicate value .tick ++ output)
                  [] [] [] []
              have hpop : EvalsToInTime
                  (step
                    (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                      fixedFieldCount)) afterTicks (some beforeEmit) 1 := by
                refine ⟨⟨1, ?_⟩, le_rfl⟩
                change step
                  (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                    fixedFieldCount) afterTicks = some beforeEmit
                simp [afterTicks, beforeEmit, step,
                  affineExactlyOneLeadingFixedCompactProjectionCfg, stepOp,
                  affineExactlyOneLeadingFixedCompactProjectionRevProgram,
                  encodeUnaryFrame, hnext]
              have hemit : EvalsToInTime
                  (step
                    (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                      fixedFieldCount)) beforeEmit
                  (some
                    (affineExactlyOneLeadingFixedCompactProjectionCfg
                      fixedFieldCount .collect (some .separator) buffer₂
                      false tail
                      (.separator :: List.replicate value .tick ++ output)
                      [] [] [] [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
              simpa using EvalsToInTime.trans
                (step
                  (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                    fixedFieldCount)) 1 1 _ beforeEmit _ hpop hemit
            let full := EvalsToInTime.trans
              (step
                (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                  fixedFieldCount)) (2 * value) 2 _ afterTicks _
              hticks hseparator
            have fullNorm : EvalsToInTime
                (step
                  (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                    fixedFieldCount))
                (affineExactlyOneLeadingFixedCompactProjectionCfg
                  fixedFieldCount (.fixed ⟨position, by omega⟩)
                  buffer₁ buffer₂ false
                  (List.replicate value .tick ++ .separator :: tail)
                  output [] [] [] [])
                (some
                  (affineExactlyOneLeadingFixedCompactProjectionCfg
                    fixedFieldCount .collect (some .separator) buffer₂ false
                    tail (.separator :: List.replicate value .tick ++ output)
                    [] [] [] []))
                (2 * value + 2) := by
              simpa [Nat.add_comm, encodeUnaryFrame] using full
            convert fullNorm using 1 <;>
              simp [encodeUnaryFrame, encodeUnaryFrameBlock,
                List.reverse_append, List.append_assoc] <;> omega
        | cons head rest =>
            simp only [List.length_cons] at hnextFit
            omega

private theorem leadingFixedCompact_collect_eval
    (fixedFieldCount : Nat) (payload tail output : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ payload, symbol ≠ UnaryFrameSym.frameEnd)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (work₂ : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[2 * payload.length + 1]
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .collect buffer₁ buffer₂ false
        (payload ++ .frameEnd :: tail) output [] work₂ [] [])) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .expectFrame (some .frameEnd) buffer₂ false tail output []
        (payload.reverse ++ work₂) [] []) := by
  induction payload generalizing buffer₁ buffer₂ work₂ with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      cases symbol with
      | frameEnd => exact (hsymbol rfl).elim
      | tick =>
          change
            (flip Option.bind
              (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                fixedFieldCount)))^[2 * rest.length + 1]
              (some (affineExactlyOneLeadingFixedCompactProjectionCfg
                fixedFieldCount .collect (some .tick) buffer₂ false
                (rest ++ .frameEnd :: tail) output [] (.tick :: work₂)
                [] [])) = _
          simpa [List.reverse_cons, List.append_assoc] using
            ih hrest (some UnaryFrameSym.tick) buffer₂
              (UnaryFrameSym.tick :: work₂)
      | separator =>
          change
            (flip Option.bind
              (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
                fixedFieldCount)))^[2 * rest.length + 1]
              (some (affineExactlyOneLeadingFixedCompactProjectionCfg
                fixedFieldCount .collect (some .separator) buffer₂
                false (rest ++ .frameEnd :: tail) output []
                (.separator :: work₂) [] [])) = _
          simpa [List.reverse_cons, List.append_assoc] using
            ih hrest (some UnaryFrameSym.separator) buffer₂
              (UnaryFrameSym.separator :: work₂)

private theorem leadingFixedCompact_scanCount_eval
    (fixedFieldCount base value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (input tail output : List UnaryFrameSym)
    (work₁ : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[2 * value + 1]
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadCount buffer₁ buffer₂ false input output work₁
        (List.replicate value .tick ++ .separator :: tail) []
        (List.replicate base ()))) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadBase buffer₁ (some .separator) false input output work₁ tail []
        (List.replicate (base + value) ())) := by
  induction value generalizing base buffer₂ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)))^[2 * value + 1]
          (some (affineExactlyOneLeadingFixedCompactProjectionCfg
            fixedFieldCount .loadCount buffer₁ (some .tick) false input output
            work₁ (List.replicate value .tick ++ .separator :: tail) []
            (() :: List.replicate base ()))) = _
      have hcounter : (() :: List.replicate base ()) =
          List.replicate (base + 1) () := by rw [List.replicate_succ]
      rw [hcounter]
      simpa only [Nat.add_assoc, Nat.add_comm 1 value] using
        ih (base + 1) (some .tick)

private theorem leadingFixedCompact_scanBase_eval
    (fixedFieldCount value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (input tail output : List UnaryFrameSym)
    (work₁ : List UnaryFrameSym) (start count : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[value + 1]
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadBase buffer₁ buffer₂ false input output work₁
        (List.replicate value .tick ++ .separator :: tail) start count)) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadStart buffer₁ (some .separator) false input output work₁ tail
        start count) := by
  induction value generalizing buffer₂ with
  | zero => rfl
  | succ value ih =>
      rw [show value + 1 + 1 = (value + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)))^[value + 1]
          (some (affineExactlyOneLeadingFixedCompactProjectionCfg
            fixedFieldCount .loadBase buffer₁ (some .tick) false input output
            work₁ (List.replicate value .tick ++ .separator :: tail)
            start count)) = _
      exact ih (some .tick)

private theorem leadingFixedCompact_scanStartNext_eval
    (fixedFieldCount base value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (input tail output : List UnaryFrameSym)
    (work₁ : List UnaryFrameSym) (count : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[2 * value + 1]
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadStart buffer₁ buffer₂ false input output work₁
        (List.replicate value .tick ++ .separator :: tail)
        (List.replicate base ()) count)) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.emitStart .nextFrame) buffer₁ (some .separator) false input output
        work₁ tail (List.replicate (base + value) ()) count) := by
  induction value generalizing base buffer₂ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)))^[2 * value + 1]
          (some (affineExactlyOneLeadingFixedCompactProjectionCfg
            fixedFieldCount .loadStart buffer₁ (some .tick) false input output
            work₁ (List.replicate value .tick ++ .separator :: tail)
            (() :: List.replicate base ()) count)) = _
      have hcounter : (() :: List.replicate base ()) =
          List.replicate (base + 1) () := by rw [List.replicate_succ]
      rw [hcounter]
      simpa only [Nat.add_assoc, Nat.add_comm 1 value] using
        ih (base + 1) (some .tick)

private theorem leadingFixedCompact_scanStartEnd_eval
    (fixedFieldCount base value : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (input output : List UnaryFrameSym)
    (work₁ : List UnaryFrameSym) (count : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[2 * value + 1]
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadStart buffer₁ buffer₂ false input output work₁
        (List.replicate value .tick) (List.replicate base ()) count)) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.emitStart .endRow) buffer₁ none false input output work₁ []
        (List.replicate (base + value) ()) count) := by
  induction value generalizing base buffer₂ with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)))^[2 * value + 1]
          (some (affineExactlyOneLeadingFixedCompactProjectionCfg
            fixedFieldCount .loadStart buffer₁ (some .tick) false input output
            work₁ (List.replicate value .tick)
            (() :: List.replicate base ()) count)) = _
      have hcounter : (() :: List.replicate base ()) =
          List.replicate (base + 1) () := by rw [List.replicate_succ]
      rw [hcounter]
      simpa only [Nat.add_assoc, Nat.add_comm 1 value] using
        ih (base + 1) (some .tick)

private theorem leadingFixedCompact_emitStart_eval
    (fixedFieldCount : Nat)
    (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (input output work₁ work₂ : List UnaryFrameSym) (count : List Unit) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[2 * value + 1]
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.emitStart after) buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate value ()) count)) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.emitStartSeparator after) buffer₁ buffer₂ false input
        (List.replicate value .tick ++ output) work₁ work₂ [] count) := by
  induction value generalizing output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)))^[2 * value + 1]
          (some (affineExactlyOneLeadingFixedCompactProjectionCfg
            fixedFieldCount (.emitStart after) buffer₁ buffer₂ false input
            (.tick :: output) work₁ work₂
            (List.replicate value ()) count)) = _
      simpa only [List.replicate_succ, List.cons_append,
        leadingFixedCompact_replicate_append_cons] using ih (.tick :: output)

private theorem leadingFixedCompact_emitCount_eval
    (fixedFieldCount : Nat)
    (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (input output work₁ work₂ : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)))^[2 * value + 1]
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.emitCount after) buffer₁ buffer₂ false input output work₁ work₂
        [] (List.replicate value ()))) =
      some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.emitCountSeparator₁ after) buffer₁ buffer₂ false input
        (List.replicate value .tick ++ output) work₁ work₂ [] []) := by
  induction value generalizing output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)))^[2 * value + 1]
          (some (affineExactlyOneLeadingFixedCompactProjectionCfg
            fixedFieldCount (.emitCount after) buffer₁ buffer₂ false input
            (.tick :: output) work₁ work₂ []
            (List.replicate value ()))) = _
      simpa only [List.replicate_succ, List.cons_append,
        leadingFixedCompact_replicate_append_cons] using ih (.tick :: output)

/-- Exact emission cost for one `(start, count, 0)` invocation. -/
def affineExactlyOneLeadingFixedCompactEmitSteps
    (start count : Nat) : Nat :=
  2 * start + 2 * count + 5

private def affineExactlyOneLeadingFixedCompactAfterLabel
    (after : AffineExactlyOneLeadingFixedCompactAfterFrame) :
    AffineExactlyOneLeadingFixedCompactProjectionLabel fixedFieldCount :=
  match after with
  | .nextFrame => .loadCount
  | .endRow => .finishRow

private def leadingFixedCompact_emit_run
    (fixedFieldCount : Nat)
    (after : AffineExactlyOneLeadingFixedCompactAfterFrame)
    (start count : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (input output work₁ work₂ : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.emitStart after) buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate start ()) (List.replicate count ()))
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (affineExactlyOneLeadingFixedCompactAfterLabel after)
        buffer₁ buffer₂ false input
        ((encodeUnaryFrame [start, count, 0]).reverse ++ output)
        work₁ work₂ [] []))
      (affineExactlyOneLeadingFixedCompactEmitSteps start count) := by
  let afterStart :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      (.emitStartSeparator after) buffer₁ buffer₂ false input
      (List.replicate start .tick ++ output) work₁ work₂ []
      (List.replicate count ())
  let beforeCount :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      (.emitCount after) buffer₁ buffer₂ false input
      (.separator :: (List.replicate start .tick ++ output))
      work₁ work₂ [] (List.replicate count ())
  let afterCount :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      (.emitCountSeparator₁ after) buffer₁ buffer₂ false input
      (List.replicate count .tick ++
        (.separator :: (List.replicate start .tick ++ output)))
      work₁ work₂ [] []
  let beforeLast :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      (.emitCountSeparator₂ after) buffer₁ buffer₂ false input
      (.separator :: List.replicate count .tick ++
        (.separator :: (List.replicate start .tick ++ output)))
      work₁ work₂ [] []
  have hstart : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (.emitStart after) buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate start ()) (List.replicate count ()))
      (some afterStart) (2 * start + 1) :=
    ⟨⟨2 * start + 1, by
      simpa [afterStart] using leadingFixedCompact_emitStart_eval
        fixedFieldCount after start buffer₁ buffer₂ input output work₁ work₂
        (List.replicate count ())⟩, le_rfl⟩
  have hstartSep : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterStart (some beforeCount) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hcount : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) beforeCount (some afterCount) (2 * count + 1) :=
    ⟨⟨2 * count + 1, by
      simpa [beforeCount, afterCount,
        leadingFixedCompact_replicate_append_cons,
        List.append_assoc] using leadingFixedCompact_emitCount_eval
          fixedFieldCount after count buffer₁ buffer₂ input
          (.separator :: (List.replicate start .tick ++ output))
          work₁ work₂⟩, le_rfl⟩
  have hcountSep : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterCount (some beforeLast) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hlast : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) beforeLast
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        (affineExactlyOneLeadingFixedCompactAfterLabel after)
        buffer₁ buffer₂ false input
        (.separator :: .separator :: List.replicate count .tick ++
          (.separator :: List.replicate start .tick ++ output))
        work₁ work₂ [] [])) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    cases after <;> rfl
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) (2 * start + 1) 1 _ afterStart _ hstart hstartSep
  let h₂ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _ (2 * count + 1) _ beforeCount _ h₁ hcount
  let h₃ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _ 1 _ afterCount _ h₂ hcountSep
  let full := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _ 1 _ beforeLast _ h₃ hlast
  convert full using 1
  · simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.reverse_append,
      affineExactlyOneLeadingFixedCompactAfterLabel,
      List.append_assoc]
  · simp [affineExactlyOneLeadingFixedCompactEmitSteps]
    omega

/-- Cost of parsing and projecting one reversed compact frame. -/
def affineExactlyOneLeadingFixedCompactFrameSteps
    (frame : AffineExactlyOneFrame) : Nat :=
  4 * frame.start + 4 * frame.count + frame.rowBase + 8

private def leadingFixedCompact_frameNext_run
    (fixedFieldCount : Nat) (frame : AffineExactlyOneFrame)
    (buffer₁ : Option UnaryFrameSym)
    (input tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadCount buffer₁ (some .separator) false input output []
        (encodeAffineExactlyOneReversedCompactBody frame ++
          .separator :: tail) [] [])
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadCount buffer₁ (some .separator) false input
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ output)
        [] tail [] []))
      (affineExactlyOneLeadingFixedCompactFrameSteps frame) := by
  let afterCount :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      .loadBase buffer₁ (some .separator) false input output []
      (List.replicate frame.rowBase .tick ++ .separator ::
        (List.replicate frame.start .tick ++ .separator :: tail))
      [] (List.replicate frame.count ())
  let afterBase :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      .loadStart buffer₁ (some .separator) false input output []
      (List.replicate frame.start .tick ++ .separator :: tail)
      [] (List.replicate frame.count ())
  let beforeEmit :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      (.emitStart .nextFrame) buffer₁ (some .separator) false input
      output [] tail (List.replicate frame.start ())
      (List.replicate frame.count ())
  have hcount : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadCount buffer₁ (some .separator) false input output []
        (encodeAffineExactlyOneReversedCompactBody frame ++
          .separator :: tail) [] [])
      (some afterCount) (2 * frame.count + 1) := by
    refine ⟨⟨2 * frame.count + 1, ?_⟩, le_rfl⟩
    simpa [afterCount, encodeAffineExactlyOneReversedCompactBody,
      List.append_assoc] using leadingFixedCompact_scanCount_eval
        fixedFieldCount 0 frame.count buffer₁ (some .separator) input
        (List.replicate frame.rowBase .tick ++ .separator ::
          (List.replicate frame.start .tick ++ .separator :: tail))
        output []
  have hbase : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterCount (some afterBase)
      (frame.rowBase + 1) := by
    refine ⟨⟨frame.rowBase + 1, ?_⟩, le_rfl⟩
    simpa [afterCount, afterBase] using leadingFixedCompact_scanBase_eval
      fixedFieldCount frame.rowBase buffer₁ (some .separator) input
      (List.replicate frame.start .tick ++ .separator :: tail)
      output [] [] (List.replicate frame.count ())
  have hstart : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterBase (some beforeEmit)
      (2 * frame.start + 1) := by
    refine ⟨⟨2 * frame.start + 1, ?_⟩, le_rfl⟩
    simpa [afterBase, beforeEmit] using
      leadingFixedCompact_scanStartNext_eval fixedFieldCount 0 frame.start
        buffer₁ (some .separator) input tail output []
        (List.replicate frame.count ())
  have hemit := leadingFixedCompact_emit_run fixedFieldCount .nextFrame
    frame.start frame.count buffer₁ (some .separator)
    input output [] tail
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) (2 * frame.count + 1) (frame.rowBase + 1)
    _ afterCount _ hcount hbase
  let h₂ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _ (2 * frame.start + 1) _ afterBase _ h₁ hstart
  let full := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _
    (affineExactlyOneLeadingFixedCompactEmitSteps frame.start frame.count)
    _ beforeEmit _ h₂ (by simpa [beforeEmit] using hemit)
  convert full using 1
  · simp [encodeAffineExactlyOneOutputSourceInvocation,
      affineExactlyOneLeadingFixedCompactAfterLabel]
  · simp [affineExactlyOneLeadingFixedCompactFrameSteps,
      affineExactlyOneLeadingFixedCompactEmitSteps]
    omega

private def leadingFixedCompact_frameEnd_run
    (fixedFieldCount : Nat) (frame : AffineExactlyOneFrame)
    (buffer₁ : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadCount buffer₁ (some .separator) false input output []
        (encodeAffineExactlyOneReversedCompactBody frame) [] [])
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .finishRow buffer₁ none false input
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ output)
        [] [] [] []))
      (affineExactlyOneLeadingFixedCompactFrameSteps frame) := by
  let afterCount :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      .loadBase buffer₁ (some .separator) false input output []
      (List.replicate frame.rowBase .tick ++ .separator ::
        List.replicate frame.start .tick) [] (List.replicate frame.count ())
  let afterBase :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      .loadStart buffer₁ (some .separator) false input output []
      (List.replicate frame.start .tick) [] (List.replicate frame.count ())
  let beforeEmit :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      (.emitStart .endRow) buffer₁ none false input output [] []
      (List.replicate frame.start ()) (List.replicate frame.count ())
  have hcount : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadCount buffer₁ (some .separator) false input output []
        (encodeAffineExactlyOneReversedCompactBody frame) [] [])
      (some afterCount) (2 * frame.count + 1) := by
    refine ⟨⟨2 * frame.count + 1, ?_⟩, le_rfl⟩
    simpa [afterCount, encodeAffineExactlyOneReversedCompactBody,
      List.append_assoc] using leadingFixedCompact_scanCount_eval
        fixedFieldCount 0 frame.count buffer₁ (some .separator) input
        (List.replicate frame.rowBase .tick ++ .separator ::
          List.replicate frame.start .tick) output []
  have hbase : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterCount (some afterBase)
      (frame.rowBase + 1) := by
    refine ⟨⟨frame.rowBase + 1, ?_⟩, le_rfl⟩
    simpa [afterCount, afterBase] using leadingFixedCompact_scanBase_eval
      fixedFieldCount frame.rowBase buffer₁ (some .separator) input
      (List.replicate frame.start .tick) output [] []
      (List.replicate frame.count ())
  have hstart : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterBase (some beforeEmit)
      (2 * frame.start + 1) := by
    refine ⟨⟨2 * frame.start + 1, ?_⟩, le_rfl⟩
    simpa [afterBase, beforeEmit] using
      leadingFixedCompact_scanStartEnd_eval fixedFieldCount 0 frame.start
        buffer₁ (some .separator) input output []
        (List.replicate frame.count ())
  have hemit := leadingFixedCompact_emit_run fixedFieldCount .endRow
    frame.start frame.count buffer₁ none input output [] []
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) (2 * frame.count + 1) (frame.rowBase + 1)
    _ afterCount _ hcount hbase
  let h₂ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _ (2 * frame.start + 1) _ afterBase _ h₁ hstart
  let full := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _
    (affineExactlyOneLeadingFixedCompactEmitSteps frame.start frame.count)
    _ beforeEmit _ h₂ (by simpa [beforeEmit] using hemit)
  convert full using 1
  · simp [encodeAffineExactlyOneOutputSourceInvocation,
      affineExactlyOneLeadingFixedCompactAfterLabel]
  · simp [affineExactlyOneLeadingFixedCompactFrameSteps,
      affineExactlyOneLeadingFixedCompactEmitSteps]
    omega

/-- Total reversed-frame projection cost inside one row. -/
def affineExactlyOneLeadingFixedCompactFramesSteps
    (frames : List AffineExactlyOneFrame) : Nat :=
  (frames.map affineExactlyOneLeadingFixedCompactFrameSteps).sum

private def leadingFixedCompact_nonemptyFrames_run
    (fixedFieldCount : Nat) (frame : AffineExactlyOneFrame) :
    (rest : List AffineExactlyOneFrame) →
    (buffer₁ : Option UnaryFrameSym) →
    (input : List UnaryFrameSym) →
    (output : List UnaryFrameSym) →
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .loadCount buffer₁ (some .separator) false input output []
        (encodeAffineExactlyOneReversedCompactBody frame ++
          encodeAffineExactlyOneReversedCompactFrameStream rest) [] [])
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .finishRow buffer₁ none false input
        ((encodeAffineExactlyOneOutputSourceInvocationFamily
          (frame :: rest)).reverse ++ output) [] [] [] []))
      (affineExactlyOneLeadingFixedCompactFramesSteps (frame :: rest))
  | [], buffer₁, input, output => by
      simpa [affineExactlyOneLeadingFixedCompactFramesSteps,
        encodeAffineExactlyOneReversedCompactFrameStream,
        encodeAffineExactlyOneOutputSourceInvocationFamily] using
        leadingFixedCompact_frameEnd_run
          fixedFieldCount frame buffer₁ input output
  | next :: rest, buffer₁, input, output => by
      let remainingTail :=
        encodeAffineExactlyOneReversedCompactBody next ++
          encodeAffineExactlyOneReversedCompactFrameStream rest
      have hframe := leadingFixedCompact_frameNext_run fixedFieldCount frame
        buffer₁ input remainingTail output
      have hrest := leadingFixedCompact_nonemptyFrames_run
        fixedFieldCount next rest buffer₁ input
        ((encodeAffineExactlyOneOutputSourceInvocation frame).reverse ++ output)
      let full := EvalsToInTime.trans
        (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount))
        (affineExactlyOneLeadingFixedCompactFrameSteps frame)
        (affineExactlyOneLeadingFixedCompactFramesSteps (next :: rest))
        _ _ _ (by
          simpa [remainingTail,
            encodeAffineExactlyOneReversedCompactFrameStream] using hframe)
        (by simpa only [remainingTail,
          encodeAffineExactlyOneReversedCompactFrameStream] using hrest)
      convert full using 1
      · simp [encodeAffineExactlyOneReversedCompactFrameStream]
      · simp [encodeAffineExactlyOneOutputSourceInvocationFamily,
          List.reverse_append, List.append_assoc]
      · change
          affineExactlyOneLeadingFixedCompactFrameSteps frame +
              affineExactlyOneLeadingFixedCompactFramesSteps (next :: rest) =
            affineExactlyOneLeadingFixedCompactFramesSteps (next :: rest) +
              affineExactlyOneLeadingFixedCompactFrameSteps frame
        omega

private def leadingFixedCompact_frames_run
    (fixedFieldCount : Nat) (frames : List AffineExactlyOneFrame)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (input : List UnaryFrameSym)
    (output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .expectFrame buffer₁ buffer₂ false input output []
        (encodeAffineExactlyOneReversedCompactFrameStream frames) [] [])
      (some (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .finishRow buffer₁ none false input
        ((encodeAffineExactlyOneOutputSourceInvocationFamily frames).reverse ++
          output) [] [] [] []))
      (affineExactlyOneLeadingFixedCompactFramesSteps frames + 1) := by
  cases frames with
  | nil =>
      refine ⟨⟨1, rfl⟩, le_rfl⟩
  | cons frame rest =>
      have hfirst : EvalsToInTime
          (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount))
          (affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
            .expectFrame buffer₁ buffer₂ false input output []
            (encodeAffineExactlyOneReversedCompactFrameStream
              (frame :: rest)) [] [])
          (some (affineExactlyOneLeadingFixedCompactProjectionCfg
            fixedFieldCount .loadCount buffer₁ (some .separator) false input
            output []
            (encodeAffineExactlyOneReversedCompactBody frame ++
              encodeAffineExactlyOneReversedCompactFrameStream rest)
            [] [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hframes := leadingFixedCompact_nonemptyFrames_run
        fixedFieldCount frame rest buffer₁ input output
      let full := EvalsToInTime.trans
        (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount)) 1
        (affineExactlyOneLeadingFixedCompactFramesSteps (frame :: rest))
        _ _ _ hfirst hframes
      convert full using 1 <;> omega

private theorem leadingFixedCompact_encodeUnaryFrame_no_frameEnd
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with (⟨hvalue, rfl⟩ | rfl) <;> simp

private theorem leadingFixedCompact_compact_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneCompactFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  induction frames with
  | nil => simp [encodeAffineExactlyOneCompactFamily] at hsymbol
  | cons frame rest ih =>
      simp only [encodeAffineExactlyOneCompactFamily,
        List.mem_append] at hsymbol
      rcases hsymbol with hframe | hrest
      · exact leadingFixedCompact_encodeUnaryFrame_no_frameEnd _
          symbol hframe
      · exact ih hrest

/-- Exact runtime of one row, excluding the next-row dispatch. -/
def affineExactlyOneLeadingFixedCompactRowSteps
    (row : AffineExactlyOneLeadingFixedCompactProjectionRow) : Nat :=
  2 * (row.leading.length + 1) +
    2 * (encodeUnaryFrame row.fixed).length +
    (2 * (encodeAffineExactlyOneCompactFamily row.frames).length + 1) +
    (affineExactlyOneLeadingFixedCompactFramesSteps row.frames.reverse + 1) +
    2

private def leadingFixedCompact_row_run
    (fixedFieldCount : Nat)
    (row : AffineExactlyOneLeadingFixedCompactProjectionRow)
    (hfixed : row.fixed.length = fixedFieldCount)
    (hleading : ∀ symbol ∈ row.leading,
      symbol ≠ UnaryFrameSym.frameEnd)
    (tail output : List UnaryFrameSym)
    (hnonempty : 0 < fixedFieldCount) :
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionLoopCfg fixedFieldCount
        (row.leading ++ [UnaryFrameSym.frameEnd] ++ encodeUnaryFrame row.fixed ++
          encodeAffineExactlyOneCompactFamily row.frames ++
          UnaryFrameSym.frameEnd :: tail) output)
      (some (affineExactlyOneLeadingFixedCompactProjectionLoopCfg
        fixedFieldCount tail
        ((row.leading ++ [UnaryFrameSym.frameEnd] ++ encodeUnaryFrame row.fixed ++
          encodeAffineExactlyOneOutputSourceInvocationFamily
            row.frames.reverse ++ [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (affineExactlyOneLeadingFixedCompactRowSteps row) := by
  let afterLeading :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      (.fixed ⟨0, by omega⟩) (some UnaryFrameSym.frameEnd) none false
      (encodeUnaryFrame row.fixed ++
        encodeAffineExactlyOneCompactFamily row.frames ++
          UnaryFrameSym.frameEnd :: tail)
      ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
      [] [] [] []
  have hleadingRun : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionLoopCfg fixedFieldCount
        (row.leading ++ UnaryFrameSym.frameEnd ::
          (encodeUnaryFrame row.fixed ++
            encodeAffineExactlyOneCompactFamily row.frames ++
            UnaryFrameSym.frameEnd :: tail)) output)
      (some afterLeading) (2 * (row.leading.length + 1)) := by
    refine ⟨⟨2 * (row.leading.length + 1), ?_⟩, le_rfl⟩
    have source := leadingFixedCompact_leading_eval fixedFieldCount
      row.leading
      (encodeUnaryFrame row.fixed ++
        encodeAffineExactlyOneCompactFamily row.frames ++
          UnaryFrameSym.frameEnd :: tail)
      output hleading
    simpa [afterLeading, hnonempty] using source
  let afterFixed :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      .collect (some .separator) none false
      (encodeAffineExactlyOneCompactFamily row.frames ++
        UnaryFrameSym.frameEnd :: tail)
      ((encodeUnaryFrame row.fixed).reverse ++
        ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output))
      [] [] [] []
  have hfixedRun : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterLeading (some afterFixed)
      (2 * (encodeUnaryFrame row.fixed).length) := by
    have source := leadingFixedCompact_fixed_values_eval fixedFieldCount 0
      row.fixed (by simpa using hfixed) hnonempty
      (some UnaryFrameSym.frameEnd) none
      (encodeAffineExactlyOneCompactFamily row.frames ++
        UnaryFrameSym.frameEnd :: tail)
      ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
    simpa [afterLeading, afterFixed] using source
  let afterCollect :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      .expectFrame (some UnaryFrameSym.frameEnd) none false tail
      ((encodeUnaryFrame row.fixed).reverse ++
        ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output)) []
      (encodeAffineExactlyOneCompactFamily row.frames).reverse [] []
  have hcollect : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterFixed (some afterCollect)
      (2 * (encodeAffineExactlyOneCompactFamily row.frames).length + 1) := by
    refine ⟨⟨2 * (encodeAffineExactlyOneCompactFamily row.frames).length + 1,
      ?_⟩, le_rfl⟩
    have source := leadingFixedCompact_collect_eval fixedFieldCount
      (encodeAffineExactlyOneCompactFamily row.frames) tail
      ((encodeUnaryFrame row.fixed).reverse ++
        ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output))
      (leadingFixedCompact_compact_no_frameEnd row.frames)
      (some .separator) none []
    simpa [afterFixed, afterCollect] using source
  let beforeFinishRow :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      .finishRow (some UnaryFrameSym.frameEnd) none false tail
      ((encodeAffineExactlyOneOutputSourceInvocationFamily
          row.frames.reverse).reverse ++
        ((encodeUnaryFrame row.fixed).reverse ++
          ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output)))
      [] [] [] []
  have hframes : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) afterCollect (some beforeFinishRow)
      (affineExactlyOneLeadingFixedCompactFramesSteps row.frames.reverse + 1) := by
    have source := leadingFixedCompact_frames_run fixedFieldCount
      row.frames.reverse (some UnaryFrameSym.frameEnd) none tail
      ((encodeUnaryFrame row.fixed).reverse ++
        ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output))
    simpa [afterCollect, beforeFinishRow,
      encodeAffineExactlyOneCompactFamily_reverse] using source
  have hfinish : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) beforeFinishRow
      (some (affineExactlyOneLeadingFixedCompactProjectionLoopCfg
        fixedFieldCount tail
        (UnaryFrameSym.frameEnd ::
          ((encodeAffineExactlyOneOutputSourceInvocationFamily
              row.frames.reverse).reverse ++
            ((encodeUnaryFrame row.fixed).reverse ++
              ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++
                output)))))) 2 := by
    let afterPush :=
      affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
        .clearRowEnd (some UnaryFrameSym.frameEnd) none false tail
        (UnaryFrameSym.frameEnd ::
          ((encodeAffineExactlyOneOutputSourceInvocationFamily
              row.frames.reverse).reverse ++
            ((encodeUnaryFrame row.fixed).reverse ++
              ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++ output))))
        [] [] [] []
    have hpush : EvalsToInTime
        (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount)) beforeFinishRow (some afterPush) 1 :=
      ⟨⟨1, rfl⟩, le_rfl⟩
    have hclear : EvalsToInTime
        (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount)) afterPush
        (some (affineExactlyOneLeadingFixedCompactProjectionLoopCfg
          fixedFieldCount tail
          (UnaryFrameSym.frameEnd ::
            ((encodeAffineExactlyOneOutputSourceInvocationFamily
                row.frames.reverse).reverse ++
              ((encodeUnaryFrame row.fixed).reverse ++
                ((row.leading ++ [UnaryFrameSym.frameEnd]).reverse ++
                  output)))))) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
    simpa using EvalsToInTime.trans
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) 1 1 _ afterPush _ hpush hclear
  let h₁ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount))
    (2 * (row.leading.length + 1))
    (2 * (encodeUnaryFrame row.fixed).length)
    _ afterLeading _ hleadingRun hfixedRun
  let h₂ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _
    (2 * (encodeAffineExactlyOneCompactFamily row.frames).length + 1)
    _ afterFixed _ h₁ hcollect
  let h₃ := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _
    (affineExactlyOneLeadingFixedCompactFramesSteps row.frames.reverse + 1)
    _ afterCollect _ h₂ hframes
  let full := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount)) _ 2 _ beforeFinishRow _ h₃ hfinish
  convert full using 1 <;>
    simp [affineExactlyOneLeadingFixedCompactRowSteps,
      List.reverse_append, List.append_assoc] <;> omega

/-- Family runtime before the final empty-input dispatch and halt. -/
def affineExactlyOneLeadingFixedCompactFamilySteps
    (rows : List AffineExactlyOneLeadingFixedCompactProjectionRow) : Nat :=
  (rows.map affineExactlyOneLeadingFixedCompactRowSteps).sum

private def leadingFixedCompact_rows_run
    (fixedFieldCount : Nat)
    (rows : List AffineExactlyOneLeadingFixedCompactProjectionRow)
    (hfixed : ∀ row ∈ rows, row.fixed.length = fixedFieldCount)
    (hleading : ∀ row ∈ rows, ∀ symbol ∈ row.leading,
      symbol ≠ UnaryFrameSym.frameEnd)
    (output : List UnaryFrameSym) (hnonempty : 0 < fixedFieldCount) :
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (affineExactlyOneLeadingFixedCompactProjectionLoopCfg fixedFieldCount
        (rows.flatMap fun row =>
          row.leading ++ [UnaryFrameSym.frameEnd] ++
            encodeUnaryFrame row.fixed ++
            encodeAffineExactlyOneCompactFamily row.frames ++
            [UnaryFrameSym.frameEnd])
        output)
      (some (affineExactlyOneLeadingFixedCompactProjectionLoopCfg
        fixedFieldCount []
        ((rows.flatMap fun row =>
          row.leading ++ [UnaryFrameSym.frameEnd] ++ encodeUnaryFrame row.fixed ++
            encodeAffineExactlyOneOutputSourceInvocationFamily
              row.frames.reverse ++ [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (affineExactlyOneLeadingFixedCompactFamilySteps rows) := by
  induction rows generalizing output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons row rest ih =>
      let restInput := rest.flatMap fun item =>
        item.leading ++ [UnaryFrameSym.frameEnd] ++
          encodeUnaryFrame item.fixed ++
          encodeAffineExactlyOneCompactFamily item.frames ++
          [UnaryFrameSym.frameEnd]
      have hrowFixed := hfixed row (by simp)
      have hrowLeading := hleading row (by simp)
      have hrestFixed : ∀ item ∈ rest,
          item.fixed.length = fixedFieldCount := by
        intro item hitem
        exact hfixed item (by simp [hitem])
      have hrestLeading : ∀ item ∈ rest, ∀ symbol ∈ item.leading,
          symbol ≠ UnaryFrameSym.frameEnd := by
        intro item hitem symbol hsymbol
        exact hleading item (by simp [hitem]) symbol hsymbol
      have hrow := leadingFixedCompact_row_run fixedFieldCount row
        hrowFixed hrowLeading restInput output hnonempty
      let rowOutput :=
        (row.leading ++ [UnaryFrameSym.frameEnd] ++ encodeUnaryFrame row.fixed ++
          encodeAffineExactlyOneOutputSourceInvocationFamily
            row.frames.reverse ++ [UnaryFrameSym.frameEnd]).reverse ++ output
      have hrest := ih hrestFixed hrestLeading rowOutput
      let full := EvalsToInTime.trans
        (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount))
        (affineExactlyOneLeadingFixedCompactRowSteps row)
        (affineExactlyOneLeadingFixedCompactFamilySteps rest)
        _ _ _ (by simpa [restInput, List.append_assoc] using hrow)
        (by simpa [restInput, rowOutput] using hrest)
      convert full using 1 <;>
        simp [List.reverse_append, List.append_assoc,
          affineExactlyOneLeadingFixedCompactFamilySteps] <;> omega

/-- Complete runtime including empty-input dispatch and halt. -/
def affineExactlyOneLeadingFixedCompactProjectionSteps
    {fixedFieldCount : Nat}
    (family : AffineExactlyOneLeadingFixedCompactProjectionFamily
      fixedFieldCount) : Nat :=
  affineExactlyOneLeadingFixedCompactFamilySteps family.rows + 2

/-- The fixed controller emits the exact reverse family output. -/
def affineExactlyOneLeadingFixedCompactProjectionRev_run
    (fixedFieldCount : Nat)
    (family : AffineExactlyOneLeadingFixedCompactProjectionFamily
      fixedFieldCount)
    (hnonempty : 0 < fixedFieldCount) :
    EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (initialCfg
        (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount)
        (encodeAffineExactlyOneLeadingFixedCompactProjectionInput family))
      (some (haltCfg
        (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount)
        (encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
          family).reverse))
      (affineExactlyOneLeadingFixedCompactProjectionSteps family) := by
  have hrows := leadingFixedCompact_rows_run fixedFieldCount family.rows
    family.fixed_lengths family.leading_frameEnd_free [] hnonempty
  let beforeHalt :=
    affineExactlyOneLeadingFixedCompactProjectionCfg fixedFieldCount
      .leading none none false []
      (encodeAffineExactlyOneLeadingFixedCompactProjectionOutput family).reverse
      [] [] [] []
  have hsource : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount))
      (initialCfg
        (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount)
        (encodeAffineExactlyOneLeadingFixedCompactProjectionInput family))
      (some beforeHalt)
      (affineExactlyOneLeadingFixedCompactFamilySteps family.rows) := by
    simpa [initialCfg,
      affineExactlyOneLeadingFixedCompactProjectionRevProgram,
      affineExactlyOneLeadingFixedCompactProjectionLoopCfg,
      affineExactlyOneLeadingFixedCompactProjectionCfg,
      encodeAffineExactlyOneLeadingFixedCompactProjectionInput,
      encodeAffineExactlyOneLeadingFixedCompactProjectionOutput,
      beforeHalt] using hrows
  have hhalt : EvalsToInTime
      (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount)) beforeHalt
      (some (haltCfg
        (affineExactlyOneLeadingFixedCompactProjectionRevProgram
          fixedFieldCount)
        (encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
          family).reverse)) 2 := by
    refine ⟨⟨2, ?_⟩, le_rfl⟩
    rfl
  let full := EvalsToInTime.trans
    (step (affineExactlyOneLeadingFixedCompactProjectionRevProgram
      fixedFieldCount))
    (affineExactlyOneLeadingFixedCompactFamilySteps family.rows) 2
    _ beforeHalt _ hsource hhalt
  simpa [affineExactlyOneLeadingFixedCompactProjectionSteps,
    Nat.add_comm] using full

private theorem leadingFixedCompact_compact_reverse_length
    (frames : List AffineExactlyOneFrame) :
    (encodeAffineExactlyOneCompactFamily frames.reverse).length =
      (encodeAffineExactlyOneCompactFamily frames).length := by
  have hreverse := congrArg List.length
    (encodeAffineExactlyOneCompactFamily_reverse frames)
  have hstream :=
    encodeAffineExactlyOneReversedCompactFrameStream_length frames.reverse
  simpa using (hreverse.trans hstream).symm

theorem affineExactlyOneLeadingFixedCompactFramesSteps_le
    (frames : List AffineExactlyOneFrame) :
    affineExactlyOneLeadingFixedCompactFramesSteps frames ≤
      4 * (encodeAffineExactlyOneCompactFamily frames).length := by
  have source := affineExactlyOneMarkedRowFramesSteps_le frames
  have hstep : affineExactlyOneLeadingFixedCompactFrameSteps =
      affineExactlyOneMarkedRowFrameSteps := by
    funext frame
    rfl
  simpa only [affineExactlyOneLeadingFixedCompactFramesSteps,
    hstep, affineExactlyOneMarkedRowFramesSteps] using source

private def encodeAffineExactlyOneLeadingFixedCompactProjectionRowInput
    (row : AffineExactlyOneLeadingFixedCompactProjectionRow) :
    List UnaryFrameSym :=
  row.leading ++ [UnaryFrameSym.frameEnd] ++ encodeUnaryFrame row.fixed ++
    encodeAffineExactlyOneCompactFamily row.frames ++
    [UnaryFrameSym.frameEnd]

theorem affineExactlyOneLeadingFixedCompactRowSteps_le
    (row : AffineExactlyOneLeadingFixedCompactProjectionRow) :
    affineExactlyOneLeadingFixedCompactRowSteps row ≤
      6 *
        (encodeAffineExactlyOneLeadingFixedCompactProjectionRowInput row).length := by
  have hframes :=
    affineExactlyOneLeadingFixedCompactFramesSteps_le row.frames.reverse
  rw [leadingFixedCompact_compact_reverse_length] at hframes
  simp only [affineExactlyOneLeadingFixedCompactRowSteps,
    encodeAffineExactlyOneLeadingFixedCompactProjectionRowInput,
    List.length_append, List.length_singleton]
  omega

theorem affineExactlyOneLeadingFixedCompactFamilySteps_le
    (rows : List AffineExactlyOneLeadingFixedCompactProjectionRow) :
    affineExactlyOneLeadingFixedCompactFamilySteps rows ≤
      6 * (rows.flatMap
        encodeAffineExactlyOneLeadingFixedCompactProjectionRowInput).length := by
  induction rows with
  | nil => simp [affineExactlyOneLeadingFixedCompactFamilySteps]
  | cons row rest ih =>
      have hrow := affineExactlyOneLeadingFixedCompactRowSteps_le row
      rw [show affineExactlyOneLeadingFixedCompactFamilySteps (row :: rest) =
          affineExactlyOneLeadingFixedCompactRowSteps row +
            affineExactlyOneLeadingFixedCompactFamilySteps rest by
        simp [affineExactlyOneLeadingFixedCompactFamilySteps]]
      rw [show ((row :: rest).flatMap
            encodeAffineExactlyOneLeadingFixedCompactProjectionRowInput).length =
          (encodeAffineExactlyOneLeadingFixedCompactProjectionRowInput row).length +
            (rest.flatMap
              encodeAffineExactlyOneLeadingFixedCompactProjectionRowInput).length by
        simp]
      omega

theorem affineExactlyOneLeadingFixedCompactProjectionSteps_le
    {fixedFieldCount : Nat}
    (family : AffineExactlyOneLeadingFixedCompactProjectionFamily
      fixedFieldCount) :
    affineExactlyOneLeadingFixedCompactProjectionSteps family ≤
      6 *
        (encodeAffineExactlyOneLeadingFixedCompactProjectionInput family).length +
      2 := by
  have hfamily :=
    affineExactlyOneLeadingFixedCompactFamilySteps_le family.rows
  simpa [affineExactlyOneLeadingFixedCompactProjectionSteps,
    encodeAffineExactlyOneLeadingFixedCompactProjectionInput,
    encodeAffineExactlyOneLeadingFixedCompactProjectionRowInput] using
    Nat.add_le_add_right hfamily 2

noncomputable def
    affineExactlyOneLeadingFixedCompactProjectionRev_computableInPolyTime
    (fixedFieldCount : Nat) (hnonempty : 0 < fixedFieldCount) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneLeadingFixedCompactProjectionInput id
      (fun family : AffineExactlyOneLeadingFixedCompactProjectionFamily
          fixedFieldCount =>
        (encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
          family).reverse) where
  tm := compile
    (affineExactlyOneLeadingFixedCompactProjectionRevProgram fixedFieldCount)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X + 2
  outputsFun := fun family => by
    have builderRun :=
      affineExactlyOneLeadingFixedCompactProjectionRev_run
        fixedFieldCount family hnonempty
    have compiledRun := compile_evalsToInTime
      (affineExactlyOneLeadingFixedCompactProjectionRevProgram
        fixedFieldCount) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile
          (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)).step
        (_root_.Turing.initList
          (compile
            (affineExactlyOneLeadingFixedCompactProjectionRevProgram
              fixedFieldCount))
          (encodeAffineExactlyOneLeadingFixedCompactProjectionInput family))
        (some (_root_.Turing.haltList
          (compile
            (affineExactlyOneLeadingFixedCompactProjectionRevProgram
              fixedFieldCount))
          (encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
            family).reverse))
        (affineExactlyOneLeadingFixedCompactProjectionSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : affineExactlyOneLeadingFixedCompactProjectionSteps family ≤
        (6 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneLeadingFixedCompactProjectionInput
            family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineExactlyOneLeadingFixedCompactProjectionSteps_le family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile
          (affineExactlyOneLeadingFixedCompactProjectionRevProgram
            fixedFieldCount)).step
        (_root_.Turing.initList
          (compile
            (affineExactlyOneLeadingFixedCompactProjectionRevProgram
              fixedFieldCount))
          (encodeAffineExactlyOneLeadingFixedCompactProjectionInput family))
        (some (_root_.Turing.haltList
          (compile
            (affineExactlyOneLeadingFixedCompactProjectionRevProgram
              fixedFieldCount))
          (encodeAffineExactlyOneLeadingFixedCompactProjectionOutput
            family).reverse))
        ((6 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneLeadingFixedCompactProjectionInput
            family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-output polynomial-time interface. -/
noncomputable def
    affineExactlyOneLeadingFixedCompactProjection_computableInPolyTime
    (fixedFieldCount : Nat) (hnonempty : 0 < fixedFieldCount) :
    _root_.Turing.TM2ComputableInPolyTime
      (fun family : AffineExactlyOneLeadingFixedCompactProjectionFamily
          fixedFieldCount =>
        encodeAffineExactlyOneLeadingFixedCompactProjectionInput family)
      id
      (fun family : AffineExactlyOneLeadingFixedCompactProjectionFamily
          fixedFieldCount =>
        encodeAffineExactlyOneLeadingFixedCompactProjectionOutput family) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineExactlyOneLeadingFixedCompactProjectionRev_computableInPolyTime
        fixedFieldCount hnonempty)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
