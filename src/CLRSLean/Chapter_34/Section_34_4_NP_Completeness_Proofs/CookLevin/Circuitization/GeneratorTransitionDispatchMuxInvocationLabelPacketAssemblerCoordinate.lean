import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerCore
import Mathlib.Tactic

/-!
# One-coordinate dispatch-mux packet assembly

This module proves the hard local zipper step of the final packet assembler.
Starting with one coordinate triple on `work₁`, its true value on `work₂`, and
its false value on the input, the fixed program emits exactly one canonical
affine-mux singleton source segment and restores the persistent selector.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Entry state for one aligned coordinate, allowing the two one-symbol
buffers and the test bit inherited from the preceding local phase.  The first
coordinate inherits the loading sentinels; later coordinates inherit the two
row separators. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateStartFromCfg
    (selector : Nat) (first : Bool) (frame : AffineMuxFinPairFrame)
    (coordinateTail trueTail falseTail output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    BuilderCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :=
  transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.coordinateCheck first) buffer₁ buffer₂ test
    (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) output
    (encodeUnaryFrame
        [frame.selectorNot, frame.trueArm, frame.falseArm] ++ coordinateTail)
    (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
    (List.replicate selector ()) [] []

/-- Clean-buffer specialization used by standalone one-coordinate clients. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateStartCfg
    (selector : Nat) (first : Bool) (frame : AffineMuxFinPairFrame)
    (coordinateTail trueTail falseTail output : List UnaryFrameSym) :
    BuilderCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :=
  transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateStartFromCfg
    selector first frame coordinateTail trueTail falseTail output none none false

/-- Exit state after one coordinate.  The next coordinate, if present, starts
at the same public loop boundary with only the aligned tails remaining. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateFinishCfg
    (selector : Nat) (first : Bool) (frame : AffineMuxFinPairFrame)
    (coordinateTail trueTail falseTail output : List UnaryFrameSym) :
    BuilderCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :=
  transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.coordinateCheck false) (some .separator) (some .separator) false
    falseTail
    ((affineMuxInvocationSingletonSourceFrames selector first frame).reverse ++
      output)
    coordinateTail trueTail (List.replicate selector ()) [] []

/-- Exact local transition count.  It is linear in the six runtime unary
values consumed or replayed by one coordinate. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps
    (selector : Nat) (frame : AffineMuxFinPairFrame) : Nat :=
  5 * selector + 4 * frame.selectorNot + 2 * frame.whenTrue +
    2 * frame.whenFalse + 2 * frame.trueArm + frame.falseArm + 17

private theorem assemblerCoordinate_replicate_append_cons {α : Type}
    (value : α) (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

@[simp] private theorem assemblerCoordinate_encodeBlock_reverse
    (value : Nat) :
    (encodeUnaryFrameBlock value).reverse =
      .separator :: List.replicate value .tick := by
  simp [encodeUnaryFrameBlock, List.reverse_append]

private theorem assemblerCoordinate_loadSelectorNot_eval
    (value : Nat) (first : Bool)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output tail work₂ : List UnaryFrameSym)
    (selector currentSelectorNot scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * value + 1]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.loadSelectorNot first) buffer₁ buffer₂ test input output
        (encodeUnaryFrameBlock value ++ tail) work₂ selector
        currentSelectorNot scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelector first) (some .separator) buffer₂ test input output
        tail work₂ selector
        (List.replicate value () ++ currentSelectorNot) scratch) := by
  induction value generalizing buffer₁ currentSelectorNot with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 =
          (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * value + 1]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            (.loadSelectorNot first) (some .tick) buffer₂ test input output
            (encodeUnaryFrameBlock value ++ tail) work₂ selector
            (() :: currentSelectorNot) scratch)) = _
      simpa only [List.replicate_succ,
        assemblerCoordinate_replicate_append_cons, List.cons_append] using
        ih (buffer₁ := some .tick)
          (currentSelectorNot := () :: currentSelectorNot)

private theorem assemblerCoordinate_copySelector_eval
    (selector : Nat) (first : Bool)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (selectorNot scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        3 * selector + 1]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelector first) buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate selector ()) selectorNot scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelectorBoundary first) buffer₁ buffer₂ false input
        (List.replicate selector .tick ++ output) work₁ work₂ [] selectorNot
        (List.replicate selector () ++ scratch)) := by
  induction selector generalizing test output scratch with
  | zero => rfl
  | succ selector ih =>
      rw [show 3 * (selector + 1) + 1 =
          (3 * selector + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            3 * selector + 1]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            (.emitSelector first) buffer₁ buffer₂ true input
            (.tick :: output) work₁ work₂ (List.replicate selector ())
            selectorNot (() :: scratch))) = _
      simpa only [List.replicate_succ,
        assemblerCoordinate_replicate_append_cons, List.cons_append] using
        ih (test := true) (output := .tick :: output)
          (scratch := () :: scratch)

private theorem assemblerCoordinate_restoreSelector_eval
    (selector : Nat) (first : Bool)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (currentSelector selectorNot : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * selector + 1]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.restoreSelector first) buffer₁ buffer₂ test input output work₁ work₂
        currentSelector selectorNot (List.replicate selector ()))) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelectorNot first) buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate selector () ++ currentSelector) selectorNot []) := by
  induction selector generalizing test currentSelector with
  | zero => rfl
  | succ selector ih =>
      rw [show 2 * (selector + 1) + 1 =
          (2 * selector + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * selector + 1]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            (.restoreSelector first) buffer₁ buffer₂ true input output work₁
            work₂ (() :: currentSelector) selectorNot
            (List.replicate selector ()))) = _
      simpa only [List.replicate_succ,
        assemblerCoordinate_replicate_append_cons, List.cons_append] using
        ih (test := true) (currentSelector := () :: currentSelector)

private def assemblerCoordinate_emitSelector
    (selector : Nat) (first : Bool)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (selectorNot : List Unit) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelector first) buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate selector ()) selectorNot [])
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelectorNot first) buffer₁ buffer₂ false input
        ((encodeUnaryFrameBlock selector).reverse ++ output) work₁ work₂
        (List.replicate selector ()) selectorNot []))
      (5 * selector + 3) := by
  let afterCopy := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.emitSelectorBoundary first) buffer₁ buffer₂ false input
    (List.replicate selector .tick ++ output) work₁ work₂ [] selectorNot
    (List.replicate selector ())
  let beforeRestore := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.restoreSelector first) buffer₁ buffer₂ false input
    (.separator :: List.replicate selector .tick ++ output) work₁ work₂ []
    selectorNot (List.replicate selector ())
  have hcopy : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelector first) buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate selector ()) selectorNot [])
      (some afterCopy) (3 * selector + 1) :=
    ⟨⟨3 * selector + 1, by
      simpa [afterCopy] using assemblerCoordinate_copySelector_eval selector
        first buffer₁ buffer₂ test input output work₁ work₂ selectorNot []⟩,
      le_rfl⟩
  have hseparator : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      afterCopy (some beforeRestore) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeRestore
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelectorNot first) buffer₁ buffer₂ false input
        ((encodeUnaryFrameBlock selector).reverse ++ output) work₁ work₂
        (List.replicate selector ()) selectorNot []))
      (2 * selector + 1) :=
    ⟨⟨2 * selector + 1, by
      simpa [beforeRestore, List.append_assoc] using
        assemblerCoordinate_restoreSelector_eval selector first buffer₁
          buffer₂ false input
          (.separator :: (List.replicate selector .tick ++ output))
          work₁ work₂ [] selectorNot⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    (3 * selector + 1) 1 _ afterCopy _ hcopy hseparator
  let full := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (2 * selector + 1) _ beforeRestore _ h₁ hrestore
  convert full using 1 <;> omega

private theorem assemblerCoordinate_emitSelectorNot_eval
    (value : Nat) (first : Bool)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (selector scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * value + 2]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitSelectorNot first) buffer₁ buffer₂ test input output work₁ work₂
        selector (List.replicate value ()) scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitHeaderFlag first) buffer₁ buffer₂ false input
        ((encodeUnaryFrameBlock value).reverse ++ output) work₁ work₂
        selector [] scratch) := by
  induction value generalizing test output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 2 =
          (2 * value + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * value + 2]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            (.emitSelectorNot first) buffer₁ buffer₂ true input
            (.tick :: output) work₁ work₂ selector
            (List.replicate value ()) scratch)) = _
      simpa only [assemblerCoordinate_encodeBlock_reverse,
        List.replicate_succ, assemblerCoordinate_replicate_append_cons,
        List.cons_append] using
        ih (test := true) (output := .tick :: output)

private theorem assemblerCoordinate_emitHeaderFlag_eval
    (first : Bool) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (selector selectorNot scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[2]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.emitHeaderFlag first) buffer₁ buffer₂ test input output work₁ work₂
        selector selectorNot scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadTrueValue buffer₁ buffer₂ test input
        ((encodeUnaryFrameBlock (if first then 1 else 0)).reverse ++ output)
        work₁ work₂ selector selectorNot scratch) := by
  cases first <;> rfl

private theorem assemblerCoordinate_emitTrue_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ tail : List UnaryFrameSym)
    (selector selectorNot scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * value + 2]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadTrueValue buffer₁ buffer₂ test input output work₁
        (encodeUnaryFrameBlock value ++ tail) selector selectorNot scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadFalseValue buffer₁ (some .separator) test input
        ((encodeUnaryFrameBlock value).reverse ++ output) work₁ tail selector
        selectorNot scratch) := by
  induction value generalizing buffer₂ output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 2 =
          (2 * value + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * value + 2]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .loadTrueValue buffer₁ (some .tick) test input (.tick :: output)
            work₁ (encodeUnaryFrameBlock value ++ tail) selector selectorNot
            scratch)) = _
      simpa only [assemblerCoordinate_encodeBlock_reverse,
        List.replicate_succ, assemblerCoordinate_replicate_append_cons,
        List.cons_append] using
        ih (buffer₂ := some .tick) (output := .tick :: output)

private theorem assemblerCoordinate_emitFalse_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (selector selectorNot scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * value + 2]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadFalseValue buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ work₂ selector
        selectorNot scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadTrueArm (some .separator) buffer₂ test tail
        ((encodeUnaryFrameBlock value).reverse ++ output) work₁ work₂ selector
        selectorNot scratch) := by
  induction value generalizing buffer₁ output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 2 =
          (2 * value + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * value + 2]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .loadFalseValue (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) (.tick :: output) work₁
            work₂ selector selectorNot scratch)) = _
      simpa only [assemblerCoordinate_encodeBlock_reverse,
        List.replicate_succ, assemblerCoordinate_replicate_append_cons,
        List.cons_append] using
        ih (buffer₁ := some .tick) (output := .tick :: output)

private theorem assemblerCoordinate_emitTrueArm_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output tail work₂ : List UnaryFrameSym)
    (selector selectorNot scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * value + 2]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadTrueArm buffer₁ buffer₂ test input output
        (encodeUnaryFrameBlock value ++ tail) work₂ selector selectorNot
        scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .discardFalseArm (some .separator) buffer₂ test input
        ((encodeUnaryFrameBlock value).reverse ++ output) tail work₂ selector
        selectorNot scratch) := by
  induction value generalizing buffer₁ output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 2 =
          (2 * value + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * value + 2]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .loadTrueArm (some .tick) buffer₂ test input (.tick :: output)
            (encodeUnaryFrameBlock value ++ tail) work₂ selector selectorNot
            scratch)) = _
      simpa only [assemblerCoordinate_encodeBlock_reverse,
        List.replicate_succ, assemblerCoordinate_replicate_append_cons,
        List.cons_append] using
        ih (buffer₁ := some .tick) (output := .tick :: output)

private theorem assemblerCoordinate_discardFalseArm_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output tail work₂ : List UnaryFrameSym)
    (selector selectorNot scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        value + 2]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .discardFalseArm buffer₁ buffer₂ test input output
        (encodeUnaryFrameBlock value ++ tail) work₂ selector selectorNot
        scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        (.coordinateCheck false) (some .separator) buffer₂ test input
        (.frameEnd :: output) tail work₂ selector selectorNot scratch) := by
  induction value generalizing buffer₁ with
  | zero => rfl
  | succ value ih =>
      rw [show (value + 1) + 2 = (value + 2) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            value + 2]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .discardFalseArm (some .tick) buffer₂ test input output
            (encodeUnaryFrameBlock value ++ tail) work₂ selector selectorNot
            scratch)) = _
      exact ih (buffer₁ := some .tick)

/-- Exact one-coordinate execution from arbitrary inherited one-symbol
buffers.  Every successful coordinate normalizes the buffers to the aligned
row separators and the test bit to `false`. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_coordinate_from
    (selector : Nat) (first : Bool) (frame : AffineMuxFinPairFrame)
    (coordinateTail trueTail falseTail output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateStartFromCfg
        selector first frame coordinateTail trueTail falseTail output buffer₁
        buffer₂ test)
      (some
        (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateFinishCfg
          selector first frame coordinateTail trueTail falseTail output))
      (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps
        selector frame) := by
  let afterCheck := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.loadSelectorNot first) buffer₁ buffer₂ test
    (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) output
    (encodeUnaryFrame [frame.selectorNot, frame.trueArm, frame.falseArm] ++
      coordinateTail)
    (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
    (List.replicate selector ()) [] []
  let afterSelectorNot := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.emitSelector first) (some .separator) buffer₂ test
    (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) output
    (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
    (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
    (List.replicate selector ()) (List.replicate frame.selectorNot ()) []
  let selectorOutput := (encodeUnaryFrameBlock selector).reverse ++ output
  let afterSelector := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.emitSelectorNot first) (some .separator) buffer₂ false
    (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) selectorOutput
    (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
    (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
    (List.replicate selector ()) (List.replicate frame.selectorNot ()) []
  let selectorNotOutput :=
    (encodeUnaryFrameBlock frame.selectorNot).reverse ++ selectorOutput
  let afterSelectorNotEmit :=
    transitionDispatchMuxInvocationLabelPacketAssemblerCfg
      (.emitHeaderFlag first) (some .separator) buffer₂ false
      (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) selectorNotOutput
      (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
      (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
      (List.replicate selector ()) [] []
  let headerOutput :=
    (encodeUnaryFrameBlock (if first then 1 else 0)).reverse ++
      selectorNotOutput
  let beforeTrue := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    .loadTrueValue (some .separator) buffer₂ false
    (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) headerOutput
    (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
    (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
    (List.replicate selector ()) [] []
  let trueOutput := (encodeUnaryFrameBlock frame.whenTrue).reverse ++ headerOutput
  let beforeFalse := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    .loadFalseValue (some .separator) (some .separator) false
    (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) trueOutput
    (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
    trueTail (List.replicate selector ()) [] []
  let falseOutput :=
    (encodeUnaryFrameBlock frame.whenFalse).reverse ++ trueOutput
  let beforeTrueArm := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    .loadTrueArm (some .separator) (some .separator) false falseTail
    falseOutput
    (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
    trueTail (List.replicate selector ()) [] []
  let trueArmOutput :=
    (encodeUnaryFrameBlock frame.trueArm).reverse ++ falseOutput
  let beforeDiscard := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    .discardFalseArm (some .separator) (some .separator) false falseTail
    trueArmOutput (encodeUnaryFrameBlock frame.falseArm ++ coordinateTail)
    trueTail (List.replicate selector ()) [] []
  have hcheck : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateStartFromCfg
        selector first frame coordinateTail trueTail falseTail output buffer₁
        buffer₂ test)
      (some afterCheck) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hloadSelectorNot : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      afterCheck (some afterSelectorNot) (2 * frame.selectorNot + 1) :=
    ⟨⟨2 * frame.selectorNot + 1, by
      simpa [afterCheck, afterSelectorNot, encodeUnaryFrame,
        List.append_assoc] using
        assemblerCoordinate_loadSelectorNot_eval frame.selectorNot first
          buffer₁ buffer₂ test
          (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) output
          (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
          (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
          (List.replicate selector ()) [] []⟩, le_rfl⟩
  have hemitSelector : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      afterSelectorNot (some afterSelector) (5 * selector + 3) := by
    simpa [afterSelectorNot, afterSelector, selectorOutput] using
      assemblerCoordinate_emitSelector selector first (some .separator) buffer₂
        test (encodeUnaryFrameBlock frame.whenFalse ++ falseTail) output
        (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
        (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
        (List.replicate frame.selectorNot ())
  have hemitSelectorNot : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      afterSelector (some afterSelectorNotEmit)
      (2 * frame.selectorNot + 2) :=
    ⟨⟨2 * frame.selectorNot + 2, by
      simpa [afterSelector, afterSelectorNotEmit, selectorOutput,
        selectorNotOutput] using
        assemblerCoordinate_emitSelectorNot_eval frame.selectorNot first
          (some .separator) buffer₂ false
          (encodeUnaryFrameBlock frame.whenFalse ++ falseTail)
          selectorOutput
          (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
          (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
          (List.replicate selector ()) []⟩, le_rfl⟩
  have hheader : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      afterSelectorNotEmit (some beforeTrue) 2 :=
    ⟨⟨2, by
      simpa [afterSelectorNotEmit, beforeTrue, selectorNotOutput,
        headerOutput] using
        assemblerCoordinate_emitHeaderFlag_eval first (some .separator) buffer₂
          false (encodeUnaryFrameBlock frame.whenFalse ++ falseTail)
          selectorNotOutput
          (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
          (encodeUnaryFrameBlock frame.whenTrue ++ trueTail)
          (List.replicate selector ()) [] []⟩, le_rfl⟩
  have htrue : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeTrue (some beforeFalse) (2 * frame.whenTrue + 2) :=
    ⟨⟨2 * frame.whenTrue + 2, by
      simpa [beforeTrue, beforeFalse, headerOutput, trueOutput] using
        assemblerCoordinate_emitTrue_eval frame.whenTrue (some .separator)
          buffer₂ false (encodeUnaryFrameBlock frame.whenFalse ++ falseTail)
          headerOutput
          (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
          trueTail (List.replicate selector ()) [] []⟩, le_rfl⟩
  have hfalse : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeFalse (some beforeTrueArm) (2 * frame.whenFalse + 2) :=
    ⟨⟨2 * frame.whenFalse + 2, by
      simpa [beforeFalse, beforeTrueArm, trueOutput, falseOutput] using
        assemblerCoordinate_emitFalse_eval frame.whenFalse (some .separator)
          (some .separator) false falseTail trueOutput
          (encodeUnaryFrame [frame.trueArm, frame.falseArm] ++ coordinateTail)
          trueTail (List.replicate selector ()) [] []⟩, le_rfl⟩
  have htrueArm : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeTrueArm (some beforeDiscard) (2 * frame.trueArm + 2) :=
    ⟨⟨2 * frame.trueArm + 2, by
      simpa [beforeTrueArm, beforeDiscard, falseOutput, trueArmOutput,
        encodeUnaryFrame, List.append_assoc] using
        assemblerCoordinate_emitTrueArm_eval frame.trueArm (some .separator)
          (some .separator) false falseTail falseOutput
          (encodeUnaryFrameBlock frame.falseArm ++ coordinateTail) trueTail
          (List.replicate selector ()) [] []⟩, le_rfl⟩
  have hdiscard : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeDiscard
      (some
        (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateFinishCfg
          selector first frame coordinateTail trueTail falseTail output))
      (frame.falseArm + 2) :=
    ⟨⟨frame.falseArm + 2, by
      simpa [beforeDiscard,
        transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateFinishCfg,
        trueArmOutput, falseOutput, trueOutput, headerOutput,
        selectorNotOutput, selectorOutput,
        affineMuxInvocationSingletonSourceFrames, encodeUnaryFrame,
        List.reverse_append, List.append_assoc] using
        assemblerCoordinate_discardFalseArm_eval frame.falseArm
          (some .separator) (some .separator) false falseTail trueArmOutput
          coordinateTail trueTail (List.replicate selector ()) [] []⟩,
      le_rfl⟩
  let h₁ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    1 (2 * frame.selectorNot + 1) _ afterCheck _ hcheck hloadSelectorNot
  let h₂ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (5 * selector + 3) _ afterSelectorNot _ h₁ hemitSelector
  let h₃ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (2 * frame.selectorNot + 2) _ afterSelector _ h₂ hemitSelectorNot
  let h₄ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ 2 _ afterSelectorNotEmit _ h₃ hheader
  let h₅ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (2 * frame.whenTrue + 2) _ beforeTrue _ h₄ htrue
  let h₆ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (2 * frame.whenFalse + 2) _ beforeFalse _ h₅ hfalse
  let h₇ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (2 * frame.trueArm + 2) _ beforeTrueArm _ h₆ htrueArm
  let full := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (frame.falseArm + 2) _ beforeDiscard _ h₇ hdiscard
  convert full using 1 <;>
    simp [transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps] <;>
    omega

/-- Clean-buffer specialization of the inherited-buffer coordinate theorem. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_coordinate
    (selector : Nat) (first : Bool) (frame : AffineMuxFinPairFrame)
    (coordinateTail trueTail falseTail output : List UnaryFrameSym) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateStartCfg
        selector first frame coordinateTail trueTail falseTail output)
      (some
        (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateFinishCfg
          selector first frame coordinateTail trueTail falseTail output))
      (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps
        selector frame) := by
  simpa [transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateStartCfg]
    using transitionDispatchMuxInvocationLabelPacketAssembler_coordinate_from
      selector first frame coordinateTail trueTail falseTail output none none
      false

end CLRS.Chapter34.Turing.CookLevin
