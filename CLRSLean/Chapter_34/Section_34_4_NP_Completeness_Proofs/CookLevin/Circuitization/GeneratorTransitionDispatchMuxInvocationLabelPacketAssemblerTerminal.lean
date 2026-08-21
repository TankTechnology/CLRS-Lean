import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerCoordinate
import Mathlib.Tactic

/-!
# Terminal cases of dispatch-mux label-packet assembly

The coordinate zipper has two terminal cases.  An empty label emits the
canonical header-only affine-mux segment.  A nonempty label merely verifies
that the aligned true and false rows end together, clears the persistent
selector, and returns to the next-label loop boundary.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact cost of the empty-coordinate label case. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerEmptySteps
    (selector : Nat) : Nat :=
  2 * selector + 11

/-- Exact cost of closing a label after at least one coordinate. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerFinishSteps
    (selector : Nat) : Nat :=
  selector + 6

/-- Stable terminal boundary after the final nonempty coordinate. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerFinishStartCfg
    (selector : Nat) (tail output : List UnaryFrameSym) :
    BuilderCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :=
  transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.coordinateCheck false) (some .separator) (some .separator) false
    (.frameEnd :: tail) output [] [] (List.replicate selector ()) [] []

private theorem assemblerTerminal_clearSelector_eval
    (selector : Nat) (buffer₁ : Option UnaryFrameSym)
    (test : Bool) (input output : List UnaryFrameSym) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        selector + 2]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .clearSelector buffer₁ none test input output [] []
        (List.replicate selector ()) [] [])) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        input output) := by
  induction selector generalizing test with
  | zero => rfl
  | succ selector ih =>
      rw [show (selector + 1) + 2 = (selector + 2) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            selector + 2]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .clearSelector buffer₁ none true input output [] []
            (List.replicate selector ()) [] [])) = _
      exact ih (test := true)

/-- After a nonempty row has consumed all aligned values, the program checks
both row endings and returns to a clean next-label boundary. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_finish
    (selector : Nat) (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerFinishStartCfg
        selector tail output)
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        tail output))
      (transitionDispatchMuxInvocationLabelPacketAssemblerFinishSteps
        selector) := by
  let beforeClear := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    .clearSelector (some .frameEnd) none false tail output [] []
    (List.replicate selector ()) [] []
  have hprefix : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerFinishStartCfg
        selector tail output)
      (some beforeClear) 4 := ⟨⟨4, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeClear
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        tail output))
      (selector + 2) :=
    ⟨⟨selector + 2, by
      simpa [beforeClear] using
        assemblerTerminal_clearSelector_eval selector (some .frameEnd) false
          tail output⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    4 (selector + 2) _ beforeClear _ hprefix hclear
  convert full using 1 <;>
    simp [transitionDispatchMuxInvocationLabelPacketAssemblerFinishSteps] <;>
    omega

private theorem assemblerTerminal_emitEmptySelector_eval
    (selector : Nat) (buffer₁ : Option UnaryFrameSym)
    (test : Bool) (input output : List UnaryFrameSym) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * selector + 7]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .emitEmptySelector buffer₁ none test input output [] []
        (List.replicate selector ()) [] [])) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg input
        ((encodeUnaryFrame [selector, 0, 1] ++
          [UnaryFrameSym.frameEnd]).reverse ++
          output)) := by
  induction selector generalizing test output with
  | zero => rfl
  | succ selector ih =>
      rw [show 2 * (selector + 1) + 7 =
          (2 * selector + 7) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * selector + 7]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .emitEmptySelector buffer₁ none true input (.tick :: output)
            [] [] (List.replicate selector ()) [] [])) = _
      simpa [encodeUnaryFrame, encodeUnaryFrameBlock,
        List.replicate_succ, List.reverse_append, List.append_assoc] using
        ih (test := true) (output := .tick :: output)

/-- A loaded label with no coordinates emits exactly the degenerate
header-only source row and returns to the clean next-label boundary. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_empty
    (selector : Nat) (tail output : List UnaryFrameSym) :
    let view : TransitionDispatchMuxInvocationView :=
      { selector := selector
        coordinates := []
        whenTrue := []
        whenFalse := [] }
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
        view tail output)
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg tail
        ((transitionDispatchMuxInvocationLabelSourceRows selector []).reverse ++
          output)))
      (transitionDispatchMuxInvocationLabelPacketAssemblerEmptySteps
        selector) := by
  dsimp only
  let beforeEmit := transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    .emitEmptySelector (some .frameEnd) none false tail output [] []
    (List.replicate selector ()) [] []
  have hprefix : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
        { selector := selector
          coordinates := []
          whenTrue := []
          whenFalse := [] }
        tail output)
      (some beforeEmit) 4 := ⟨⟨4, rfl⟩, le_rfl⟩
  have hemit : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeEmit
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg tail
        ((transitionDispatchMuxInvocationLabelSourceRows selector []).reverse ++
          output)))
      (2 * selector + 7) :=
    ⟨⟨2 * selector + 7, by
      simpa [beforeEmit, transitionDispatchMuxInvocationLabelSourceRows] using
        assemblerTerminal_emitEmptySelector_eval selector (some .frameEnd)
          false tail output⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    4 (2 * selector + 7) _ beforeEmit _ hprefix hemit
  convert full using 1 <;>
    simp [transitionDispatchMuxInvocationLabelPacketAssemblerEmptySteps] <;>
    omega

end CLRS.Chapter34.Turing.CookLevin
