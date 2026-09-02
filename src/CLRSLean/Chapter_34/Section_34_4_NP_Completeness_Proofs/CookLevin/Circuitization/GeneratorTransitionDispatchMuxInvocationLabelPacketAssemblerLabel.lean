import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerTerminal
import Mathlib.Tactic

/-!
# Whole-label dispatch-mux packet assembly

This module composes the local coordinate zipper over three aligned runtime
rows.  It proves that one loaded four-row label packet is consumed by the
fixed assembler and replaced byte-for-byte by the canonical Cook--Levin mux
invocation source for that label.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Source emitted by a suffix of a label.  The initial suffix emits a
header-only segment when empty; a proper suffix emits nothing when empty. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerRows
    (selector : Nat) (first : Bool) :
    List AffineMuxFinPairFrame → List UnaryFrameSym
  | [] => if first then
      encodeUnaryFrame [selector, 0, 1] ++ [.frameEnd]
    else []
  | frame :: frames =>
      affineMuxInvocationSingletonSourceFrames selector first frame ++
        transitionDispatchMuxInvocationLabelPacketAssemblerRows
          selector false frames

private theorem transitionDispatchMuxInvocationLabelPacketAssemblerRows_false
    (selector : Nat) (frames : List AffineMuxFinPairFrame) :
    transitionDispatchMuxInvocationLabelPacketAssemblerRows selector false
        frames =
      frames.flatMap
        (affineMuxInvocationSingletonSourceFrames selector false) := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      simp [transitionDispatchMuxInvocationLabelPacketAssemblerRows, ih]

/-- At the initial label boundary the suffix formula is the canonical label
source formula. -/
theorem transitionDispatchMuxInvocationLabelPacketAssemblerRows_true
    (selector : Nat) (frames : List AffineMuxFinPairFrame) :
    transitionDispatchMuxInvocationLabelPacketAssemblerRows selector true
        frames =
      transitionDispatchMuxInvocationLabelSourceRows selector frames := by
  cases frames with
  | nil => rfl
  | cons frame frames =>
      simp [transitionDispatchMuxInvocationLabelPacketAssemblerRows,
        transitionDispatchMuxInvocationLabelSourceRows,
        transitionDispatchMuxInvocationLabelPacketAssemblerRows_false]

/-- Exact running time for a suffix of aligned mux coordinates. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
    (selector : Nat) (first : Bool) :
    List AffineMuxFinPairFrame → Nat
  | [] => if first then
      transitionDispatchMuxInvocationLabelPacketAssemblerEmptySteps selector
    else
      transitionDispatchMuxInvocationLabelPacketAssemblerFinishSteps selector
  | frame :: frames =>
      transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps
          selector frame +
        transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
          selector false frames

/-- The controller invariant at the start of a coordinate suffix. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg
    (selector : Nat) (first : Bool)
    (coordinates : List (Nat × Nat × Nat))
    (whenTrue whenFalse : List Nat)
    (tail output : List UnaryFrameSym) :
    BuilderCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :=
  transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.coordinateCheck first)
    (if first then some .frameEnd else some .separator)
    (if first then none else some .separator) false
    (encodeUnaryFrame whenFalse ++ .frameEnd :: tail) output
    (transitionDispatchMuxCoordinateRowFrames coordinates)
    (encodeUnaryFrame whenTrue) (List.replicate selector ()) [] []

/-- Reconstructed affine frames for three raw coordinate-indexed rows. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerFrames
    (selector : Nat) (coordinates : List (Nat × Nat × Nat))
    (whenTrue whenFalse : List Nat) : List AffineMuxFinPairFrame :=
  ({ selector := selector
     coordinates := coordinates
     whenTrue := whenTrue
     whenFalse := whenFalse } : TransitionDispatchMuxInvocationView).frames

/-- Exact execution over any three equally long coordinate-indexed rows. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_rows
    (selector : Nat) (first : Bool)
    (coordinates : List (Nat × Nat × Nat))
    (whenTrue whenFalse : List Nat)
    (tail output : List UnaryFrameSym)
    (htrue : coordinates.length = whenTrue.length)
    (hfalse : coordinates.length = whenFalse.length) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg
        selector first coordinates whenTrue whenFalse tail output)
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg tail
        ((transitionDispatchMuxInvocationLabelPacketAssemblerRows selector
          first (transitionDispatchMuxInvocationLabelPacketAssemblerFrames
            selector coordinates whenTrue whenFalse)
          ).reverse ++ output)))
      (transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps selector
        first (transitionDispatchMuxInvocationLabelPacketAssemblerFrames
          selector coordinates whenTrue whenFalse)) := by
  induction coordinates generalizing first whenTrue whenFalse output with
  | nil =>
      have htrueNil : whenTrue = [] := by simpa using htrue.symm
      have hfalseNil : whenFalse = [] := by simpa using hfalse.symm
      subst whenTrue
      subst whenFalse
      cases first with
      | false =>
          simpa [transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg,
            transitionDispatchMuxInvocationLabelPacketAssemblerRows,
            transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps,
            transitionDispatchMuxInvocationLabelPacketAssemblerFrames,
            TransitionDispatchMuxInvocationView.frames, encodeUnaryFrame,
            transitionDispatchMuxCoordinateRowFrames,
            transitionDispatchMuxInvocationLabelPacketAssemblerFinishStartCfg]
            using
              transitionDispatchMuxInvocationLabelPacketAssembler_finish
                selector tail output
      | true =>
          simpa [transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg,
            transitionDispatchMuxInvocationLabelPacketAssemblerRows,
            transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps,
            transitionDispatchMuxInvocationLabelPacketAssemblerFrames,
            TransitionDispatchMuxInvocationView.frames, encodeUnaryFrame,
            transitionDispatchMuxCoordinateRowFrames,
            transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg,
            transitionDispatchMuxInvocationLabelSourceRows]
            using
              transitionDispatchMuxInvocationLabelPacketAssembler_empty
                selector tail output
  | cons coordinate coordinates ih =>
      cases whenTrue with
      | nil => simp at htrue
      | cons whenTrue whenTrueTail =>
          cases whenFalse with
          | nil => simp at hfalse
          | cons whenFalse whenFalseTail =>
              have htrueTail : coordinates.length = whenTrueTail.length := by
                simpa using Nat.succ.inj htrue
              have hfalseTail : coordinates.length = whenFalseTail.length := by
                simpa using Nat.succ.inj hfalse
              let frame : AffineMuxFinPairFrame :=
                { whenTrue := whenTrue
                  whenFalse := whenFalse
                  selector := selector
                  selectorNot := coordinate.1
                  trueArm := coordinate.2.1
                  falseArm := coordinate.2.2 }
              let coordinateOutput :=
                (affineMuxInvocationSingletonSourceFrames selector first
                  frame).reverse ++ output
              have hcoordinate : EvalsToInTime
                  (step
                    transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
                  (transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg
                    selector first (coordinate :: coordinates)
                    (whenTrue :: whenTrueTail) (whenFalse :: whenFalseTail)
                    tail output)
                  (some
                    (transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg
                      selector false coordinates whenTrueTail whenFalseTail tail
                      coordinateOutput))
                  (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps
                    selector frame) := by
                simpa [transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg,
                  transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateStartFromCfg,
                  transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateFinishCfg,
                  transitionDispatchMuxCoordinateRowFrames, encodeUnaryFrame,
                  frame, coordinateOutput, List.append_assoc] using
                  transitionDispatchMuxInvocationLabelPacketAssembler_coordinate_from
                    selector first frame
                    (transitionDispatchMuxCoordinateRowFrames coordinates)
                    (encodeUnaryFrame whenTrueTail)
                    (encodeUnaryFrame whenFalseTail ++ .frameEnd :: tail)
                    output
                    (if first then some .frameEnd else some .separator)
                    (if first then none else some .separator) false
              have htail := ih (first := false)
                (whenTrue := whenTrueTail) (whenFalse := whenFalseTail)
                (output := coordinateOutput) htrueTail hfalseTail
              let full := EvalsToInTime.trans
                (step
                  transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
                (transitionDispatchMuxInvocationLabelPacketAssemblerCoordinateSteps
                  selector frame)
                (transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
                  selector false
                  (transitionDispatchMuxInvocationLabelPacketAssemblerFrames
                    selector coordinates whenTrueTail whenFalseTail))
                _
                (transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg
                  selector false coordinates whenTrueTail whenFalseTail tail
                  coordinateOutput)
                _ hcoordinate htail
              convert full using 1 <;>
                simp [transitionDispatchMuxInvocationLabelPacketAssemblerFrames,
                  TransitionDispatchMuxInvocationView.frames,
                  List.zipWith3,
                transitionDispatchMuxInvocationLabelPacketAssemblerRows,
                transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps,
                frame, coordinateOutput, List.reverse_append,
                  List.append_assoc] <;>
                omega

/-- A well-formed loaded label packet is assembled into its exact canonical
source rows and returns to the clean next-label boundary. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_label
    (view : TransitionDispatchMuxInvocationView)
    (tail output : List UnaryFrameSym) (haligned : view.RowAligned) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
        view tail output)
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg tail
        ((transitionDispatchMuxInvocationLabelSourceRows
          view.selector view.frames).reverse ++ output)))
      (transitionDispatchMuxInvocationLabelPacketAssemblerRowsSteps
        view.selector true view.frames) := by
  rcases view with ⟨selector, coordinates, whenTrue, whenFalse⟩
  rcases haligned with ⟨htrue, hfalse⟩
  simpa [transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg,
    transitionDispatchMuxInvocationLabelPacketAssemblerRowsStartCfg,
    transitionDispatchMuxInvocationLabelPacketAssemblerFrames,
    transitionDispatchMuxInvocationLabelPacketAssemblerRows_true] using
    transitionDispatchMuxInvocationLabelPacketAssembler_rows
      selector true coordinates whenTrue whenFalse tail
      output htrue hfalse

end CLRS.Chapter34.Turing.CookLevin
