import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorLabelChannels

/-!
# Row-level source formula for one dispatch-mux label

The final label reassembler must emit the source accepted by the generic
affine mux controller.  This module unfolds that source to the exact bytes a
local TM2 must write.  The empty-coordinate case emits one header-only
segment; otherwise the first coordinate carries the header flag and every
remaining coordinate emits a header-free singleton segment.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Explicit bytes of one nonempty singleton mux segment. -/
def affineMuxInvocationSingletonSourceFrames
    (selector : Nat) (emitsHeader : Bool)
    (frame : AffineMuxFinPairFrame) : List UnaryFrameSym :=
  encodeUnaryFrame
      [selector, frame.selectorNot, if emitsHeader then 1 else 0] ++
    encodeUnaryFrame [frame.whenTrue, frame.whenFalse, frame.trueArm] ++
    [.frameEnd]

/-- The degenerate empty mux is a single header row followed immediately by
the segment boundary. -/
theorem affineMuxInvocationEmptySegment_sourceFrames
    (selector : Nat) :
    (affineMuxInvocationEmptySegment selector).sourceFrames =
      encodeUnaryFrame [selector, 0, 1] ++ [.frameEnd] := by
  simp [AffineMuxInvocationProgression.sourceFrames,
    affineMuxInvocationEmptySegment,
    AffineMuxInvocationProgression.headerProgression,
    AffineMuxInvocationProgression.dataProgression,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionRows,
    affineUnaryTripleProgressionRowsFrom,
    affineUnaryTripleRowValues]

/-- A singleton segment expands to one explicit header triple, one explicit
data triple, and its physical segment boundary. -/
theorem affineMuxInvocationSingletonSegment_sourceFrames
    (selector : Nat) (emitsHeader : Bool)
    (frame : AffineMuxFinPairFrame) :
    (affineMuxInvocationSingletonSegment selector emitsHeader frame).sourceFrames =
      affineMuxInvocationSingletonSourceFrames selector emitsHeader frame := by
  simp [AffineMuxInvocationProgression.sourceFrames,
    affineMuxInvocationSingletonSegment,
    affineMuxInvocationSingletonSourceFrames,
    AffineMuxInvocationProgression.headerProgression,
    AffineMuxInvocationProgression.dataProgression,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleProgressionRows,
    affineUnaryTripleProgressionRowsFrom,
    affineUnaryTripleRowValues]
  rfl

private theorem affineMuxInvocationSingletonSegments_tail_sourceFrames
    (selector : Nat) (frames : List AffineMuxFinPairFrame) :
    (frames.map
        (affineMuxInvocationSingletonSegment selector false)).flatMap
        AffineMuxInvocationProgression.sourceFrames =
      frames.flatMap
        (affineMuxInvocationSingletonSourceFrames selector false) := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [affineMuxInvocationSingletonSegment_sourceFrames, ih]

/-- Exact row program for the singleton-segment source of one mux view. -/
def transitionDispatchMuxInvocationLabelSourceRows (selector : Nat) :
    List AffineMuxFinPairFrame → List UnaryFrameSym
  | [] => encodeUnaryFrame [selector, 0, 1] ++ [.frameEnd]
  | frame :: frames =>
      affineMuxInvocationSingletonSourceFrames selector true frame ++
        frames.flatMap
          (affineMuxInvocationSingletonSourceFrames selector false)

/-- The abstract segment source of one reconstructed label is exactly the
explicit empty/first/rest row program above. -/
theorem TransitionDispatchMuxInvocationView.sourceFrames_eq_rows
    (view : TransitionDispatchMuxInvocationView) :
    view.sourceFrames =
      transitionDispatchMuxInvocationLabelSourceRows
        view.selector view.frames := by
  unfold TransitionDispatchMuxInvocationView.sourceFrames
    TransitionDispatchMuxInvocationView.invocationSegments
  cases hframes : view.frames with
  | nil =>
      simp [affineMuxInvocationSingletonSegments,
        transitionDispatchMuxInvocationLabelSourceRows,
        affineMuxInvocationEmptySegment_sourceFrames]
  | cons frame frames =>
      simp [affineMuxInvocationSingletonSegments,
        transitionDispatchMuxInvocationLabelSourceRows,
        affineMuxInvocationSingletonSegment_sourceFrames]
      exact affineMuxInvocationSingletonSegments_tail_sourceFrames
        view.selector frames

/-- Consequently the complete verifier dispatch source is a seed-major,
label-major concatenation of the explicit row programs. -/
theorem
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq_labelRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxDescriptorInvocationViews W.machine.tm
          seed).flatMap fun view =>
            transitionDispatchMuxInvocationLabelSourceRows
              view.selector view.frames := by
  rw [
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq_reassembledViews]
  apply List.flatMap_congr
  intro seed hseed
  apply List.flatMap_congr
  intro view hview
  exact view.sourceFrames_eq_rows

end CLRS.Chapter34.Turing.CookLevin
