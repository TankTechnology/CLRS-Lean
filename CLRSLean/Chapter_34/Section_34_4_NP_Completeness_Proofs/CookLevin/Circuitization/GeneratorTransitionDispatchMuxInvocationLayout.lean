import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxOutput
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmLayout

/-!
# Reassembling complete dispatch-mux invocations

The raw-input transition sources expose the selector, fresh coordinates, true
arm, and false arm separately.  This file proves that those four views are a
lossless decomposition of every canonical dispatch mux.  In particular, the
exact delimiter-bearing `encodeAffineMuxFinFrames` payload is pinned to a
builder-free reconstruction, so the remaining source compiler has a precise
byte-level target rather than only four projection theorems.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The four operand views needed to reconstruct one whole-row mux. -/
structure TransitionDispatchMuxInvocationView where
  selector : Nat
  coordinates : List (Nat × Nat × Nat)
  whenTrue : List Nat
  whenFalse : List Nat
deriving DecidableEq, Repr

/-- Reconnect the fresh-coordinate, true-arm, and false-arm projections in
coordinate order.  `zipWith3` is intentional: canonical mux projections have
the same width, and this is the executable row-wise assembly operation. -/
def TransitionDispatchMuxInvocationView.frames
    (view : TransitionDispatchMuxInvocationView) :
    List AffineMuxFinPairFrame :=
  List.zipWith3
    (fun coordinates whenTrue whenFalse =>
      { whenTrue := whenTrue
        whenFalse := whenFalse
        selector := view.selector
        selectorNot := coordinates.1
        trueArm := coordinates.2.1
        falseArm := coordinates.2.2 })
    view.coordinates view.whenTrue view.whenFalse

/-- Exact delimiter-bearing controller payload reconstructed from the four
operand views. -/
def TransitionDispatchMuxInvocationView.encode
    (view : TransitionDispatchMuxInvocationView) : List UnaryFrameSym :=
  encodeAffineMuxFinFrames view.selector view.frames

/-- Forget one proof-carrying label artifact to the four independently
generated mux operand views. -/
def TransitionDispatchLabelArtifact.muxInvocationView
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) :
    TransitionDispatchMuxInvocationView :=
  { selector := artifact.selector
    coordinates := artifact.muxFreshLayout.coordinates
    whenTrue := artifact.muxTrueInputValues
    whenFalse := artifact.muxFalseInputValues }

private theorem muxFramesFromProjections_eq
    (selector : Nat) (frames : List AffineMuxFinPairFrame)
    (hselector : ∀ frame ∈ frames, frame.selector = selector) :
    TransitionDispatchMuxInvocationView.frames
        { selector := selector
          coordinates := frames.map fun frame =>
            (frame.selectorNot, frame.trueArm, frame.falseArm)
          whenTrue := frames.map fun frame => frame.whenTrue
          whenFalse := frames.map fun frame => frame.whenFalse } =
      frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      have hhead := hselector frame (by simp)
      have htail : ∀ other ∈ frames, other.selector = selector := by
        intro other hother
        exact hselector other (by simp [hother])
      rcases frame with
        ⟨whenTrue, whenFalse, frameSelector, selectorNot, trueArm,
          falseArm⟩
      change frameSelector = selector at hhead
      subst frameSelector
      simp only [List.map_cons, TransitionDispatchMuxInvocationView.frames,
        List.zipWith3]
      congr 1
      simpa only [TransitionDispatchMuxInvocationView.frames] using ih htail

/-- Every canonical finite mux repeats its header selector in every
coordinate frame. -/
theorem affineMuxFinCanonicalFrames_selector
    (start selector width : Nat)
    (whenTrue whenFalse : Fin width → CircuitBuilder.Wire) :
    ∀ frame ∈ affineMuxFinCanonicalFrames start selector width
        whenTrue whenFalse,
      frame.selector = selector := by
  induction width with
  | zero => simp [affineMuxFinCanonicalFrames]
  | succ width ih =>
      intro frame hframe
      rw [show affineMuxFinCanonicalFrames start selector (width + 1)
          whenTrue whenFalse =
        affineMuxFinCanonicalFrames start selector width
            (fun coordinate => whenTrue coordinate.castSucc)
            (fun coordinate => whenFalse coordinate.castSucc) ++
          [{ whenTrue := whenTrue (Fin.last width)
             whenFalse := whenFalse (Fin.last width)
             selector := selector
             selectorNot := start
             trueArm := start + 1 + 3 * width
             falseArm := start + 2 + 3 * width }] by rfl] at hframe
      rw [List.mem_append] at hframe
      rcases hframe with hprefix | hlast
      · exact ih _ _ frame hprefix
      · rw [List.mem_singleton] at hlast
        subst frame
        rfl

/-- The four projections of a canonical finite mux reassemble its complete
runtime frame list exactly, field for field. -/
theorem affineMuxFinCanonicalFrames_reassemble
    (start selector width : Nat)
    (whenTrue whenFalse : Fin width → CircuitBuilder.Wire) :
    let frames := affineMuxFinCanonicalFrames start selector width
      whenTrue whenFalse
    TransitionDispatchMuxInvocationView.frames
        { selector := selector
          coordinates := frames.map fun frame =>
            (frame.selectorNot, frame.trueArm, frame.falseArm)
          whenTrue := frames.map fun frame => frame.whenTrue
          whenFalse := frames.map fun frame => frame.whenFalse } =
      frames := by
  dsimp only
  exact muxFramesFromProjections_eq selector _
    (affineMuxFinCanonicalFrames_selector start selector width
      whenTrue whenFalse)

/-- Canonical label artifacts produced by the builder-free dispatch recursion
retain their shared selector in every mux coordinate. -/
theorem transitionDispatchLabelArtifacts_mux_selector_aligned
    (tm : _root_.Turing.FinTM2) (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height))
    (start : Nat) (fallback : CfgWires tm (workHeight tm height))
    (labels : List tm.Λ) :
    ∀ artifact ∈ transitionDispatchLabelArtifacts tm height falseWire
        trueWire source start fallback labels,
      ∀ frame ∈ artifact.muxFrames,
        frame.selector = artifact.selector := by
  induction labels generalizing start fallback with
  | nil => simp [transitionDispatchLabelArtifacts]
  | cons label labels ih =>
      intro artifact hartifact
      simp only [transitionDispatchLabelArtifacts, List.mem_cons] at hartifact
      rcases hartifact with rfl | htail
      · exact affineMuxFinCanonicalFrames_selector _ _ _ _ _
      · exact ih _ _ artifact htail

/-- Every seed-derived label artifact is recovered exactly from its four
operand views. -/
theorem transitionDispatchArtifactsFromSeed_muxInvocationView_frames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (artifact : TransitionDispatchLabelArtifact tm)
    (hartifact : artifact ∈ transitionDispatchArtifactsFromSeed tm seed) :
    artifact.muxInvocationView.frames = artifact.muxFrames := by
  unfold TransitionDispatchLabelArtifact.muxInvocationView
    TransitionDispatchLabelArtifact.muxFreshLayout
    TransitionDispatchLabelArtifact.muxTrueInputValues
    TransitionDispatchLabelArtifact.muxFalseInputValues
  apply muxFramesFromProjections_eq artifact.selector artifact.muxFrames
  exact transitionDispatchLabelArtifacts_mux_selector_aligned tm seed.height
    seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (seed.start + 2)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (programLabels tm) artifact hartifact

/-- Consequently the reconstructed byte stream is literally the canonical
mux-controller input, including its header and every internal delimiter. -/
theorem transitionDispatchArtifactsFromSeed_muxInvocationView_encode
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (artifact : TransitionDispatchLabelArtifact tm)
    (hartifact : artifact ∈ transitionDispatchArtifactsFromSeed tm seed) :
    artifact.muxInvocationView.encode =
      encodeAffineMuxFinFrames artifact.selector artifact.muxFrames := by
  unfold TransitionDispatchMuxInvocationView.encode
  rw [transitionDispatchArtifactsFromSeed_muxInvocationView_frames tm seed
    artifact hartifact]
  rfl

/-- Row-major reconstruction of every dispatch mux payload.  This is the
exact byte-level mux substream required by the complete transition script. -/
theorem transitionDispatchArtifactsFromSeed_muxInvocationViews_encode
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchArtifactsFromSeed tm seed).flatMap
        (fun artifact => artifact.muxInvocationView.encode) =
      (transitionDispatchArtifactsFromSeed tm seed).flatMap
        (fun artifact =>
          encodeAffineMuxFinFrames artifact.selector artifact.muxFrames) := by
  apply List.flatMap_congr
  intro artifact hartifact
  exact transitionDispatchArtifactsFromSeed_muxInvocationView_encode tm seed
    artifact hartifact

end CLRS.Chapter34.Turing.CookLevin
