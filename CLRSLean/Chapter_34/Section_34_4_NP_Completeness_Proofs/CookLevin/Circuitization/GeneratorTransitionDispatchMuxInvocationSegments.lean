import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineMuxInvocationProgressionControllerRuntime

/-!
# Concrete invocation segments for transition-dispatch muxes

This module instantiates the generic affine mux-invocation controller at the
actual proof-carrying Cook--Levin dispatch artifacts.  A singleton affine
segment is enough to represent an arbitrary canonical coordinate; the first
segment emits the shared mux header, while all later segments emit only their
coordinate frame.  The zero-width case is represented by one empty
header-only segment.

This deliberately separates the exact byte-level semantic bridge from the
later compression of singleton segments into longer affine spans.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One canonical mux coordinate represented as a length-one affine segment. -/
def affineMuxInvocationSingletonSegment (selector : Nat)
    (emitsHeader : Bool) (frame : AffineMuxFinPairFrame) :
    AffineMuxInvocationProgression :=
  { selector := selector
    selectorNot := frame.selectorNot
    emitsHeader := emitsHeader
    whenTrueBase := frame.whenTrue
    whenFalseBase := frame.whenFalse
    trueArmBase := frame.trueArm
    whenTrueStep := 0
    whenFalseStep := 0
    trueArmStep := 0
    count := 1 }

/-- Header-only representation of the degenerate zero-coordinate mux. -/
def affineMuxInvocationEmptySegment (selector : Nat) :
    AffineMuxInvocationProgression :=
  { selector := selector
    selectorNot := 0
    emitsHeader := true
    whenTrueBase := 0
    whenFalseBase := 0
    trueArmBase := 0
    whenTrueStep := 0
    whenFalseStep := 0
    trueArmStep := 0
    count := 0 }

/-- Exact segment family associated with an explicit canonical frame list. -/
def affineMuxInvocationSingletonSegments (selector : Nat) :
    List AffineMuxFinPairFrame → List AffineMuxInvocationProgression
  | [] => [affineMuxInvocationEmptySegment selector]
  | frame :: frames =>
      affineMuxInvocationSingletonSegment selector true frame ::
        frames.map (affineMuxInvocationSingletonSegment selector false)

@[simp] theorem affineMuxInvocationEmptySegment_invocationFrames
    (selector : Nat) :
    (affineMuxInvocationEmptySegment selector).invocationFrames =
      encodeAffineMuxFinHeader selector := by
  simp [affineMuxInvocationEmptySegment,
    AffineMuxInvocationProgression.invocationFrames,
    AffineMuxInvocationProgression.headerFrames,
    AffineMuxInvocationProgression.frames_eq_ofFn]

theorem affineMuxInvocationSingletonSegment_invocationFrames
    (selector : Nat) (emitsHeader : Bool)
    (frame : AffineMuxFinPairFrame)
    (hselector : frame.selector = selector)
    (hfalseArm : frame.falseArm = frame.trueArm + 1) :
    AffineMuxInvocationProgression.invocationFrames
        (affineMuxInvocationSingletonSegment selector emitsHeader frame) =
      (if emitsHeader then encodeAffineMuxFinHeader selector else []) ++
        encodeAffineMuxFinPairFrame frame := by
  rcases frame with
    ⟨whenTrue, whenFalse, frameSelector, selectorNot, trueArm, falseArm⟩
  change frameSelector = selector at hselector
  change falseArm = trueArm + 1 at hfalseArm
  subst frameSelector
  subst falseArm
  simp [affineMuxInvocationSingletonSegment,
    AffineMuxInvocationProgression.invocationFrames,
    AffineMuxInvocationProgression.headerFrames,
    AffineMuxInvocationProgression.frames_eq_ofFn]

private theorem affineMuxInvocationSingletonSegment_body
    (selector : Nat) (frames : List AffineMuxFinPairFrame)
    (hselector : ∀ frame ∈ frames, frame.selector = selector)
    (hfalseArm : ∀ frame ∈ frames,
      frame.falseArm = frame.trueArm + 1) :
    (frames.map
        (affineMuxInvocationSingletonSegment selector false)).flatMap
        AffineMuxInvocationProgression.invocationFrames =
      frames.flatMap encodeAffineMuxFinPairFrame := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      have hheadSelector := hselector frame (by simp)
      have hheadFalse := hfalseArm frame (by simp)
      have htailSelector : ∀ other ∈ frames,
          other.selector = selector := by
        intro other hother
        exact hselector other (by simp [hother])
      have htailFalse : ∀ other ∈ frames,
          other.falseArm = other.trueArm + 1 := by
        intro other hother
        exact hfalseArm other (by simp [hother])
      simp only [List.map_cons, List.flatMap_cons]
      rw [affineMuxInvocationSingletonSegment_invocationFrames selector false
        frame hheadSelector hheadFalse]
      rw [ih htailSelector htailFalse]
      rfl

/-- Singleton affine segments reproduce an arbitrary canonical mux payload
exactly, including the shared header and every delimiter. -/
theorem affineMuxInvocationSingletonSegments_frames
    (selector : Nat) (frames : List AffineMuxFinPairFrame)
    (hselector : ∀ frame ∈ frames, frame.selector = selector)
    (hfalseArm : ∀ frame ∈ frames,
      frame.falseArm = frame.trueArm + 1) :
    affineMuxInvocationProgressionFamilyFrames
        (affineMuxInvocationSingletonSegments selector frames) =
      encodeAffineMuxFinFrames selector frames := by
  cases frames with
  | nil =>
      simp [affineMuxInvocationSingletonSegments,
        affineMuxInvocationProgressionFamilyFrames,
        encodeAffineMuxFinFrames]
  | cons frame frames =>
      have hheadSelector := hselector frame (by simp)
      have hheadFalse := hfalseArm frame (by simp)
      have htailSelector : ∀ other ∈ frames,
          other.selector = selector := by
        intro other hother
        exact hselector other (by simp [hother])
      have htailFalse : ∀ other ∈ frames,
          other.falseArm = other.trueArm + 1 := by
        intro other hother
        exact hfalseArm other (by simp [hother])
      unfold affineMuxInvocationSingletonSegments
        affineMuxInvocationProgressionFamilyFrames encodeAffineMuxFinFrames
      simp only [List.flatMap_cons]
      rw [affineMuxInvocationSingletonSegment_invocationFrames selector true
        frame hheadSelector hheadFalse]
      rw [affineMuxInvocationSingletonSegment_body selector frames
        htailSelector htailFalse]
      simp [List.append_assoc]

/-- Canonical finite-mux frames allocate the false-arm wire immediately after
the corresponding true-arm wire. -/
theorem affineMuxFinCanonicalFrames_falseArm
    (start selector width : Nat)
    (whenTrue whenFalse : Fin width → CircuitBuilder.Wire) :
    ∀ frame ∈ affineMuxFinCanonicalFrames start selector width
        whenTrue whenFalse,
      frame.falseArm = frame.trueArm + 1 := by
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
        change start + 2 + 3 * width =
          (start + 1 + 3 * width) + 1
        omega

/-- Every proof-carrying dispatch artifact has canonical adjacent arm-output
coordinates. -/
theorem transitionDispatchLabelArtifacts_mux_falseArm_aligned
    (tm : _root_.Turing.FinTM2) (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height))
    (start : Nat) (fallback : CfgWires tm (workHeight tm height))
    (labels : List tm.Λ) :
    ∀ artifact ∈ transitionDispatchLabelArtifacts tm height falseWire
        trueWire source start fallback labels,
      ∀ frame ∈ artifact.muxFrames,
        frame.falseArm = frame.trueArm + 1 := by
  induction labels generalizing start fallback with
  | nil => simp [transitionDispatchLabelArtifacts]
  | cons label labels ih =>
      intro artifact hartifact
      simp only [transitionDispatchLabelArtifacts, List.mem_cons] at hartifact
      rcases hartifact with rfl | htail
      · exact affineMuxFinCanonicalFrames_falseArm _ _ _ _ _
      · exact ih _ _ artifact htail

/-- Singleton invocation segments of one actual dispatch artifact. -/
def TransitionDispatchLabelArtifact.muxInvocationSegments
    {tm : _root_.Turing.FinTM2}
    (artifact : TransitionDispatchLabelArtifact tm) :
    List AffineMuxInvocationProgression :=
  affineMuxInvocationSingletonSegments artifact.selector artifact.muxFrames

/-- One actual artifact is encoded exactly by the generic invocation segment
controller's semantic target. -/
theorem transitionDispatchArtifactsFromSeed_muxInvocationSegments_frames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (artifact : TransitionDispatchLabelArtifact tm)
    (hartifact : artifact ∈ transitionDispatchArtifactsFromSeed tm seed) :
    affineMuxInvocationProgressionFamilyFrames
        artifact.muxInvocationSegments =
      encodeAffineMuxFinFrames artifact.selector artifact.muxFrames := by
  apply affineMuxInvocationSingletonSegments_frames
  · exact transitionDispatchLabelArtifacts_mux_selector_aligned tm seed.height
      seed.start (seed.start + 1)
      (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
      (seed.start + 2)
      (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
      (programLabels tm) artifact hartifact
  · exact transitionDispatchLabelArtifacts_mux_falseArm_aligned tm seed.height
      seed.start (seed.start + 1)
      (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
      (seed.start + 2)
      (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
      (programLabels tm) artifact hartifact

/-- Complete actual segment family of one seed-derived transition dispatch. -/
def transitionDispatchMuxInvocationSegmentsFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineMuxInvocationProgression :=
  (transitionDispatchArtifactsFromSeed tm seed).flatMap
    TransitionDispatchLabelArtifact.muxInvocationSegments

/-- The complete seed-local segment family expands byte-for-byte to the
canonical mux payloads already present in the transition script. -/
theorem transitionDispatchMuxInvocationSegmentsFromSeed_frames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineMuxInvocationProgressionFamilyFrames
        (transitionDispatchMuxInvocationSegmentsFromSeed tm seed) =
      (transitionDispatchArtifactsFromSeed tm seed).flatMap fun artifact =>
        encodeAffineMuxFinFrames artifact.selector artifact.muxFrames := by
  unfold transitionDispatchMuxInvocationSegmentsFromSeed
    affineMuxInvocationProgressionFamilyFrames
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro artifact hartifact
  exact transitionDispatchArtifactsFromSeed_muxInvocationSegments_frames
    tm seed artifact hartifact

/-- Complete actual mux invocation segments for all verifier transition rows. -/
noncomputable def verifierTransitionDispatchMuxInvocationSegments
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineMuxInvocationProgression :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchMuxInvocationSegmentsFromSeed W.machine.tm)

/-- Compact arithmetic source consumed by the fixed generic invocation
controller for the actual verifier transition rows. -/
noncomputable def verifierTransitionDispatchMuxInvocationSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineMuxInvocationProgressionFamilySourceFrames
    (verifierTransitionDispatchMuxInvocationSegments W input)

/-- Exact semantic mux payload required by all transition rows. -/
noncomputable def verifierTransitionDispatchMuxInvocationFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchArtifactsFromSeed W.machine.tm seed).flatMap
      fun artifact =>
        encodeAffineMuxFinFrames artifact.selector artifact.muxFrames

theorem verifierTransitionDispatchMuxInvocationSegments_frames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineMuxInvocationProgressionFamilyFrames
        (verifierTransitionDispatchMuxInvocationSegments W input) =
      verifierTransitionDispatchMuxInvocationFrames W input := by
  unfold verifierTransitionDispatchMuxInvocationSegments
    verifierTransitionDispatchMuxInvocationFrames
    affineMuxInvocationProgressionFamilyFrames
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionDispatchMuxInvocationSegmentsFromSeed_frames W.machine.tm
    seed

/-- The newly verified generic controller is already a fixed polynomial-time
TM2 for expanding the actual Cook--Levin mux segment source.  The remaining
raw-input obligation is solely to generate `...SourceFrames` from `input`. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationFrames_fromSource_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime
      (verifierTransitionDispatchMuxInvocationSourceFrames W) id
      (verifierTransitionDispatchMuxInvocationFrames W) := by
  let generic :=
    affineMuxInvocationProgressionFamilyFrames_computableInPolyTime
  exact
    { tm := generic.tm
      inputAlphabet := generic.inputAlphabet
      outputAlphabet := generic.outputAlphabet
      time := generic.time
      outputsFun := fun input => by
        have run := generic.outputsFun
          (verifierTransitionDispatchMuxInvocationSegments W input)
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationSourceFrames,
          verifierTransitionDispatchMuxInvocationSegments_frames W input]
          using run }

end CLRS.Chapter34.Turing.CookLevin
