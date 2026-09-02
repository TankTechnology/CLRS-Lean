import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorAlignment
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationSegments

/-!
# Reassembly of dispatch-mux descriptor views

The four aligned semantic sections are reconnected here into complete mux
invocation views.  For every transition seed emitted by the verifier source,
the result is proved equal to the projection of the actual proof-carrying
dispatch artifacts.  Converting those views to singleton affine invocation
segments therefore reproduces the exact canonical mux byte stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Builder-free artifacts retain the source selector of each fixed label. -/
theorem transitionDispatchLabelArtifacts_selectors
    (tm : _root_.Turing.FinTM2) (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height))
    (start : Nat) (fallback : CfgWires tm (workHeight tm height))
    (labels : List tm.Λ) :
    (transitionDispatchLabelArtifacts tm height falseWire trueWire source
      start fallback labels).map (fun artifact => artifact.selector) =
      labels.map fun label =>
        source.label (Fin.castSucc (labelEquivFin tm label)) := by
  induction labels generalizing start fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchLabelArtifacts, List.map_cons]
      congr 1
      exact ih _ _

/-- Seed-derived artifact selectors are exactly the raw affine selector
section of the unified packet. -/
theorem transitionDispatchArtifactsFromSeed_selectors
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchArtifactsFromSeed tm seed).map
        (fun artifact => artifact.selector) =
      transitionDispatchSelectors tm seed := by
  unfold transitionDispatchArtifactsFromSeed transitionDispatchSelectors
  exact transitionDispatchLabelArtifacts_selectors tm seed.height seed.start
    (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (seed.start + 2)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (programLabels tm)

/-- Builder-free artifacts carry exactly the recursive fresh-coordinate
layouts used by the affine progression source. -/
theorem transitionDispatchLabelArtifacts_muxFreshLayouts
    (tm : _root_.Turing.FinTM2) (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height))
    (start : Nat) (fallback : CfgWires tm (workHeight tm height))
    (labels : List tm.Λ) :
    (transitionDispatchLabelArtifacts tm height falseWire trueWire source
      start fallback labels).map
        TransitionDispatchLabelArtifact.muxFreshLayout =
      transitionDispatchMuxFreshLayouts tm height source start labels := by
  induction labels generalizing start fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchLabelArtifacts,
        transitionDispatchMuxFreshLayouts, List.map_cons]
      congr 1
      · unfold TransitionDispatchLabelArtifact.muxFreshLayout
          transitionDispatchMuxFreshLayout
        rw [affineMuxFinCanonicalFrames_freshCoordinates]
      · exact ih _ _

/-- Seed-derived artifact coordinate rows are exactly the semantic layouts
denoted by the coordinate progression groups. -/
theorem transitionDispatchArtifactsFromSeed_muxFreshLayouts
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchArtifactsFromSeed tm seed).map
        TransitionDispatchLabelArtifact.muxFreshLayout =
      transitionDispatchMuxFreshLayoutsFromSeed tm seed := by
  unfold transitionDispatchArtifactsFromSeed
    transitionDispatchMuxFreshLayoutsFromSeed
  exact transitionDispatchLabelArtifacts_muxFreshLayouts tm seed.height
    seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (seed.start + 2)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (programLabels tm)

theorem transitionDispatchArtifactsFromSeed_muxCoordinateRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchArtifactsFromSeed tm seed).map
        (fun artifact => artifact.muxFreshLayout.coordinates) =
      (transitionDispatchMuxFreshLayoutsFromSeed tm seed).map
        TransitionDispatchMuxFreshLayout.coordinates := by
  have hlayouts := transitionDispatchArtifactsFromSeed_muxFreshLayouts tm seed
  have hcoordinates := congrArg
    (List.map TransitionDispatchMuxFreshLayout.coordinates) hlayouts
  simpa [List.map_map, Function.comp_def] using hcoordinates

/-- Total four-way row zipper.  Unequal malformed inputs stop at the shortest
section; the alignment theorem proves that verifier-produced sections all
have the full fixed-label length. -/
def transitionDispatchMuxInvocationViewsFromRows :
    List Nat → List (List (Nat × Nat × Nat)) →
      List (List Nat) → List (List Nat) →
        List TransitionDispatchMuxInvocationView
  | selector :: selectors, coordinates :: coordinateRows,
      whenTrue :: trueRows, whenFalse :: falseRows =>
      { selector := selector
        coordinates := coordinates
        whenTrue := whenTrue
        whenFalse := whenFalse } ::
        transitionDispatchMuxInvocationViewsFromRows selectors coordinateRows
          trueRows falseRows
  | _, _, _, _ => []

/-- Zipping four projections of the same view list recovers that list. -/
theorem transitionDispatchMuxInvocationViewsFromRows_maps
    (views : List TransitionDispatchMuxInvocationView) :
    transitionDispatchMuxInvocationViewsFromRows
        (views.map TransitionDispatchMuxInvocationView.selector)
        (views.map TransitionDispatchMuxInvocationView.coordinates)
        (views.map TransitionDispatchMuxInvocationView.whenTrue)
        (views.map TransitionDispatchMuxInvocationView.whenFalse) =
      views := by
  induction views with
  | nil => rfl
  | cons view views ih =>
      simp only [List.map_cons,
        transitionDispatchMuxInvocationViewsFromRows]
      rw [ih]

/-- Complete invocation views denoted by the four descriptor sections of one
transition seed. -/
noncomputable def transitionDispatchMuxDescriptorInvocationViews
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List TransitionDispatchMuxInvocationView :=
  transitionDispatchMuxInvocationViewsFromRows
    (transitionDispatchSelectors tm seed)
    ((transitionDispatchMuxCoordinateProgressionGroups tm seed).map
      fun progressions =>
        progressions.flatMap affineUnaryTripleProgressionRows)
    ((transitionDispatchTrueArmSpanProgressionGroups tm seed).map
      fun progressions =>
        progressions.flatMap transitionProgressionFirstValues)
    ((transitionDispatchFalseArmProgressionGroups tm seed).map
      fun progressions =>
        progressions.flatMap transitionProgressionFirstValues)

/-- The unified descriptor interpretation reconstructs every actual artifact
view field-for-field. -/
theorem transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed =
      (transitionDispatchArtifactsFromSeed W.machine.tm seed).map
        TransitionDispatchLabelArtifact.muxInvocationView := by
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
    rw [hheight]
    unfold workHeight
    exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _
  unfold transitionDispatchMuxDescriptorInvocationViews
  rw [transitionDispatchMuxCoordinateProgressionGroups_values
    W.machine.tm seed hwork]
  rw [transitionDispatchTrueArmSpanProgressionGroups_eq_seed
    W input seed hseed]
  rw [transitionDispatchFalseArmProgressionGroups_values
    W.machine.tm seed hwork]
  rw [← transitionDispatchArtifactsFromSeed_selectors]
  rw [← transitionDispatchArtifactsFromSeed_muxCoordinateRows]
  rw [← transitionDispatchArtifactsFromSeed_trueArmRows]
  rw [← transitionDispatchArtifactsFromSeed_falseArmRows]
  simpa [TransitionDispatchLabelArtifact.muxInvocationView, List.map_map,
    Function.comp_def] using
    (transitionDispatchMuxInvocationViewsFromRows_maps
      ((transitionDispatchArtifactsFromSeed W.machine.tm seed).map
        TransitionDispatchLabelArtifact.muxInvocationView))

/-- Singleton affine invocation segments denoted by one reconstructed view. -/
def TransitionDispatchMuxInvocationView.invocationSegments
    (view : TransitionDispatchMuxInvocationView) :
    List AffineMuxInvocationProgression :=
  affineMuxInvocationSingletonSegments view.selector view.frames

/-- Descriptor-derived invocation segments for one complete transition
dispatch. -/
noncomputable def transitionDispatchMuxDescriptorInvocationSegments
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineMuxInvocationProgression :=
  (transitionDispatchMuxDescriptorInvocationViews tm seed).flatMap
    TransitionDispatchMuxInvocationView.invocationSegments

private theorem artifact_muxInvocationView_invocationSegments
    {tm : _root_.Turing.FinTM2} (seed : TransitionRowSeed)
    (artifact : TransitionDispatchLabelArtifact tm)
    (hartifact : artifact ∈ transitionDispatchArtifactsFromSeed tm seed) :
    artifact.muxInvocationView.invocationSegments =
      artifact.muxInvocationSegments := by
  unfold TransitionDispatchMuxInvocationView.invocationSegments
    TransitionDispatchLabelArtifact.muxInvocationSegments
  change affineMuxInvocationSingletonSegments artifact.selector
      artifact.muxInvocationView.frames =
    affineMuxInvocationSingletonSegments artifact.selector artifact.muxFrames
  rw [transitionDispatchArtifactsFromSeed_muxInvocationView_frames tm seed
    artifact hartifact]

/-- The descriptor interpretation produces literally the established
canonical segment family, not merely an extensionally equal byte stream. -/
theorem transitionDispatchMuxDescriptorInvocationSegments_eq_artifacts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    transitionDispatchMuxDescriptorInvocationSegments W.machine.tm seed =
      transitionDispatchMuxInvocationSegmentsFromSeed W.machine.tm seed := by
  unfold transitionDispatchMuxDescriptorInvocationSegments
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts
    W input seed hseed]
  rw [List.flatMap_map]
  unfold transitionDispatchMuxInvocationSegmentsFromSeed
  apply List.flatMap_congr
  intro artifact hartifact
  exact artifact_muxInvocationView_invocationSegments seed artifact hartifact

/-- The descriptor-derived segment family expands byte-for-byte to every
canonical mux payload already present in the actual dispatch script. -/
theorem transitionDispatchMuxDescriptorInvocationSegments_frames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    affineMuxInvocationProgressionFamilyFrames
        (transitionDispatchMuxDescriptorInvocationSegments W.machine.tm seed) =
      (transitionDispatchArtifactsFromSeed W.machine.tm seed).flatMap
        fun artifact =>
          encodeAffineMuxFinFrames artifact.selector artifact.muxFrames := by
  rw [transitionDispatchMuxDescriptorInvocationSegments_eq_artifacts
    W input seed hseed]
  exact transitionDispatchMuxInvocationSegmentsFromSeed_frames W.machine.tm
    seed

/-- Descriptor-interpreted invocation segments for every verifier transition
row. -/
noncomputable def verifierTransitionDispatchMuxDescriptorInvocationSegments
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineMuxInvocationProgression :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchMuxDescriptorInvocationSegments W.machine.tm)

/-- Row-major descriptor interpretation is literally the canonical segment
family already accepted by the generic mux controller. -/
theorem verifierTransitionDispatchMuxDescriptorInvocationSegments_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxDescriptorInvocationSegments W input =
      verifierTransitionDispatchMuxInvocationSegments W input := by
  unfold verifierTransitionDispatchMuxDescriptorInvocationSegments
    verifierTransitionDispatchMuxInvocationSegments
  apply List.flatMap_congr
  intro seed hseed
  exact transitionDispatchMuxDescriptorInvocationSegments_eq_artifacts
    W input seed hseed

/-- Exact arithmetic source target of the remaining unified descriptor
interpreter. -/
noncomputable def
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineMuxInvocationProgressionFamilySourceFrames
    (verifierTransitionDispatchMuxDescriptorInvocationSegments W input)

/-- The new interpreter target is byte-for-byte the source of the already
verified generic affine mux controller. -/
theorem verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxDescriptorInvocationSourceFrames W input =
      verifierTransitionDispatchMuxInvocationSourceFrames W input := by
  unfold verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
    verifierTransitionDispatchMuxInvocationSourceFrames
  rw [verifierTransitionDispatchMuxDescriptorInvocationSegments_eq]

end CLRS.Chapter34.Turing.CookLevin
