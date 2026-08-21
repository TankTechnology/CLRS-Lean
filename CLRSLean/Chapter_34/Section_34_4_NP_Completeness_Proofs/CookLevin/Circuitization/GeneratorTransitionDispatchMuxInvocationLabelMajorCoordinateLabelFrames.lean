import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorCoordinateExecute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames

/-!
# Label boundaries for label-major coordinate execution

The label-major route has already selected, decoded, and executed every
coordinate descriptor.  This module restores the one-row-per-label boundary
needed by the existing mux packet assembler.  The central bridge proves that
the coordinate families stored in the new typed packets are exactly the
singleton coordinate families of the established descriptor route.  We can
therefore reuse its verified boundary controller and row semantics without
introducing another machine.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_coordinateProgressions
    (tm : _root_.Turing.FinTM2)
    (selectors : List Nat)
    (coordinateGroups : List (List AffineUnaryTripleProgression))
    (trueLayouts : List (TransitionDispatchTrueArmNormalizedLayout tm))
    (falseGroups : List (List AffineUnaryTripleProgression))
    (hcoordinate : coordinateGroups.length = selectors.length)
    (htrue : trueLayouts.length = selectors.length)
    (hfalse : falseGroups.length = selectors.length) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom tm
        selectors coordinateGroups trueLayouts falseGroups).map
        (fun packet => packet.coordinateProgressions) = coordinateGroups := by
  induction selectors generalizing coordinateGroups trueLayouts falseGroups with
  | nil =>
      simp only [List.length_nil] at hcoordinate htrue hfalse
      have hcoordinateNil : coordinateGroups = [] := by
        simpa using hcoordinate
      have htrueNil : trueLayouts = [] := by
        simpa using htrue
      have hfalseNil : falseGroups = [] := by
        simpa using hfalse
      subst coordinateGroups
      subst trueLayouts
      subst falseGroups
      rfl
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil => simp at hcoordinate
      | cons coordinates coordinateGroups =>
          cases trueLayouts with
          | nil => simp at htrue
          | cons trueLayout trueLayouts =>
              cases falseGroups with
              | nil => simp at hfalse
              | cons whenFalse falseGroups =>
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom,
                    List.map_cons]
                  congr 1
                  apply ih
                  · simpa using hcoordinate
                  · simpa using htrue
                  · simpa using hfalse

/-- On a verifier-produced seed, projecting the coordinate field of every
typed label packet recovers the canonical singleton progression groups. -/
theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_coordinateProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
        W.machine.tm seed).map (fun packet => packet.coordinateProgressions) =
      transitionDispatchMuxCoordinateProgressionGroups W.machine.tm seed := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorPackets
  apply
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_coordinateProgressions
  · rw [transitionDispatchMuxCoordinateProgressionGroups_length,
      transitionDispatchSelectors_length]
  · have hlength :=
      transitionDispatchTrueArmSpanProgressionGroups_length W.machine.tm seed
    unfold transitionDispatchTrueArmSpanProgressionGroups at hlength
    simp only [List.length_map] at hlength
    rw [hlength, transitionDispatchSelectors_length]
  · rw [transitionDispatchFalseArmProgressionGroups_length W input seed hseed,
      transitionDispatchSelectors_length]

/-- Flattening the new packet-local coordinate fields gives exactly the
established label-ordered affine progression family. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions
        W input =
      (verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchMuxAffineProgressions W.machine.tm) := by
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions
  apply List.flatMap_congr
  intro seed hseed
  have hgroups :=
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_coordinateProgressions
      W input seed hseed
  have hflattened := congrArg List.flatten hgroups
  simpa [List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def,
    transitionDispatchMuxCoordinateProgressionGroups] using hflattened

/-- Coordinate execution with one retained boundary per label in the new
label-major pipeline. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStream 0
    (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions
      W input)

/-- The new label-major coordinate channel is byte-for-byte the already
verified coordinate-label channel. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_existing
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
        W input := by
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
  rw [verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions_eq]

/-- Hence every retained boundary denotes exactly one semantic fresh-
coordinate row of one dispatch label. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_layouts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxFreshLayoutsFromSeed W.machine.tm seed).flatMap
          fun layout =>
            transitionDispatchMuxCoordinateRowFrames layout.coordinates ++
              [.frameEnd] := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_existing,
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_eq_layouts]

/-- The complete label-major coordinate route, including restored label
boundaries, is realized by one fixed polynomial-time TM2 from the raw input. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
        W) := by
  let existing :=
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_computableInPolyTime
      W
  exact
    { tm := existing.tm
      inputAlphabet := existing.inputAlphabet
      outputAlphabet := existing.outputAlphabet
      time := existing.time
      outputsFun := fun input => by
        have run := existing.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames_eq_existing]
          using run }

end CLRS.Chapter34.Turing.CookLevin
