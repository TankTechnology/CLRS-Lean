import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueFrames

/-!
# True-arm descriptors from label-major dispatch packets

The third row of every physical label-major packet contains the complete
normalized true-arm descriptor payload for that label.  This module selects
those rows, removes their temporary label markers, and proves that the result
is exactly the established adjacent eight-field true-arm block stream.  All
later verified true-arm interpreters can therefore be reused unchanged.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_trueLayouts
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
        (fun packet => packet.trueLayout) = trueLayouts := by
  induction selectors generalizing coordinateGroups trueLayouts falseGroups with
  | nil =>
      simp only [List.length_nil] at htrue
      have htrueNil : trueLayouts = [] := by simpa using htrue
      subst trueLayouts
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

/-- Projecting the third field of every typed packet recovers the verifier-
fixed normalized true layouts. -/
theorem transitionDispatchMuxInvocationLabelMajorDescriptorPackets_trueLayouts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
        W.machine.tm seed).map (fun packet => packet.trueLayout) =
      transitionDispatchTrueArmNormalizedLayouts W.machine.tm := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorPackets
  apply
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_trueLayouts
  · rw [transitionDispatchMuxCoordinateProgressionGroups_length,
      transitionDispatchSelectors_length]
  · have hlength :=
      transitionDispatchTrueArmSpanProgressionGroups_length W.machine.tm seed
    unfold transitionDispatchTrueArmSpanProgressionGroups at hlength
    simp only [List.length_map] at hlength
    rw [hlength, transitionDispatchSelectors_length]
  · rw [transitionDispatchFalseArmProgressionGroups_length W input seed hseed,
      transitionDispatchSelectors_length]

/-- Select the third row of each selector/coordinate/true/false packet. -/
def transitionDispatchMuxInvocationLabelMajorTrueSelection : List Bool :=
  [false, false, true, false]

theorem transitionDispatchMuxInvocationLabelMajorTrueSelection_nonempty :
    0 < transitionDispatchMuxInvocationLabelMajorTrueSelection.length := by
  simp [transitionDispatchMuxInvocationLabelMajorTrueSelection]

/-- Selected, still label-marked true-arm descriptor rows. -/
noncomputable def verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationLabelMajorTrueSelection
    transitionDispatchMuxInvocationLabelMajorTrueSelection_nonempty
    (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
      W input)

/-- The selected physical rows carry precisely each packet's normalized
true-arm span descriptors. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
          W.machine.tm seed).flatMap fun packet =>
            encodeUnaryFrame
                (packet.trueLayout.affineSpanDescriptorValues
                  W.machine.tm seed) ++ [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames_eq]
  rw [rewriteUnaryFramePeriodicMarkedRows_encode]
  rw [encodeUnaryFramePeriodicMarkedRowOutput_groups _ _ _]
  · unfold
      verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
    rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro seed hseed
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro packet hpacket
    simp [transitionDispatchMuxInvocationLabelMajorTrueSelection,
      TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.fourRowDescriptorValueGroups,
      encodeUnaryFramePeriodicSelectedMarkedRows]
  · intro group hgroup
    simpa [transitionDispatchMuxInvocationLabelMajorTrueSelection] using
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups_length
        W input group hgroup)

/-- Remove temporary label markers and expose the adjacent true-arm block
stream expected by the established eight-to-seven-field interpreter. -/
noncomputable def verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows W input)

theorem verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames_eq_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
            W.machine.tm seed).flatMap fun packet =>
              packet.trueLayout.affineSpanDescriptorValues
                W.machine.tm seed) := by
  unfold verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames
  rw [verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
              W.machine.tm seed).flatMap fun packet =>
                encodeUnaryFrame
                    (packet.trueLayout.affineSpanDescriptorValues
                      W.machine.tm seed) ++ [.frameEnd]) =
        (((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
            W.machine.tm seed).map fun packet =>
              packet.trueLayout.affineSpanDescriptorValues
                W.machine.tm seed).flatMap fun row =>
                  encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_assoc, List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  congr 1
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  rw [List.flatMap_map]
  simp only [id_eq]

/-- The label-major true descriptor bytes are byte-for-byte the established
true descriptor channel. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames_eq_existing
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames W input =
      verifierTransitionDispatchMuxInvocationDescriptorTrueFrames W input := by
  rw [verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames_eq_values,
    verifierTransitionDispatchMuxInvocationDescriptorTrueFrames_eq_values]
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  have hlayouts :=
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_trueLayouts
      W input seed hseed
  have hvalues := congrArg
    (List.flatMap fun layout =>
      layout.affineSpanDescriptorValues W.machine.tm seed) hlayouts
  simpa [List.flatMap_map, Function.comp_def,
    transitionDispatchTrueArmSpanDescriptorValues] using hvalues

noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationLabelMajorTrueSelection
        transitionDispatchMuxInvocationLabelMajorTrueSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationLabelMajorTrueSelection
      transitionDispatchMuxInvocationLabelMajorTrueSelection_nonempty
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
        W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- The raw verifier input reaches the exact established true descriptor
block stream through the label-major source in polynomial time. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationLabelMajorTrueMarkedRows
        W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
