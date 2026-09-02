import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorCoordinateLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames

/-!
# Selector rows from label-major dispatch packets

The first row of every physical label-major packet is already the final
singleton selector row.  A fixed four-period filter extracts those rows.  We
prove that their payload order is exactly the established selector channel,
so this route can feed the existing label-packet assembler directly.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_selectors
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
        (fun packet => packet.selector) = selectors := by
  induction selectors generalizing coordinateGroups trueLayouts falseGroups with
  | nil => rfl
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

/-- Projecting the first field of every typed packet recovers the canonical
selector table on every verifier seed. -/
theorem transitionDispatchMuxInvocationLabelMajorDescriptorPackets_selectors
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
        W.machine.tm seed).map (fun packet => packet.selector) =
      transitionDispatchSelectors W.machine.tm seed := by
  unfold transitionDispatchMuxInvocationLabelMajorDescriptorPackets
  apply
    transitionDispatchMuxInvocationLabelMajorDescriptorPacketsFrom_selectors
  · rw [transitionDispatchMuxCoordinateProgressionGroups_length,
      transitionDispatchSelectors_length]
  · have hlength :=
      transitionDispatchTrueArmSpanProgressionGroups_length W.machine.tm seed
    unfold transitionDispatchTrueArmSpanProgressionGroups at hlength
    simp only [List.length_map] at hlength
    rw [hlength, transitionDispatchSelectors_length]
  · rw [transitionDispatchFalseArmProgressionGroups_length W input seed hseed,
      transitionDispatchSelectors_length]

/-- Select the first row of each selector/coordinate/true/false packet. -/
def transitionDispatchMuxInvocationLabelMajorSelectorSelection : List Bool :=
  [true, false, false, false]

theorem transitionDispatchMuxInvocationLabelMajorSelectorSelection_nonempty :
    0 < transitionDispatchMuxInvocationLabelMajorSelectorSelection.length := by
  simp [transitionDispatchMuxInvocationLabelMajorSelectorSelection]

/-- Canonical marked selector rows extracted directly from the label-major
four-row stream. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationLabelMajorSelectorSelection
    transitionDispatchMuxInvocationLabelMajorSelectorSelection_nonempty
    (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
      W input)

/-- The physical filter returns one marked singleton row for every typed
packet, in seed-major and label-major order. -/
theorem verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
          W.machine.tm seed).flatMap fun packet =>
            encodeUnaryFrame [packet.selector] ++ [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
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
    simp [transitionDispatchMuxInvocationLabelMajorSelectorSelection,
      TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.fourRowDescriptorValueGroups,
      encodeUnaryFramePeriodicSelectedMarkedRows]
  · intro group hgroup
    simpa [transitionDispatchMuxInvocationLabelMajorSelectorSelection] using
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups_length
        W input group hgroup)

/-- The newly extracted selector rows are byte-for-byte the established
selector-label channel. -/
theorem
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq_existing
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
        W input =
      verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames
        W input := by
  rw [verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_eq,
    verifierTransitionDispatchMuxInvocationDescriptorSelectorLabelFrames_eq_semantic]
  apply List.flatMap_congr
  intro seed hseed
  have hselectors :=
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_selectors
      W input seed hseed
  have hframes := congrArg
    (List.flatMap fun selector =>
      encodeUnaryFrame [selector] ++ [.frameEnd]) hselectors
  simpa [List.flatMap_map, Function.comp_def] using hframes

/-- The selector extraction pass is a fixed polynomial-time TM2 from the raw
verifier input. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorSelectorLabelFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationLabelMajorSelectorSelection
        transitionDispatchMuxInvocationLabelMajorSelectorSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationLabelMajorSelectorSelection
      transitionDispatchMuxInvocationLabelMajorSelectorSelection_nonempty
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
        W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
