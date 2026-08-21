import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueLabelFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowSelection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowUnmark

/-!
# Executing the label-major coordinate descriptor rows

This module is the first concrete consumer of the new label-major source.  A
linear normalizer restores the ordinary separator before every compact row
boundary.  A four-state periodic controller then retains the coordinate row
of each label packet, after which the existing generic affine-progression
machine executes the recovered descriptors.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem transitionDispatchProgressionDescriptorValues_nonempty
    (progressions : List AffineUnaryTripleProgression)
    (hnonempty : progressions ≠ []) :
    transitionDispatchProgressionDescriptorValues progressions ≠ [] := by
  cases progressions with
  | nil => exact False.elim (hnonempty rfl)
  | cons progression progressions =>
      simp [transitionDispatchProgressionDescriptorValues]

private theorem
    TransitionDispatchTrueArmNormalizedLayout.affineSpanDescriptorValues_nonempty
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    layout.affineSpanDescriptorValues tm seed ≠ [] := by
  have hamounts :=
    transitionDispatchTrueArmNormalizedLayout_dropAmounts_nonempty tm layout
  have haligned := layout.affineSpanDropAmounts_length tm
  cases hdrop : layout.affineSpanDropAmounts tm with
  | nil => simp [hdrop] at hamounts
  | cons amount amounts =>
      cases hsegments : layout.affineSpanSegments tm with
      | nil =>
          rw [hdrop, hsegments] at haligned
          simp at haligned
      | cons segment segments =>
          unfold
            TransitionDispatchTrueArmNormalizedLayout.affineSpanDescriptorValues
          rw [hdrop, hsegments]
          simp [transitionDispatchTrueArmSpanDescriptorValuesFrom,
            transitionDispatchTrueArmSpanDescriptorBlockValues]

private theorem transitionDispatchFalseArmProgressionGroups_nonempty
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ group ∈ transitionDispatchFalseArmProgressionGroups tm seed,
      group ≠ [] := by
  intro group hgroup
  unfold transitionDispatchFalseArmProgressionGroups at hgroup
  simp only [List.mem_cons, List.mem_map] at hgroup
  rcases hgroup with rfl | ⟨progression, hprogression, rfl⟩
  · simp [transitionWidenedFallbackProgressions,
      transitionWidenedFallbackSegments]
  · simp

private theorem
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom_nonempty
    (selectors : List Nat)
    (coordinateGroups trueGroups falseGroups : List (List Nat))
    (hcoordinate : ∀ group ∈ coordinateGroups, group ≠ [])
    (htrue : ∀ group ∈ trueGroups, group ≠ [])
    (hfalse : ∀ group ∈ falseGroups, group ≠ []) :
    ∀ row ∈
        transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom
          selectors coordinateGroups trueGroups falseGroups,
      row ≠ [] := by
  intro row hrow
  induction selectors generalizing coordinateGroups trueGroups falseGroups with
  | nil =>
      simp [
        transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom]
        at hrow
  | cons selector selectors ih =>
      cases coordinateGroups with
      | nil =>
          simp [
            transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom]
            at hrow
      | cons coordinates coordinateGroups =>
          cases trueGroups with
          | nil =>
              simp [
                transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom]
                at hrow
          | cons whenTrue trueGroups =>
              cases falseGroups with
              | nil =>
                  simp [
                    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom]
                    at hrow
              | cons whenFalse falseGroups =>
                  simp only [
                    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom,
                    List.mem_append, List.mem_cons] at hrow
                  rcases hrow with hhead | hrow
                  · rcases hhead with hselector | hcoordinates |
                      hwhenTrue | hwhenFalse | hnil
                    · subst row
                      simp
                    · subst row
                      exact hcoordinate coordinates (by simp)
                    · subst row
                      exact htrue whenTrue (by simp)
                    · subst row
                      exact hfalse whenFalse (by simp)
                    · simp at hnil
                  · apply ih coordinateGroups trueGroups falseGroups
                    · intro group hgroup
                      exact hcoordinate group (by simp [hgroup])
                    · intro group hgroup
                      exact htrue group (by simp [hgroup])
                    · intro group hgroup
                      exact hfalse group (by simp [hgroup])
                    · exact hrow

/-- Every canonical descriptor row really exists physically; in particular,
none of the four advertised sections silently collapses to an empty row. -/
theorem
    transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups_nonempty
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ row ∈
        transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups
          tm seed,
      row ≠ [] := by
  apply
    transitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroupsFrom_nonempty
  · intro values hvalues
    rw [List.mem_map] at hvalues
    rcases hvalues with ⟨progressions, hprogressions, rfl⟩
    apply transitionDispatchProgressionDescriptorValues_nonempty
    unfold transitionDispatchMuxCoordinateProgressionGroups at hprogressions
    rw [List.mem_map] at hprogressions
    rcases hprogressions with ⟨progression, hprogression, rfl⟩
    simp
  · intro values hvalues
    rw [List.mem_map] at hvalues
    rcases hvalues with ⟨layout, hlayout, rfl⟩
    exact layout.affineSpanDescriptorValues_nonempty tm seed
  · intro values hvalues
    rw [List.mem_map] at hvalues
    rcases hvalues with ⟨progressions, hprogressions, rfl⟩
    exact transitionDispatchProgressionDescriptorValues_nonempty progressions
      (transitionDispatchFalseArmProgressionGroups_nonempty tm seed
        progressions hprogressions)

/-- Four-row groups, one group per typed label packet. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
      W.machine.tm seed).map fun packet =>
        packet.fourRowDescriptorValueGroups seed

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups_flatten
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
      W input).flatten =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups
          W.machine.tm seed := by
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  rw [List.flatMap_map]
  exact
    transitionDispatchMuxInvocationLabelMajorDescriptorPackets_fourRows
      W.machine.tm seed

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ group ∈
        verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
          W input,
      group.length = 4 := by
  intro group hgroup
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
    at hgroup
  rw [List.mem_flatMap] at hgroup
  rcases hgroup with ⟨seed, hseed, hgroup⟩
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨packet, hpacket, rfl⟩
  rfl

private theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorRows_nonempty
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ row ∈
        (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
          W input).flatten,
      row ≠ [] := by
  intro row hrow
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups_flatten]
    at hrow
  rw [List.mem_flatMap] at hrow
  rcases hrow with ⟨seed, hseed, hrow⟩
  exact
    transitionDispatchMuxInvocationLabelMajorCanonicalFourRowDescriptorValueGroups_nonempty
      W.machine.tm seed row hrow

private theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames_eq_groupEncoding
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames
        W input =
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
        W input).flatten.flatMap encodeUnaryFrameFixedWidthPacket := by
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames_eq_packets]
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
  simp [
    TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.fourRowDescriptorFrames,
    List.flatten_eq_flatMap, List.flatMap_assoc, List.flatMap_map]

/-- Canonicalize the compact physical rows before periodic dispatch. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  restoreUnaryFrameFixedWidthPacketSeparators
    (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames
      W input)

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
        W input =
      encodeUnaryFramePeriodicMarkedRowInput
        (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups
          W input).flatten := by
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames_eq_groupEncoding]
  rw [restoreUnaryFrameFixedWidthPacketSeparators_family]
  · rfl
  · exact
      verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorRows_nonempty
        W input

/-- The raw verifier input reaches the canonical four-row stream by one fixed
polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames_computableInPolyTime
        W)
      restoreUnaryFrameFixedWidthPacketSeparators_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => restoreUnaryFrameFixedWidthPacketSeparators
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorFrames
        W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Keep the second row of every selector/coordinate/true/false packet. -/
def transitionDispatchMuxInvocationLabelMajorCoordinateSelection : List Bool :=
  [false, true, false, false]

theorem transitionDispatchMuxInvocationLabelMajorCoordinateSelection_nonempty :
    0 < transitionDispatchMuxInvocationLabelMajorCoordinateSelection.length := by
  simp [transitionDispatchMuxInvocationLabelMajorCoordinateSelection]

/-- Selected, still-marked coordinate descriptor rows. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationLabelMajorCoordinateSelection
    transitionDispatchMuxInvocationLabelMajorCoordinateSelection_nonempty
    (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
      W input)

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
          W.machine.tm seed).flatMap fun packet =>
            encodeUnaryFrame
                (transitionDispatchProgressionDescriptorValues
                  packet.coordinateProgressions) ++ [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows
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
    simp [transitionDispatchMuxInvocationLabelMajorCoordinateSelection,
      TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.fourRowDescriptorValueGroups,
      encodeUnaryFramePeriodicSelectedMarkedRows]
  · intro group hgroup
    simpa [transitionDispatchMuxInvocationLabelMajorCoordinateSelection] using
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowDescriptorValueGroups_length
        W input group hgroup)

noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationLabelMajorCoordinateSelection
        transitionDispatchMuxInvocationLabelMajorCoordinateSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationLabelMajorCoordinateSelection
      transitionDispatchMuxInvocationLabelMajorCoordinateSelection_nonempty
      (verifierTransitionDispatchMuxInvocationLabelMajorFourRowNormalizedFrames
        W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Coordinate progression family carried by all label-major packets. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineUnaryTripleProgression :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
      W.machine.tm seed).flatMap
        TransitionDispatchMuxInvocationLabelMajorDescriptorPacket.coordinateProgressions

/-- Ordinary adjacent descriptor stream after erasing selected row markers. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows
      W input)

theorem
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions
          W input) := by
  unfold verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFrames
  rw [
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
              W.machine.tm seed).flatMap fun packet =>
                encodeUnaryFrame
                    (transitionDispatchProgressionDescriptorValues
                      packet.coordinateProgressions) ++ [.frameEnd]) =
        (((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchMuxInvocationLabelMajorDescriptorPackets
            W.machine.tm seed).map fun packet =>
              transitionDispatchProgressionDescriptorValues
                packet.coordinateProgressions).flatMap fun row =>
                  encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_assoc, List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  rw [encodeAffineUnaryTripleProgressionFamily_eq_encodeUnaryFrame]
  congr 1
  unfold
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions
    transitionDispatchProgressionDescriptorValues
  rw [List.flatten_eq_flatMap]
  conv_lhs => rw [List.flatMap_assoc]
  simp only [List.flatMap_map, id_eq]
  conv_rhs => rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  conv_rhs => rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro packet hpacket
  apply List.flatMap_congr
  intro progression hprogression
  rfl

noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateMarkedRows
        W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Executed coordinate rows of the new label-major route. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressionFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions
      W input)

/-- A single fixed polynomial-time TM2 now reaches executed coordinate rows
from the original verifier word through the label-major route. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressionFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressionFrames
        W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFrames_computableInPolyTime
      W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressions
        W) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationLabelMajorCoordinateFrames_eq
            W input] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      affineUnaryTripleProgressionFamilyFrameStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchMuxInvocationLabelMajorCoordinateProgressionFrames]
          using run }

end CLRS.Chapter34.Turing.CookLevin
