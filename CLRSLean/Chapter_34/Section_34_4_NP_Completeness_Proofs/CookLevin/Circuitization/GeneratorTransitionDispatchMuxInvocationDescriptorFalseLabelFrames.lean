import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorFalseExecute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorAlignment
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryTripleGroupFirstProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicBoundaryFilter

/-!
# Label boundaries for the routed dispatch false arm

The first dispatch label reads the widened fallback row, which is assembled
from a fixed nonempty progression family.  Every later label reads one
preceding-mux output progression.  Thus one fixed boundary period merges only
the first family and retains every later progression boundary.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem fixedGroupZeroFirstFrameStream_eq
    (progressions : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFixedGroupFirstFrameStream 0 progressions =
      progressions.flatMap fun progression =>
        encodeUnaryFrame (transitionProgressionFirstValues progression) ++
          [.frameEnd] := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFixedGroupFirstFrameStream,
        affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom,
        List.flatMap_cons]
      change encodeUnaryFrame (transitionProgressionFirstValues progression) ++
          .frameEnd ::
            affineUnaryTripleProgressionFixedGroupFirstFrameStream 0 rest = _
      rw [ih]
      simp [List.append_assoc]

private theorem
    transitionDispatchPreviousOutputProgressionsForLabels_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (offset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchPreviousOutputProgressionsForLabels tm seed
        offset labels).length = labels.length - 1 := by
  intro offset labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      cases labels with
      | nil => rfl
      | cons next labels =>
          simp only [transitionDispatchPreviousOutputProgressionsForLabels,
            List.length_cons]
          rw [ih]
          simp

private theorem transitionDispatchPreviousOutputProgressions_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchPreviousOutputProgressions tm seed).length =
      (programLabels tm).length - 1 := by
  exact transitionDispatchPreviousOutputProgressionsForLabels_length tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Fixed boundary period: keep only the final widened-fallback span marker,
then keep every preceding-output marker. -/
noncomputable def transitionDispatchFalseArmLabelBoundarySelection
    (tm : _root_.Turing.FinTM2) : List Bool :=
  List.replicate ((transitionWidenedFallbackSegments tm).length - 1) false ++
    [true] ++ List.replicate ((programLabels tm).length - 1) true

theorem transitionDispatchFalseArmLabelBoundarySelection_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionDispatchFalseArmLabelBoundarySelection tm).length := by
  simp [transitionDispatchFalseArmLabelBoundarySelection]

/-- The fixed period consumes exactly the complete false-arm progression
family of every transition seed. -/
theorem transitionDispatchFalseArmLabelBoundarySelection_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchFalseArmLabelBoundarySelection tm).length =
      (transitionDispatchFalseArmProgressions tm seed).length := by
  have hsegments : 0 < (transitionWidenedFallbackSegments tm).length := by
    simp [transitionWidenedFallbackSegments]
  unfold transitionDispatchFalseArmLabelBoundarySelection
    transitionDispatchFalseArmProgressions
  simp only [List.length_append, List.length_replicate,
    List.length_singleton, transitionWidenedFallbackProgressions,
    List.length_map]
  rw [transitionDispatchPreviousOutputProgressions_length]
  omega

/-- First-coordinate value rows of the complete false progression family,
grouped by transition seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseRawValueRowGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).map fun seed =>
    (transitionDispatchFalseArmProgressions W.machine.tm seed).map
      transitionProgressionFirstValues

/-- Execute every recovered false descriptor as a singleton group and retain
its first-coordinate value row marker. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (affineUnaryTripleProgressionFixedGroupFrameStream 0
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchFalseArmProgressions W.machine.tm)))

theorem
    verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames
        W input =
      encodeUnaryFramePeriodicMarkedRowInput
        (verifierTransitionDispatchMuxInvocationDescriptorFalseRawValueRowGroups
          W input).flatten := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames
  rw [projectUnaryTripleGroupFirst_fixedGroupStream]
  rw [fixedGroupZeroFirstFrameStream_eq]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFalseRawValueRowGroups
    encodeUnaryFramePeriodicMarkedRowInput
  rw [List.flatten_eq_flatMap, List.flatMap_map, List.flatMap_assoc]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  simp only [id_eq]
  rw [List.flatMap_map]

/-- The routed descriptor recovery, singleton execution, and first-coordinate
projection form one concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames
        W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationDescriptorFalseFrames_computableInPolyTime
      W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchFalseArmProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorFalseFrames_eq
            W input] using run }
  let executed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime 0)
  let projected :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice executed)
      projectUnaryTripleGroupFirst_computableInPolyTime
  let result := Classical.choice projected
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames]
          using run }

/-- Merge the widened-fallback progression markers into the first label row,
while retaining every later label boundary. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicBoundaries
    (transitionDispatchFalseArmLabelBoundarySelection W.machine.tm)
    (transitionDispatchFalseArmLabelBoundarySelection_nonempty W.machine.tm)
    (verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames
      W input)

theorem verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames W input =
      encodeUnaryFramePeriodicBoundaryOutput
        (transitionDispatchFalseArmLabelBoundarySelection W.machine.tm)
        (transitionDispatchFalseArmLabelBoundarySelection_nonempty W.machine.tm)
        (verifierTransitionDispatchMuxInvocationDescriptorFalseRawValueRowGroups
          W input).flatten := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames_eq]
  exact rewriteUnaryFramePeriodicBoundaries_encode _ _ _

/-- The complete false-label boundary restoration remains polynomial-time
from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicBoundaryFilter_computableInPolyTime
        (transitionDispatchFalseArmLabelBoundarySelection W.machine.tm)
        (transitionDispatchFalseArmLabelBoundarySelection_nonempty
          W.machine.tm))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicBoundaries
      (transitionDispatchFalseArmLabelBoundarySelection W.machine.tm)
      (transitionDispatchFalseArmLabelBoundarySelection_nonempty W.machine.tm)
      (verifierTransitionDispatchMuxInvocationDescriptorFalseRawMarkedFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
