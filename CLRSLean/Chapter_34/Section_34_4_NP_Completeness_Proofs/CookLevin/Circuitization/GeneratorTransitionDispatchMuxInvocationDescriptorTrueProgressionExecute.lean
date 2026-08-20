import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionFixedGroups
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryTripleGroupFirstProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicPrefixDrop

/-!
# Executing routed true-arm progression descriptors

The preceding physical interpreter recovers the ordinary seven-field affine
progression family stored in the routed true-arm channel.  This module feeds
that exact byte stream to the generic fixed-group progression executor with
group size one and projects each triple row to its first coordinate.

Consequently every original true-arm affine span becomes one independently
marked unary value row.  Those boundaries are retained for the next fixed
periodic prefix-drop pass.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First-coordinate rows of all raw true-arm progressions belonging to one
transition seed. -/
noncomputable def transitionDispatchTrueArmSpanRawValueRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  (transitionDispatchTrueArmSpanRawProgressions tm seed).map
    transitionProgressionFirstValues

/-- One complete fixed row period for every transition seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawValueRowGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).map
    (transitionDispatchTrueArmSpanRawValueRows W.machine.tm)

private theorem fixedGroupZeroFirstFrameStream
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

/-- Execute every recovered descriptor as its own marked triple-row group and
retain only the first coordinate. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (affineUnaryTripleProgressionFixedGroupFrameStream 0
      (verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions
        W input))

/-- The physical execution result is exactly the complete marked-row family
expected by the periodic prefix-drop controller. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames
        W input =
      encodeUnaryFramePeriodicPrefixDropInput
        (verifierTransitionDispatchMuxInvocationDescriptorTrueRawValueRowGroups
          W input) := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames
  rw [projectUnaryTripleGroupFirst_fixedGroupStream]
  rw [fixedGroupZeroFirstFrameStream]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawValueRowGroups
    transitionDispatchTrueArmSpanRawValueRows
    encodeUnaryFramePeriodicPrefixDropInput
  simp [List.flatMap_map, List.flatMap_assoc]

/-- The routed descriptor recovery, singleton-group execution, and first
coordinate projection form one concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames_computableInPolyTime
      W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (verifierTransitionDispatchMuxInvocationDescriptorTrueRawProgressions W) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorTrueProgressionFrames_eq
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
          verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames]
          using run }

end CLRS.Chapter34.Turing.CookLevin
