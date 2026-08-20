import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorFourWayRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowSelection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowUnmark

/-!
# Executing the physical dispatch-mux false-arm descriptor channel

The four-way router emits one marked `false / true / coordinates / selectors`
group per transition seed.  This module selects the first physical row of
every group, removes its outer marker, and feeds the recovered adjacent
descriptor family to the existing affine triple-progression executor.

This is the first end-to-end execution bridge out of the unified four-channel
source.  It deliberately exposes the selected stream as a separate checkpoint;
the later preserving interpreter will retain and reassemble all four channels.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Keep the false-arm row and erase the other three routed rows. -/
def transitionDispatchMuxInvocationDescriptorFalseSelection : List Bool :=
  [true, false, false, false]

theorem transitionDispatchMuxInvocationDescriptorFalseSelection_nonempty :
    0 < transitionDispatchMuxInvocationDescriptorFalseSelection.length := by
  simp [transitionDispatchMuxInvocationDescriptorFalseSelection]

/-- Final semantic four-row groups consumed by the periodic selector. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).map fun seed =>
    [ transitionDispatchMuxFalseArmDescriptorValues W.machine.tm seed,
      transitionDispatchTrueArmSpanDescriptorValues W.machine.tm seed,
      transitionDispatchMuxCoordinateDescriptorValues W.machine.tm seed,
      transitionDispatchSelectors W.machine.tm seed ]

theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ group ∈
        verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
          W input,
      group.length =
        transitionDispatchMuxInvocationDescriptorFalseSelection.length := by
  intro group hgroup
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups at hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨seed, hseed, rfl⟩
  rfl

/-- The semantic four-row family is byte-for-byte the final physical route. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFramePeriodicMarkedRowInput
        (verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
          W input).flatten =
      verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_eq]
  unfold encodeUnaryFramePeriodicMarkedRowInput
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
  rw [List.flatten_eq_flatMap, List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [List.append_assoc]

/-- Physical marked stream containing only the false-arm descriptor row of
each transition seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationDescriptorFalseSelection
    transitionDispatchMuxInvocationDescriptorFalseSelection_nonempty
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input)

/-- Periodic selection retains exactly one marked false-arm row per seed. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (transitionDispatchMuxFalseArmDescriptorValues
              W.machine.tm seed) ++ [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_encoding_eq]
  rw [rewriteUnaryFramePeriodicMarkedRows_encode]
  rw [encodeUnaryFramePeriodicMarkedRowOutput_groups _ _ _
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_length
      W input)]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [transitionDispatchMuxInvocationDescriptorFalseSelection,
    encodeUnaryFramePeriodicSelectedMarkedRows]

/-- The unified raw descriptor source followed by periodic row selection is
still one concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationDescriptorFalseSelection
        transitionDispatchMuxInvocationDescriptorFalseSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationDescriptorFalseSelection
      transitionDispatchMuxInvocationDescriptorFalseSelection_nonempty
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Adjacent seven-field descriptor family recovered from the selected rows. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows W input)

/-- Marker removal recovers exactly the canonical false-arm progression
descriptor family. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorFalseFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFalseFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchFalseArmProgressions W.machine.tm)) := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorFalseFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            encodeUnaryFrame
                (transitionDispatchMuxFalseArmDescriptorValues
                  W.machine.tm seed) ++ [.frameEnd]) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionDispatchMuxFalseArmDescriptorValues
            W.machine.tm seed).flatMap
              (fun row => encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  rw [encodeAffineUnaryTripleProgressionFamily_eq_encodeUnaryFrame]
  congr 1
  unfold transitionDispatchMuxFalseArmDescriptorValues
    transitionDispatchProgressionDescriptorValues
  rw [List.flatten_eq_flatMap, List.flatMap_map, List.flatMap_assoc]
  rfl

/-- The selected marker-removal bridge is a concrete polynomial-time TM2 from
the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFalseFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationDescriptorFalseMarkedRows
        W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Executed affine triple frames of the physically selected false-arm
descriptor channel. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseProgressionFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionDispatchFalseArmProgressions W.machine.tm))

/-- Physical four-way selection reaches the already established false-arm
coordinate-frame semantic target. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorFalseProgressionFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFalseProgressionFrames
        W input =
      verifierTransitionDispatchFalseArmCoordinateFrameStream W input := by
  rfl

/-- A single concrete polynomial-time TM2 follows the unified four-way route,
selects and unmasks the false descriptors, and executes every progression. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFalseProgressionFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFalseProgressionFrames
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
          verifierTransitionDispatchMuxInvocationDescriptorFalseProgressionFrames]
          using run }

end CLRS.Chapter34.Turing.CookLevin
