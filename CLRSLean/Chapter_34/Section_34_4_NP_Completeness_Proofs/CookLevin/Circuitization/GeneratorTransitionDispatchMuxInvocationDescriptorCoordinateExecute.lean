import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorFalseExecute

/-!
# Executing the physical dispatch-mux coordinate descriptor channel

The final four-way route stores `false / true / coordinates / selectors` for
each transition seed.  This module selects the third marked row, removes its
outer boundary, and executes the recovered affine triple progressions.  The
result is identified with the established semantic fresh-coordinate stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Keep the coordinate row and erase the other three routed rows. -/
def transitionDispatchMuxInvocationDescriptorCoordinateSelection : List Bool :=
  [false, false, true, false]

theorem transitionDispatchMuxInvocationDescriptorCoordinateSelection_nonempty :
    0 < transitionDispatchMuxInvocationDescriptorCoordinateSelection.length := by
  simp [transitionDispatchMuxInvocationDescriptorCoordinateSelection]

/-- Physical marked stream containing only the coordinate descriptor row of
each transition seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationDescriptorCoordinateSelection
    transitionDispatchMuxInvocationDescriptorCoordinateSelection_nonempty
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input)

/-- Periodic selection retains exactly one marked coordinate row per seed. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (transitionDispatchMuxCoordinateDescriptorValues
              W.machine.tm seed) ++ [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_encoding_eq]
  rw [rewriteUnaryFramePeriodicMarkedRows_encode]
  have hgroups : ∀ group ∈
      verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
        W input,
      group.length =
        transitionDispatchMuxInvocationDescriptorCoordinateSelection.length := by
    intro group hgroup
    have hlength :=
      verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_length
        W input group hgroup
    simpa [transitionDispatchMuxInvocationDescriptorFalseSelection,
      transitionDispatchMuxInvocationDescriptorCoordinateSelection] using
        hlength
  rw [encodeUnaryFramePeriodicMarkedRowOutput_groups
    transitionDispatchMuxInvocationDescriptorCoordinateSelection
    transitionDispatchMuxInvocationDescriptorCoordinateSelection_nonempty _
    hgroups]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [transitionDispatchMuxInvocationDescriptorCoordinateSelection,
    encodeUnaryFramePeriodicSelectedMarkedRows]

/-- The unified raw descriptor source followed by coordinate-row selection is
one concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationDescriptorCoordinateSelection
        transitionDispatchMuxInvocationDescriptorCoordinateSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationDescriptorCoordinateSelection
      transitionDispatchMuxInvocationDescriptorCoordinateSelection_nonempty
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Adjacent seven-field coordinate descriptor family recovered from the
selected marked rows. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows
      W input)

/-- Marker removal recovers exactly the canonical coordinate progression
descriptor family. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames W input =
      encodeAffineUnaryTripleProgressionFamily
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxAffineProgressions W.machine.tm)) := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            encodeUnaryFrame
                (transitionDispatchMuxCoordinateDescriptorValues
                  W.machine.tm seed) ++ [.frameEnd]) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionDispatchMuxCoordinateDescriptorValues
            W.machine.tm seed).flatMap
              (fun row => encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  rw [encodeAffineUnaryTripleProgressionFamily_eq_encodeUnaryFrame]
  congr 1
  unfold transitionDispatchMuxCoordinateDescriptorValues
    transitionDispatchProgressionDescriptorValues
  rw [List.flatten_eq_flatMap, List.flatMap_map, List.flatMap_assoc]
  rfl

/-- The selected coordinate marker-removal bridge is a concrete
polynomial-time TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationDescriptorCoordinateMarkedRows
        W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Executed affine triple frames of the physically selected coordinate
descriptor channel. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateProgressionFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFamilyFrameStream
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionDispatchMuxAffineProgressions W.machine.tm))

/-- Physical four-way selection reaches the established mux-coordinate
semantic target. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateProgressionFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateProgressionFrames
        W input =
      verifierTransitionDispatchMuxCoordinateFrameStream W input := by
  rfl

/-- A single concrete polynomial-time TM2 follows the unified four-way route,
selects and unmasks the coordinate descriptors, and executes every
progression. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateProgressionFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorCoordinateProgressionFrames
        W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames_computableInPolyTime
      W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxAffineProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames_eq
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
          verifierTransitionDispatchMuxInvocationDescriptorCoordinateProgressionFrames]
          using run }

end CLRS.Chapter34.Turing.CookLevin
