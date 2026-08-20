import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorCoordinateExecute

/-!
# Recovering the physical dispatch-mux selector channel

The final four-way descriptor route stores one marked selector row after the
false, true, and coordinate rows of each transition seed.  This module selects
that fourth row and removes its outer marker.  The recovered bytes are proved
equal to the established raw-input selector frame stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Keep the selector row and erase the other three routed rows. -/
def transitionDispatchMuxInvocationDescriptorSelectorSelection : List Bool :=
  [false, false, false, true]

theorem transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty :
    0 < transitionDispatchMuxInvocationDescriptorSelectorSelection.length := by
  simp [transitionDispatchMuxInvocationDescriptorSelectorSelection]

/-- Physical marked stream containing only the selector row of each
transition seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationDescriptorSelectorSelection
    transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input)

/-- Periodic selection retains exactly one marked selector row per seed. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame (transitionDispatchSelectors W.machine.tm seed) ++
          [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_encoding_eq]
  rw [rewriteUnaryFramePeriodicMarkedRows_encode]
  have hgroups : ∀ group ∈
      verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
        W input,
      group.length =
        transitionDispatchMuxInvocationDescriptorSelectorSelection.length := by
    intro group hgroup
    have hlength :=
      verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_length
        W input group hgroup
    simpa [transitionDispatchMuxInvocationDescriptorFalseSelection,
      transitionDispatchMuxInvocationDescriptorSelectorSelection] using
        hlength
  rw [encodeUnaryFramePeriodicMarkedRowOutput_groups
    transitionDispatchMuxInvocationDescriptorSelectorSelection
    transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty _
    hgroups]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [transitionDispatchMuxInvocationDescriptorSelectorSelection,
    encodeUnaryFramePeriodicSelectedMarkedRows]

/-- The unified raw descriptor source followed by selector-row selection is
one concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationDescriptorSelectorSelection
        transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationDescriptorSelectorSelection
      transitionDispatchMuxInvocationDescriptorSelectorSelection_nonempty
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Ordinary selector frame stream recovered from the selected marked rows. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
      W input)

/-- Marker removal recovers exactly the established selector source. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames W input =
      verifierTransitionDispatchSelectorFrames W input := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            encodeUnaryFrame (transitionDispatchSelectors W.machine.tm seed) ++
              [.frameEnd]) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionDispatchSelectors W.machine.tm seed).flatMap
            (fun row => encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  rw [verifierTransitionDispatchSelectorFrames_eq]
  congr 1

/-- A concrete polynomial-time TM2 follows the unified route, selects the
fourth physical channel, and emits the canonical selector frames. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationDescriptorSelectorMarkedRows
        W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
