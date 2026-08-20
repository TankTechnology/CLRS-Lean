import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSelectorFrames

/-!
# Recovering the physical dispatch-mux true-arm descriptor channel

The second row of every final four-way group contains the true-arm affine-span
descriptor blocks.  This module selects and unmasks that physical row.  It
proves both the exact value-level encoding and equality with evaluation of the
fixed affine form table.  Interpreting each eight-field block as a normalized
seven-field progression is intentionally left to the next small module.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Keep the true-arm row and erase the other three routed rows. -/
def transitionDispatchMuxInvocationDescriptorTrueSelection : List Bool :=
  [false, true, false, false]

theorem transitionDispatchMuxInvocationDescriptorTrueSelection_nonempty :
    0 < transitionDispatchMuxInvocationDescriptorTrueSelection.length := by
  simp [transitionDispatchMuxInvocationDescriptorTrueSelection]

/-- Physical marked stream containing only the true-arm descriptor row of
each transition seed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    transitionDispatchMuxInvocationDescriptorTrueSelection
    transitionDispatchMuxInvocationDescriptorTrueSelection_nonempty
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input)

/-- Periodic selection retains exactly one marked true-arm row per seed. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (transitionDispatchTrueArmSpanDescriptorValues
              W.machine.tm seed) ++ [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_encoding_eq]
  rw [rewriteUnaryFramePeriodicMarkedRows_encode]
  have hgroups : ∀ group ∈
      verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
        W input,
      group.length =
        transitionDispatchMuxInvocationDescriptorTrueSelection.length := by
    intro group hgroup
    have hlength :=
      verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups_length
        W input group hgroup
    simpa [transitionDispatchMuxInvocationDescriptorFalseSelection,
      transitionDispatchMuxInvocationDescriptorTrueSelection] using hlength
  rw [encodeUnaryFramePeriodicMarkedRowOutput_groups
    transitionDispatchMuxInvocationDescriptorTrueSelection
    transitionDispatchMuxInvocationDescriptorTrueSelection_nonempty _ hgroups]
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWayValueGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [transitionDispatchMuxInvocationDescriptorTrueSelection,
    encodeUnaryFramePeriodicSelectedMarkedRows]

/-- The unified raw descriptor source followed by true-arm row selection is
one concrete polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_computableInPolyTime
        W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        transitionDispatchMuxInvocationDescriptorTrueSelection
        transitionDispatchMuxInvocationDescriptorTrueSelection_nonempty)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicMarkedRows
      transitionDispatchMuxInvocationDescriptorTrueSelection
      transitionDispatchMuxInvocationDescriptorTrueSelection_nonempty
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Ordinary eight-field true-arm block stream recovered from the selected
marked rows. -/
noncomputable def verifierTransitionDispatchMuxInvocationDescriptorTrueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows W input)

/-- Marker removal preserves every eight-field block in row-major order. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorTrueFrames_eq_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchTrueArmSpanDescriptorValues W.machine.tm)) := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorTrueFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            encodeUnaryFrame
                (transitionDispatchTrueArmSpanDescriptorValues
                  W.machine.tm seed) ++ [.frameEnd]) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionDispatchTrueArmSpanDescriptorValues
            W.machine.tm seed).flatMap
              (fun row => encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_map]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  congr 1

/-- The physical true-arm bytes are exactly evaluation of the verifier-fixed
affine descriptor table. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorTrueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueFrames W input =
      verifierTransitionAffineMapFrames W
        (transitionDispatchTrueArmSpanDescriptorForms W.machine.tm) input := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueFrames_eq_values]
  unfold verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  congr 1
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  exact (transitionDispatchTrueArmSpanDescriptorForms_value
    W.machine.tm seed).symm

/-- A concrete polynomial-time TM2 follows the unified route, selects the
second physical channel, and emits the exact true-arm descriptor blocks. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationDescriptorTrueMarkedRows W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
