import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorFourWayPrefixRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicSuffixDrop

/-!
# Final four-way routing of dispatch-mux descriptors

The prefix pass left `false / full-tail / coordinates / full-head`.  This
module deletes the false-arm suffix from `full-tail` and the coordinate suffix
from `full-head`, producing four independent physical channels:

`false / true / coordinates / selectors`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The false-arm descriptor section has verifier-fixed width. -/
theorem transitionDispatchMuxFalseArmDescriptorValues_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxFalseArmDescriptorValues tm seed).length =
      (transitionDispatchFalseArmDescriptorForms tm).length := by
  have h := congrArg List.length
    (transitionDispatchFalseArmDescriptorForms_value tm seed)
  simpa [transitionDispatchMuxFalseArmDescriptorValues,
    transitionDispatchProgressionDescriptorValues,
    affineUnaryTripleMap] using h.symm

/-- The mux-coordinate descriptor section has verifier-fixed width. -/
theorem transitionDispatchMuxCoordinateDescriptorValues_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxCoordinateDescriptorValues tm seed).length =
      (transitionDispatchMuxDescriptorForms tm).length := by
  have h := congrArg List.length
    (transitionDispatchMuxDescriptorForms_value tm seed)
  simpa [transitionDispatchMuxCoordinateDescriptorValues,
    transitionDispatchProgressionDescriptorValues,
    affineUnaryTripleMap] using h.symm

/-- Removing the trailing false-arm descriptors leaves the true-arm section. -/
theorem transitionDispatchMuxInvocationDescriptorTailValues_rdrop_false
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationDescriptorTailValues tm seed).rdrop
        (transitionDispatchFalseArmDescriptorForms tm).length =
      transitionDispatchTrueArmSpanDescriptorValues tm seed := by
  unfold transitionDispatchMuxInvocationDescriptorTailValues
  change
    (transitionDispatchTrueArmSpanDescriptorValues tm seed ++
        transitionDispatchMuxFalseArmDescriptorValues tm seed).rdrop
        (transitionDispatchFalseArmDescriptorForms tm).length = _
  rw [← transitionDispatchMuxFalseArmDescriptorValues_length tm seed]
  rw [List.rdrop_append_length]

/-- Removing the trailing coordinate descriptors leaves the selectors. -/
theorem transitionDispatchMuxInvocationDescriptorHeadValues_rdrop_coordinates
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationDescriptorHeadValues tm seed).rdrop
        (transitionDispatchMuxDescriptorForms tm).length =
      transitionDispatchSelectors tm seed := by
  unfold transitionDispatchMuxInvocationDescriptorHeadValues
  change
    (transitionDispatchSelectors tm seed ++
        transitionDispatchMuxCoordinateDescriptorValues tm seed).rdrop
        (transitionDispatchMuxDescriptorForms tm).length = _
  rw [← transitionDispatchMuxCoordinateDescriptorValues_length tm seed]
  rw [List.rdrop_append_length]

/-- Verifier-fixed suffix deletion table for the four routed copies. -/
def transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops
    (tm : _root_.Turing.FinTM2) : List Nat :=
  [ 0,
    (transitionDispatchFalseArmDescriptorForms tm).length,
    0,
    (transitionDispatchMuxDescriptorForms tm).length ]

/-- Semantic groups expected by the final suffix router. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).map fun seed =>
    [ transitionDispatchMuxFalseArmDescriptorValues W.machine.tm seed,
      transitionDispatchMuxInvocationDescriptorTailValues W.machine.tm seed,
      transitionDispatchMuxCoordinateDescriptorValues W.machine.tm seed,
      transitionDispatchMuxInvocationDescriptorHeadValues W.machine.tm seed ]

theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ group ∈
        verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups
          W input,
      group.length =
        (transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops
          W.machine.tm).length := by
  intro group hgroup
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups at hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨seed, hseed, rfl⟩
  rfl

/-- The semantic suffix-router input is exactly the prefix-routed physical
stream. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFramePeriodicSuffixDropInput
        (verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups
          W input) =
      verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows_eq]
  unfold encodeUnaryFramePeriodicSuffixDropInput
    verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [List.append_assoc]

/-- Final four independent descriptor rows for every transition seed. -/
noncomputable def verifierTransitionDispatchMuxInvocationDescriptorFourWayRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicSuffixDrop
    (transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops W.machine.tm)
    (by simp [transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops])
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows
      W input)

/-- Exact seed-major shape of the fully separated physical descriptor
channels. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (transitionDispatchMuxFalseArmDescriptorValues
              W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchTrueArmSpanDescriptorValues
              W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchMuxCoordinateDescriptorValues
              W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame (transitionDispatchSelectors W.machine.tm seed) ++
          [.frameEnd] := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorFourWayRows
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups_encoding_eq]
  rw [rewriteUnaryFramePeriodicSuffixDrop_groups _ _ _
    (verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups_length
      W input)]
  unfold encodeUnaryFramePeriodicSuffixDropOutput
    verifierTransitionDispatchMuxInvocationDescriptorFourWaySuffixGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops,
    unaryFramePeriodicSuffixDropValues,
    unaryFramePeriodicReversedDropValues]
  rw [transitionDispatchMuxInvocationDescriptorTailValues_rdrop_false,
    transitionDispatchMuxInvocationDescriptorHeadValues_rdrop_coordinates]

/-- The complete raw-input source through four-way physical routing remains
one polynomial-time TM2 pipeline. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W) := by
  let source :=
    verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows_computableInPolyTime
      W
  let routed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFramePeriodicSuffixDrop_computableInPolyTime
        (transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops
          W.machine.tm)
        (by simp [transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops]))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFramePeriodicSuffixDrop
        (transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops
          W.machine.tm)
        (by simp [transitionDispatchMuxInvocationDescriptorFourWaySuffixDrops])
        (verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows
          W input))
  simpa [Function.comp_def] using Classical.choice routed

end CLRS.Chapter34.Turing.CookLevin
