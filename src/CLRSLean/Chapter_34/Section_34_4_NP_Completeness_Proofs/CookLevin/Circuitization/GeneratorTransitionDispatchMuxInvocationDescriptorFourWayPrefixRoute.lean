import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorHalfDuplicate
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicPrefixDrop

/-!
# Prefix-routing four dispatch-mux descriptor channels

The duplicated physical layout is `tail / tail / head / head`.  A periodic
prefix pass gives the four copies distinct roles:

* remove the true-arm section from the first tail copy;
* retain the second tail copy;
* remove the selector section from the first head copy; and
* retain the second head copy.

The result is `false / full-tail / coordinates / full-head`, with every row
boundary retained for the subsequent suffix-routing pass.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Runtime fresh-coordinate progression descriptors. -/
def transitionDispatchMuxCoordinateDescriptorValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  transitionDispatchProgressionDescriptorValues
    (transitionDispatchMuxAffineProgressions tm seed)

/-- Runtime false-arm progression descriptors. -/
noncomputable def transitionDispatchMuxFalseArmDescriptorValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  transitionDispatchProgressionDescriptorValues
    (transitionDispatchFalseArmProgressions tm seed)

/-- The true-arm descriptor section has verifier-fixed width. -/
theorem transitionDispatchTrueArmSpanDescriptorValues_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchTrueArmSpanDescriptorValues tm seed).length =
      (transitionDispatchTrueArmSpanDescriptorForms tm).length := by
  have h := congrArg List.length
    (transitionDispatchTrueArmSpanDescriptorForms_value tm seed)
  simpa [affineUnaryTripleMap] using h.symm

/-- The selector descriptor section has verifier-fixed width. -/
theorem transitionDispatchSelectors_length_forms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchSelectors tm seed).length =
      (transitionDispatchSelectorForms tm).length := by
  have h := congrArg List.length
    (transitionDispatchSelectorForms_value tm seed)
  simpa [affineUnaryTripleMap] using h.symm

/-- Removing the leading true-arm section exposes the false-arm descriptors. -/
theorem transitionDispatchMuxInvocationDescriptorTailValues_drop_true
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationDescriptorTailValues tm seed).drop
        (transitionDispatchTrueArmSpanDescriptorForms tm).length =
      transitionDispatchMuxFalseArmDescriptorValues tm seed := by
  unfold transitionDispatchMuxInvocationDescriptorTailValues
    transitionDispatchMuxFalseArmDescriptorValues
  rw [← transitionDispatchTrueArmSpanDescriptorValues_length tm seed]
  simp

/-- Removing the leading selector section exposes the coordinate descriptors. -/
theorem transitionDispatchMuxInvocationDescriptorHeadValues_drop_selectors
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchMuxInvocationDescriptorHeadValues tm seed).drop
        (transitionDispatchSelectorForms tm).length =
      transitionDispatchMuxCoordinateDescriptorValues tm seed := by
  unfold transitionDispatchMuxInvocationDescriptorHeadValues
    transitionDispatchMuxCoordinateDescriptorValues
  rw [← transitionDispatchSelectors_length_forms tm seed]
  simp

/-- Verifier-fixed prefix deletion table for the four physical copies. -/
def transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops
    (tm : _root_.Turing.FinTM2) : List Nat :=
  [ (transitionDispatchTrueArmSpanDescriptorForms tm).length,
    0,
    (transitionDispatchSelectorForms tm).length,
    0 ]

/-- Four semantic rows per transition seed, matching the duplicated physical
stream exactly. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).map fun seed =>
    [ transitionDispatchMuxInvocationDescriptorTailValues W.machine.tm seed,
      transitionDispatchMuxInvocationDescriptorTailValues W.machine.tm seed,
      transitionDispatchMuxInvocationDescriptorHeadValues W.machine.tm seed,
      transitionDispatchMuxInvocationDescriptorHeadValues W.machine.tm seed ]

/-- Every semantic group has exactly the four rows required by the periodic
controller. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ group ∈
        verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups W input,
      group.length =
        (transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops
          W.machine.tm).length := by
  intro group hgroup
  unfold verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups at hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨seed, hseed, rfl⟩
  rfl

/-- The semantic four-row family is byte-for-byte the physical duplicated
half-row stream. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFramePeriodicPrefixDropInput
        (verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups
          W input) =
      verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows
        W input := by
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows_eq]
  unfold encodeUnaryFramePeriodicPrefixDropInput
    verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp [List.append_assoc]

/-- Physical stream after the first four-way routing pass. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicPrefixDrop
    (transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops W.machine.tm)
    (by simp [transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops])
    (verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows
      W input)

/-- Exact seed-major shape after prefix routing: false-arm descriptors,
complete tail, coordinate descriptors, and complete head. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (transitionDispatchMuxFalseArmDescriptorValues
              W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchMuxInvocationDescriptorTailValues
              W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchMuxCoordinateDescriptorValues
              W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchMuxInvocationDescriptorHeadValues
              W.machine.tm seed) ++
          [.frameEnd] := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows
  rw [←
    verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups_encoding_eq]
  rw [rewriteUnaryFramePeriodicPrefixDrop_groups _ _ _
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups_length
      W input)]
  unfold encodeUnaryFramePeriodicPrefixDropOutput
    verifierTransitionDispatchMuxInvocationDescriptorFourWayGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  simp only [transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops,
    unaryFramePeriodicPrefixDropValues, List.drop_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [transitionDispatchMuxInvocationDescriptorTailValues_drop_true,
    transitionDispatchMuxInvocationDescriptorHeadValues_drop_selectors]
  simp [List.append_assoc]

/-- The raw descriptor source through first-stage four-way routing is one
continuous polynomial-time TM2 from the verifier input. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayPrefixRows
        W) := by
  let source :=
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows_computableInPolyTime
      W
  let routed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFramePeriodicPrefixDrop_computableInPolyTime
        (transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops
          W.machine.tm)
        (by simp [transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops]))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      rewriteUnaryFramePeriodicPrefixDrop
        (transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops
          W.machine.tm)
        (by simp [transitionDispatchMuxInvocationDescriptorFourWayPrefixDrops])
        (verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows
          W input))
  simpa [Function.comp_def] using Classical.choice routed

end CLRS.Chapter34.Turing.CookLevin
