import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueProgressionExecute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorSemantics

/-!
# End-to-end execution of the routed dispatch true-arm channel

The unified mux descriptor source stores one verifier-fixed prefix-drop amount
before every raw true-arm affine span.  The preceding modules physically
recover and execute those spans while retaining one boundary per span.  This
module cycles through the fixed drop table, removes the declared row prefixes,
and erases the temporary span boundaries.

The resulting byte stream is proved equal both to the established complete
true-arm compiler and to the actual semantic true inputs of every dispatch
mux.  Thus the routed true channel is closed end to end from the original
verifier word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fixed prefix-drop period stored by one complete transition seed. -/
noncomputable def transitionDispatchTrueArmSpanDropAmounts
    (tm : _root_.Turing.FinTM2) : List Nat :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.affineSpanDropAmounts tm)

private theorem
    TransitionDispatchTrueArmNormalizedLayout.affineSpanDropAmounts_nonempty
    (tm : _root_.Turing.FinTM2)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    0 < (layout.affineSpanDropAmounts tm).length := by
  cases layout with
  | branch =>
      simp [TransitionDispatchTrueArmNormalizedLayout.affineSpanDropAmounts]
  | terminal labelOffset label rowLayout hlayout =>
      exact rowLayout.terminalAffineSpanDropAmounts_nonempty tm labelOffset

private theorem transitionDispatchTrueArmNormalizedLayouts_nonempty
    (tm : _root_.Turing.FinTM2) :
    transitionDispatchTrueArmNormalizedLayouts tm ≠ [] := by
  unfold transitionDispatchTrueArmNormalizedLayouts
  cases hlabels : programLabels tm with
  | nil => exact False.elim (programLabels_nonempty tm hlabels)
  | cons label labels =>
      simp only [transitionDispatchTrueArmNormalizedLayoutsForLabels]
      split <;> simp

/-- The fixed drop period is nonempty because the verifier program has at
least one label and every normalized label contributes at least one span. -/
theorem transitionDispatchTrueArmSpanDropAmounts_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionDispatchTrueArmSpanDropAmounts tm).length := by
  obtain ⟨layout, layouts, hlayouts⟩ := List.exists_cons_of_ne_nil
    (transitionDispatchTrueArmNormalizedLayouts_nonempty tm)
  unfold transitionDispatchTrueArmSpanDropAmounts
  rw [hlayouts]
  simp only [List.flatMap_cons, List.length_append]
  have hhead := layout.affineSpanDropAmounts_nonempty tm
  omega

private theorem transitionDispatchTrueArmSpanRawProgressionsFrom_length
    (seed : TransitionRowSeed) :
    ∀ (amounts : List Nat)
      (segments : List TransitionWidenedFallbackSegment),
      amounts.length = segments.length →
      (transitionDispatchTrueArmSpanRawProgressionsFrom seed amounts
        segments).length = amounts.length := by
  intro amounts
  induction amounts with
  | nil =>
      intro segments hlength
      have hnil : segments = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst segments
      rfl
  | cons amount amounts ih =>
      intro segments hlength
      cases segments with
      | nil => simp at hlength
      | cons segment segments =>
          simp only [List.length_cons] at hlength
          simp only [transitionDispatchTrueArmSpanRawProgressionsFrom,
            List.length_cons]
          rw [ih segments (by omega)]

/-- Every executed span-row period has exactly the length of the fixed drop
table that accompanies it. -/
theorem transitionDispatchTrueArmSpanRawValueRows_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchTrueArmSpanRawValueRows tm seed).length =
      (transitionDispatchTrueArmSpanDropAmounts tm).length := by
  unfold transitionDispatchTrueArmSpanRawValueRows
    transitionDispatchTrueArmSpanRawProgressions
    transitionDispatchTrueArmSpanDropAmounts
  rw [List.length_map]
  induction transitionDispatchTrueArmNormalizedLayouts tm with
  | nil => rfl
  | cons layout layouts ih =>
      simp only [List.flatMap_cons, List.length_append]
      rw [transitionDispatchTrueArmSpanRawProgressionsFrom_length seed
        (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)
        (layout.affineSpanDropAmounts_length tm), ih]

private theorem unaryFramePeriodicPrefixDropValues_append
    (leftDrops rightDrops : List Nat)
    (leftRows rightRows : List (List Nat))
    (hlength : leftDrops.length = leftRows.length) :
    unaryFramePeriodicPrefixDropValues (leftDrops ++ rightDrops)
        (leftRows ++ rightRows) =
      unaryFramePeriodicPrefixDropValues leftDrops leftRows ++
        unaryFramePeriodicPrefixDropValues rightDrops rightRows := by
  induction leftDrops generalizing leftRows with
  | nil =>
      have hnil : leftRows = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst leftRows
      rfl
  | cons amount amounts ih =>
      cases leftRows with
      | nil => simp at hlength
      | cons row rows =>
          simp only [List.length_cons] at hlength
          simp only [List.cons_append,
            unaryFramePeriodicPrefixDropValues]
          rw [ih rows (by omega)]

private theorem transitionDispatchTrueArmSpanDroppedValueRowsFrom
    (seed : TransitionRowSeed) :
    ∀ (amounts : List Nat)
      (segments : List TransitionWidenedFallbackSegment),
      unaryFramePeriodicPrefixDropValues amounts
          ((transitionDispatchTrueArmSpanRawProgressionsFrom seed amounts
            segments).map transitionProgressionFirstValues) =
        (transitionDispatchTrueArmSpanProgressionsFrom seed amounts
          segments).map transitionProgressionFirstValues := by
  intro amounts
  induction amounts with
  | nil =>
      intro segments
      rfl
  | cons amount amounts ih =>
      intro segments
      cases segments with
      | nil => rfl
      | cons segment segments =>
          simp only [transitionDispatchTrueArmSpanRawProgressionsFrom,
            transitionDispatchTrueArmSpanProgressionsFrom, List.map_cons,
            unaryFramePeriodicPrefixDropValues]
          rw [ih]
          rw [show transitionProgressionFirstValues
              (transitionWidenedFallbackSegmentProgression seed segment) =
                transitionWidenedFallbackSegmentValues seed segment by rfl]
          rw [transitionDispatchTrueArmSpanProgression_firstValues]

private theorem list_flatten_append {α : Type}
    (left right : List (List α)) :
    (left ++ right).flatten = left.flatten ++ right.flatten := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, List.flatten_cons, ih,
        List.append_assoc]

private theorem list_flatten_map_eq_flatMap {α β : Type}
    (values : List α) (f : α → List β) :
    (values.map f).flatten = values.flatMap f := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]

private theorem flattenedProgressionGroups_firstValues
    (groups : List (List AffineUnaryTripleProgression)) :
    ((groups.flatten.map transitionProgressionFirstValues).flatten) =
      (groups.map fun progressions =>
        progressions.flatMap transitionProgressionFirstValues).flatten := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      simp only [List.flatten_cons, List.map_append, List.map_cons]
      rw [list_flatten_append]
      rw [list_flatten_map_eq_flatMap]
      rw [ih]

/-- Semantic value rows after applying the fixed drop table to one executed
raw span period. -/
noncomputable def transitionDispatchTrueArmSpanDroppedValueRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  unaryFramePeriodicPrefixDropValues
    (transitionDispatchTrueArmSpanDropAmounts tm)
    (transitionDispatchTrueArmSpanRawValueRows tm seed)

/-- Periodic physical prefix deletion is exactly descriptor-level
normalization of every true-arm span. -/
theorem transitionDispatchTrueArmSpanDroppedValueRows_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchTrueArmSpanDroppedValueRows tm seed =
      (transitionDispatchTrueArmSpanProgressionGroups tm seed).flatten.map
        transitionProgressionFirstValues := by
  unfold transitionDispatchTrueArmSpanDroppedValueRows
    transitionDispatchTrueArmSpanDropAmounts
    transitionDispatchTrueArmSpanRawValueRows
    transitionDispatchTrueArmSpanRawProgressions
    transitionDispatchTrueArmSpanProgressionGroups
    TransitionDispatchTrueArmNormalizedLayout.affineSpanProgressions
  rw [List.map_flatMap]
  induction transitionDispatchTrueArmNormalizedLayouts tm with
  | nil => rfl
  | cons layout layouts ih =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons,
        List.map_append]
      rw [unaryFramePeriodicPrefixDropValues_append]
      · rw [transitionDispatchTrueArmSpanDroppedValueRowsFrom, ih]
      · rw [List.length_map]
        exact (transitionDispatchTrueArmSpanRawProgressionsFrom_length seed
          (layout.affineSpanDropAmounts tm)
          (layout.affineSpanSegments tm)
          (layout.affineSpanDropAmounts_length tm)).symm

/-- Apply the fixed drop period while preserving every temporary span
boundary. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicPrefixDrop
    (transitionDispatchTrueArmSpanDropAmounts W.machine.tm)
    (transitionDispatchTrueArmSpanDropAmounts_nonempty W.machine.tm)
    (verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames
      W input)

/-- Exact marked-row semantics after the periodic prefix-drop pass. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
        W input =
      encodeUnaryFramePeriodicPrefixDropOutput
        (transitionDispatchTrueArmSpanDropAmounts W.machine.tm)
        (verifierTransitionDispatchMuxInvocationDescriptorTrueRawValueRowGroups
          W input) := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames_eq]
  apply rewriteUnaryFramePeriodicPrefixDrop_groups
  intro group hgroup
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorTrueRawValueRowGroups at hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨seed, hseed, rfl⟩
  exact transitionDispatchTrueArmSpanRawValueRows_length W.machine.tm seed

/-- Erase temporary span boundaries after every declared prefix has been
removed. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
      W input)

/-- The routed true channel evaluates to the actual semantic true inputs of
every dispatch mux. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchTrueArmRowsFromSeed W.machine.tm seed).flatten) := by
  unfold verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames_eq]
  rw [show
      encodeUnaryFramePeriodicPrefixDropOutput
          (transitionDispatchTrueArmSpanDropAmounts W.machine.tm)
          (verifierTransitionDispatchMuxInvocationDescriptorTrueRawValueRowGroups
            W input) =
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          transitionDispatchTrueArmSpanDroppedValueRows W.machine.tm seed).flatMap
            (fun row => encodeUnaryFrame row ++ [.frameEnd]) by
      unfold encodeUnaryFramePeriodicPrefixDropOutput
        verifierTransitionDispatchMuxInvocationDescriptorTrueRawValueRowGroups
        transitionDispatchTrueArmSpanDroppedValueRows
      simp [List.flatMap_map, List.flatMap_assoc]]
  rw [unmarkAffineUnaryTripleProgressionRows_markedValues]
  congr 1
  rw [List.flatten_eq_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchTrueArmSpanDroppedValueRows_eq]
  have hsemantic := transitionDispatchTrueArmSpanProgressionGroups_eq_seed
    W input seed hseed
  have hflatten := congrArg List.flatten hsemantic
  rw [← List.flatten_eq_flatMap]
  rw [flattenedProgressionGroups_firstValues]
  exact hflatten

/-- The routed execution is byte-for-byte the established complete true-arm
compiler. -/
theorem verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames W input =
      verifierTransitionDispatchTrueArmAffineSpanFrames W input := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames_eq_semantic,
    verifierTransitionDispatchTrueArmAffineSpanFrames_eq_semantic]

/-- Periodic prefix deletion is polynomial-time from the original verifier
word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
        W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames_computableInPolyTime
        W)
      (unaryFramePeriodicPrefixDrop_computableInPolyTime
        (transitionDispatchTrueArmSpanDropAmounts W.machine.tm)
        (transitionDispatchTrueArmSpanDropAmounts_nonempty W.machine.tm))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicPrefixDrop
      (transitionDispatchTrueArmSpanDropAmounts W.machine.tm)
      (transitionDispatchTrueArmSpanDropAmounts_nonempty W.machine.tm)
      (verifierTransitionDispatchMuxInvocationDescriptorTrueRawMarkedFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames]
    using Classical.choice composed

/-- The complete physical true-channel interpreter is one concrete
polynomial-time TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanMarkedFrames
        W input))
  simpa [Function.comp_def,
    verifierTransitionDispatchMuxInvocationDescriptorTrueValueFrames]
    using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
