import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorFalseLabelFrames

/-!
# Semantic closure of routed dispatch false-arm label rows

The physical boundary period from the preceding module merges the complete
widened fallback family into the first label and retains each later singleton
preceding-output row.  This module identifies those marked payloads with the
actual dispatch-mux `whenFalse` rows.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem encodeUnaryFrame_append_values_false
    (left right : List Nat) :
    encodeUnaryFrame (left ++ right) =
      encodeUnaryFrame left ++ encodeUnaryFrame right := by
  simp [encodeUnaryFrame, List.flatMap_append]

private theorem encodeSelectedBoundaries_append_false
    (leftKeeps rightKeeps : List Bool)
    (leftRows rightRows : List (List Nat))
    (hlength : leftKeeps.length = leftRows.length) :
    encodeUnaryFramePeriodicSelectedBoundaries
        (leftKeeps ++ rightKeeps) (leftRows ++ rightRows) =
      encodeUnaryFramePeriodicSelectedBoundaries leftKeeps leftRows ++
        encodeUnaryFramePeriodicSelectedBoundaries rightKeeps rightRows := by
  induction leftKeeps generalizing leftRows with
  | nil =>
      have hnil : leftRows = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst leftRows
      rfl
  | cons keep keeps ih =>
      cases leftRows with
      | nil => simp at hlength
      | cons row rows =>
          simp only [List.length_cons] at hlength
          simp only [List.cons_append,
            encodeUnaryFramePeriodicSelectedBoundaries]
          rw [ih rows (by omega)]
          simp [List.append_assoc]

private theorem encodeSelectedBoundaries_keepLastRows_false
    (row : List Nat) (rows : List (List Nat)) :
    encodeUnaryFramePeriodicSelectedBoundaries
        (List.replicate rows.length false ++ [true]) (row :: rows) =
      encodeUnaryFrame (row :: rows).flatten ++ [.frameEnd] := by
  induction rows generalizing row with
  | nil =>
      simp [encodeUnaryFramePeriodicSelectedBoundaries]
  | cons next rows ih =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append,
        encodeUnaryFramePeriodicSelectedBoundaries,
        List.flatten_cons]
      rw [ih]
      rw [encodeUnaryFrame_append_values_false]
      simp [List.append_assoc]

private theorem encodeSelectedBoundaries_keepLastGroups_false
    (groups : List (List (List Nat)))
    (hnonempty : ∀ group ∈ groups, 0 < group.length) :
    encodeUnaryFramePeriodicSelectedBoundaries
        (groups.flatMap fun group =>
          List.replicate (group.length - 1) false ++ [true])
        groups.flatten =
      groups.flatMap fun group =>
        encodeUnaryFrame group.flatten ++ [.frameEnd] := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      have hgroup := hnonempty group (by simp)
      obtain ⟨row, rows, rfl⟩ := List.exists_cons_of_ne_nil
        (List.ne_nil_of_length_pos hgroup)
      have hgroups : ∀ other ∈ groups, 0 < other.length := by
        intro other hother
        exact hnonempty other (by simp [hother])
      simp only [List.flatMap_cons, List.flatten_cons]
      rw [encodeSelectedBoundaries_append_false]
      · rw [show (row :: rows).length - 1 = rows.length by simp]
        rw [encodeSelectedBoundaries_keepLastRows_false, ih hgroups]
        rfl
      · simp

private theorem singletonProgressionValueGroups_flatten
    (progressions : List AffineUnaryTripleProgression) :
    ((progressions.map fun progression => [progression]).map fun group =>
        group.map transitionProgressionFirstValues).flatten =
      progressions.map transitionProgressionFirstValues := by
  induction progressions with
  | nil => rfl
  | cons progression progressions ih =>
      simp only [List.map_cons, List.flatten_cons]
      rw [ih]
      rfl

private theorem singletonProgressionValueGroups_boundaries
    (progressions : List AffineUnaryTripleProgression) :
    (((progressions.map fun progression => [progression]).map fun group =>
        group.map transitionProgressionFirstValues).flatMap fun group =>
          List.replicate (group.length - 1) false ++ [true]) =
      List.replicate progressions.length true := by
  induction progressions with
  | nil => rfl
  | cons progression progressions ih =>
      simp only [List.map_cons, List.flatMap_cons, List.length_cons,
        List.length_nil, Nat.add_one_sub_one, List.replicate_zero,
        List.nil_append, List.length_map, List.replicate_succ]
      rw [ih]
      rfl

/-- The raw false progression rows are the flattened label-preserving false
progression groups. -/
theorem transitionDispatchFalseArmValueRows_eq_progressionGroups
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchFalseArmProgressions tm seed).map
        transitionProgressionFirstValues =
      ((transitionDispatchFalseArmProgressionGroups tm seed).map fun group =>
        group.map transitionProgressionFirstValues).flatten := by
  unfold transitionDispatchFalseArmProgressions
    transitionDispatchFalseArmProgressionGroups
  rw [List.map_append]
  simp only [List.map_cons, List.flatten_cons]
  rw [singletonProgressionValueGroups_flatten]

private theorem
    transitionDispatchFalseArmLabelBoundarySelection_eq_valueGroups
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchFalseArmLabelBoundarySelection tm =
      ((transitionDispatchFalseArmProgressionGroups tm seed).map fun group =>
        group.map transitionProgressionFirstValues).flatMap fun group =>
          List.replicate (group.length - 1) false ++ [true] := by
  unfold transitionDispatchFalseArmLabelBoundarySelection
    transitionDispatchFalseArmProgressionGroups
  simp only [List.map_cons, List.flatMap_cons, List.length_map]
  rw [singletonProgressionValueGroups_boundaries]
  rw [transitionDispatchPreviousOutputProgressions_length]
  simp [transitionWidenedFallbackProgressions, List.append_assoc]

private theorem transitionDispatchFalseArmValueGroups_nonempty
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ group ∈
        (transitionDispatchFalseArmProgressionGroups tm seed).map
          (fun progressions =>
            progressions.map transitionProgressionFirstValues),
      0 < group.length := by
  intro group hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨progressions, hprogressions, rfl⟩
  rw [List.length_map]
  unfold transitionDispatchFalseArmProgressionGroups at hprogressions
  simp only [List.mem_cons, List.mem_map] at hprogressions
  rcases hprogressions with hfirst | ⟨progression, hprogression, hlater⟩
  · simpa [hfirst, transitionWidenedFallbackProgressions,
      transitionWidenedFallbackSegments]
  · rw [← hlater]
    simp

private theorem transitionDispatchFalseArmLabelFrames_oneSeed
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    encodeUnaryFramePeriodicSelectedBoundaries
        (transitionDispatchFalseArmLabelBoundarySelection W.machine.tm)
        ((transitionDispatchFalseArmProgressions W.machine.tm seed).map
          transitionProgressionFirstValues) =
      (transitionDispatchFalseArmRowsFromSeed W.machine.tm seed).flatMap
        fun row => encodeUnaryFrame row ++ [.frameEnd] := by
  rw [transitionDispatchFalseArmValueRows_eq_progressionGroups]
  rw [transitionDispatchFalseArmLabelBoundarySelection_eq_valueGroups]
  let groups :=
    (transitionDispatchFalseArmProgressionGroups W.machine.tm seed).map
      (fun progressions =>
        progressions.map transitionProgressionFirstValues)
  rw [encodeSelectedBoundaries_keepLastGroups_false groups
    (transitionDispatchFalseArmValueGroups_nonempty W.machine.tm seed)]
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
    rw [hheight]
    unfold workHeight
    exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _
  have hsemantic := transitionDispatchFalseArmProgressionGroups_values
    W.machine.tm seed hwork
  have hgroupRows :
      groups.map List.flatten =
        (transitionDispatchFalseArmProgressionGroups W.machine.tm seed).map
          (fun progressions =>
            progressions.flatMap transitionProgressionFirstValues) := by
    unfold groups
    rw [List.map_map]
    apply List.map_congr_left
    intro progressions hprogressions
    simp only [Function.comp_apply]
    rw [List.flatten_eq_flatMap, List.flatMap_map]
    simp
  have hrows := hgroupRows.trans hsemantic
  have hencoded := congrArg
    (List.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) hrows
  simpa only [List.flatMap_map] using hencoded

/-- The routed and boundary-restored false stream is exactly one marked
semantic `whenFalse` row per transition seed and program label. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchFalseArmRowsFromSeed W.machine.tm seed).flatMap
          fun row => encodeUnaryFrame row ++ [.frameEnd] := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorFalseLabelFrames_eq]
  rw [encodeUnaryFramePeriodicBoundaryOutput_groups]
  · unfold
      verifierTransitionDispatchMuxInvocationDescriptorFalseRawValueRowGroups
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    exact transitionDispatchFalseArmLabelFrames_oneSeed W input seed hseed
  · intro group hgroup
    unfold
      verifierTransitionDispatchMuxInvocationDescriptorFalseRawValueRowGroups at hgroup
    rw [List.mem_map] at hgroup
    rcases hgroup with ⟨seed, hseed, rfl⟩
    simpa only [List.length_map] using
      (transitionDispatchFalseArmLabelBoundarySelection_length
        W.machine.tm seed).symm

end CLRS.Chapter34.Turing.CookLevin
