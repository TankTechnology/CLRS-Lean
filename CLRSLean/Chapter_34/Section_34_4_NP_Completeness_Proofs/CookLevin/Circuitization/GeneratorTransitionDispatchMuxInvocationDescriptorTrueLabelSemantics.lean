import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorTrueLabelFrames

/-!
# Semantic closure of routed dispatch true-arm label rows

The physical boundary period from the preceding module is now identified with
the normalized program-label grouping.  Consequently its output is exactly
one marked unary row for every actual dispatch-mux `whenTrue` input row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem encodeUnaryFrame_append_values
    (left right : List Nat) :
    encodeUnaryFrame (left ++ right) =
      encodeUnaryFrame left ++ encodeUnaryFrame right := by
  simp [encodeUnaryFrame, List.flatMap_append]

private theorem encodeSelectedBoundaries_append
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

private theorem encodeSelectedBoundaries_keepLastRows
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
      rw [encodeUnaryFrame_append_values]
      simp [List.append_assoc]

private theorem encodeSelectedBoundaries_keepLastGroups
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
      rw [encodeSelectedBoundaries_append]
      · rw [show (row :: rows).length - 1 = rows.length by simp]
        rw [encodeSelectedBoundaries_keepLastRows, ih hgroups]
        rfl
      · simp

private theorem transitionDispatchTrueArmSpanProgressionsFrom_length
    (seed : TransitionRowSeed) :
    ∀ (amounts : List Nat)
      (segments : List TransitionWidenedFallbackSegment),
      amounts.length = segments.length →
      (transitionDispatchTrueArmSpanProgressionsFrom seed amounts segments).length =
        amounts.length := by
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
          simp only [transitionDispatchTrueArmSpanProgressionsFrom,
            List.length_cons]
          rw [ih segments (by omega)]

private theorem
    TransitionDispatchTrueArmNormalizedLayout.affineSpanProgressions_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    (layout.affineSpanProgressions tm seed).length =
      (layout.affineSpanDropAmounts tm).length := by
  unfold TransitionDispatchTrueArmNormalizedLayout.affineSpanProgressions
  exact transitionDispatchTrueArmSpanProgressionsFrom_length seed
    (layout.affineSpanDropAmounts tm) (layout.affineSpanSegments tm)
    (layout.affineSpanDropAmounts_length tm)

/-- The normalized span rows retain the fixed label grouping before their
temporary boundaries are merged. -/
theorem transitionDispatchTrueArmSpanDroppedValueRows_eq_labelSpans
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchTrueArmSpanDroppedValueRows tm seed =
      ((transitionDispatchTrueArmNormalizedLayouts tm).map fun layout =>
        (layout.affineSpanProgressions tm seed).map
          transitionProgressionFirstValues).flatten := by
  rw [transitionDispatchTrueArmSpanDroppedValueRows_eq]
  rw [List.map_flatten]
  unfold transitionDispatchTrueArmSpanProgressionGroups
  rw [List.map_map]
  rfl

private theorem transitionDispatchTrueArmDroppedRows_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchTrueArmSpanDroppedValueRows tm seed).length =
      (transitionDispatchTrueArmSpanLabelBoundarySelection tm).length := by
  rw [transitionDispatchTrueArmSpanDroppedValueRows_eq_labelSpans]
  unfold transitionDispatchTrueArmSpanLabelBoundarySelection
  induction transitionDispatchTrueArmNormalizedLayouts tm with
  | nil => rfl
  | cons layout layouts ih =>
      simp only [List.map_cons, List.flatten_cons, List.flatMap_cons,
        List.length_append, List.length_map]
      rw [layout.affineSpanProgressions_length]
      rw [show
          (transitionDispatchTrueArmKeepLastBoundary
            (layout.affineSpanDropAmounts tm)).length =
              (layout.affineSpanDropAmounts tm).length by
        unfold transitionDispatchTrueArmKeepLastBoundary
        have hpositive :=
          transitionDispatchTrueArmNormalizedLayout_dropAmounts_nonempty
            tm layout
        simp
        omega]
      exact congrArg (fun value =>
        (layout.affineSpanDropAmounts tm).length + value) ih

private theorem transitionDispatchTrueArmLabelSelection_eq_rows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchTrueArmSpanLabelBoundarySelection tm =
      (((transitionDispatchTrueArmNormalizedLayouts tm).map fun layout =>
        (layout.affineSpanProgressions tm seed).map
          transitionProgressionFirstValues).flatMap fun group =>
            List.replicate (group.length - 1) false ++ [true]) := by
  unfold transitionDispatchTrueArmSpanLabelBoundarySelection
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro layout hlayout
  rw [List.length_map, layout.affineSpanProgressions_length]
  rfl

private theorem transitionDispatchTrueArmLabelFrames_oneSeed
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    encodeUnaryFramePeriodicSelectedBoundaries
        (transitionDispatchTrueArmSpanLabelBoundarySelection W.machine.tm)
        (transitionDispatchTrueArmSpanDroppedValueRows W.machine.tm seed) =
      (transitionDispatchTrueArmRowsFromSeed W.machine.tm seed).flatMap
        fun row => encodeUnaryFrame row ++ [.frameEnd] := by
  rw [transitionDispatchTrueArmSpanDroppedValueRows_eq_labelSpans]
  rw [transitionDispatchTrueArmLabelSelection_eq_rows]
  let groups :=
    (transitionDispatchTrueArmNormalizedLayouts W.machine.tm).map fun layout =>
      (layout.affineSpanProgressions W.machine.tm seed).map
        transitionProgressionFirstValues
  have hnonempty : ∀ group ∈ groups, 0 < group.length := by
    intro group hgroup
    unfold groups at hgroup
    rw [List.mem_map] at hgroup
    rcases hgroup with ⟨layout, hlayout, rfl⟩
    rw [List.length_map, layout.affineSpanProgressions_length]
    exact transitionDispatchTrueArmNormalizedLayout_dropAmounts_nonempty
      W.machine.tm layout
  rw [encodeSelectedBoundaries_keepLastGroups groups hnonempty]
  have hsemantic := transitionDispatchTrueArmSpanProgressionGroups_eq_seed
    W input seed hseed
  have hgroupRows :
      groups.map List.flatten =
        (transitionDispatchTrueArmSpanProgressionGroups W.machine.tm seed).map
          (fun progressions =>
            progressions.flatMap transitionProgressionFirstValues) := by
    unfold groups transitionDispatchTrueArmSpanProgressionGroups
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro layout hlayout
    simp only [Function.comp_apply]
    rw [List.flatten_eq_flatMap, List.flatMap_map]
    rfl
  have hrows := hgroupRows.trans hsemantic
  have hencoded := congrArg
    (List.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) hrows
  simpa only [List.flatMap_map] using hencoded

/-- The concrete routed and boundary-restored true stream is exactly one
marked semantic `whenTrue` row per transition seed and program label. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchTrueArmRowsFromSeed W.machine.tm seed).flatMap
          fun row => encodeUnaryFrame row ++ [.frameEnd] := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorTrueLabelFrames_eq]
  rw [encodeUnaryFramePeriodicBoundaryOutput_groups]
  · unfold
      verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanValueRowGroups
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    exact transitionDispatchTrueArmLabelFrames_oneSeed W input seed hseed
  · intro group hgroup
    unfold
      verifierTransitionDispatchMuxInvocationDescriptorTrueDroppedSpanValueRowGroups at hgroup
    rw [List.mem_map] at hgroup
    rcases hgroup with ⟨seed, hseed, rfl⟩
    exact transitionDispatchTrueArmDroppedRows_length W.machine.tm seed

end CLRS.Chapter34.Turing.CookLevin
