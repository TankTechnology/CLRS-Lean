import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchQuotedMuxRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeedRowSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowPeriodicFilterCycle

/-!
# One quoted outer-dispatch mux row per transition seed

The global mux compiler emits one row for every `(seed, label)` pair.  Since
the label count is machine-fixed, a one-hot periodic controller selects one
fixed label position from every seed group, yielding a reusable
`VerifierTransitionSeedRowSource`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The builder-free artifact recursion preserves its input label count. -/
@[simp] theorem transitionDispatchLabelArtifacts_length
    (tm : _root_.Turing.FinTM2) (height falseWire trueWire : Nat)
    (source : CfgWires tm (workHeight tm height)) :
    ∀ (start : Nat) (fallback : CfgWires tm (workHeight tm height))
      (labels : List tm.Λ),
      (transitionDispatchLabelArtifacts tm height falseWire trueWire source
        start fallback labels).length = labels.length := by
  intro start fallback labels
  induction labels generalizing start fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchLabelArtifacts, List.length_cons]
      rw [ih]

/-- Quoted mux rows contributed by one canonical transition seed. -/
def transitionDispatchQuotedMuxRowsFromSeed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List UnaryFrameSym) :=
  (transitionDispatchArtifactsFromSeed tm seed).map fun artifact =>
    quoteUnaryFrameStream artifact.muxInvocationView.encode

@[simp] theorem transitionDispatchQuotedMuxRowsFromSeed_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionDispatchQuotedMuxRowsFromSeed tm seed).length =
      labelCount tm := by
  unfold transitionDispatchQuotedMuxRowsFromSeed
    transitionDispatchArtifactsFromSeed
  simp [programLabels]

/-- The public global quoted family is grouped seed-major, with exactly the
canonical artifact rows inside each group. -/
theorem verifierTransitionDispatchQuotedMuxFamily_rows_eq_groups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchQuotedMuxFamily W input).rows =
      (verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchQuotedMuxRowsFromSeed W.machine.tm) := by
  rw [verifierTransitionDispatchQuotedMuxFamily_rows]
  unfold verifierTransitionDispatchMuxInvocationViews
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchMuxDescriptorInvocationViews_eq_artifacts W input
    seed hseed]
  simp [transitionDispatchQuotedMuxRowsFromSeed, List.map_map,
    Function.comp_def]

/-- The fixed periodic position selecting one machine label. -/
def verifierTransitionDispatchMuxLabelSelection
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (position : Fin (labelCount W.machine.tm)) : List Bool :=
  unaryFrameMarkedRowOneHotSelection (labelCount W.machine.tm) position

theorem verifierTransitionDispatchMuxLabelSelection_nonempty
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (position : Fin (labelCount W.machine.tm)) :
    0 < (verifierTransitionDispatchMuxLabelSelection W position).length := by
  exact unaryFrameMarkedRowOneHotSelection_nonempty _ position

/-- Selected global family: one outer mux row per transition seed. -/
noncomputable def verifierTransitionDispatchQuotedMuxLabelFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (position : Fin (labelCount W.machine.tm))
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  UnaryFrameMarkedRowPeriodicFilter.selectedFamily
    (family := verifierTransitionDispatchQuotedMuxFamily W)
    (verifierTransitionDispatchMuxLabelSelection W position)
    (verifierTransitionDispatchMuxLabelSelection_nonempty W position) input

/-- Concrete raw-input source selecting one fixed outer mux label. -/
noncomputable def verifierTransitionDispatchQuotedMuxLabelSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (position : Fin (labelCount W.machine.tm)) :
    VerifierTransitionSeedRowSource W := by
  letI : Fintype Γ := W.alphabetFintype
  let selection := verifierTransitionDispatchMuxLabelSelection W position
  let hnonempty :=
    verifierTransitionDispatchMuxLabelSelection_nonempty W position
  let source :=
    UnaryFrameMarkedRowPeriodicFilter.computableInPolyTime
      (family := verifierTransitionDispatchQuotedMuxFamily W)
      selection hnonempty
      (verifierTransitionDispatchQuotedMuxFamily_computableInPolyTime W)
  exact
    { row := fun seed =>
        (transitionDispatchQuotedMuxRowsFromSeed W.machine.tm seed).getD
          position.val []
      family := verifierTransitionDispatchQuotedMuxLabelFamily W position
      rows_eq := fun input => by
        change selectUnaryFrameMarkedRows selection hnonempty
            (verifierTransitionDispatchQuotedMuxFamily W input).rows = _
        rw [verifierTransitionDispatchQuotedMuxFamily_rows_eq_groups W input]
        let groups := (verifierTransitionRowSeeds W input).map
          (transitionDispatchQuotedMuxRowsFromSeed W.machine.tm)
        have hgroups : ∀ rows ∈ groups,
            rows.length = labelCount W.machine.tm := by
          intro rows hrows
          rw [List.mem_map] at hrows
          rcases hrows with ⟨seed, hseed, rfl⟩
          exact transitionDispatchQuotedMuxRowsFromSeed_length W.machine.tm
            seed
        have hselected := selectUnaryFrameMarkedRows_groups_oneHot
          (labelCount W.machine.tm) position groups hgroups
        simpa only [selection,
          verifierTransitionDispatchMuxLabelSelection,
          groups, List.flatten_eq_flatMap, List.flatMap_map, List.map_map,
          Function.comp_def, id_eq] using
            hselected
      computableInPolyTime := by
        change _root_.Turing.TM2ComputableInPolyTime id
          encodeUnaryFrameMarkedRowFamily
          (UnaryFrameMarkedRowPeriodicFilter.selectedFamily
            (family := verifierTransitionDispatchQuotedMuxFamily W)
            selection hnonempty)
        exact source }

@[simp] theorem verifierTransitionDispatchQuotedMuxLabelSeedRowSource_row
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (position : Fin (labelCount W.machine.tm)) (seed : TransitionRowSeed) :
    (verifierTransitionDispatchQuotedMuxLabelSeedRowSource W position).row
        seed =
      (transitionDispatchQuotedMuxRowsFromSeed W.machine.tm seed).getD
        position.val [] := rfl

end CLRS.Chapter34.Turing.CookLevin
