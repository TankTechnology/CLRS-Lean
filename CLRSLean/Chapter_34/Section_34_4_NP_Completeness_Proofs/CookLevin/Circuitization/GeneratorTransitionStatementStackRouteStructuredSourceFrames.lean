import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteBlockSourceFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicBoundaryFilter

/-!
# Structured complete-stack source rows

Every selected descriptor is first executed as its own marked group.  A fixed
periodic boundary filter then merges the first two descriptor rows into the
height row and the remaining descriptor rows into the cell row.  The result
retains exactly the two structural boundaries required by later push/pop
streaming controllers.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First-coordinate value row denoted by one progression descriptor. -/
def affineUnaryTripleProgressionFirstRow
    (progression : AffineUnaryTripleProgression) : List Nat :=
  (affineUnaryTripleProgressionRows progression).map fun row => row.1

/-- Marking every single descriptor and projecting its first coordinate gives
one ordinary marked unary row per descriptor. -/
theorem affineUnaryTripleProgressionFixedSingletonFirstFrameStream_eq
    (progressions : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFixedGroupFirstFrameStream 0 progressions =
      encodeUnaryFramePeriodicMarkedRowInput
        (progressions.map affineUnaryTripleProgressionFirstRow) := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      rw [show progression :: rest = [progression] ++ rest by rfl]
      rw [affineUnaryTripleProgressionFixedGroupFirstFrameStream_append_group
        0 [progression] rest (by simp)]
      rw [ih]
      simp [encodeUnaryFramePeriodicMarkedRowInput,
        affineUnaryTripleProgressionFirstRow, List.append_assoc]

/-- Keep only the height/cell split and complete-block end in a periodic
descriptor row of size `3 + 2 * maxPushesPerStep tm`. -/
def transitionStackRouteStructuredBoundarySelection
    (tm : _root_.Turing.FinTM2) : List Bool :=
  [false, true] ++ List.replicate (2 * maxPushesPerStep tm) false ++ [true]

@[simp] theorem transitionStackRouteStructuredBoundarySelection_length
    (tm : _root_.Turing.FinTM2) :
    (transitionStackRouteStructuredBoundarySelection tm).length =
      transitionWidenedFallbackStackSegmentCount tm := by
  simp [transitionStackRouteStructuredBoundarySelection,
    transitionWidenedFallbackStackSegmentCount]
  omega

theorem transitionStackRouteStructuredBoundarySelection_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionStackRouteStructuredBoundarySelection tm).length := by
  rw [transitionStackRouteStructuredBoundarySelection_length]
  unfold transitionWidenedFallbackStackSegmentCount
  omega

/-- Descriptor first-coordinate rows grouped by their transition seed. -/
noncomputable def verifierTransitionStackRouteBlockDescriptorFirstRowGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).map fun seed =>
    (transitionStackRouteBlockProgressions W.machine.tm seed k).map
      affineUnaryTripleProgressionFirstRow

/-- Every descriptor is still separately marked after execution and
first-coordinate projection. -/
noncomputable def verifierTransitionStackRouteBlockDescriptorFirstFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  projectUnaryTripleGroupFirst
    (affineUnaryTripleProgressionFixedGroupFrameStream 0
      (verifierTransitionStackRouteBlockProgressions W k input))

/-- Exact marked descriptor-row semantics before structural boundary
selection. -/
theorem verifierTransitionStackRouteBlockDescriptorFirstFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteBlockDescriptorFirstFrames W k input =
      encodeUnaryFramePeriodicMarkedRowInput
        (verifierTransitionStackRouteBlockDescriptorFirstRowGroups
          W k input).flatten := by
  unfold verifierTransitionStackRouteBlockDescriptorFirstFrames
  rw [projectUnaryTripleGroupFirst_fixedGroupStream]
  rw [affineUnaryTripleProgressionFixedSingletonFirstFrameStream_eq]
  unfold verifierTransitionStackRouteBlockDescriptorFirstRowGroups
    verifierTransitionStackRouteBlockProgressions
  rw [List.map_flatMap]
  rfl

/-- A concrete polynomial-time machine emits the separately marked first-row
descriptor stream. -/
noncomputable def
    verifierTransitionStackRouteBlockDescriptorFirstFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteBlockDescriptorFirstFrames W k) := by
  let descriptors :=
    verifierTransitionStackRouteBlockDescriptorFrames_computableInPolyTime W k
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (verifierTransitionStackRouteBlockProgressions W k) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionStackRouteBlockDescriptorFrames_eq W k input]
          using run }
  let markedComposed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime 0)
  let marked := Classical.choice markedComposed
  let projectedComposed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch marked
      projectUnaryTripleGroupFirst_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => projectUnaryTripleGroupFirst
      (affineUnaryTripleProgressionFixedGroupFrameStream 0
        (verifierTransitionStackRouteBlockProgressions W k input)))
  simpa [Function.comp_def] using Classical.choice projectedComposed

/-- Two-boundary structured stack source produced from the raw verifier word.
-/
noncomputable def verifierTransitionStackRouteStructuredSourceFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicBoundaries
    (transitionStackRouteStructuredBoundarySelection W.machine.tm)
    (transitionStackRouteStructuredBoundarySelection_nonempty W.machine.tm)
    (verifierTransitionStackRouteBlockDescriptorFirstFrames W k input)

/-- Exact fixed-boundary semantics of the structured source. -/
theorem verifierTransitionStackRouteStructuredSourceFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteStructuredSourceFrames W k input =
      (verifierTransitionStackRouteBlockDescriptorFirstRowGroups W k input).flatMap
        (encodeUnaryFramePeriodicSelectedBoundaries
          (transitionStackRouteStructuredBoundarySelection W.machine.tm)) := by
  unfold verifierTransitionStackRouteStructuredSourceFrames
  rw [verifierTransitionStackRouteBlockDescriptorFirstFrames_eq]
  rw [rewriteUnaryFramePeriodicBoundaries_encode]
  apply encodeUnaryFramePeriodicBoundaryOutput_groups
  intro rows hrows
  unfold verifierTransitionStackRouteBlockDescriptorFirstRowGroups at hrows
  rw [List.mem_map] at hrows
  rcases hrows with ⟨seed, hseed, rfl⟩
  simp only [List.length_map]
  rw [transitionStackRouteBlockProgressions_length,
    transitionStackRouteStructuredBoundarySelection_length]

@[simp] private theorem encodeSelectedBoundaries_false_then_final
    (head : List Nat) (rows : List (List Nat)) :
    encodeUnaryFramePeriodicSelectedBoundaries
        (List.replicate rows.length false ++ [true]) (head :: rows) =
      encodeUnaryFrame head ++ encodeUnaryFrame rows.flatten ++ [.frameEnd] := by
  induction rows generalizing head with
  | nil =>
      simp [encodeUnaryFramePeriodicSelectedBoundaries, encodeUnaryFrame]
  | cons row rows ih =>
      rw [show (row :: rows).length = rows.length + 1 by simp,
        List.replicate_succ]
      simp only [List.cons_append,
        encodeUnaryFramePeriodicSelectedBoundaries, Bool.false_eq,
        List.flatten_cons]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

private theorem encodeSelectedBoundaries_two_groups
    (amount : Nat) (heightRows cellRows : List (List Nat))
    (hheight : heightRows.length = 2)
    (hcell : cellRows.length = 1 + 2 * amount) :
    encodeUnaryFramePeriodicSelectedBoundaries
        ([false, true] ++ List.replicate (2 * amount) false ++ [true])
        (heightRows ++ cellRows) =
      encodeUnaryFrame heightRows.flatten ++ [.frameEnd] ++
        encodeUnaryFrame cellRows.flatten ++ [.frameEnd] := by
  cases heightRows with
  | nil => simp at hheight
  | cons first rest =>
      cases rest with
      | nil => simp at hheight
      | cons second rest =>
          have hrestLength : rest.length = 0 := by
            simp only [List.length_cons] at hheight
            omega
          have hrest : rest = [] :=
            List.eq_nil_of_length_eq_zero hrestLength
          subst rest
          cases cellRows with
          | nil => omega
          | cons cell rest =>
              have htail : rest.length = 2 * amount := by
                simp only [List.length_cons] at hcell
                omega
              simp only [List.cons_append, List.nil_append,
                encodeUnaryFramePeriodicSelectedBoundaries,
                Bool.false_eq, if_true]
              rw [← htail, encodeSelectedBoundaries_false_then_final]
              simp [encodeUnaryFrame, List.append_assoc]

/-- Within one selected block, the retained boundaries merge the first two
descriptors into the height row and all remaining descriptors into the cell
row. -/
theorem transitionStackRouteStructuredBoundarySelection_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    encodeUnaryFramePeriodicSelectedBoundaries
        (transitionStackRouteStructuredBoundarySelection tm)
        ((transitionStackRouteBlockProgressions tm seed k).map
          affineUnaryTripleProgressionFirstRow) =
      encodeUnaryFrame
          (transitionStackRouteFirstValues
            (transitionStackRouteHeightProgressions tm seed k)) ++
        [.frameEnd] ++
        encodeUnaryFrame
          (transitionStackRouteFirstValues
            (transitionStackRouteCellProgressions tm seed k)) ++
        [.frameEnd] := by
  rw [transitionStackRouteBlockProgressions_eq_height_append_cell]
  rw [List.map_append]
  unfold transitionStackRouteStructuredBoundarySelection
  rw [encodeSelectedBoundaries_two_groups
    (maxPushesPerStep tm)
    ((transitionStackRouteHeightProgressions tm seed k).map
      affineUnaryTripleProgressionFirstRow)
    ((transitionStackRouteCellProgressions tm seed k).map
      affineUnaryTripleProgressionFirstRow)]
  · unfold transitionStackRouteFirstValues
      affineUnaryTripleProgressionFirstRow encodeUnaryFrame
    simp only [List.map_flatMap]
    rfl
  · simp [transitionStackRouteHeightProgressions_length]
  · simp [transitionStackRouteCellProgressions_length]

/-- The projected height family is the height field of the reconstructed
complete source block. -/
theorem transitionStackRouteFirstValues_eq_sourceBlock_height
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    transitionStackRouteFirstValues
        (transitionStackRouteHeightProgressions tm seed k) =
      (transitionStackRouteSourceBlock tm seed k).heightValues := by
  rfl

/-- The projected cell family is the flattened cell field of the reconstructed
complete source block. -/
theorem transitionStackRouteFirstValues_eq_sourceBlock_cells
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    transitionStackRouteFirstValues
        (transitionStackRouteCellProgressions tm seed k) =
      (transitionStackRouteSourceBlock tm seed k).cellRows.flatten := by
  have hblock := congrArg (fun block => block.cellRows.flatten)
    (transitionStackRouteSourceBlock_eq tm seed k)
  exact (transitionWidenedStackCellValues_eq_routeSource tm seed k).symm.trans
    hblock.symm

/-- Canonical two-row packet for every complete selected stack source. -/
noncomputable def transitionStackRouteStructuredSourceFrames
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  seeds.flatMap fun seed =>
    encodeUnaryFrame (transitionStackRouteSourceBlock tm seed k).heightValues ++
      [.frameEnd] ++
      encodeUnaryFrame
        (transitionStackRouteSourceBlock tm seed k).cellRows.flatten ++
      [.frameEnd]

/-- The concrete boundary-filtered output is exactly the two-row complete
stack source packet. -/
theorem verifierTransitionStackRouteStructuredSourceFrames_eq_source
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteStructuredSourceFrames W k input =
      transitionStackRouteStructuredSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input) := by
  rw [verifierTransitionStackRouteStructuredSourceFrames_eq]
  unfold verifierTransitionStackRouteBlockDescriptorFirstRowGroups
    transitionStackRouteStructuredSourceFrames
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionStackRouteStructuredBoundarySelection_values]
  rw [transitionStackRouteFirstValues_eq_sourceBlock_height,
    transitionStackRouteFirstValues_eq_sourceBlock_cells]

/-- The two-boundary source is a fixed polynomial-time output of the original
verifier word. -/
noncomputable def
    verifierTransitionStackRouteStructuredSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteStructuredSourceFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionStackRouteBlockDescriptorFirstFrames_computableInPolyTime
        W k)
      (unaryFramePeriodicBoundaryFilter_computableInPolyTime
        (transitionStackRouteStructuredBoundarySelection W.machine.tm)
        (transitionStackRouteStructuredBoundarySelection_nonempty W.machine.tm))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFramePeriodicBoundaries
      (transitionStackRouteStructuredBoundarySelection W.machine.tm)
      (transitionStackRouteStructuredBoundarySelection_nonempty W.machine.tm)
      (verifierTransitionStackRouteBlockDescriptorFirstFrames W k input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Unconditional polynomial-time machine for the canonical two-row complete
stack source packets. -/
noncomputable def
    transitionStackRouteStructuredSourceFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRouteStructuredSourceFrames W.machine.tm k
        (verifierTransitionRowSeeds W input)) := by
  let generated :=
    verifierTransitionStackRouteStructuredSourceFrames_computableInPolyTime W k
  exact
    { tm := generated.tm
      inputAlphabet := generated.inputAlphabet
      outputAlphabet := generated.outputAlphabet
      time := generated.time
      outputsFun := fun input => by
        have run := generated.outputsFun input
        simpa only [id_eq,
          verifierTransitionStackRouteStructuredSourceFrames_eq_source
            W k input] using run }

end CLRS.Chapter34.Turing.CookLevin
