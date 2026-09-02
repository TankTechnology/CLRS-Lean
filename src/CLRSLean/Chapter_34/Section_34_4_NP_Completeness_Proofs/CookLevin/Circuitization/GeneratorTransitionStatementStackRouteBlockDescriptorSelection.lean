import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteDescriptorSelectionSemantics

/-!
# Selecting one complete stack descriptor block

The height and cell selectors are useful for primitive projections.  A
sequential stack-action controller instead needs the complete selected stack
as one row.  This file supplies the corresponding fixed Boolean mask and
proves its concrete periodic-filter output contract.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Keep every progression of one selected stack and erase the prefix and all
other stack blocks. -/
noncomputable def transitionStackRouteBlockDescriptorSelection
    (tm : _root_.Turing.FinTM2) (k : tm.K) : List Bool :=
  false ::
    ((arithmeticRuntimeStackSourceIndices tm).map fun position =>
      if position = arithmeticStackEquiv tm k then
        List.replicate (transitionWidenedFallbackStackSegmentCount tm) true
      else
        List.replicate
          (transitionWidenedFallbackStackSegmentCount tm) false).flatten

theorem transitionStackRouteBlockDescriptorSelection_nonempty
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    0 < (transitionStackRouteBlockDescriptorSelection tm k).length := by
  simp [transitionStackRouteBlockDescriptorSelection]

/-- The block selector consumes exactly one complete widened descriptor row.
-/
theorem transitionStackRouteBlockDescriptorSelection_length
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    (transitionStackRouteBlockDescriptorSelection tm k).length =
      (transitionWidenedFallbackSegments tm).length := by
  simp only [transitionStackRouteBlockDescriptorSelection,
    transitionWidenedFallbackSegments, List.length_cons,
    List.length_flatten]
  apply congrArg Nat.succ
  rw [List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro position hposition
  simp only [Function.comp_apply]
  rw [transitionWidenedFallbackStackSegments_length]
  split_ifs <;> simp

/-- One runtime progression row has exactly the fixed block-selector width. -/
theorem transitionStackRouteBlockDescriptorSelection_progressions_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    (transitionStackRouteBlockDescriptorSelection tm k).length =
      (transitionWidenedFallbackProgressions tm seed).length := by
  rw [transitionStackRouteBlockDescriptorSelection_length]
  simp [transitionWidenedFallbackProgressions]

private theorem block_flatMap_if_eq_nil_of_not_mem {ι α : Type}
    [DecidableEq ι] (target : ι) (values : List α)
    (indices : List ι) (hnot : target ∉ indices) :
    indices.flatMap (fun index => if index = target then values else []) =
      [] := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      have hne : index ≠ target := by
        intro heq
        apply hnot
        simp [heq]
      have htail : target ∉ indices := by
        intro hmem
        exact hnot (by simp [hmem])
      simp [hne, ih htail]

private theorem block_flatMap_if_eq_of_mem_nodup {ι α : Type}
    [DecidableEq ι] (target : ι) (values : List α)
    (indices : List ι) (hmem : target ∈ indices)
    (hnodup : indices.Nodup) :
    indices.flatMap (fun index => if index = target then values else []) =
      values := by
  induction indices with
  | nil => simp at hmem
  | cons index indices ih =>
      rw [List.nodup_cons] at hnodup
      by_cases heq : index = target
      · subst index
        rw [List.flatMap_cons, if_pos rfl,
          block_flatMap_if_eq_nil_of_not_mem target values indices hnodup.1]
        simp
      · have htail : target ∈ indices := by
          simpa [heq, Ne.symm heq] using hmem
        rw [List.flatMap_cons, if_neg heq, ih htail hnodup.2]
        rfl

/-- The block mask selects literally the complete progression table of the
requested stack. -/
theorem transitionStackRouteBlockDescriptorSelection_segments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    selectListByBool
        (transitionStackRouteBlockDescriptorSelection tm k)
        (transitionWidenedFallbackSegments tm) =
      transitionWidenedFallbackStackSegments tm k := by
  unfold transitionStackRouteBlockDescriptorSelection
    transitionWidenedFallbackSegments
  change selectListByBool
      ((arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
        if position = arithmeticStackEquiv tm k then
          List.replicate
            (transitionWidenedFallbackStackSegmentCount tm) true
        else
          List.replicate
            (transitionWidenedFallbackStackSegmentCount tm) false)
      ((arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
        transitionWidenedFallbackStackSegments tm
          ((arithmeticStackEquiv tm).symm position)) =
    transitionWidenedFallbackStackSegments tm k
  have hlength : ∀ position ∈ arithmeticRuntimeStackSourceIndices tm,
      (if position = arithmeticStackEquiv tm k then
          List.replicate
            (transitionWidenedFallbackStackSegmentCount tm) true
        else
          List.replicate
            (transitionWidenedFallbackStackSegmentCount tm) false).length =
        (transitionWidenedFallbackStackSegments tm
          ((arithmeticStackEquiv tm).symm position)).length := by
    intro position hposition
    rw [transitionWidenedFallbackStackSegments_length]
    split_ifs <;> simp
  rw [selectListByBool_flatMap _ _ _ hlength]
  have hlocal :
      (arithmeticRuntimeStackSourceIndices tm).flatMap (fun position =>
        selectListByBool
          (if position = arithmeticStackEquiv tm k then
            List.replicate
              (transitionWidenedFallbackStackSegmentCount tm) true
          else
            List.replicate
              (transitionWidenedFallbackStackSegmentCount tm) false)
          (transitionWidenedFallbackStackSegments tm
            ((arithmeticStackEquiv tm).symm position))) =
        (arithmeticRuntimeStackSourceIndices tm).flatMap (fun position =>
          if position = arithmeticStackEquiv tm k then
            transitionWidenedFallbackStackSegments tm k
          else []) := by
    apply List.flatMap_congr
    intro position hposition
    by_cases htarget : position = arithmeticStackEquiv tm k
    · simp only [if_pos htarget]
      subst position
      simp [transitionWidenedFallbackStackSegments_length]
    · simp [htarget]
  rw [hlocal]
  apply block_flatMap_if_eq_of_mem_nodup
      (arithmeticStackEquiv tm k)
      (transitionWidenedFallbackStackSegments tm k)
  · simp [arithmeticRuntimeStackSourceIndices]
  · exact List.nodup_finRange _

/-- Runtime progressions of one complete selected stack. -/
noncomputable def transitionStackRouteBlockProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    List AffineUnaryTripleProgression :=
  (transitionWidenedFallbackStackSegments tm k).map
    (transitionWidenedFallbackSegmentProgression seed)

/-- The descriptor mask selects exactly the complete stack progression family.
-/
theorem transitionStackRouteBlockDescriptorSelection_progressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    selectListByBool
        (transitionStackRouteBlockDescriptorSelection tm k)
        (transitionWidenedFallbackProgressions tm seed) =
      transitionStackRouteBlockProgressions tm seed k := by
  unfold transitionWidenedFallbackProgressions
    transitionStackRouteBlockProgressions
  rw [selectListByBool_map,
    transitionStackRouteBlockDescriptorSelection_segments]

private theorem block_encode_progressionMarkedFamily_eq_periodicInput
    (progressions : List AffineUnaryTripleProgression) :
    encodeAffineUnaryTripleProgressionMarkedFamily progressions =
      encodeUnaryFramePeriodicMarkedRowInput
        (progressions.map affineUnaryTripleProgressionFields) := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      simp only [encodeAffineUnaryTripleProgressionMarkedFamily,
        encodeUnaryFramePeriodicMarkedRowInput, List.flatMap_cons,
        List.map_cons]
      have hih := ih
      simp only [encodeAffineUnaryTripleProgressionMarkedFamily,
        encodeUnaryFramePeriodicMarkedRowInput] at hih
      rw [hih]
      rfl

/-- Marked complete-stack descriptors selected from the raw verifier input. -/
noncomputable def verifierTransitionStackRouteBlockMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    (transitionStackRouteBlockDescriptorSelection W.machine.tm k)
    (transitionStackRouteBlockDescriptorSelection_nonempty W.machine.tm k)
    (verifierTransitionWidenedFallbackMarkedDescriptorFrames W input)

/-- Exact periodic-selection semantics for the complete stack block. -/
theorem verifierTransitionStackRouteBlockMarkedDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteBlockMarkedDescriptorFrames W k input =
      encodeUnaryFramePeriodicMarkedRowOutput
        (transitionStackRouteBlockDescriptorSelection W.machine.tm k)
        (transitionStackRouteBlockDescriptorSelection_nonempty W.machine.tm k)
        (verifierTransitionWidenedFallbackDescriptorRows W input) := by
  unfold verifierTransitionStackRouteBlockMarkedDescriptorFrames
    verifierTransitionWidenedFallbackDescriptorRows
  rw [verifierTransitionWidenedFallbackMarkedDescriptorFrames_eq]
  rw [block_encode_progressionMarkedFamily_eq_periodicInput]
  exact rewriteUnaryFramePeriodicMarkedRows_encode _ _ _

/-- The selector restarts at zero for every transition seed. -/
theorem verifierTransitionStackRouteBlockMarkedDescriptorFrames_eq_groups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteBlockMarkedDescriptorFrames W k input =
      (verifierTransitionWidenedFallbackDescriptorRowGroups W input).flatMap
        (encodeUnaryFramePeriodicSelectedMarkedRows
          (transitionStackRouteBlockDescriptorSelection W.machine.tm k)) := by
  rw [verifierTransitionStackRouteBlockMarkedDescriptorFrames_eq]
  rw [verifierTransitionWidenedFallbackDescriptorRows_eq_groups]
  apply encodeUnaryFramePeriodicMarkedRowOutput_groups
  intro rows hrows
  unfold verifierTransitionWidenedFallbackDescriptorRowGroups at hrows
  rw [List.mem_map] at hrows
  rcases hrows with ⟨seed, hseed, rfl⟩
  simp only [List.length_map]
  exact (transitionStackRouteBlockDescriptorSelection_progressions_length
    W.machine.tm seed k).symm

/-- The selected marked stream is exactly one complete stack progression
family per transition row. -/
theorem
    verifierTransitionStackRouteBlockMarkedDescriptorFrames_eq_routeProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteBlockMarkedDescriptorFrames W k input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineUnaryTripleProgressionMarkedFamily
          (transitionStackRouteBlockProgressions W.machine.tm seed k) := by
  rw [verifierTransitionStackRouteBlockMarkedDescriptorFrames_eq_groups]
  unfold verifierTransitionWidenedFallbackDescriptorRowGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [encodeUnaryFramePeriodicSelectedMarkedProgressions]
  rw [transitionStackRouteBlockDescriptorSelection_progressions]

/-- A fixed polynomial-time TM2 selects the complete stack descriptor block
directly from the original verifier word. -/
noncomputable def
    verifierTransitionStackRouteBlockMarkedDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteBlockMarkedDescriptorFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionWidenedFallbackMarkedDescriptorFrames_computableInPolyTime W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        (transitionStackRouteBlockDescriptorSelection W.machine.tm k)
        (transitionStackRouteBlockDescriptorSelection_nonempty W.machine.tm k))
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionStackRouteBlockMarkedDescriptorFrames] using run }

end CLRS.Chapter34.Turing.CookLevin
