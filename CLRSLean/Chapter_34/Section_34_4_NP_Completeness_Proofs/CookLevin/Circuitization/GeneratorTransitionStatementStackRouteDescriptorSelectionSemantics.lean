import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteDescriptorSelection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteCellSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowSelection

/-!
# Exact stack-route descriptor selection semantics

The machine-fixed height and cell masks are identified with the corresponding
semantic progression families.  Consequently the concrete raw-input selector
emits exactly those marked descriptor families for every transition seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem flatMap_if_eq_nil_of_not_mem {ι α : Type}
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

private theorem flatMap_if_eq_of_mem_nodup {ι α : Type}
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
          flatMap_if_eq_nil_of_not_mem target values indices hnodup.1]
        simp
      · have htail : target ∈ indices := by
          simpa [heq, Ne.symm heq] using hmem
        rw [List.flatMap_cons, if_neg heq, ih htail hnodup.2]
        rfl

private theorem select_heightStackBlock
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    selectListByBool
        ([true, true] ++
          List.replicate (1 + 2 * maxPushesPerStep tm) false)
        (transitionWidenedFallbackStackSegments tm k) =
      transitionStackRouteHeightSegments tm k := by
  unfold transitionWidenedFallbackStackSegments
    transitionStackRouteHeightSegments
  rw [show
      [transitionWidenedFallbackPublicHeightSegment tm k,
          transitionWidenedFallbackOverflowHeightSegment tm,
          transitionWidenedFallbackPublicCellSegment tm k] ++
          (List.replicate (maxPushesPerStep tm)
            (transitionWidenedFallbackBlankCellSegments tm k)).flatten =
        [transitionWidenedFallbackPublicHeightSegment tm k,
          transitionWidenedFallbackOverflowHeightSegment tm] ++
          (transitionWidenedFallbackPublicCellSegment tm k ::
            (List.replicate (maxPushesPerStep tm)
              (transitionWidenedFallbackBlankCellSegments tm k)).flatten) by
      rfl]
  rw [selectListByBool_append]
  · simp [selectListByBool]
  · simp

private theorem select_cellStackBlock
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    selectListByBool
        ([false, false] ++
          List.replicate (1 + 2 * maxPushesPerStep tm) true)
        (transitionWidenedFallbackStackSegments tm k) =
      transitionStackRouteCellSegments tm k := by
  unfold transitionWidenedFallbackStackSegments
    transitionStackRouteCellSegments
  rw [show
      [transitionWidenedFallbackPublicHeightSegment tm k,
          transitionWidenedFallbackOverflowHeightSegment tm,
          transitionWidenedFallbackPublicCellSegment tm k] ++
          (List.replicate (maxPushesPerStep tm)
            (transitionWidenedFallbackBlankCellSegments tm k)).flatten =
        [transitionWidenedFallbackPublicHeightSegment tm k,
          transitionWidenedFallbackOverflowHeightSegment tm] ++
          (transitionWidenedFallbackPublicCellSegment tm k ::
            (List.replicate (maxPushesPerStep tm)
              (transitionWidenedFallbackBlankCellSegments tm k)).flatten) by
      rfl]
  rw [selectListByBool_append]
  · simp only [selectListByBool,
      selectListByBool_replicate_true]
    apply List.take_of_length_le
    simp [transitionWidenedFallbackBlankCellSegments]
    omega
  · simp

private theorem heightSelection_stackSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    selectListByBool
        (transitionStackRouteHeightDescriptorSelection tm k)
        (transitionWidenedFallbackSegments tm) =
      transitionStackRouteHeightSegments tm k := by
  unfold transitionStackRouteHeightDescriptorSelection
    transitionWidenedFallbackSegments
  change selectListByBool
      ((arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
        if position = arithmeticStackEquiv tm k then
          [true, true] ++
            List.replicate (1 + 2 * maxPushesPerStep tm) false
        else
          List.replicate
            (transitionWidenedFallbackStackSegmentCount tm) false)
      ((arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
        transitionWidenedFallbackStackSegments tm
          ((arithmeticStackEquiv tm).symm position)) =
    transitionStackRouteHeightSegments tm k
  have hlength : ∀ position ∈ arithmeticRuntimeStackSourceIndices tm,
      (if position = arithmeticStackEquiv tm k then
          [true, true] ++
            List.replicate (1 + 2 * maxPushesPerStep tm) false
        else
          List.replicate
            (transitionWidenedFallbackStackSegmentCount tm) false).length =
        (transitionWidenedFallbackStackSegments tm
          ((arithmeticStackEquiv tm).symm position)).length := by
    intro position hposition
    rw [transitionWidenedFallbackStackSegments_length]
    by_cases htarget : position = arithmeticStackEquiv tm k
    · simp [htarget, transitionWidenedFallbackStackSegmentCount]
      omega
    · simp [htarget]
  rw [selectListByBool_flatMap _ _ _ hlength]
  have hlocal :
      (arithmeticRuntimeStackSourceIndices tm).flatMap (fun position =>
        selectListByBool
          (if position = arithmeticStackEquiv tm k then
            [true, true] ++
              List.replicate (1 + 2 * maxPushesPerStep tm) false
          else
            List.replicate
              (transitionWidenedFallbackStackSegmentCount tm) false)
          (transitionWidenedFallbackStackSegments tm
            ((arithmeticStackEquiv tm).symm position))) =
        (arithmeticRuntimeStackSourceIndices tm).flatMap (fun position =>
          if position = arithmeticStackEquiv tm k then
            transitionStackRouteHeightSegments tm k
          else []) := by
    apply List.flatMap_congr
    intro position hposition
    by_cases htarget : position = arithmeticStackEquiv tm k
    · simp only [if_pos htarget]
      subst position
      simpa only [Equiv.symm_apply_apply, List.cons_append,
        List.nil_append] using
        select_heightStackBlock tm k
    · simp [htarget]
  rw [hlocal]
  apply flatMap_if_eq_of_mem_nodup
      (arithmeticStackEquiv tm k)
      (transitionStackRouteHeightSegments tm k)
  · simp [arithmeticRuntimeStackSourceIndices]
  · exact List.nodup_finRange _

private theorem cellSelection_stackSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    selectListByBool
        (transitionStackRouteCellDescriptorSelection tm k)
        (transitionWidenedFallbackSegments tm) =
      transitionStackRouteCellSegments tm k := by
  unfold transitionStackRouteCellDescriptorSelection
    transitionWidenedFallbackSegments
  change selectListByBool
      ((arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
        if position = arithmeticStackEquiv tm k then
          [false, false] ++
            List.replicate (1 + 2 * maxPushesPerStep tm) true
        else
          List.replicate
            (transitionWidenedFallbackStackSegmentCount tm) false)
      ((arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
        transitionWidenedFallbackStackSegments tm
          ((arithmeticStackEquiv tm).symm position)) =
    transitionStackRouteCellSegments tm k
  have hlength : ∀ position ∈ arithmeticRuntimeStackSourceIndices tm,
      (if position = arithmeticStackEquiv tm k then
          [false, false] ++
            List.replicate (1 + 2 * maxPushesPerStep tm) true
        else
          List.replicate
            (transitionWidenedFallbackStackSegmentCount tm) false).length =
        (transitionWidenedFallbackStackSegments tm
          ((arithmeticStackEquiv tm).symm position)).length := by
    intro position hposition
    rw [transitionWidenedFallbackStackSegments_length]
    by_cases htarget : position = arithmeticStackEquiv tm k
    · simp [htarget, transitionWidenedFallbackStackSegmentCount]
      omega
    · simp [htarget]
  rw [selectListByBool_flatMap _ _ _ hlength]
  have hlocal :
      (arithmeticRuntimeStackSourceIndices tm).flatMap (fun position =>
        selectListByBool
          (if position = arithmeticStackEquiv tm k then
            [false, false] ++
              List.replicate (1 + 2 * maxPushesPerStep tm) true
          else
            List.replicate
              (transitionWidenedFallbackStackSegmentCount tm) false)
          (transitionWidenedFallbackStackSegments tm
            ((arithmeticStackEquiv tm).symm position))) =
        (arithmeticRuntimeStackSourceIndices tm).flatMap (fun position =>
          if position = arithmeticStackEquiv tm k then
            transitionStackRouteCellSegments tm k
          else []) := by
    apply List.flatMap_congr
    intro position hposition
    by_cases htarget : position = arithmeticStackEquiv tm k
    · simp only [if_pos htarget]
      subst position
      simpa only [Equiv.symm_apply_apply, List.cons_append,
        List.nil_append] using
        select_cellStackBlock tm k
    · simp [htarget]
  rw [hlocal]
  apply flatMap_if_eq_of_mem_nodup
      (arithmeticStackEquiv tm k)
      (transitionStackRouteCellSegments tm k)
  · simp [arithmeticRuntimeStackSourceIndices]
  · exact List.nodup_finRange _

/-- The height mask selects exactly the two height progressions of one stack. -/
theorem transitionStackRouteHeightDescriptorSelection_progressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    selectListByBool
        (transitionStackRouteHeightDescriptorSelection tm k)
        (transitionWidenedFallbackProgressions tm seed) =
      transitionStackRouteHeightProgressions tm seed k := by
  unfold transitionWidenedFallbackProgressions
    transitionStackRouteHeightProgressions
  rw [selectListByBool_map, heightSelection_stackSegments]

/-- The cell mask selects exactly the public-cell and blank-cell progressions
of one stack. -/
theorem transitionStackRouteCellDescriptorSelection_progressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    selectListByBool
        (transitionStackRouteCellDescriptorSelection tm k)
        (transitionWidenedFallbackProgressions tm seed) =
      transitionStackRouteCellProgressions tm seed k := by
  unfold transitionWidenedFallbackProgressions
    transitionStackRouteCellProgressions
  rw [selectListByBool_map, cellSelection_stackSegments]

/-- From the raw verifier input, the height selector emits exactly the marked
height progression family for every transition seed. -/
theorem
    verifierTransitionStackRouteHeightMarkedDescriptorFrames_eq_routeProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteHeightMarkedDescriptorFrames W k input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineUnaryTripleProgressionMarkedFamily
          (transitionStackRouteHeightProgressions W.machine.tm seed k) := by
  rw [verifierTransitionStackRouteHeightMarkedDescriptorFrames_eq_groups]
  unfold verifierTransitionWidenedFallbackDescriptorRowGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [encodeUnaryFramePeriodicSelectedMarkedProgressions]
  rw [transitionStackRouteHeightDescriptorSelection_progressions]

/-- From the raw verifier input, the cell selector emits exactly the marked
cell progression family for every transition seed. -/
theorem
    verifierTransitionStackRouteCellMarkedDescriptorFrames_eq_routeProgressions
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteCellMarkedDescriptorFrames W k input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineUnaryTripleProgressionMarkedFamily
          (transitionStackRouteCellProgressions W.machine.tm seed k) := by
  rw [verifierTransitionStackRouteCellMarkedDescriptorFrames_eq_groups]
  unfold verifierTransitionWidenedFallbackDescriptorRowGroups
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [encodeUnaryFramePeriodicSelectedMarkedProgressions]
  rw [transitionStackRouteCellDescriptorSelection_progressions]

end CLRS.Chapter34.Turing.CookLevin
