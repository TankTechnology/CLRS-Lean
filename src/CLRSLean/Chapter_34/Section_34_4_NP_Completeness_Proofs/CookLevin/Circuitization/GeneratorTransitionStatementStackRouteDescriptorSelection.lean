import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackMarkedDescriptors
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowFilterCycle

/-!
# Selecting one stack's widened descriptors from the raw verifier word

The widened fallback source repeats one machine-fixed progression layout for
every transition seed.  These fixed Boolean tables retain exactly the height
or cell segment positions of one stack.  Composing them with the marked raw
descriptor source closes the first concrete source boundary needed by the
stack-route controllers.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Number of progression segments occupied by every widened stack. -/
def transitionWidenedFallbackStackSegmentCount
    (tm : _root_.Turing.FinTM2) : Nat :=
  3 + 2 * maxPushesPerStep tm

/-- Every stack occupies the same machine-fixed number of progression slots. -/
theorem transitionWidenedFallbackStackSegments_length
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    (transitionWidenedFallbackStackSegments tm k).length =
      transitionWidenedFallbackStackSegmentCount tm := by
  simp [transitionWidenedFallbackStackSegments,
    transitionWidenedFallbackBlankCellSegments,
    transitionWidenedFallbackStackSegmentCount]
  omega

/-- Keep the two height progressions of the selected stack and erase every
other widened-fallback descriptor position. -/
noncomputable def transitionStackRouteHeightDescriptorSelection
    (tm : _root_.Turing.FinTM2) (k : tm.K) : List Bool :=
  false ::
    ((arithmeticRuntimeStackSourceIndices tm).map fun position =>
      if position = arithmeticStackEquiv tm k then
        [true, true] ++ List.replicate (1 + 2 * maxPushesPerStep tm) false
      else
        List.replicate (transitionWidenedFallbackStackSegmentCount tm) false).flatten

/-- Keep the public-cell progression and all fixed blank-cell progressions of
the selected stack and erase every other descriptor position. -/
noncomputable def transitionStackRouteCellDescriptorSelection
    (tm : _root_.Turing.FinTM2) (k : tm.K) : List Bool :=
  false ::
    ((arithmeticRuntimeStackSourceIndices tm).map fun position =>
      if position = arithmeticStackEquiv tm k then
        [false, false] ++
          List.replicate (1 + 2 * maxPushesPerStep tm) true
      else
        List.replicate (transitionWidenedFallbackStackSegmentCount tm) false).flatten

theorem transitionStackRouteHeightDescriptorSelection_nonempty
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    0 < (transitionStackRouteHeightDescriptorSelection tm k).length := by
  simp [transitionStackRouteHeightDescriptorSelection]

theorem transitionStackRouteCellDescriptorSelection_nonempty
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    0 < (transitionStackRouteCellDescriptorSelection tm k).length := by
  simp [transitionStackRouteCellDescriptorSelection]

/-- The height selector consumes exactly one complete widened segment row. -/
theorem transitionStackRouteHeightDescriptorSelection_length
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    (transitionStackRouteHeightDescriptorSelection tm k).length =
      (transitionWidenedFallbackSegments tm).length := by
  simp only [transitionStackRouteHeightDescriptorSelection,
    transitionWidenedFallbackSegments, List.length_cons,
    List.length_flatten]
  apply congrArg Nat.succ
  rw [List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro position hposition
  simp only [Function.comp_apply]
  rw [transitionWidenedFallbackStackSegments_length]
  by_cases htarget : position = arithmeticStackEquiv tm k
  · simp [htarget, transitionWidenedFallbackStackSegmentCount]
    omega
  · simp [htarget]

/-- The cell selector consumes exactly one complete widened segment row. -/
theorem transitionStackRouteCellDescriptorSelection_length
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    (transitionStackRouteCellDescriptorSelection tm k).length =
      (transitionWidenedFallbackSegments tm).length := by
  simp only [transitionStackRouteCellDescriptorSelection,
    transitionWidenedFallbackSegments, List.length_cons,
    List.length_flatten]
  apply congrArg Nat.succ
  rw [List.map_map, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro position hposition
  simp only [Function.comp_apply]
  rw [transitionWidenedFallbackStackSegments_length]
  by_cases htarget : position = arithmeticStackEquiv tm k
  · simp [htarget, transitionWidenedFallbackStackSegmentCount]
    omega
  · simp [htarget]

/-- One runtime progression row has exactly the fixed selector width. -/
theorem transitionStackRouteHeightDescriptorSelection_progressions_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    (transitionStackRouteHeightDescriptorSelection tm k).length =
      (transitionWidenedFallbackProgressions tm seed).length := by
  rw [transitionStackRouteHeightDescriptorSelection_length]
  simp [transitionWidenedFallbackProgressions]

/-- The cell selector is aligned to the same complete progression row. -/
theorem transitionStackRouteCellDescriptorSelection_progressions_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    (transitionStackRouteCellDescriptorSelection tm k).length =
      (transitionWidenedFallbackProgressions tm seed).length := by
  rw [transitionStackRouteCellDescriptorSelection_length]
  simp [transitionWidenedFallbackProgressions]

/-- Descriptor rows underlying the complete marked widened source. -/
noncomputable def verifierTransitionWidenedFallbackDescriptorRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List Nat) :=
  (((verifierTransitionRowSeeds W input).flatMap
      (transitionWidenedFallbackProgressions W.machine.tm)).map
    affineUnaryTripleProgressionFields)

/-- The same descriptor rows, grouped by their originating transition seed. -/
noncomputable def verifierTransitionWidenedFallbackDescriptorRowGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List (List (List Nat)) :=
  (verifierTransitionRowSeeds W input).map fun seed =>
    (transitionWidenedFallbackProgressions W.machine.tm seed).map
      affineUnaryTripleProgressionFields

theorem verifierTransitionWidenedFallbackDescriptorRows_eq_groups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionWidenedFallbackDescriptorRows W input =
      (verifierTransitionWidenedFallbackDescriptorRowGroups W input).flatten := by
  unfold verifierTransitionWidenedFallbackDescriptorRows
    verifierTransitionWidenedFallbackDescriptorRowGroups
  rw [List.map_flatMap]
  rfl

private theorem encode_progressionMarkedFamily_eq_periodicInput
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

/-- Marked height descriptors of one fixed stack, selected directly from the
raw verifier input. -/
noncomputable def verifierTransitionStackRouteHeightMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    (transitionStackRouteHeightDescriptorSelection W.machine.tm k)
    (transitionStackRouteHeightDescriptorSelection_nonempty W.machine.tm k)
    (verifierTransitionWidenedFallbackMarkedDescriptorFrames W input)

/-- Marked cell descriptors of one fixed stack, selected directly from the
raw verifier input. -/
noncomputable def verifierTransitionStackRouteCellMarkedDescriptorFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFramePeriodicMarkedRows
    (transitionStackRouteCellDescriptorSelection W.machine.tm k)
    (transitionStackRouteCellDescriptorSelection_nonempty W.machine.tm k)
    (verifierTransitionWidenedFallbackMarkedDescriptorFrames W input)

/-- Exact periodic-selection semantics for the height descriptor source. -/
theorem verifierTransitionStackRouteHeightMarkedDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteHeightMarkedDescriptorFrames W k input =
      encodeUnaryFramePeriodicMarkedRowOutput
        (transitionStackRouteHeightDescriptorSelection W.machine.tm k)
        (transitionStackRouteHeightDescriptorSelection_nonempty W.machine.tm k)
        (verifierTransitionWidenedFallbackDescriptorRows W input) := by
  unfold verifierTransitionStackRouteHeightMarkedDescriptorFrames
    verifierTransitionWidenedFallbackDescriptorRows
  rw [verifierTransitionWidenedFallbackMarkedDescriptorFrames_eq]
  rw [encode_progressionMarkedFamily_eq_periodicInput]
  exact rewriteUnaryFramePeriodicMarkedRows_encode _ _ _

/-- Exact periodic-selection semantics for the cell descriptor source. -/
theorem verifierTransitionStackRouteCellMarkedDescriptorFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteCellMarkedDescriptorFrames W k input =
      encodeUnaryFramePeriodicMarkedRowOutput
        (transitionStackRouteCellDescriptorSelection W.machine.tm k)
        (transitionStackRouteCellDescriptorSelection_nonempty W.machine.tm k)
        (verifierTransitionWidenedFallbackDescriptorRows W input) := by
  unfold verifierTransitionStackRouteCellMarkedDescriptorFrames
    verifierTransitionWidenedFallbackDescriptorRows
  rw [verifierTransitionWidenedFallbackMarkedDescriptorFrames_eq]
  rw [encode_progressionMarkedFamily_eq_periodicInput]
  exact rewriteUnaryFramePeriodicMarkedRows_encode _ _ _

/-- The height selector restarts at position zero for every transition seed. -/
theorem verifierTransitionStackRouteHeightMarkedDescriptorFrames_eq_groups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteHeightMarkedDescriptorFrames W k input =
      (verifierTransitionWidenedFallbackDescriptorRowGroups W input).flatMap
        (encodeUnaryFramePeriodicSelectedMarkedRows
          (transitionStackRouteHeightDescriptorSelection W.machine.tm k)) := by
  rw [verifierTransitionStackRouteHeightMarkedDescriptorFrames_eq]
  rw [verifierTransitionWidenedFallbackDescriptorRows_eq_groups]
  apply encodeUnaryFramePeriodicMarkedRowOutput_groups
  intro rows hrows
  unfold verifierTransitionWidenedFallbackDescriptorRowGroups at hrows
  rw [List.mem_map] at hrows
  rcases hrows with ⟨seed, hseed, rfl⟩
  simp only [List.length_map]
  exact (transitionStackRouteHeightDescriptorSelection_progressions_length
    W.machine.tm seed k).symm

/-- The cell selector restarts at position zero for every transition seed. -/
theorem verifierTransitionStackRouteCellMarkedDescriptorFrames_eq_groups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRouteCellMarkedDescriptorFrames W k input =
      (verifierTransitionWidenedFallbackDescriptorRowGroups W input).flatMap
        (encodeUnaryFramePeriodicSelectedMarkedRows
          (transitionStackRouteCellDescriptorSelection W.machine.tm k)) := by
  rw [verifierTransitionStackRouteCellMarkedDescriptorFrames_eq]
  rw [verifierTransitionWidenedFallbackDescriptorRows_eq_groups]
  apply encodeUnaryFramePeriodicMarkedRowOutput_groups
  intro rows hrows
  unfold verifierTransitionWidenedFallbackDescriptorRowGroups at hrows
  rw [List.mem_map] at hrows
  rcases hrows with ⟨seed, hseed, rfl⟩
  simp only [List.length_map]
  exact (transitionStackRouteCellDescriptorSelection_progressions_length
    W.machine.tm seed k).symm

/-- The selected height descriptors are emitted by one fixed polynomial-time
TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionStackRouteHeightMarkedDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteHeightMarkedDescriptorFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionWidenedFallbackMarkedDescriptorFrames_computableInPolyTime W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        (transitionStackRouteHeightDescriptorSelection W.machine.tm k)
        (transitionStackRouteHeightDescriptorSelection_nonempty W.machine.tm k))
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionStackRouteHeightMarkedDescriptorFrames] using run }

/-- The selected cell descriptors are emitted by one fixed polynomial-time
TM2 from the original verifier word. -/
noncomputable def
    verifierTransitionStackRouteCellMarkedDescriptorFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRouteCellMarkedDescriptorFrames W k) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionWidenedFallbackMarkedDescriptorFrames_computableInPolyTime W)
      (unaryFramePeriodicMarkedRowFilter_computableInPolyTime
        (transitionStackRouteCellDescriptorSelection W.machine.tm k)
        (transitionStackRouteCellDescriptorSelection_nonempty W.machine.tm k))
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionStackRouteCellMarkedDescriptorFrames] using run }

end CLRS.Chapter34.Turing.CookLevin
