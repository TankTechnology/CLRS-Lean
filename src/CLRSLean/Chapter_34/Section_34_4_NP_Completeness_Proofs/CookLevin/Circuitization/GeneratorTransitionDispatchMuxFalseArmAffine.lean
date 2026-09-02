import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxFalseArmLayout
import Mathlib.Tactic

/-!
# Affine source table for dispatch-mux false arms

After the initial widened row, every later false arm is the preceding mux's
output row.  These output wires form one stride-three progression.  The fixed
descriptor recursion below emits exactly those progressions for all but the
last program label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- First-coordinate values of an arbitrary triple progression. -/
def transitionProgressionFirstValues
    (progression : AffineUnaryTripleProgression) : List Nat :=
  (affineUnaryTripleProgressionRows progression).map fun row => row.1

/-- Output row of the mux belonging to one label at the current affine gate
offset. -/
def transitionDispatchPreviousOutputProgression
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (offset : TransitionAffineNat) (label : tm.Λ) :
    AffineUnaryTripleProgression :=
  let muxOffset := offset.add (transitionDispatchStmtGateAffine tm label)
  { base₁ := seed.start + muxOffset.eval seed.height + 3
    base₂ := 0
    base₃ := 0
    step₁ := 3
    step₂ := 0
    step₃ := 0
    count := cfgBitCount tm (workHeight tm seed.height) }

/-- Previous-mux output progressions needed by a fixed label suffix.  A
singleton suffix needs no preceding output row. -/
def transitionDispatchPreviousOutputProgressionsForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ →
      List AffineUnaryTripleProgression
  | _, [] => []
  | _, [_] => []
  | offset, label :: next :: labels =>
      let muxOffset := offset.add (transitionDispatchStmtGateAffine tm label)
      transitionDispatchPreviousOutputProgression tm seed offset label ::
        transitionDispatchPreviousOutputProgressionsForLabels tm seed
          (muxOffset.add (transitionDispatchMuxGateAffine tm))
          (next :: labels)

/-- Complete preceding-mux output family for the canonical label list. -/
def transitionDispatchPreviousOutputProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  transitionDispatchPreviousOutputProgressionsForLabels tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Seven fixed forms describing one preceding-mux output row. -/
def transitionDispatchPreviousOutputDescriptorBlock
    (tm : _root_.Turing.FinTM2) (offset : TransitionAffineNat)
    (label : tm.Λ) : List AffineUnaryTripleForm :=
  let muxOffset := offset.add (transitionDispatchStmtGateAffine tm label)
  [ transitionAbsoluteStartForm
      (muxOffset.add (TransitionAffineNat.const 3)),
    transitionZeroForm, transitionZeroForm,
    transitionHeightAffineForm (TransitionAffineNat.const 3),
    transitionZeroForm, transitionZeroForm,
    transitionHeightAffineForm
      ((transitionCfgBitAffine tm).shiftInput (maxPushesPerStep tm)) ]

/-- Fixed descriptor recursion parallel to the runtime progression family. -/
def transitionDispatchPreviousOutputDescriptorFormsForLabels
    (tm : _root_.Turing.FinTM2) :
    TransitionAffineNat → List tm.Λ → List AffineUnaryTripleForm
  | _, [] => []
  | _, [_] => []
  | offset, label :: next :: labels =>
      let muxOffset := offset.add (transitionDispatchStmtGateAffine tm label)
      transitionDispatchPreviousOutputDescriptorBlock tm offset label ++
        transitionDispatchPreviousOutputDescriptorFormsForLabels tm
          (muxOffset.add (transitionDispatchMuxGateAffine tm))
          (next :: labels)

/-- Complete verifier-fixed descriptor table for preceding mux outputs. -/
def transitionDispatchPreviousOutputDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionDispatchPreviousOutputDescriptorFormsForLabels tm
    (TransitionAffineNat.const 2) (programLabels tm)

/-- One fixed descriptor block evaluates to its runtime progression. -/
theorem transitionDispatchPreviousOutputDescriptorBlock_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (offset : TransitionAffineNat) (label : tm.Λ) :
    affineUnaryTripleMap
        (transitionDispatchPreviousOutputDescriptorBlock tm offset label)
        (transitionTailAffineSeed seed) =
      let progression :=
        transitionDispatchPreviousOutputProgression tm seed offset label
      [ progression.base₁, progression.base₂, progression.base₃,
        progression.step₁, progression.step₂, progression.step₃,
        progression.count ] := by
  simp [transitionDispatchPreviousOutputDescriptorBlock,
    transitionDispatchPreviousOutputProgression, affineUnaryTripleMap,
    transitionAbsoluteStartForm, transitionZeroForm,
    transitionHeightAffineForm, transitionTailAffineSeed,
    affineUnaryTripleFormValue, TransitionAffineNat.eval,
    TransitionAffineNat.add, TransitionAffineNat.const,
    workHeight]
  constructor
  · ring
  · change ((transitionCfgBitAffine tm).shiftInput
        (maxPushesPerStep tm)).eval seed.height = _
    rw [TransitionAffineNat.eval_shiftInput, transitionCfgBitAffine_eval]

/-- Evaluating the fixed recursive table gives exactly the concatenated
runtime descriptors. -/
theorem transitionDispatchPreviousOutputDescriptorFormsForLabels_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (offset : TransitionAffineNat) (labels : List tm.Λ),
      affineUnaryTripleMap
          (transitionDispatchPreviousOutputDescriptorFormsForLabels tm
            offset labels)
          (transitionTailAffineSeed seed) =
        (transitionDispatchPreviousOutputProgressionsForLabels tm seed
          offset labels).flatMap fun progression =>
            [ progression.base₁, progression.base₂, progression.base₃,
              progression.step₁, progression.step₂, progression.step₃,
              progression.count ] := by
  intro offset labels
  induction labels generalizing offset with
  | nil => rfl
  | cons label labels ih =>
      cases labels with
      | nil => rfl
      | cons next labels =>
          simp only [transitionDispatchPreviousOutputDescriptorFormsForLabels,
            transitionDispatchPreviousOutputProgressionsForLabels]
          rw [show affineUnaryTripleMap
              (transitionDispatchPreviousOutputDescriptorBlock tm offset label ++
                transitionDispatchPreviousOutputDescriptorFormsForLabels tm
                  ((offset.add
                    (transitionDispatchStmtGateAffine tm label)).add
                      (transitionDispatchMuxGateAffine tm))
                  (next :: labels))
              (transitionTailAffineSeed seed) =
            affineUnaryTripleMap
                (transitionDispatchPreviousOutputDescriptorBlock tm offset label)
                (transitionTailAffineSeed seed) ++
              affineUnaryTripleMap
                (transitionDispatchPreviousOutputDescriptorFormsForLabels tm
                  ((offset.add
                    (transitionDispatchStmtGateAffine tm label)).add
                      (transitionDispatchMuxGateAffine tm))
                  (next :: labels))
                (transitionTailAffineSeed seed) by
              simp [affineUnaryTripleMap, List.map_append]]
          rw [transitionDispatchPreviousOutputDescriptorBlock_value, ih]
          rfl

theorem transitionDispatchPreviousOutputDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap
        (transitionDispatchPreviousOutputDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionDispatchPreviousOutputProgressions tm seed).flatMap
        fun progression =>
          [ progression.base₁, progression.base₂, progression.base₃,
            progression.step₁, progression.step₂, progression.step₃,
            progression.count ] := by
  exact transitionDispatchPreviousOutputDescriptorFormsForLabels_value
    tm seed (TransitionAffineNat.const 2) (programLabels tm)

/-- The descriptor bytes are exactly the generic progression-family input. -/
theorem encode_transitionDispatchPreviousOutputDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap
          (transitionDispatchPreviousOutputDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionDispatchPreviousOutputProgressions tm seed) := by
  rw [transitionDispatchPreviousOutputDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionDispatchPreviousOutputProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

/-- One preceding-output progression is exactly the canonical arithmetic mux
output row. -/
theorem transitionDispatchPreviousOutputProgression_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (offset : TransitionAffineNat) (start : Nat) (label : tm.Λ)
    (hstart : start = seed.start + offset.eval seed.height)
    (hwork : 0 < workHeight tm seed.height) :
    transitionProgressionFirstValues
        (transitionDispatchPreviousOutputProgression tm seed offset label) =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (arithmeticMuxCfgWires tm (workHeight tm seed.height)
          (start + compileStmtGateCost tm (workHeight tm seed.height)
            (tm.m label))) := by
  unfold transitionProgressionFirstValues transitionCfgWireValues
    transitionDispatchPreviousOutputProgression arithmeticMuxCfgWires
  rw [affineUnaryTripleProgressionRows_eq_ofFn, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext coordinate
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [TransitionAffineNat.eval_add,
    transitionDispatchStmtGateAffine_eval tm label seed.height hwork]
  rw [hstart]
  ring

/-- The generated preceding-output progressions are exactly the false-arm
rows of the remaining label suffix. -/
theorem transitionDispatchPreviousOutputProgressionsForLabels_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (source : CfgWires tm (workHeight tm seed.height))
    (hwork : 0 < workHeight tm seed.height) :
    ∀ (offset : TransitionAffineNat) (start : Nat)
      (label : tm.Λ) (labels : List tm.Λ),
      start = seed.start + offset.eval seed.height →
      (transitionDispatchPreviousOutputProgressionsForLabels tm seed
          offset (label :: labels)).flatMap
          transitionProgressionFirstValues =
        (transitionDispatchFalseArmRowsForLabels tm seed.height source
          (start + compileStmtGateCost tm (workHeight tm seed.height)
              (tm.m label) +
            (3 * cfgBitCount tm (workHeight tm seed.height) + 1))
          (arithmeticMuxCfgWires tm (workHeight tm seed.height)
            (start + compileStmtGateCost tm (workHeight tm seed.height)
              (tm.m label))) labels).flatten := by
  intro offset start label labels hstart
  induction labels generalizing offset start label with
  | nil => rfl
  | cons next labels ih =>
      simp only [transitionDispatchPreviousOutputProgressionsForLabels,
        List.flatMap_cons, transitionDispatchFalseArmRowsForLabels,
        List.flatten_cons]
      rw [transitionDispatchPreviousOutputProgression_values tm seed offset
        start label hstart hwork]
      congr 1
      apply ih
      rw [TransitionAffineNat.eval_add, TransitionAffineNat.eval_add,
        transitionDispatchStmtGateAffine_eval tm label seed.height hwork,
        transitionDispatchMuxGateAffine_eval tm seed.height, hstart]
      omega

/-- Complete false-arm progression family: canonical widened row followed by
the output rows of every mux except the final one. -/
def transitionDispatchFalseArmProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  transitionWidenedFallbackProgressions tm seed ++
    transitionDispatchPreviousOutputProgressions tm seed

/-- Complete fixed descriptor table for the false-arm family. -/
def transitionDispatchFalseArmDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionWidenedFallbackDescriptorForms tm ++
    transitionDispatchPreviousOutputDescriptorForms tm

private theorem transitionWidenedFallbackProgressions_firstValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionWidenedFallbackProgressions tm seed).flatMap
        transitionProgressionFirstValues =
      transitionWidenedFallbackValues tm seed := by
  unfold transitionWidenedFallbackProgressions
  rw [List.flatMap_map]
  change (transitionWidenedFallbackSegments tm).flatMap
      (transitionWidenedFallbackSegmentValues seed) = _
  exact transitionWidenedFallbackSegments_values tm seed

/-- The complete generated first-track stream is exactly the flattened
semantic false-arm rows of the seed-derived dispatch. -/
theorem transitionDispatchFalseArmProgressions_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionDispatchFalseArmProgressions tm seed).flatMap
        transitionProgressionFirstValues =
      (transitionDispatchFalseArmRowsFromSeed tm seed).flatten := by
  unfold transitionDispatchFalseArmProgressions
    transitionDispatchPreviousOutputProgressions
    transitionDispatchFalseArmRowsFromSeed
  rw [List.flatMap_append,
    transitionWidenedFallbackProgressions_firstValues]
  cases hlabels : programLabels tm with
  | nil => exact False.elim (programLabels_nonempty tm hlabels)
  | cons label labels =>
      simp only [transitionDispatchFalseArmRowsForLabels, List.flatten_cons]
      rw [show transitionCfgWireValues tm (workHeight tm seed.height)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase) =
          transitionWidenedFallbackValues tm seed by
        unfold transitionCfgWireValues
        exact (transitionWidenedFallbackValues_eq_canonical tm seed).symm]
      congr 1
      apply transitionDispatchPreviousOutputProgressionsForLabels_values
        tm seed
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
        hwork (TransitionAffineNat.const 2) (seed.start + 2) label labels
      simp

/-- Evaluating the complete fixed descriptor table gives the combined runtime
progression family. -/
theorem transitionDispatchFalseArmDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap (transitionDispatchFalseArmDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionDispatchFalseArmProgressions tm seed).flatMap
        fun progression =>
          [ progression.base₁, progression.base₂, progression.base₃,
            progression.step₁, progression.step₂, progression.step₃,
            progression.count ] := by
  unfold transitionDispatchFalseArmDescriptorForms
    transitionDispatchFalseArmProgressions
  rw [show affineUnaryTripleMap
      (transitionWidenedFallbackDescriptorForms tm ++
        transitionDispatchPreviousOutputDescriptorForms tm)
      (transitionTailAffineSeed seed) =
    affineUnaryTripleMap (transitionWidenedFallbackDescriptorForms tm)
        (transitionTailAffineSeed seed) ++
      affineUnaryTripleMap
        (transitionDispatchPreviousOutputDescriptorForms tm)
        (transitionTailAffineSeed seed) by
      simp [affineUnaryTripleMap, List.map_append]]
  rw [transitionWidenedFallbackDescriptorForms_value,
    transitionDispatchPreviousOutputDescriptorForms_value,
    List.flatMap_append]

/-- The combined descriptor bytes are the exact generic family encoding. -/
theorem encode_transitionDispatchFalseArmDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap (transitionDispatchFalseArmDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionDispatchFalseArmProgressions tm seed) := by
  rw [transitionDispatchFalseArmDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionDispatchFalseArmProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

end CLRS.Chapter34.Turing.CookLevin
