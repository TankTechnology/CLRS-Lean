import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementFinalBranch
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxFalseArmAffine

/-!
# Affine true-arm rows ending in a statement branch

For every fixed program label whose linear statement spine terminates in
`branch`, the complete `whenTrue` row is one stride-three progression: the
output row of that final branch mux.  This module emits a fixed descriptor
table for exactly those labels and proves its values against the semantic
statement-output recursion.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Complete output progression of a statement's final branch mux.  The
label offset is already expressed in transition-seed height; the inner
statement offset is shifted from workspace height to seed height here. -/
def transitionDispatchBranchOutputProgression
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset branchOffset : TransitionAffineNat) :
    AffineUnaryTripleProgression :=
  let muxOffset := labelOffset.add
    (branchOffset.shiftInput (maxPushesPerStep tm))
  { base₁ := seed.start + muxOffset.eval seed.height + 3
    base₂ := 0
    base₃ := 0
    step₁ := 3
    step₂ := 0
    step₃ := 0
    count := cfgBitCount tm (workHeight tm seed.height) }

/-- Branch-ending output progressions for a fixed label suffix.  Labels whose
spine terminates in `halt` or `goto` are deliberately omitted. -/
def transitionDispatchBranchOutputProgressionsForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ → List AffineUnaryTripleProgression
  | _, [] => []
  | labelOffset, label :: labels =>
      let nextOffset :=
        (labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
          (transitionDispatchMuxGateAffine tm)
      let rest := transitionDispatchBranchOutputProgressionsForLabels tm seed
        nextOffset labels
      match transitionStmtFinalBranchMuxOffsetAffine tm (tm.m label) with
      | none => rest
      | some branchOffset =>
          transitionDispatchBranchOutputProgression tm seed labelOffset
            branchOffset :: rest

/-- Complete branch-ending output family for the canonical program labels. -/
def transitionDispatchBranchOutputProgressions
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineUnaryTripleProgression :=
  transitionDispatchBranchOutputProgressionsForLabels tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Semantic true-arm rows selected by the same fixed branch-ending mask. -/
def transitionDispatchBranchTrueArmRowsForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ → List (List Nat)
  | _, [] => []
  | labelOffset, label :: labels =>
      let nextOffset :=
        (labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
          (transitionDispatchMuxGateAffine tm)
      let rest := transitionDispatchBranchTrueArmRowsForLabels tm seed
        nextOffset labels
      match transitionStmtFinalBranchMuxOffsetAffine tm (tm.m label) with
      | none => rest
      | some _ =>
          transitionCfgWireValues tm (workHeight tm seed.height)
            (transitionStmtOutputWires tm (workHeight tm seed.height)
              seed.start (seed.start + 1)
              (seed.start + labelOffset.eval seed.height)
              (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
              (tm.m label) (stmtPushSet_program_subset tm label)) :: rest

/-- Complete semantic branch-ending row family. -/
def transitionDispatchBranchTrueArmRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  transitionDispatchBranchTrueArmRowsForLabels tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Seven fixed forms describing one branch output progression. -/
def transitionDispatchBranchOutputDescriptorBlock
    (tm : _root_.Turing.FinTM2)
    (labelOffset branchOffset : TransitionAffineNat) :
    List AffineUnaryTripleForm :=
  let muxOffset := labelOffset.add
    (branchOffset.shiftInput (maxPushesPerStep tm))
  [ transitionAbsoluteStartForm
      (muxOffset.add (TransitionAffineNat.const 3)),
    transitionZeroForm, transitionZeroForm,
    transitionHeightAffineForm (TransitionAffineNat.const 3),
    transitionZeroForm, transitionZeroForm,
    transitionHeightAffineForm
      ((transitionCfgBitAffine tm).shiftInput (maxPushesPerStep tm)) ]

/-- Fixed descriptor recursion for branch-ending labels. -/
def transitionDispatchBranchOutputDescriptorFormsForLabels
    (tm : _root_.Turing.FinTM2) :
    TransitionAffineNat → List tm.Λ → List AffineUnaryTripleForm
  | _, [] => []
  | labelOffset, label :: labels =>
      let nextOffset :=
        (labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
          (transitionDispatchMuxGateAffine tm)
      let rest := transitionDispatchBranchOutputDescriptorFormsForLabels tm
        nextOffset labels
      match transitionStmtFinalBranchMuxOffsetAffine tm (tm.m label) with
      | none => rest
      | some branchOffset =>
          transitionDispatchBranchOutputDescriptorBlock tm labelOffset
            branchOffset ++ rest

/-- Complete verifier-fixed descriptor table for branch-ending true arms. -/
def transitionDispatchBranchOutputDescriptorForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionDispatchBranchOutputDescriptorFormsForLabels tm
    (TransitionAffineNat.const 2) (programLabels tm)

/-- One fixed branch descriptor block evaluates to its runtime progression. -/
theorem transitionDispatchBranchOutputDescriptorBlock_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset branchOffset : TransitionAffineNat) :
    affineUnaryTripleMap
        (transitionDispatchBranchOutputDescriptorBlock tm labelOffset
          branchOffset)
        (transitionTailAffineSeed seed) =
      let progression := transitionDispatchBranchOutputProgression tm seed
        labelOffset branchOffset
      [ progression.base₁, progression.base₂, progression.base₃,
        progression.step₁, progression.step₂, progression.step₃,
        progression.count ] := by
  simp [transitionDispatchBranchOutputDescriptorBlock,
    transitionDispatchBranchOutputProgression, affineUnaryTripleMap,
    transitionAbsoluteStartForm, transitionZeroForm,
    transitionHeightAffineForm, transitionTailAffineSeed,
    affineUnaryTripleFormValue, TransitionAffineNat.eval,
    TransitionAffineNat.add, TransitionAffineNat.const,
    TransitionAffineNat.shiftInput, workHeight]
  constructor
  · ring
  · rw [← transitionCfgBitAffine_eval tm
      (seed.height + maxPushesPerStep tm)]
    unfold TransitionAffineNat.eval
    ring

/-- Evaluating the fixed recursive table yields the runtime branch
progression descriptors in label order. -/
theorem transitionDispatchBranchOutputDescriptorFormsForLabels_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (labelOffset : TransitionAffineNat) (labels : List tm.Λ),
      affineUnaryTripleMap
          (transitionDispatchBranchOutputDescriptorFormsForLabels tm
            labelOffset labels)
          (transitionTailAffineSeed seed) =
        (transitionDispatchBranchOutputProgressionsForLabels tm seed
          labelOffset labels).flatMap fun progression =>
            [ progression.base₁, progression.base₂, progression.base₃,
              progression.step₁, progression.step₂, progression.step₃,
              progression.count ] := by
  intro labelOffset labels
  induction labels generalizing labelOffset with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchBranchOutputDescriptorFormsForLabels,
        transitionDispatchBranchOutputProgressionsForLabels]
      cases hbranch :
          transitionStmtFinalBranchMuxOffsetAffine tm (tm.m label) with
      | none => exact ih _
      | some branchOffset =>
        rw [show affineUnaryTripleMap
            (transitionDispatchBranchOutputDescriptorBlock tm labelOffset
                branchOffset ++
              transitionDispatchBranchOutputDescriptorFormsForLabels tm
                (((labelOffset.add
                  (transitionDispatchStmtGateAffine tm label)).add
                    (transitionDispatchMuxGateAffine tm))) labels)
            (transitionTailAffineSeed seed) =
          affineUnaryTripleMap
              (transitionDispatchBranchOutputDescriptorBlock tm labelOffset
                branchOffset)
              (transitionTailAffineSeed seed) ++
            affineUnaryTripleMap
              (transitionDispatchBranchOutputDescriptorFormsForLabels tm
                (((labelOffset.add
                  (transitionDispatchStmtGateAffine tm label)).add
                    (transitionDispatchMuxGateAffine tm))) labels)
              (transitionTailAffineSeed seed) by
            simp [affineUnaryTripleMap, List.map_append]]
        rw [transitionDispatchBranchOutputDescriptorBlock_value, ih]
        rfl

theorem transitionDispatchBranchOutputDescriptorForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    affineUnaryTripleMap
        (transitionDispatchBranchOutputDescriptorForms tm)
        (transitionTailAffineSeed seed) =
      (transitionDispatchBranchOutputProgressions tm seed).flatMap
        fun progression =>
          [ progression.base₁, progression.base₂, progression.base₃,
            progression.step₁, progression.step₂, progression.step₃,
            progression.count ] := by
  exact transitionDispatchBranchOutputDescriptorFormsForLabels_value tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Descriptor bytes are exactly the generic progression-family input. -/
theorem encode_transitionDispatchBranchOutputDescriptorForms
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    encodeUnaryFrame
        (affineUnaryTripleMap
          (transitionDispatchBranchOutputDescriptorForms tm)
          (transitionTailAffineSeed seed)) =
      encodeAffineUnaryTripleProgressionFamily
        (transitionDispatchBranchOutputProgressions tm seed) := by
  rw [transitionDispatchBranchOutputDescriptorForms_value]
  unfold encodeUnaryFrame
  induction transitionDispatchBranchOutputProgressions tm seed with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons,
        encodeAffineUnaryTripleProgressionFamily,
        encodeAffineUnaryTripleProgression, List.flatMap_append]
      rw [ih]
      simp [encodeUnaryFrame, List.append_assoc]

/-- A branch output progression enumerates exactly the corresponding
semantic `whenTrue` row. -/
theorem transitionDispatchBranchOutputProgression_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset branchOffset : TransitionAffineNat) (label : tm.Λ)
    (hbranch : transitionStmtFinalBranchMuxOffsetAffine tm (tm.m label) =
      some branchOffset)
    (hwork : 0 < workHeight tm seed.height) :
    transitionProgressionFirstValues
        (transitionDispatchBranchOutputProgression tm seed labelOffset
          branchOffset) =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (transitionStmtOutputWires tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          (seed.start + labelOffset.eval seed.height)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
          (tm.m label) (stmtPushSet_program_subset tm label)) := by
  unfold transitionProgressionFirstValues transitionCfgWireValues
    transitionDispatchBranchOutputProgression
  rw [affineUnaryTripleProgressionRows_eq_ofFn, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext coordinate
  simp only [Function.comp_apply]
  rw [transitionStmtOutputWires_eq_finalBranchMux tm
    (workHeight tm seed.height) hwork seed.start (seed.start + 1)
    (seed.start + labelOffset.eval seed.height)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    (tm.m label) (stmtPushSet_program_subset tm label) branchOffset hbranch]
  unfold arithmeticMuxCfgWires
  simp only [Equiv.apply_symm_apply]
  rw [TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_shiftInput]
  simp only [workHeight]
  ring

/-- The complete generated progression stream is exactly the flattened
semantic family selected by the fixed branch-ending mask. -/
theorem transitionDispatchBranchOutputProgressionsForLabels_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    ∀ (labelOffset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchBranchOutputProgressionsForLabels tm seed
          labelOffset labels).flatMap transitionProgressionFirstValues =
        (transitionDispatchBranchTrueArmRowsForLabels tm seed
          labelOffset labels).flatten := by
  intro labelOffset labels
  induction labels generalizing labelOffset with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchBranchOutputProgressionsForLabels,
        transitionDispatchBranchTrueArmRowsForLabels]
      split <;> rename_i hbranch
      · exact ih _
      · simp only [List.flatMap_cons, List.flatten_cons]
        rw [transitionDispatchBranchOutputProgression_values tm seed
          labelOffset _ label hbranch hwork]
        rw [ih]

theorem transitionDispatchBranchOutputProgressions_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionDispatchBranchOutputProgressions tm seed).flatMap
        transitionProgressionFirstValues =
      (transitionDispatchBranchTrueArmRows tm seed).flatten := by
  exact transitionDispatchBranchOutputProgressionsForLabels_values tm seed
    hwork (TransitionAffineNat.const 2) (programLabels tm)

end CLRS.Chapter34.Turing.CookLevin
