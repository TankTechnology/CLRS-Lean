import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalAffineSpanFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmRouteFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowUnmark

/-!
# Complete dispatch true-arm compiler from affine spans

Branch rows are single affine segments, while terminal rows use the compact
multi-stack span tables.  This module places both cases in the original fixed
label order, executes one segment group per transition seed, and erases the
outer seed markers to obtain the exact complete true-arm operand stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One fixed segment denoting the complete output row of a branch-ending
statement. -/
def transitionDispatchBranchOutputSegment
    (tm : _root_.Turing.FinTM2)
    (labelOffset branchOffset : TransitionAffineNat) :
    TransitionWidenedFallbackSegment :=
  let muxOffset := labelOffset.add
    (branchOffset.shiftInput (maxPushesPerStep tm))
  { base := transitionAbsoluteStartForm
      (muxOffset.add (TransitionAffineNat.const 3))
    step := 3
    count := (transitionCfgBitAffine tm).shiftInput
      (maxPushesPerStep tm) }

theorem transitionDispatchBranchOutputSegment_progression
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset branchOffset : TransitionAffineNat) :
    transitionWidenedFallbackSegmentProgression seed
        (transitionDispatchBranchOutputSegment tm labelOffset branchOffset) =
      transitionDispatchBranchOutputProgression tm seed labelOffset
        branchOffset := by
  simp [transitionDispatchBranchOutputSegment,
      transitionDispatchBranchOutputProgression,
      transitionWidenedFallbackSegmentProgression,
      transitionAbsoluteStartForm_value, TransitionAffineNat.eval_add,
      TransitionAffineNat.eval_shiftInput, workHeight]
  omega

theorem transitionDispatchBranchOutputSegment_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset branchOffset : TransitionAffineNat) :
    transitionWidenedFallbackSegmentValues seed
        (transitionDispatchBranchOutputSegment tm labelOffset branchOffset) =
      transitionProgressionFirstValues
        (transitionDispatchBranchOutputProgression tm seed labelOffset
          branchOffset) := by
  unfold transitionWidenedFallbackSegmentValues
    transitionProgressionFirstValues
  rw [transitionDispatchBranchOutputSegment_progression]

/-- Affine segment table contributed by one normalized true-arm row. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.affineSpanSegments
    (tm : _root_.Turing.FinTM2) :
    TransitionDispatchTrueArmNormalizedLayout tm →
      List TransitionWidenedFallbackSegment
  | .branch labelOffset _ branchOffset _ =>
      [transitionDispatchBranchOutputSegment tm labelOffset branchOffset]
  | .terminal labelOffset _ rowLayout _ =>
      rowLayout.terminalAffineSpanSegments tm labelOffset

/-- Fixed prefix drops corresponding to one normalized true-arm row. -/
def TransitionDispatchTrueArmNormalizedLayout.affineSpanDropAmounts
    (tm : _root_.Turing.FinTM2) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | .branch _ _ _ _ => [0]
  | .terminal labelOffset _ rowLayout _ =>
      rowLayout.terminalAffineSpanDropAmounts tm labelOffset

theorem
    TransitionDispatchTrueArmNormalizedLayout.affineSpanDropAmounts_length
    (tm : _root_.Turing.FinTM2)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    (layout.affineSpanDropAmounts tm).length =
      (layout.affineSpanSegments tm).length := by
  cases layout with
  | branch => rfl
  | terminal labelOffset label rowLayout hlayout =>
      exact rowLayout.terminalAffineSpanDropAmounts_length tm labelOffset

/-- Every normalized layout's segment table evaluates to its established
descriptor route. -/
theorem TransitionDispatchTrueArmNormalizedLayout.affineSpanSegments_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input)
    (layout : TransitionDispatchTrueArmNormalizedLayout W.machine.tm) :
    unaryFrameFixedGroupPrefixDropValues
        (layout.affineSpanDropAmounts W.machine.tm)
        (transitionAffineSegmentValueRows seed
          (layout.affineSpanSegments W.machine.tm)) =
      layout.descriptorValueRoute W.machine.tm seed := by
  cases layout with
  | branch labelOffset label branchOffset hbranch =>
      change unaryFrameFixedGroupPrefixDropValues [0]
          (transitionAffineSegmentValueRows seed
            [transitionDispatchBranchOutputSegment W.machine.tm labelOffset
              branchOffset]) =
        transitionProgressionFirstValues
          (transitionDispatchBranchOutputProgression W.machine.tm seed
            labelOffset branchOffset)
      unfold transitionAffineSegmentValueRows
      rw [List.map_singleton,
        transitionDispatchBranchOutputSegment_values]
      simp [unaryFrameFixedGroupPrefixDropValues]
  | terminal labelOffset label rowLayout hlayout =>
      exact rowLayout.terminalAffineSpanSegments_values W input seed hseed
        label labelOffset hlayout

/-- A zero-length sentinel keeps the fixed segment group nonempty without
contributing an operand. -/
def transitionDispatchTrueArmEmptySegment :
    TransitionWidenedFallbackSegment :=
  { base := transitionZeroForm
    step := 0
    count := TransitionAffineNat.const 0 }

@[simp] theorem transitionDispatchTrueArmEmptySegment_values
    (seed : TransitionRowSeed) :
    transitionWidenedFallbackSegmentValues seed
        transitionDispatchTrueArmEmptySegment = [] := by
  rw [transitionWidenedFallbackSegmentValues_eq_replicate]
  · simp [transitionDispatchTrueArmEmptySegment,
      TransitionAffineNat.const, TransitionAffineNat.eval]
  · rfl

/-- Complete fixed segment table in verifier program-label order. -/
noncomputable def transitionDispatchTrueArmAffineSpanSegments
    (tm : _root_.Turing.FinTM2) :
    List TransitionWidenedFallbackSegment :=
  transitionDispatchTrueArmEmptySegment ::
    (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
      (TransitionDispatchTrueArmNormalizedLayout.affineSpanSegments tm)

/-- Complete fixed prefix-drop table in the same order. -/
def transitionDispatchTrueArmAffineSpanDropAmounts
    (tm : _root_.Turing.FinTM2) : List Nat :=
  0 :: (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.affineSpanDropAmounts tm)

theorem transitionDispatchTrueArmAffineSpanDropAmounts_length
    (tm : _root_.Turing.FinTM2) :
    (transitionDispatchTrueArmAffineSpanDropAmounts tm).length =
      (transitionDispatchTrueArmAffineSpanSegments tm).length := by
  simp only [transitionDispatchTrueArmAffineSpanDropAmounts,
    transitionDispatchTrueArmAffineSpanSegments, List.length_cons]
  congr 1
  induction transitionDispatchTrueArmNormalizedLayouts tm with
  | nil => rfl
  | cons layout layouts ih =>
      simp only [List.flatMap_cons, List.length_append]
      rw [layout.affineSpanDropAmounts_length, ih]

theorem transitionDispatchTrueArmAffineSpanDropAmounts_nonempty
    (tm : _root_.Turing.FinTM2) :
    0 < (transitionDispatchTrueArmAffineSpanDropAmounts tm).length := by
  simp [transitionDispatchTrueArmAffineSpanDropAmounts]

private theorem transitionDispatchTrueArmAffineSpanValuesForLayouts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    ∀ layouts : List
        (TransitionDispatchTrueArmNormalizedLayout W.machine.tm),
      unaryFrameFixedGroupPrefixDropValues
          (layouts.flatMap fun layout =>
            layout.affineSpanDropAmounts W.machine.tm)
          (transitionAffineSegmentValueRows seed
            (layouts.flatMap fun layout =>
              layout.affineSpanSegments W.machine.tm)) =
        (layouts.map fun layout =>
          layout.descriptorValueRoute W.machine.tm seed).flatten := by
  intro layouts
  unfold transitionAffineSegmentValueRows
  induction layouts with
  | nil => rfl
  | cons layout layouts ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons,
        List.flatten_cons]
      rw [unaryFrameFixedGroupPrefixDropValues_append]
      · have hlayout := layout.affineSpanSegments_values W input seed hseed
        unfold transitionAffineSegmentValueRows at hlayout
        rw [hlayout]
        rw [ih]
      · rw [List.length_map,
          layout.affineSpanDropAmounts_length]

/-- One complete segment group evaluates to every true-arm row in the exact
original label order. -/
theorem transitionDispatchTrueArmAffineSpanValues
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionDispatchTrueArmAffineSpanDropAmounts W.machine.tm)
        (transitionAffineSegmentValueRows seed
          (transitionDispatchTrueArmAffineSpanSegments W.machine.tm)) =
      (transitionDispatchTrueArmDescriptorRoutes W.machine.tm seed).flatten := by
  unfold transitionDispatchTrueArmAffineSpanDropAmounts
    transitionDispatchTrueArmAffineSpanSegments
    transitionAffineSegmentValueRows
  simp only [List.map_cons, unaryFrameFixedGroupPrefixDropValues,
    List.drop_zero, transitionDispatchTrueArmEmptySegment_values,
    List.nil_append]
  exact transitionDispatchTrueArmAffineSpanValuesForLayouts W input seed hseed
    (transitionDispatchTrueArmNormalizedLayouts W.machine.tm)

/-- Marked complete true-arm rows, one fixed group per transition seed. -/
noncomputable def verifierTransitionDispatchTrueArmAffineSpanMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedGroupPrefixDrop
    (transitionDispatchTrueArmAffineSpanDropAmounts W.machine.tm)
    (transitionDispatchTrueArmAffineSpanDropAmounts_nonempty W.machine.tm)
    (verifierTransitionAffineSegmentRowFrames W
      (transitionDispatchTrueArmAffineSpanSegments W.machine.tm) input)

noncomputable def
    verifierTransitionDispatchTrueArmAffineSpanMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchTrueArmAffineSpanMarkedFrames W) := by
  let source := verifierTransitionAffineSegmentRowFrames_computableInPolyTime W
    (transitionDispatchTrueArmAffineSpanSegments W.machine.tm)
  let rewritten :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedGroupPrefixDrop_computableInPolyTime
        (transitionDispatchTrueArmAffineSpanDropAmounts W.machine.tm)
        (transitionDispatchTrueArmAffineSpanDropAmounts_nonempty
          W.machine.tm))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedGroupPrefixDrop
      (transitionDispatchTrueArmAffineSpanDropAmounts W.machine.tm)
      (transitionDispatchTrueArmAffineSpanDropAmounts_nonempty W.machine.tm)
      (verifierTransitionAffineSegmentRowFrames W
        (transitionDispatchTrueArmAffineSpanSegments W.machine.tm) input))
  simpa [Function.comp_def] using Classical.choice rewritten

theorem verifierTransitionDispatchTrueArmAffineSpanMarkedFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTrueArmAffineSpanMarkedFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            ((transitionDispatchTrueArmDescriptorRoutes W.machine.tm
              seed).flatten) ++ [.frameEnd] := by
  unfold verifierTransitionDispatchTrueArmAffineSpanMarkedFrames
  rw [verifierTransitionAffineSegmentRowFrames_eq]
  rw [rewriteUnaryFrameFixedGroupPrefixDrop_groups]
  · unfold encodeUnaryFrameFixedGroupPrefixDropOutput
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    rw [transitionDispatchTrueArmAffineSpanValues W input seed hseed]
  · intro group hgroup
    rw [List.mem_map] at hgroup
    rcases hgroup with ⟨seed, hseed, rfl⟩
    unfold transitionAffineSegmentValueRows
    rw [List.length_map]
    exact (transitionDispatchTrueArmAffineSpanDropAmounts_length
      W.machine.tm).symm

private theorem unmarkUnaryFrame_ticks (count : Nat) :
    (List.replicate count UnaryFrameSym.tick).flatMap
        affineUnaryTripleProgressionRowUnmarkBody.emit =
      List.replicate count UnaryFrameSym.tick := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      rfl

private theorem unmarkUnaryFrame_encodeUnaryFrame (values : List Nat) :
    (encodeUnaryFrame values).flatMap
        affineUnaryTripleProgressionRowUnmarkBody.emit =
      encodeUnaryFrame values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) =
          List.replicate value .tick ++ .separator ::
            encodeUnaryFrame values by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock]]
      rw [List.flatMap_append, unmarkUnaryFrame_ticks]
      change List.replicate value .tick ++
          .separator :: (encodeUnaryFrame values).flatMap
            affineUnaryTripleProgressionRowUnmarkBody.emit =
        List.replicate value .tick ++
          .separator :: encodeUnaryFrame values
      rw [ih]

private theorem unmarkUnaryFrame_markedRows (rows : List (List Nat)) :
    unmarkAffineUnaryTripleProgressionRows
        (rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) =
      encodeUnaryFrame rows.flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      unfold unmarkAffineUnaryTripleProgressionRows at ih ⊢
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [unmarkUnaryFrame_encodeUnaryFrame]
      change encodeUnaryFrame row ++ [] ++
          (rows.flatMap fun other =>
            encodeUnaryFrame other ++ [.frameEnd]).flatMap
              affineUnaryTripleProgressionRowUnmarkBody.emit = _
      simp only [List.append_nil]
      rw [ih]
      simp [encodeUnaryFrame, List.flatten_cons,
        List.flatMap_append]

/-- Unmarked byte stream consumed by the complete dispatch source target. -/
noncomputable def verifierTransitionDispatchTrueArmAffineSpanFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unmarkAffineUnaryTripleProgressionRows
    (verifierTransitionDispatchTrueArmAffineSpanMarkedFrames W input)

/-- A fixed polynomial-time TM2 emits the complete dispatch true-arm operand
stream directly from the raw verifier input. -/
noncomputable def
    verifierTransitionDispatchTrueArmAffineSpanFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchTrueArmAffineSpanFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionDispatchTrueArmAffineSpanMarkedFrames_computableInPolyTime
        W)
      unmarkAffineUnaryTripleProgressionRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unmarkAffineUnaryTripleProgressionRows
      (verifierTransitionDispatchTrueArmAffineSpanMarkedFrames W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Exact closure against the previously frozen byte-level semantic target. -/
theorem verifierTransitionDispatchTrueArmAffineSpanFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTrueArmAffineSpanFrames W input =
      verifierTransitionDispatchTrueArmRouteValueFrames W input := by
  unfold verifierTransitionDispatchTrueArmAffineSpanFrames
  rw [verifierTransitionDispatchTrueArmAffineSpanMarkedFrames_eq]
  rw [show
      (verifierTransitionRowSeeds W input).flatMap
          (fun seed =>
            encodeUnaryFrame
                ((transitionDispatchTrueArmDescriptorRoutes W.machine.tm
                  seed).flatten) ++ [.frameEnd]) =
        ((verifierTransitionRowSeeds W input).map fun seed =>
          (transitionDispatchTrueArmDescriptorRoutes W.machine.tm
            seed).flatten).flatMap
            (fun row => encodeUnaryFrame row ++ [.frameEnd]) by
      simp [List.flatMap_map]]
  rw [unmarkUnaryFrame_markedRows]
  rfl

/-- The generated bytes are the semantic true inputs of every dispatch mux,
with all routing descriptors eliminated from the public statement. -/
theorem verifierTransitionDispatchTrueArmAffineSpanFrames_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTrueArmAffineSpanFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchTrueArmRowsFromSeed W.machine.tm seed).flatten) := by
  rw [verifierTransitionDispatchTrueArmAffineSpanFrames_eq]
  exact verifierTransitionDispatchTrueArmRouteValueFrames_eq_semantic W input

end CLRS.Chapter34.Turing.CookLevin
