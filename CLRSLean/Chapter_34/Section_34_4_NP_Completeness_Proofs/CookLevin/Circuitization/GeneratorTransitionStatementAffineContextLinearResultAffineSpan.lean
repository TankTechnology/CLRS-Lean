import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalAffineSpanFrames

/-!
# Concrete affine-span sources for arbitrary linear statement results

Branch leaves end in affine contexts that need not be the root context of a
program label.  This module generalizes the existing terminal-row source to
those arbitrary contexts.  A fixed segment table is compiled by an actual
polynomial-time TM2, while explicit endpoint bounds state exactly when its
rows are the canonical complete output routes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Endpoint conditions required by the compact widened-stack segment source.
-/
def TransitionStmtLinearResult.RouteBounds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) : Prop :=
  ∀ k,
    let route := result.context.stackRoute tm labelOffset k
    route.heightSpan.sourceDrop ≤ seed.height + 1 ∧
      route.cellSpan.sourceDrop ≤ seed.height ∧
      route.heightSpan.sourceRdrop ≤ maxPushesPerStep tm ∧
      route.cellSpan.sourceRdrop ≤ maxPushesPerStep tm

/-- Generic compact stack-block segments evaluate to their route whenever
their deletions stay inside the public and overflow portions. -/
theorem transitionStackAffineSpanBlockSegments_values_of_bounds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock)
    (hheightLeft : route.heightSpan.sourceDrop ≤ seed.height + 1)
    (hcellLeft : route.cellSpan.sourceDrop ≤ seed.height)
    (hheightRight : route.heightSpan.sourceRdrop ≤ maxPushesPerStep tm)
    (hcellRight : route.cellSpan.sourceRdrop ≤ maxPushesPerStep tm) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackAffineSpanBlockDropAmounts tm k route)
        (transitionAffineSegmentValueRows seed
          (transitionStackAffineSpanBlockSegments tm k route)) =
      (route.eval seed (transitionStackRouteSourceBlock tm seed k)).flatten := by
  unfold transitionStackAffineSpanBlockDropAmounts
    transitionStackAffineSpanBlockSegments transitionAffineSegmentValueRows
  rw [List.map_append]
  rw [unaryFrameFixedGroupPrefixDropValues_append]
  · have hheight := transitionStackAffineSpanHeightSegments_values tm seed k
      route.heightSpan hheightLeft hheightRight
    have hcells := transitionStackAffineSpanCellSegments_values tm seed k
      route.cellSpan hcellLeft hcellRight
    unfold transitionAffineSegmentValueRows at hheight hcells
    rw [hheight, hcells]
    rfl
  · rw [List.length_map,
      transitionStackAffineSpanHeightDropAmounts_length,
      transitionStackAffineSpanHeightSegments_length]

/-- Compact affine segment tables for all stacks of a linear result. -/
noncomputable def TransitionStmtLinearResult.stackAffineSpanSegments
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    List TransitionWidenedFallbackSegment :=
  (arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
    let k := (arithmeticStackEquiv tm).symm position
    transitionStackAffineSpanBlockSegments tm k
      (result.context.stackRoute tm labelOffset k)

/-- Prefix-drop table matching every stack segment. -/
def TransitionStmtLinearResult.stackAffineSpanDropAmounts
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) : List Nat :=
  (arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
    let k := (arithmeticStackEquiv tm).symm position
    transitionStackAffineSpanBlockDropAmounts tm k
      (result.context.stackRoute tm labelOffset k)

theorem TransitionStmtLinearResult.stackAffineSpanDropAmounts_length
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    (result.stackAffineSpanDropAmounts tm labelOffset).length =
      (result.stackAffineSpanSegments tm labelOffset).length := by
  unfold TransitionStmtLinearResult.stackAffineSpanDropAmounts
    TransitionStmtLinearResult.stackAffineSpanSegments
  induction arithmeticRuntimeStackSourceIndices tm with
  | nil => rfl
  | cons position positions ih =>
      simp only [List.flatMap_cons, List.length_append]
      rw [transitionStackAffineSpanBlockDropAmounts_length, ih]

/-- One fixed segment group for the complete halted/label/state/stack row. -/
noncomputable def TransitionStmtLinearResult.completeAffineSpanSegments
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    List TransitionWidenedFallbackSegment :=
  transitionStackAffineSpanConstantSegments
      (result.prefixForms tm labelOffset) ++
    result.stackAffineSpanSegments tm labelOffset

/-- Complete prefix-drop table; fixed prefix values require no deletion. -/
def TransitionStmtLinearResult.completeAffineSpanDropAmounts
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) : List Nat :=
  List.replicate (result.prefixForms tm labelOffset).length 0 ++
    result.stackAffineSpanDropAmounts tm labelOffset

theorem TransitionStmtLinearResult.completeAffineSpanDropAmounts_length
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    (result.completeAffineSpanDropAmounts tm labelOffset).length =
      (result.completeAffineSpanSegments tm labelOffset).length := by
  simp only [TransitionStmtLinearResult.completeAffineSpanDropAmounts,
    TransitionStmtLinearResult.completeAffineSpanSegments,
    List.length_append, List.length_replicate,
    transitionStackAffineSpanConstantSegments_length]
  rw [result.stackAffineSpanDropAmounts_length]

theorem TransitionStmtLinearResult.completeAffineSpanDropAmounts_nonempty
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    0 < (result.completeAffineSpanDropAmounts tm labelOffset).length := by
  unfold TransitionStmtLinearResult.completeAffineSpanDropAmounts
    TransitionStmtLinearResult.prefixForms
  simp

/-- The stack portion evaluates to the result's canonical routed blocks. -/
theorem TransitionStmtLinearResult.stackAffineSpanSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm)
    (hbounds : result.RouteBounds tm seed labelOffset) :
    unaryFrameFixedGroupPrefixDropValues
        (result.stackAffineSpanDropAmounts tm labelOffset)
        (transitionAffineSegmentValueRows seed
          (result.stackAffineSpanSegments tm labelOffset)) =
      (result.stackRouteBlocks tm seed labelOffset).flatten := by
  unfold TransitionStmtLinearResult.stackAffineSpanDropAmounts
    TransitionStmtLinearResult.stackAffineSpanSegments
    TransitionStmtLinearResult.stackRouteBlocks
    transitionAffineSegmentValueRows
  induction arithmeticRuntimeStackSourceIndices tm with
  | nil => rfl
  | cons position positions ih =>
      let k := (arithmeticStackEquiv tm).symm position
      simp only [List.flatMap_cons, List.map_append, List.map_cons,
        List.flatten_cons]
      rw [unaryFrameFixedGroupPrefixDropValues_append]
      · rcases hbounds k with ⟨hhl, hcl, hhr, hcr⟩
        have hblock := transitionStackAffineSpanBlockSegments_values_of_bounds
          tm seed k (result.context.stackRoute tm labelOffset k)
          hhl hcl hhr hcr
        unfold transitionAffineSegmentValueRows at hblock
        rw [hblock]
        rw [transitionStackRouteSourceBlock_eq]
        rw [ih]
      · rw [List.length_map,
          transitionStackAffineSpanBlockDropAmounts_length]

/-- The complete segment group denotes the exact complete route. -/
theorem TransitionStmtLinearResult.completeAffineSpanSegments_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm)
    (hbounds : result.RouteBounds tm seed labelOffset) :
    unaryFrameFixedGroupPrefixDropValues
        (result.completeAffineSpanDropAmounts tm labelOffset)
        (transitionAffineSegmentValueRows seed
          (result.completeAffineSpanSegments tm labelOffset)) =
      result.completeRouteValues tm seed labelOffset := by
  unfold TransitionStmtLinearResult.completeAffineSpanDropAmounts
    TransitionStmtLinearResult.completeAffineSpanSegments
    TransitionStmtLinearResult.completeRouteValues
    transitionAffineSegmentValueRows
  rw [List.map_append]
  rw [unaryFrameFixedGroupPrefixDropValues_append]
  · have hprefix := transitionStackAffineSpanConstantSegments_zeroDrop_values
      seed (result.prefixForms tm labelOffset)
    unfold transitionAffineSegmentValueRows at hprefix
    rw [hprefix]
    rw [result.prefixForms_value]
    have hstacks := result.stackAffineSpanSegments_values tm seed labelOffset
      hbounds
    unfold transitionAffineSegmentValueRows at hstacks
    rw [hstacks]
  · simp [transitionStackAffineSpanConstantSegments_length]

/-- Concrete marked rows generated for an arbitrary fixed linear result. -/
noncomputable def verifierTransitionLinearResultAffineSpanFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult W.machine.tm)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedGroupPrefixDrop
    (result.completeAffineSpanDropAmounts W.machine.tm labelOffset)
    (result.completeAffineSpanDropAmounts_nonempty W.machine.tm labelOffset)
    (verifierTransitionAffineSegmentRowFrames W
      (result.completeAffineSpanSegments W.machine.tm labelOffset) input)

/-- The affine-segment pipeline is an actual fixed polynomial-time TM2. -/
noncomputable def
    verifierTransitionLinearResultAffineSpanFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult W.machine.tm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionLinearResultAffineSpanFrames W labelOffset result) := by
  let source := verifierTransitionAffineSegmentRowFrames_computableInPolyTime W
    (result.completeAffineSpanSegments W.machine.tm labelOffset)
  let rewritten :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedGroupPrefixDrop_computableInPolyTime
        (result.completeAffineSpanDropAmounts W.machine.tm labelOffset)
        (result.completeAffineSpanDropAmounts_nonempty W.machine.tm
          labelOffset))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedGroupPrefixDrop
      (result.completeAffineSpanDropAmounts W.machine.tm labelOffset)
      (result.completeAffineSpanDropAmounts_nonempty W.machine.tm labelOffset)
      (verifierTransitionAffineSegmentRowFrames W
        (result.completeAffineSpanSegments W.machine.tm labelOffset) input))
  simpa [Function.comp_def] using Classical.choice rewritten

/-- Under the explicit endpoint invariant, the concrete source emits exactly
one canonical complete-route row per transition seed. -/
theorem TransitionStmtLinearResult.verifierLinearResultAffineSpanFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult W.machine.tm)
    (hbounds : ∀ seed ∈ verifierTransitionRowSeeds W input,
      result.RouteBounds W.machine.tm seed labelOffset) :
    verifierTransitionLinearResultAffineSpanFrames W labelOffset result input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame (result.completeRouteValues W.machine.tm seed
          labelOffset) ++ [.frameEnd] := by
  unfold verifierTransitionLinearResultAffineSpanFrames
  rw [verifierTransitionAffineSegmentRowFrames_eq]
  rw [rewriteUnaryFrameFixedGroupPrefixDrop_groups]
  · unfold encodeUnaryFrameFixedGroupPrefixDropOutput
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    rw [result.completeAffineSpanSegments_values W.machine.tm seed
      labelOffset (hbounds seed hseed)]
  · intro group hgroup
    rw [List.mem_map] at hgroup
    rcases hgroup with ⟨seed, hseed, rfl⟩
    unfold transitionAffineSegmentValueRows
    rw [List.length_map]
    exact (result.completeAffineSpanDropAmounts_length W.machine.tm
      labelOffset).symm

end CLRS.Chapter34.Turing.CookLevin
