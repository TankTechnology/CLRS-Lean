import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanBlockFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteTerminal

/-!
# Complete terminal-row compiler from compact affine spans

The affine terminal prefix and all normalized stack blocks are placed in one
fixed segment group.  The resulting concrete polynomial-time machine emits a
complete terminal true-arm row per verifier transition seed, in canonical
machine-stack order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- All normalized stack segment tables in canonical machine-stack order. -/
noncomputable def TransitionStmtTerminalRowLayout.stackAffineSpanSegments
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) :
    List TransitionWidenedFallbackSegment :=
  (arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
    let k := (arithmeticStackEquiv tm).symm position
    transitionStackAffineSpanBlockSegments tm k
      (layout.stackAffineSpanRoute tm k labelOffset)

/-- Prefix-drop tables corresponding to every normalized stack segment table.
-/
def TransitionStmtTerminalRowLayout.stackAffineSpanDropAmounts
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) : List Nat :=
  (arithmeticRuntimeStackSourceIndices tm).flatMap fun position =>
    let k := (arithmeticStackEquiv tm).symm position
    transitionStackAffineSpanBlockDropAmounts tm k
      (layout.stackAffineSpanRoute tm k labelOffset)

theorem TransitionStmtTerminalRowLayout.stackAffineSpanDropAmounts_length
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) :
    (layout.stackAffineSpanDropAmounts tm labelOffset).length =
      (layout.stackAffineSpanSegments tm labelOffset).length := by
  unfold TransitionStmtTerminalRowLayout.stackAffineSpanDropAmounts
    TransitionStmtTerminalRowLayout.stackAffineSpanSegments
  induction arithmeticRuntimeStackSourceIndices tm with
  | nil => rfl
  | cons position positions ih =>
      simp only [List.flatMap_cons, List.length_append]
      rw [transitionStackAffineSpanBlockDropAmounts_length, ih]

/-- Complete affine segment table for one terminal true-arm row. -/
noncomputable def TransitionStmtTerminalRowLayout.terminalAffineSpanSegments
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) :
    List TransitionWidenedFallbackSegment :=
  transitionStackAffineSpanConstantSegments
      (transitionStmtTerminalPrefixForms tm labelOffset layout) ++
    layout.stackAffineSpanSegments tm labelOffset

/-- Complete fixed prefix-drop table for one terminal true-arm row. -/
def TransitionStmtTerminalRowLayout.terminalAffineSpanDropAmounts
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) : List Nat :=
  List.replicate
      (transitionStmtTerminalPrefixForms tm labelOffset layout).length 0 ++
    layout.stackAffineSpanDropAmounts tm labelOffset

theorem TransitionStmtTerminalRowLayout.terminalAffineSpanDropAmounts_length
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) :
    (layout.terminalAffineSpanDropAmounts tm labelOffset).length =
      (layout.terminalAffineSpanSegments tm labelOffset).length := by
  simp only [TransitionStmtTerminalRowLayout.terminalAffineSpanDropAmounts,
    TransitionStmtTerminalRowLayout.terminalAffineSpanSegments,
    List.length_append, List.length_replicate,
    transitionStackAffineSpanConstantSegments_length]
  rw [layout.stackAffineSpanDropAmounts_length]

theorem TransitionStmtTerminalRowLayout.terminalAffineSpanDropAmounts_nonempty
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) :
    0 < (layout.terminalAffineSpanDropAmounts tm labelOffset).length := by
  unfold TransitionStmtTerminalRowLayout.terminalAffineSpanDropAmounts
    transitionStmtTerminalPrefixForms
  simp

/-- All normalized stack segment groups evaluate to the established terminal
stack descriptor routes. -/
theorem TransitionStmtTerminalRowLayout.stackAffineSpanSegments_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input)
    (label : W.machine.tm.Λ) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) = some layout) :
    unaryFrameFixedGroupPrefixDropValues
        (layout.stackAffineSpanDropAmounts W.machine.tm labelOffset)
        (transitionAffineSegmentValueRows seed
          (layout.stackAffineSpanSegments W.machine.tm labelOffset)) =
      (layout.stackDescriptorRouteValues W.machine.tm
        (seed.start + labelOffset.eval seed.height) seed).flatten := by
  unfold TransitionStmtTerminalRowLayout.stackAffineSpanDropAmounts
    TransitionStmtTerminalRowLayout.stackAffineSpanSegments
    TransitionStmtTerminalRowLayout.stackDescriptorRouteValues
    transitionAffineSegmentValueRows
  induction arithmeticRuntimeStackSourceIndices W.machine.tm with
  | nil => rfl
  | cons position positions ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons,
        List.flatten_cons]
      rw [unaryFrameFixedGroupPrefixDropValues_append]
      · let k := (arithmeticStackEquiv W.machine.tm).symm position
        have hblock := layout.stackAffineSpanBlockSegments_values W input seed
          hseed label labelOffset hlayout k
        unfold transitionAffineSegmentValueRows at hblock
        rw [hblock]
        rw [layout.stackAffineSpanRoute_eval W input seed hseed label
          labelOffset hlayout k]
        rw [ih]
      · rw [List.length_map,
          transitionStackAffineSpanBlockDropAmounts_length]

/-- The whole terminal segment group evaluates exactly to the already verified
descriptor-derived terminal row. -/
theorem TransitionStmtTerminalRowLayout.terminalAffineSpanSegments_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input)
    (label : W.machine.tm.Λ) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) = some layout) :
    unaryFrameFixedGroupPrefixDropValues
        (layout.terminalAffineSpanDropAmounts W.machine.tm labelOffset)
        (transitionAffineSegmentValueRows seed
          (layout.terminalAffineSpanSegments W.machine.tm labelOffset)) =
      (TransitionDispatchTrueArmNormalizedLayout.terminal labelOffset label
        layout hlayout).terminalRowDescriptorRoute W.machine.tm seed := by
  unfold TransitionStmtTerminalRowLayout.terminalAffineSpanDropAmounts
    TransitionStmtTerminalRowLayout.terminalAffineSpanSegments
    transitionAffineSegmentValueRows
  rw [List.map_append]
  rw [unaryFrameFixedGroupPrefixDropValues_append]
  · have hprefix := transitionStackAffineSpanConstantSegments_zeroDrop_values
      seed (transitionStmtTerminalPrefixForms W.machine.tm labelOffset layout)
    unfold transitionAffineSegmentValueRows at hprefix
    rw [hprefix]
    have hstacks := layout.stackAffineSpanSegments_values W input seed hseed
      label labelOffset hlayout
    unfold transitionAffineSegmentValueRows at hstacks
    rw [hstacks]
    simp only [
      TransitionDispatchTrueArmNormalizedLayout.terminalRowDescriptorRoute]
  · simp [transitionStackAffineSpanConstantSegments_length]

/-- Raw-input generated marked rows for one fixed terminal layout. -/
noncomputable def verifierTransitionTerminalAffineSpanFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedGroupPrefixDrop
    (layout.terminalAffineSpanDropAmounts W.machine.tm labelOffset)
    (layout.terminalAffineSpanDropAmounts_nonempty W.machine.tm labelOffset)
    (verifierTransitionAffineSegmentRowFrames W
      (layout.terminalAffineSpanSegments W.machine.tm labelOffset) input)

/-- A concrete polynomial-time TM2 emits every complete row of one fixed
terminal layout directly from the verifier input. -/
noncomputable def
    verifierTransitionTerminalAffineSpanFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionTerminalAffineSpanFrames W labelOffset layout) := by
  let source := verifierTransitionAffineSegmentRowFrames_computableInPolyTime W
    (layout.terminalAffineSpanSegments W.machine.tm labelOffset)
  let rewritten :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedGroupPrefixDrop_computableInPolyTime
        (layout.terminalAffineSpanDropAmounts W.machine.tm labelOffset)
        (layout.terminalAffineSpanDropAmounts_nonempty
          W.machine.tm labelOffset))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedGroupPrefixDrop
      (layout.terminalAffineSpanDropAmounts W.machine.tm labelOffset)
      (layout.terminalAffineSpanDropAmounts_nonempty W.machine.tm labelOffset)
      (verifierTransitionAffineSegmentRowFrames W
        (layout.terminalAffineSpanSegments W.machine.tm labelOffset) input))
  simpa [Function.comp_def] using Classical.choice rewritten

/-- Exact semantic output of the fixed terminal-layout source machine. -/
theorem TransitionStmtTerminalRowLayout.verifierTerminalAffineSpanFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (label : W.machine.tm.Λ)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) = some layout) :
    verifierTransitionTerminalAffineSpanFrames W labelOffset layout input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            ((TransitionDispatchTrueArmNormalizedLayout.terminal labelOffset
              label layout hlayout).terminalRowValueRoute W.machine.tm seed) ++
          [.frameEnd] := by
  unfold verifierTransitionTerminalAffineSpanFrames
  rw [verifierTransitionAffineSegmentRowFrames_eq]
  rw [rewriteUnaryFrameFixedGroupPrefixDrop_groups]
  · unfold encodeUnaryFrameFixedGroupPrefixDropOutput
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    rw [layout.terminalAffineSpanSegments_values W input seed hseed label
      labelOffset hlayout]
    rw [TransitionDispatchTrueArmNormalizedLayout.terminalRowDescriptorRoute_eq]
  · intro group hgroup
    rw [List.mem_map] at hgroup
    rcases hgroup with ⟨seed, hseed, rfl⟩
    unfold transitionAffineSegmentValueRows
    rw [List.length_map]
    exact (layout.terminalAffineSpanDropAmounts_length W.machine.tm
      labelOffset).symm

end CLRS.Chapter34.Turing.CookLevin
