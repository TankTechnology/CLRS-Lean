import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanCellFrames

/-!
# Complete compact affine stack-block compiler

The height and flattened-cell segment tables are concatenated inside one
fixed group.  The prefix-drop controller consequently emits one canonical
marked stack block per transition seed, and the existing affine source
pipeline makes the whole transformation a concrete polynomial-time TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Complete segment table of one normalized stack block. -/
noncomputable def transitionStackAffineSpanBlockSegments
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock) :
    List TransitionWidenedFallbackSegment :=
  transitionStackAffineSpanHeightSegments tm k route.heightSpan ++
    transitionStackAffineSpanCellSegments tm k route.cellSpan

/-- Complete per-segment prefix-drop table of one normalized stack block. -/
def transitionStackAffineSpanBlockDropAmounts
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock) : List Nat :=
  transitionStackAffineSpanHeightDropAmounts route.heightSpan ++
    transitionStackAffineSpanCellDropAmounts tm k route.cellSpan

theorem transitionStackAffineSpanBlockDropAmounts_length
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock) :
    (transitionStackAffineSpanBlockDropAmounts tm k route).length =
      (transitionStackAffineSpanBlockSegments tm k route).length := by
  simp only [transitionStackAffineSpanBlockDropAmounts,
    transitionStackAffineSpanBlockSegments, List.length_append]
  rw [transitionStackAffineSpanHeightDropAmounts_length,
    transitionStackAffineSpanHeightSegments_length,
    transitionStackAffineSpanCellDropAmounts_length]

theorem transitionStackAffineSpanBlockDropAmounts_nonempty
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock) :
    0 < (transitionStackAffineSpanBlockDropAmounts tm k route).length := by
  unfold transitionStackAffineSpanBlockDropAmounts
  simp only [List.length_append]
  have h := transitionStackAffineSpanHeightDropAmounts_nonempty
    route.heightSpan
  omega

private theorem fixedGroupPrefixDropValues_append
    (leftDrops rightDrops : List Nat)
    (leftRows rightRows : List (List Nat))
    (hlength : leftDrops.length = leftRows.length) :
    unaryFrameFixedGroupPrefixDropValues (leftDrops ++ rightDrops)
        (leftRows ++ rightRows) =
      unaryFrameFixedGroupPrefixDropValues leftDrops leftRows ++
        unaryFrameFixedGroupPrefixDropValues rightDrops rightRows := by
  induction leftDrops generalizing leftRows with
  | nil =>
      have hnil : leftRows = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst leftRows
      rfl
  | cons amount amounts ih =>
      cases leftRows with
      | nil => simp at hlength
      | cons row rows =>
          simp only [List.length_cons] at hlength
          simp only [List.cons_append,
            unaryFrameFixedGroupPrefixDropValues]
          rw [ih rows (by omega)]
          simp [List.append_assoc]

/-- On a real terminal route, the combined segment table evaluates to the
canonical flattened output of the complete selected action sequence. -/
theorem TransitionStmtTerminalRowLayout.stackAffineSpanBlockSegments_values
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input)
    (label : W.machine.tm.Λ) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) = some layout)
    (k : W.machine.tm.K) :
    unaryFrameFixedGroupPrefixDropValues
        (transitionStackAffineSpanBlockDropAmounts W.machine.tm k
          (layout.stackAffineSpanRoute W.machine.tm k labelOffset))
        (transitionAffineSegmentValueRows seed
          (transitionStackAffineSpanBlockSegments W.machine.tm k
            (layout.stackAffineSpanRoute W.machine.tm k labelOffset))) =
      ((layout.stackAffineSpanRoute W.machine.tm k labelOffset).eval seed
        (transitionStackRouteSourceBlock W.machine.tm seed k)).flatten := by
  unfold transitionStackAffineSpanBlockDropAmounts
    transitionStackAffineSpanBlockSegments transitionAffineSegmentValueRows
  rw [List.map_append]
  rw [fixedGroupPrefixDropValues_append]
  · have hheight := layout.stackAffineSpanHeightSegments_values W input seed
      hseed label labelOffset hlayout k
    have hcells := layout.stackAffineSpanCellSegments_values W input seed hseed
      label labelOffset hlayout k
    unfold transitionAffineSegmentValueRows at hheight hcells
    rw [hheight, hcells]
    rfl
  · rw [List.length_map,
      transitionStackAffineSpanHeightDropAmounts_length,
      transitionStackAffineSpanHeightSegments_length]

/-- Generated marked complete-stack rows for one verifier-fixed compact
route. -/
noncomputable def verifierTransitionStackAffineSpanBlockFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (route : TransitionStackAffineRouteSpanBlock)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedGroupPrefixDrop
    (transitionStackAffineSpanBlockDropAmounts W.machine.tm k route)
    (transitionStackAffineSpanBlockDropAmounts_nonempty W.machine.tm k route)
    (verifierTransitionAffineSegmentRowFrames W
      (transitionStackAffineSpanBlockSegments W.machine.tm k route) input)

/-- Exact fixed-group semantics of the complete stack-block compiler. -/
theorem verifierTransitionStackAffineSpanBlockFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (route : TransitionStackAffineRouteSpanBlock)
    (input : List Γ) :
    verifierTransitionStackAffineSpanBlockFrames W k route input =
      encodeUnaryFrameFixedGroupPrefixDropOutput
        (transitionStackAffineSpanBlockDropAmounts W.machine.tm k route)
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionAffineSegmentValueRows seed
            (transitionStackAffineSpanBlockSegments W.machine.tm k route)) := by
  unfold verifierTransitionStackAffineSpanBlockFrames
  rw [verifierTransitionAffineSegmentRowFrames_eq]
  apply rewriteUnaryFrameFixedGroupPrefixDrop_groups
  intro group hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨seed, hseed, rfl⟩
  unfold transitionAffineSegmentValueRows
  rw [List.length_map]
  exact (transitionStackAffineSpanBlockDropAmounts_length W.machine.tm k
    route).symm

/-- A concrete polynomial-time TM2 emits every normalized complete-stack row
directly from the raw verifier input. -/
noncomputable def
    verifierTransitionStackAffineSpanBlockFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (route : TransitionStackAffineRouteSpanBlock) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackAffineSpanBlockFrames W k route) := by
  let source := verifierTransitionAffineSegmentRowFrames_computableInPolyTime W
    (transitionStackAffineSpanBlockSegments W.machine.tm k route)
  let rewritten :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedGroupPrefixDrop_computableInPolyTime
        (transitionStackAffineSpanBlockDropAmounts W.machine.tm k route)
        (transitionStackAffineSpanBlockDropAmounts_nonempty
          W.machine.tm k route))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedGroupPrefixDrop
      (transitionStackAffineSpanBlockDropAmounts W.machine.tm k route)
      (transitionStackAffineSpanBlockDropAmounts_nonempty
        W.machine.tm k route)
      (verifierTransitionAffineSegmentRowFrames W
        (transitionStackAffineSpanBlockSegments W.machine.tm k route) input))
  simpa [Function.comp_def] using Classical.choice rewritten

/-- For an actual terminal row, the raw-input machine emits exactly the final
sequential value route of the selected stack at every transition seed. -/
theorem TransitionStmtTerminalRowLayout.verifierStackAffineSpanBlockFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (label : W.machine.tm.Λ)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) = some layout)
    (k : W.machine.tm.K) :
    verifierTransitionStackAffineSpanBlockFrames W k
        (layout.stackAffineSpanRoute W.machine.tm k labelOffset) input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            ((transitionStackRouteActionValues W.machine.tm k
              (seed.start + labelOffset.eval seed.height) seed
              (transitionStmtStackActionsFor W.machine.tm k
                layout.stackActions)).flatten) ++ [.frameEnd] := by
  rw [verifierTransitionStackAffineSpanBlockFrames_eq]
  unfold encodeUnaryFrameFixedGroupPrefixDropOutput
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [layout.stackAffineSpanBlockSegments_values W input seed hseed label
    labelOffset hlayout k]
  rw [layout.stackAffineSpanRoute_eval W input seed hseed label labelOffset
    hlayout k]

end CLRS.Chapter34.Turing.CookLevin
