import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanHeightSegments

/-!
# Raw-input compiler for compact stack-height spans

The affine segment source and fixed-position prefix-drop controller now compose
into one concrete polynomial-time TM2.  For a real terminal layout its output
is exactly one marked normalized height row per verifier transition seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Generated marked height rows for one verifier-fixed compact span. -/
noncomputable def verifierTransitionStackAffineSpanHeightFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (span : TransitionRouteSpan AffineUnaryTripleForm)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedGroupPrefixDrop
    (transitionStackAffineSpanHeightDropAmounts span)
    (transitionStackAffineSpanHeightDropAmounts_nonempty span)
    (verifierTransitionAffineSegmentRowFrames W
      (transitionStackAffineSpanHeightSegments W.machine.tm k span) input)

/-- Exact fixed-group semantics of the generated height-row compiler. -/
theorem verifierTransitionStackAffineSpanHeightFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (span : TransitionRouteSpan AffineUnaryTripleForm)
    (input : List Γ) :
    verifierTransitionStackAffineSpanHeightFrames W k span input =
      encodeUnaryFrameFixedGroupPrefixDropOutput
        (transitionStackAffineSpanHeightDropAmounts span)
        ((verifierTransitionRowSeeds W input).map fun seed =>
          transitionAffineSegmentValueRows seed
            (transitionStackAffineSpanHeightSegments W.machine.tm k span)) := by
  unfold verifierTransitionStackAffineSpanHeightFrames
  rw [verifierTransitionAffineSegmentRowFrames_eq]
  apply rewriteUnaryFrameFixedGroupPrefixDrop_groups
  intro group hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨seed, hseed, rfl⟩
  unfold transitionAffineSegmentValueRows
  rw [List.length_map,
    transitionStackAffineSpanHeightSegments_length,
    transitionStackAffineSpanHeightDropAmounts_length]

/-- One fixed polynomial-time TM2 compiles all marked height rows directly
from the original verifier input. -/
noncomputable def
    verifierTransitionStackAffineSpanHeightFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K)
    (span : TransitionRouteSpan AffineUnaryTripleForm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackAffineSpanHeightFrames W k span) := by
  let source := verifierTransitionAffineSegmentRowFrames_computableInPolyTime W
    (transitionStackAffineSpanHeightSegments W.machine.tm k span)
  let rewritten :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedGroupPrefixDrop_computableInPolyTime
        (transitionStackAffineSpanHeightDropAmounts span)
        (transitionStackAffineSpanHeightDropAmounts_nonempty span))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameFixedGroupPrefixDrop
      (transitionStackAffineSpanHeightDropAmounts span)
      (transitionStackAffineSpanHeightDropAmounts_nonempty span)
      (verifierTransitionAffineSegmentRowFrames W
        (transitionStackAffineSpanHeightSegments W.machine.tm k span) input))
  simpa [Function.comp_def] using Classical.choice rewritten

/-- For an actual terminal row, the raw-input compiler emits exactly the
height component of the complete normalized affine route at every seed. -/
theorem
    TransitionStmtTerminalRowLayout.verifierStackAffineSpanHeightFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (label : W.machine.tm.Λ)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout W.machine.tm)
    (hlayout : transitionStmtTerminalRowLayout W.machine.tm
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) = some layout)
    (k : W.machine.tm.K) :
    verifierTransitionStackAffineSpanHeightFrames W k
        (layout.stackAffineSpanRoute W.machine.tm k labelOffset).heightSpan
        input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame
            (((layout.stackAffineSpanRoute W.machine.tm k labelOffset).eval
              seed (transitionStackRouteSourceBlock W.machine.tm seed k)
              ).heightValues) ++ [.frameEnd] := by
  rw [verifierTransitionStackAffineSpanHeightFrames_eq]
  unfold encodeUnaryFrameFixedGroupPrefixDropOutput
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [layout.stackAffineSpanHeightSegments_values W input seed hseed label
    labelOffset hlayout k]

end CLRS.Chapter34.Turing.CookLevin
