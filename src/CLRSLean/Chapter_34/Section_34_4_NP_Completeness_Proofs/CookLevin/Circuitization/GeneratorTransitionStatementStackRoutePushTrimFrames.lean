import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteStructuredSourceFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameAlternatingSuffixDrop

/-!
# Concrete suffix trimming for stack-push routes

The structured source machine emits two rows for every transition seed: the
height values and the flattened cell values.  A push discards one bottom
height value and one verifier-fixed symbol row.  This module applies the
alternating suffix controller to those concrete source packets and identifies
the result with the descriptor-level push tails.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The two runtime rows carried by every transition seed. -/
noncomputable def transitionStackRouteSourcePairs
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) : List (List Nat × List Nat) :=
  seeds.map fun seed =>
    ((transitionStackRouteSourceBlock tm seed k).heightValues,
      (transitionStackRouteSourceBlock tm seed k).cellRows.flatten)

/-- The canonical structured source is precisely the generic alternating-row
input encoding. -/
theorem transitionStackRouteStructuredSourceFrames_eq_alternatingInput
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) :
    transitionStackRouteStructuredSourceFrames tm k seeds =
      encodeUnaryFrameAlternatingSuffixDropInput
        (transitionStackRouteSourcePairs tm k seeds) := by
  unfold transitionStackRouteStructuredSourceFrames
    transitionStackRouteSourcePairs
    encodeUnaryFrameAlternatingSuffixDropInput
  rw [List.flatMap_map]

/-- Stack-push payload tails after removing the bottom height coordinate and
the bottom symbol row.  The newly inserted head values are deliberately left
to the next fixed-prefix controller. -/
noncomputable def transitionStackRoutePushTrimFrames
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  encodeUnaryFrameAlternatingSuffixDropOutput 1
    ((reachableAlphabet tm k).card + 1)
    (transitionStackRouteSourcePairs tm k seeds)

/-- The trimmed concrete rows are exactly the suffix-trimmed affine descriptor
families used by the semantic push route. -/
theorem transitionStackRoutePushTrimFrames_eq_descriptorTails
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) :
    transitionStackRoutePushTrimFrames tm k seeds =
      seeds.flatMap fun seed =>
        encodeUnaryFrame
            (transitionStackRouteFirstValues
              (transitionStackRouteTrimSuffix 1
                (transitionStackRouteHeightProgressions tm seed k))) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionStackRouteFirstValues
              (transitionStackRouteTrimSuffix
                ((reachableAlphabet tm k).card + 1)
                (transitionStackRouteCellProgressions tm seed k))) ++
          [.frameEnd] := by
  unfold transitionStackRoutePushTrimFrames
    transitionStackRouteSourcePairs
    encodeUnaryFrameAlternatingSuffixDropOutput
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionStackRouteFirstValues_trimSuffix,
    transitionStackRouteFirstValues_trimSuffix,
    transitionStackRouteFirstValues_eq_sourceBlock_height,
    transitionStackRouteFirstValues_eq_sourceBlock_cells]

/-- Raw-input specialization of the alternating suffix controller. -/
noncomputable def verifierTransitionStackRoutePushTrimFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameAlternatingSuffixDrop 1
    ((reachableAlphabet W.machine.tm k).card + 1)
    (verifierTransitionStackRouteStructuredSourceFrames W k input)

/-- Exact push-tail output from the original verifier input. -/
theorem verifierTransitionStackRoutePushTrimFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) (input : List Γ) :
    verifierTransitionStackRoutePushTrimFrames W k input =
      transitionStackRoutePushTrimFrames W.machine.tm k
        (verifierTransitionRowSeeds W input) := by
  unfold verifierTransitionStackRoutePushTrimFrames
  rw [verifierTransitionStackRouteStructuredSourceFrames_eq_source]
  rw [transitionStackRouteStructuredSourceFrames_eq_alternatingInput]
  rw [rewriteUnaryFrameAlternatingSuffixDrop_pairs]
  rfl

/-- A fixed polynomial-time TM2 computes every suffix-trimmed push payload
directly from the original verifier word. -/
noncomputable def
    verifierTransitionStackRoutePushTrimFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (k : W.machine.tm.K) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionStackRoutePushTrimFrames W k) := by
  let source :=
    verifierTransitionStackRouteStructuredSourceFrames_computableInPolyTime W k
  let trimmed := unaryFrameAlternatingSuffixDrop_computableInPolyTime 1
    ((reachableAlphabet W.machine.tm k).card + 1)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source trimmed
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameAlternatingSuffixDrop 1
      ((reachableAlphabet W.machine.tm k).card + 1)
      (verifierTransitionStackRouteStructuredSourceFrames W k input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
