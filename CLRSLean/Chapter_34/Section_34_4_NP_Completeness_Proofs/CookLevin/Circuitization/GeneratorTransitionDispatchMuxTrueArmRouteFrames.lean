import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteTrueArms

/-!
# Exact raw-input frame target for complete dispatch true arms

The branch-ending true arms already have a concrete affine source.  The
terminal-ending arms now have exact descriptor-derived stack routes.  This
module freezes their common raw-input unary-frame target and proves that it is
byte-for-byte the complete semantic true-arm operand stream.  The separate
controller-realization theorem will consume this exact target.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Unary encoding of the complete descriptor-derived true-arm route family,
in transition-row order and then verifier program-label order. -/
noncomputable def verifierTransitionDispatchTrueArmRouteValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    ((verifierTransitionRowSeeds W input).flatMap fun seed =>
      (transitionDispatchTrueArmDescriptorRoutes W.machine.tm seed).flatten)

/-- The descriptor-derived frame target is exactly the already verified
complete value-route stream. -/
theorem verifierTransitionDispatchTrueArmRouteValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTrueArmRouteValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchTrueArmValueRoutes W.machine.tm seed).flatten) := by
  unfold verifierTransitionDispatchTrueArmRouteValueFrames
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  congr 1
  apply transitionDispatchTrueArmDescriptorRoutes_eq
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  rw [hheight]
  unfold workHeight
  exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

/-- Consequently the frozen byte target is the semantic true-arm family used
by dispatch, with no descriptor or routing abstraction left in the statement.
-/
theorem verifierTransitionDispatchTrueArmRouteValueFrames_eq_semantic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTrueArmRouteValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchTrueArmRowsFromSeed W.machine.tm seed).flatten) := by
  unfold verifierTransitionDispatchTrueArmRouteValueFrames
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  congr 1
  apply transitionDispatchTrueArmDescriptorRoutes_eq_seed
  have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
  rw [hheight]
  unfold workHeight
  exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _

end CLRS.Chapter34.Turing.CookLevin
