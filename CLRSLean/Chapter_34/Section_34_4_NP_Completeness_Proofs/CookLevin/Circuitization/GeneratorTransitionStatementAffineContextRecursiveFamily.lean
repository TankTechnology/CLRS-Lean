import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveDispatch
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionInputCompiler

/-!
# Complete transition-family packets with recursive statements

The unrestricted recursive dispatch stream is joined here with the fixed
statement boundary and the already compiled post-dispatch tail.  The result
is proved byte-for-byte equal to the canonical unary input of the complete
transition-family controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One complete local transition packet with its dispatch supplied by the
unrestricted recursive statement source. -/
def transitionSeedRecursiveLocalUnaryInput
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List UnaryFrameSym :=
  transitionDispatchRecursiveControllerFramesFromSeed tm seed ++
    affineStmtTransitionBoundaryCode ++
    encodeAffineTransitionTail
      (transitionScriptFromSeed tm seed
        (seed.rowBase + cfgBitCount tm seed.height)) ++
    [.frameEnd]

/-- Row-major complete transition-family input assembled from recursive local
packets.  The leading marker of each row belongs to the outer family
controller. -/
def verifierTransitionRecursiveFamilyUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    .frameEnd :: transitionSeedRecursiveLocalUnaryInput W.machine.tm seed

/-- The recursively assembled packets are exactly the canonical raw-input
transition-family target, with no statement-shape restriction. -/
theorem verifierTransitionRecursiveFamilyUnaryTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRecursiveFamilyUnaryTarget W input =
      verifierTransitionFamilyUnaryInputTarget W input := by
  rw [verifierTransitionFamilyUnaryInputTarget_eq_flatMap]
  unfold verifierTransitionRecursiveFamilyUnaryTarget
  apply List.flatMap_congr
  intro seed hseed
  have hdispatch :=
    verifierTransitionDispatchRecursiveControllerFramesFromSeed_eq_script
      W input seed (verifierTransitionRowSeeds_height_eq W input seed hseed)
  unfold transitionSeedRecursiveLocalUnaryInput transitionSeedLocalUnaryInput
    encodeAffineTransitionLocalUnary
  rw [hdispatch]
  rfl

end CLRS.Chapter34.Turing.CookLevin
