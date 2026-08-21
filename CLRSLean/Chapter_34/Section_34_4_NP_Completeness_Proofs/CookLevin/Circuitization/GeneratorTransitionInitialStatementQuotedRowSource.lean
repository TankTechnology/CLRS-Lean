import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementQuotedRowSource

/-!
# Quoted controller rows for one verifier program label

The general recursive source is instantiated here with the verifier's initial
statement context, its uniform route theorem, and its public-row padding
theorem.  The resulting concrete TM2 source directly targets the textbook
statement script for a fixed program label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Initial-context recursive padding, uniform over all canonical seeds. -/
theorem verifierTransitionInitialStmtPadding
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (label : W.machine.tm.Λ) :
    VerifierTransitionRecursiveStmtPadding W
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) := by
  intro input seed hseed
  exact transitionStmtRecursiveContextPadding_initial_verifier W input seed
    (verifierTransitionRowSeeds_height_eq W input seed hseed) label

/-- Concrete quoted statement source for one fixed verifier label. -/
noncomputable def verifierTransitionInitialStmtQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    VerifierTransitionSeedRowSource W :=
  verifierTransitionStmtQuotedSeedRowSource W labelOffset
    (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label)
    (stmtPushSet_program_subset W.machine.tm label)
    (verifierTransitionRecursivePlan_uniformLinearRouteBounds W labelOffset
      label)
    (verifierTransitionInitialStmtPadding W label)

/-- On every canonical seed, the physical row is exactly the quotation of
the canonical statement-controller script for this label. -/
theorem verifierTransitionInitialStmtQuotedSeedRowSource_row_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (verifierTransitionInitialStmtQuotedSeedRowSource W labelOffset label).row
        seed =
      quoteUnaryFrameStream
        (encodeAffineStmtControllerScript
          (transitionStmtScript W.machine.tm
            (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
            (seed.start + labelOffset.eval seed.height)
            (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
              seed.rowBase)
            (W.machine.tm.m label)
            (stmtPushSet_program_subset W.machine.tm label))) := by
  unfold verifierTransitionInitialStmtQuotedSeedRowSource
  rw [verifierTransitionStmtQuotedSeedRowSource_row_eq W labelOffset
    (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
    (verifierTransitionRecursivePlan_uniformLinearRouteBounds W labelOffset
      label)
    (verifierTransitionInitialStmtPadding W label) input seed hseed]
  rw [transitionStmtRecursiveInitialControllerFrames_eq_script W input seed
    (verifierTransitionRowSeeds_height_eq W input seed hseed) labelOffset
    label]

end CLRS.Chapter34.Turing.CookLevin
