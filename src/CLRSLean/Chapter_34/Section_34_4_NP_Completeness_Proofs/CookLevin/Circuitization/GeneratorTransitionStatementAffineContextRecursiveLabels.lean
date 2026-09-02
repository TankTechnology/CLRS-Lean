import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveSource

/-!
# Recursive statement-controller streams for all dispatch labels

One local transition dispatch compiles every fixed program label at a distinct
affine offset.  This module folds the unrestricted recursive statement source
over the canonical label order and proves exact agreement with the semantic
statement scripts for the whole label family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Interleaved recursive controller output for an arbitrary label suffix. -/
noncomputable def
    transitionDispatchRecursiveStatementControllerFramesForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ → List UnaryFrameSym
  | _, [] => []
  | labelOffset, label :: labels =>
      transitionStmtRecursiveControllerFrames tm seed labelOffset
          (TransitionStmtAffineContext.initial tm) (tm.m label)
          (stmtPushSet_program_subset tm label) ++
        transitionDispatchRecursiveStatementControllerFramesForLabels tm seed
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm)) labels

/-- Semantic controller encodings of the same statement-script family. -/
def transitionDispatchRecursiveStatementSemanticFramesForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ → List UnaryFrameSym
  | _, [] => []
  | labelOffset, label :: labels =>
      encodeAffineStmtControllerScript
          (transitionStmtScript tm (workHeight tm seed.height) seed.start
            (seed.start + 1)
            (seed.start + labelOffset.eval seed.height)
            (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
            (tm.m label) (stmtPushSet_program_subset tm label)) ++
        transitionDispatchRecursiveStatementSemanticFramesForLabels tm seed
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm)) labels

/-- Complete recursive statement-controller output in canonical label order. -/
def transitionDispatchRecursiveStatementControllerFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List UnaryFrameSym :=
  transitionDispatchRecursiveStatementControllerFramesForLabels tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Complete semantic statement-script encoding in canonical label order. -/
def transitionDispatchRecursiveStatementSemanticFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List UnaryFrameSym :=
  transitionDispatchRecursiveStatementSemanticFramesForLabels tm seed
    (TransitionAffineNat.const 2) (programLabels tm)

/-- Every verifier label suffix is generated exactly. -/
theorem
    verifierTransitionDispatchRecursiveStatementControllerFramesForLabels_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length) :
    ∀ (labelOffset : TransitionAffineNat)
      (labels : List W.machine.tm.Λ),
      transitionDispatchRecursiveStatementControllerFramesForLabels
          W.machine.tm seed labelOffset labels =
        transitionDispatchRecursiveStatementSemanticFramesForLabels
          W.machine.tm seed labelOffset labels := by
  intro labelOffset labels
  induction labels generalizing labelOffset with
  | nil => rfl
  | cons label labels ih =>
      simp only [
        transitionDispatchRecursiveStatementControllerFramesForLabels,
        transitionDispatchRecursiveStatementSemanticFramesForLabels]
      rw [transitionStmtRecursiveInitialControllerFrames_eq_script W input
        seed hseed labelOffset label]
      rw [ih]

/-- Hence the complete canonical label family has no residual statement-shape
restriction. -/
theorem verifierTransitionDispatchRecursiveStatementControllerFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length) :
    transitionDispatchRecursiveStatementControllerFrames W.machine.tm seed =
      transitionDispatchRecursiveStatementSemanticFrames W.machine.tm
        seed := by
  exact
    verifierTransitionDispatchRecursiveStatementControllerFramesForLabels_eq
      W input seed hseed (TransitionAffineNat.const 2)
      (programLabels W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin
