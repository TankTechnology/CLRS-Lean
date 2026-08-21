import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionProgramStatementDescriptorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementRecursiveDescriptorSemantics

/-!
# Program-wide semantics of recursive statement descriptors

The concrete source is compared with an independent depth-first fold over
the verifier's canonical program-label order.  This exposes the precise
runtime row consumed by the eventual fixed descriptor interpreter.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Explicit numeric descriptor semantics for an arbitrary suffix of program
labels, including the real statement and outer-mux offset advance. -/
noncomputable def transitionLabelListStatementNumericDescriptorRow
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionAffineNat → List tm.Λ → List UnaryFrameSym
  | _, [] => []
  | labelOffset, label :: labels =>
      transitionStmtRecursiveNumericDescriptorRow tm seed labelOffset
          (TransitionStmtAffineContext.initial tm) (tm.m label)
          (stmtPushSet_program_subset tm label) ++
        transitionLabelListStatementNumericDescriptorRow tm seed
          ((labelOffset.add
            (transitionDispatchStmtGateAffine tm label)).add
              (transitionDispatchMuxGateAffine tm)) labels

/-- The concrete label-list source implements the explicit program fold
exactly. -/
theorem verifierTransitionLabelListStatementDescriptorSeedRowSource_row_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (seed : TransitionRowSeed) :
    ∀ (labelOffset : TransitionAffineNat)
      (labels : List W.machine.tm.Λ),
      (verifierTransitionLabelListStatementDescriptorSeedRowSource W
          labelOffset labels).row seed =
        transitionLabelListStatementNumericDescriptorRow W.machine.tm seed
          labelOffset labels := by
  intro labelOffset labels
  induction labels generalizing labelOffset with
  | nil =>
      simp [verifierTransitionLabelListStatementDescriptorSeedRowSource,
        verifierTransitionAffineFormSeedRowSource, affineUnaryTripleMap,
        encodeUnaryFrame,
        transitionLabelListStatementNumericDescriptorRow]
  | cons label labels ih =>
      simp only [
        verifierTransitionLabelListStatementDescriptorSeedRowSource,
        transitionLabelListStatementNumericDescriptorRow,
        VerifierTransitionSeedRowSource.append_row]
      unfold verifierTransitionLabelRecursiveDescriptorSeedRowSource
      rw [verifierTransitionStmtRecursiveDescriptorSeedRowSource_row_eq]
      rw [ih]

/-- Exact program-wide source row in the canonical label order. -/
theorem verifierTransitionProgramStatementDescriptorSeedRowSource_row_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (seed : TransitionRowSeed) :
    (verifierTransitionProgramStatementDescriptorSeedRowSource W).row seed =
      transitionLabelListStatementNumericDescriptorRow W.machine.tm seed
        (TransitionAffineNat.const 2) (programLabels W.machine.tm) := by
  exact verifierTransitionLabelListStatementDescriptorSeedRowSource_row_eq W
    seed (TransitionAffineNat.const 2) (programLabels W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin
