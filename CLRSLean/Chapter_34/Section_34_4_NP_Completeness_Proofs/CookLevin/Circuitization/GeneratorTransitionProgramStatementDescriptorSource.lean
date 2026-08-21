import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionLabelRecursiveDescriptorSource

/-!
# Recursive statement descriptors for every verifier program label

The label-local source is folded over the canonical program-label order.
Offsets follow the real dispatch layout: after each statement, space is
reserved for the outer label mux before compiling the next statement.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- All fixed statement-tree descriptors for a label suffix, concatenated
within each transition-seed row in dispatch order. -/
noncomputable def verifierTransitionLabelListStatementDescriptorSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    TransitionAffineNat → List W.machine.tm.Λ →
      VerifierTransitionSeedRowSource W
  | _, [] => verifierTransitionAffineFormSeedRowSource W []
  | labelOffset, label :: labels =>
      let current :=
        verifierTransitionLabelRecursiveDescriptorSeedRowSource W labelOffset
          label
      let nextOffset :=
        (labelOffset.add
          (transitionDispatchStmtGateAffine W.machine.tm label)).add
            (transitionDispatchMuxGateAffine W.machine.tm)
      current.append
        (verifierTransitionLabelListStatementDescriptorSeedRowSource W
          nextOffset labels)

/-- Complete statement-tree descriptor source for the canonical verifier
program-label order. -/
noncomputable def verifierTransitionProgramStatementDescriptorSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierTransitionSeedRowSource W :=
  verifierTransitionLabelListStatementDescriptorSeedRowSource W
    (TransitionAffineNat.const 2) (programLabels W.machine.tm)

/-- Public marked-row family containing every verifier statement descriptor
at its dispatch offset. -/
noncomputable def verifierTransitionProgramStatementDescriptorFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (verifierTransitionProgramStatementDescriptorSeedRowSource W).family input

/-- Program-wide statement descriptors retain one row per transition seed. -/
theorem verifierTransitionProgramStatementDescriptorFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionProgramStatementDescriptorFamily W input).rows =
      (verifierTransitionRowSeeds W input).map
        (verifierTransitionProgramStatementDescriptorSeedRowSource W).row :=
  (verifierTransitionProgramStatementDescriptorSeedRowSource W).rows_eq input

/-- One fixed polynomial-time TM2 emits all recursive statement descriptors
of the fixed verifier program directly from its raw input. -/
noncomputable def
    verifierTransitionProgramStatementDescriptorFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionProgramStatementDescriptorFamily W) :=
  (verifierTransitionProgramStatementDescriptorSeedRowSource W
    ).computableInPolyTime

end CLRS.Chapter34.Turing.CookLevin
