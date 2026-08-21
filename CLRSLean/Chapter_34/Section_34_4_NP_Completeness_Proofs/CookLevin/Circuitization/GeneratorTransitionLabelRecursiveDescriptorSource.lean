import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementRecursiveDescriptorSource

/-!
# Complete recursive descriptor source for a verifier program label

The generic statement-tree source is instantiated with the actual verifier
program statement, its initial affine context, the program support theorem,
and the already established uniform route bounds.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One complete recursive statement descriptor row per transition seed for
one fixed verifier program label. -/
noncomputable def verifierTransitionLabelRecursiveDescriptorSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    VerifierTransitionSeedRowSource W :=
  verifierTransitionStmtRecursiveDescriptorSeedRowSource W labelOffset
    (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
    (verifierTransitionRecursivePlan_uniformLinearRouteBounds W labelOffset
      label)

/-- Public marked-row family for one verifier program label. -/
noncomputable def verifierTransitionLabelRecursiveDescriptorFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (verifierTransitionLabelRecursiveDescriptorSeedRowSource W labelOffset
    label).family input

/-- The label source remains aligned with the canonical transition seeds. -/
theorem verifierTransitionLabelRecursiveDescriptorFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ)
    (input : List Γ) :
    (verifierTransitionLabelRecursiveDescriptorFamily W labelOffset label
      input).rows =
      (verifierTransitionRowSeeds W input).map
        (verifierTransitionLabelRecursiveDescriptorSeedRowSource W
          labelOffset label).row := by
  exact (verifierTransitionLabelRecursiveDescriptorSeedRowSource W
    labelOffset label).rows_eq input

/-- A fixed polynomial-time TM2 generates the complete recursive descriptor
for an actual verifier program label from the raw verifier input. -/
noncomputable def
    verifierTransitionLabelRecursiveDescriptorFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionLabelRecursiveDescriptorFamily W labelOffset
        label) :=
  (verifierTransitionLabelRecursiveDescriptorSeedRowSource W labelOffset
    label).computableInPolyTime

end CLRS.Chapter34.Turing.CookLevin
