import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineFormDescriptorSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeedRowSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveBranchDescriptorSource

/-!
# Seed-row adapters for statement descriptor fragments

The affine head compiler and recursive branch descriptor compiler predate the
uniform seed-row interface.  This module exposes both through that interface,
without changing either underlying target or machine.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A fixed affine form table as a uniform one-row-per-transition-seed
source.  Empty tables are supported and therefore cover `halt`. -/
noncomputable def verifierTransitionAffineFormSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm) :
    VerifierTransitionSeedRowSource W where
  row seed := encodeUnaryFrame
    (affineUnaryTripleMap forms (transitionTailAffineSeed seed))
  family := verifierTransitionAffineFormDescriptorFamily W forms
  rows_eq _ := rfl
  computableInPolyTime :=
    verifierTransitionAffineFormDescriptorFamilyTotal_computableInPolyTime W
      forms

/-- The numeric descriptor of one fixed recursive branch as a uniform
one-row-per-transition-seed source. -/
noncomputable def verifierTransitionRecursiveBranchSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext W.machine.tm)
    (test : W.machine.tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt W.machine.tm.Γ
      W.machine.tm.Λ W.machine.tm.σ)
    (hsupport : ∀ k,
      stmtPushSet W.machine.tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet W.machine.tm k)
    (htrueBounds :
      (transitionStmtRecursivePlan W.machine.tm labelOffset
        (transitionStmtBranchTrueContext W.machine.tm context test) whenTrue
        (transitionStmtBranchTrueSupport W.machine.tm test whenTrue whenFalse
          hsupport)).UniformLinearRouteBounds W labelOffset)
    (hfalseBounds :
      (transitionStmtRecursivePlan W.machine.tm labelOffset
        (transitionStmtBranchFalseContext W.machine.tm context test whenTrue)
        whenFalse
        (transitionStmtBranchFalseSupport W.machine.tm test whenTrue whenFalse
          hsupport)).UniformLinearRouteBounds W labelOffset) :
    VerifierTransitionSeedRowSource W where
  row seed :=
    (transitionStmtRecursiveBranchMuxInvocationView W.machine.tm seed
      labelOffset context test whenTrue whenFalse hsupport).numericDescriptorRow
  family := verifierTransitionRecursiveBranchDescriptorFamily W labelOffset
    context test whenTrue whenFalse hsupport
  rows_eq input := by
    rw [verifierTransitionRecursiveBranchDescriptorFamily_rows]
    unfold verifierTransitionRecursiveBranchViews
    rw [List.map_map]
    apply List.map_congr_left
    intro seed hseed
    rfl
  computableInPolyTime :=
    verifierTransitionRecursiveBranchDescriptorFamily_computableInPolyTime W
      labelOffset context test whenTrue whenFalse hsupport htrueBounds
        hfalseBounds

end CLRS.Chapter34.Turing.CookLevin
