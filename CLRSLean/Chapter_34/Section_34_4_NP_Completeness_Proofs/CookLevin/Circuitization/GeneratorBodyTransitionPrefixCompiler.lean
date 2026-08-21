import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowInputCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionCompleteInputCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.VerifierBodyController

/-!
# Concrete verifier-body input through the transition phase

The independently verified validity and transition input compilers are joined
on their common raw verifier word.  This closes the complete runtime operand
prefix consumed before the post-transition verifier tail.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact unary verifier-body operands through all local transitions. -/
def verifierBodyTransitionPrefixUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierValidityRowFamilyInputTarget W input ++
    verifierTransitionFamilyUnaryInputTarget W input

/-- The joined source is the literal prefix of the canonical body script. -/
theorem verifierBodyTransitionPrefixUnaryTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierBodyTransitionPrefixUnaryTarget W input =
      encodeAffineValidityRowFamilyInput
          (verifierValidityRowFramesByLength W input.length) ++
        encodeAffineTransitionFamilyUnary
          (verifierTransitionFamilyScripts W input) := by
  unfold verifierBodyTransitionPrefixUnaryTarget
  rw [verifierValidityRowFamilyInputTarget_eq_canonical]
  rfl

/-- A single fixed polynomial-time TM2 emits the validity-plus-transition
operand prefix directly from the raw verifier input. -/
noncomputable def
    verifierBodyTransitionPrefixUnaryTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierBodyTransitionPrefixUnaryTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact unaryFrameSameInputConcat_computableInPolyTime
    (verifierValidityRowFamilyInputTarget_computableInPolyTime W)
    (verifierTransitionFamilyUnaryInputTarget_computableInPolyTime W)

end CLRS.Chapter34.Turing.CookLevin
