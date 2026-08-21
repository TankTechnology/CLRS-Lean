import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveLabels

/-!
# Recursive statement streams for every transition row

The canonical transition-row seed family supplies one dispatch start and one
public row base for each adjacent tableau pair.  Flattening the recursive
all-label statement stream over those seeds therefore covers every statement
subscript in the complete transition family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- All generated recursive statement-controller frames, in row-major order. -/
def verifierTransitionRecursiveStatementControllerTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchRecursiveStatementControllerFrames W.machine.tm)

/-- All corresponding semantic statement-script frames, in row-major order. -/
def verifierTransitionRecursiveStatementSemanticTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap
    (transitionDispatchRecursiveStatementSemanticFrames W.machine.tm)

/-- The unrestricted recursive generator covers every label of every local
transition row. -/
theorem verifierTransitionRecursiveStatementControllerTarget_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRecursiveStatementControllerTarget W input =
      verifierTransitionRecursiveStatementSemanticTarget W input := by
  unfold verifierTransitionRecursiveStatementControllerTarget
    verifierTransitionRecursiveStatementSemanticTarget
  apply List.flatMap_congr
  intro seed hseed
  apply verifierTransitionDispatchRecursiveStatementControllerFrames_eq
    W input seed
  exact verifierTransitionRowSeeds_height_eq W input seed hseed

end CLRS.Chapter34.Turing.CookLevin
