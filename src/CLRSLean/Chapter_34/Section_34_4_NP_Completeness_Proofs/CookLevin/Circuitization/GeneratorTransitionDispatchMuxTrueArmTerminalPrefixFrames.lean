import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmTerminalPrefixAffine

/-!
# Concrete raw-input source for terminal true-arm prefixes

The existing generic affine-map source evaluates the verifier-fixed terminal
prefix table over every runtime transition-row seed.  The resulting fixed TM2
emits exactly the halted, label, and state operands of all terminal true arms.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Raw-input unary values for every terminal true-arm prefix. -/
noncomputable def verifierTransitionDispatchTerminalPrefixValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionDispatchTerminalPrefixForms W.machine.tm) input

/-- Exact semantic contract of the generated terminal-prefix values. -/
theorem verifierTransitionDispatchTerminalPrefixValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTerminalPrefixValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchTerminalPrefixValues W.machine.tm)) := by
  unfold verifierTransitionDispatchTerminalPrefixValueFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily encodeUnaryFrame
  congr 1
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionDispatchTerminalPrefixForms_value W.machine.tm seed

/-- One fixed polynomial-time TM2 emits every terminal-prefix operand directly
from the raw verifier word. -/
noncomputable def
    verifierTransitionDispatchTerminalPrefixValueFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchTerminalPrefixValueFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionDispatchTerminalPrefixForms W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin
