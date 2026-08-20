import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteTerminal

/-!
# Exact frame target for terminal true-arm stack suffixes

Terminal statement rows consist of an already concrete affine prefix followed
by the stack blocks.  This module isolates precisely that remaining suffix in
the fixed normalized label order and proves its descriptor route equal to the
established semantic stack route.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Stack suffix selected by one normalized true-arm entry.  Branch entries
contribute no terminal stack bytes. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.terminalStackDescriptorRoute
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | .branch _ _ _ _ => []
  | .terminal labelOffset _ rowLayout _ =>
      (rowLayout.stackDescriptorRouteValues tm
        (seed.start + labelOffset.eval seed.height) seed).flatten

/-- Semantic stack suffix selected by the same normalized entry. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.terminalStackValueRoute
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | .branch _ _ _ _ => []
  | .terminal labelOffset _ rowLayout _ =>
      (rowLayout.stackValueRouteValues tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase)).flatten

/-- Descriptor routing and the prior semantic stack routing agree for each
label entry. -/
theorem
    TransitionDispatchTrueArmNormalizedLayout.terminalStackDescriptorRoute_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    layout.terminalStackDescriptorRoute tm seed =
      layout.terminalStackValueRoute tm seed := by
  cases layout with
  | branch labelOffset label branchOffset hbranch => rfl
  | terminal labelOffset label rowLayout hlayout =>
      simp only [
        TransitionDispatchTrueArmNormalizedLayout.terminalStackDescriptorRoute,
        TransitionDispatchTrueArmNormalizedLayout.terminalStackValueRoute]
      exact congrArg List.flatten
        (rowLayout.stackDescriptorRouteValues_eq tm
          (seed.start + labelOffset.eval seed.height) seed)

/-- Frozen unary-frame target containing exactly the terminal stack suffixes
of all transition rows. -/
noncomputable def verifierTransitionDispatchTerminalStackRouteValueFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    ((verifierTransitionRowSeeds W input).flatMap fun seed =>
      (transitionDispatchTrueArmNormalizedLayouts W.machine.tm).flatMap
        (TransitionDispatchTrueArmNormalizedLayout.terminalStackDescriptorRoute
          W.machine.tm seed))

/-- The frozen target is byte-for-byte the semantic terminal stack suffix
stream, in row-major and then program-label order. -/
theorem verifierTransitionDispatchTerminalStackRouteValueFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchTerminalStackRouteValueFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionDispatchTrueArmNormalizedLayouts W.machine.tm).flatMap
            (TransitionDispatchTrueArmNormalizedLayout.terminalStackValueRoute
              W.machine.tm seed)) := by
  unfold verifierTransitionDispatchTerminalStackRouteValueFrames
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  apply List.flatMap_congr
  intro layout hlayout
  exact layout.terminalStackDescriptorRoute_eq W.machine.tm seed

end CLRS.Chapter34.Turing.CookLevin
