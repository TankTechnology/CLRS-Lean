import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearPadding

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

example {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ)
    (hterminal :
      (transitionStmtTerminalLayout W.machine.tm
        (W.machine.tm.m label)).isSome)
    (forms : List TransitionAffineStmtPhaseForm)
    (hforms : transitionStmtLinearContextPhaseForms W.machine.tm labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label) =
        some forms) :
    forms.map (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionStmtScript W.machine.tm
        (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
        (seed.start + labelOffset.eval seed.height)
        (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
          seed.rowBase)
        (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label) := by
  exact transitionStmtLinearInitialPhaseForms_eval W input seed hseed
    labelOffset label hterminal forms hforms

end CLRS.Chapter34.Turing.CookLevin
