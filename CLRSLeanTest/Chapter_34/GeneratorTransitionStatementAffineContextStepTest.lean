import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextStep

namespace CLRS.Chapter34.Turing.CookLevin

example (tm : _root_.Turing.FinTM2)
    (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (update : tm.σ → tm.σ) :
    (context.afterLoad tm update).wires tm originStart height falseWire
        trueWire source =
      CfgBundle.replaceState
        (context.wires tm originStart height falseWire trueWire source)
        (oneHotMapGateTrace
          (originStart + context.gateOffset.eval height)
          (context.wires tm originStart height falseWire trueWire source).state
          (stmtStateTable tm update)).wires := by
  exact context.afterLoad_wires tm originStart height falseWire trueWire source
    update

example (tm : _root_.Turing.FinTM2)
    (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (k : tm.K) (update : tm.σ → Option (tm.Γ k) → tm.σ) :
    (context.afterPop tm k update).wires tm originStart height falseWire
        trueWire source =
      let current :=
        context.wires tm originStart height falseWire trueWire source
      let popped := arithmeticPopCfgWires tm height k falseWire trueWire
        (originStart + context.gateOffset.eval height) current
      popped.replaceState
        (oneHotPairMapGateTrace
          (originStart + context.gateOffset.eval height + 1)
          popped.state
          (arithmeticPopHeadWires tm k falseWire trueWire height
            (current.stack k))
          (stmtHeadStateTable tm k update)).wires := by
  exact context.afterPop_wires tm originStart height falseWire trueWire source k
    update

end CLRS.Chapter34.Turing.CookLevin
