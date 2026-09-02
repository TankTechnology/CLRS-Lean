import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalRoute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementFinalBranch

/-!
# Canonical routed outputs of branch-ending statements

The output of any statement whose linear spine ends in `branch` is the final
whole-row mux.  This file packages that row as a canonical list of wire
coordinates relative to an arbitrary affine statement context.  Unlike the
earlier label-family progression, this interface is compositional: a nested
branch can use it directly as one arm of its parent mux.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Canonical coordinate-order output row of a branch mux at `offset` from the
current statement context. -/
def transitionStmtBranchRouteValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (offset : TransitionAffineNat) : List Nat :=
  List.ofFn fun coordinate :
      Fin (cfgBitCount tm (workHeight tm seed.height)) =>
    ((seed.start + labelOffset.eval seed.height) +
        context.gateOffset.eval (workHeight tm seed.height)) +
      offset.eval (workHeight tm seed.height) + 3 + 3 * coordinate.val

@[simp] theorem transitionStmtBranchRouteValues_length
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (offset : TransitionAffineNat) :
    (transitionStmtBranchRouteValues tm seed labelOffset context offset).length =
      cfgBitCount tm (workHeight tm seed.height) := by
  simp [transitionStmtBranchRouteValues]

/-- The canonical branch route is exactly the semantic output row of the
original statement, even when either branch arm contains further branches. -/
theorem transitionStmtBranchRouteValues_eq_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (offset : TransitionAffineNat)
    (hoffset : transitionStmtFinalBranchMuxOffsetAffine tm q = some offset) :
    transitionStmtBranchRouteValues tm seed labelOffset context offset =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (transitionStmtOutputWires tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          ((seed.start + labelOffset.eval seed.height) +
            context.gateOffset.eval (workHeight tm seed.height))
          (context.rowWires tm seed labelOffset) q hsupport) := by
  unfold transitionStmtBranchRouteValues transitionCfgWireValues
  rw [transitionStmtOutputWires_eq_finalBranchMux tm
    (workHeight tm seed.height) hwork seed.start (seed.start + 1)
    ((seed.start + labelOffset.eval seed.height) +
      context.gateOffset.eval (workHeight tm seed.height))
    (context.rowWires tm seed labelOffset) q hsupport offset hoffset]
  apply List.ofFn_inj.mpr
  funext coordinate
  unfold arithmeticMuxCfgWires
  simp only [Equiv.apply_symm_apply]

end CLRS.Chapter34.Turing.CookLevin
