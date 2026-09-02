import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearPadding

/-!
# Terminal results of affine statement contexts

Branch arms need both their controller phases and their complete output rows.
This module normalizes every branch-free arm to the exact affine context at
its final `halt` or `goto`.  The result is independent of the runtime tableau
height and retains the state and stack effects accumulated by the arm.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A branch-free statement's final context and terminal instruction. -/
structure TransitionStmtLinearResult (tm : _root_.Turing.FinTM2) where
  context : TransitionStmtAffineContext tm
  terminal : TransitionStmtTerminal tm

/-- Execute the static context updates of a branch-free statement.  A branch
returns `none`; its two recursively compiled arms are handled by the branch
compiler. -/
noncomputable def transitionStmtLinearResult
    (tm : _root_.Turing.FinTM2) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      Option (TransitionStmtLinearResult tm)
  | context, halt, _ => some { context, terminal := .halt }
  | context, goto jump, _ => some { context, terminal := .goto jump }
  | context, load update continuation, hsupport =>
      let hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      transitionStmtLinearResult tm (context.afterLoad tm update)
        continuation hcontinuation
  | context, push k emit continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      transitionStmtLinearResult tm (context.afterPush tm k table)
        continuation hcontinuation
  | context, peek k update continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      transitionStmtLinearResult tm (context.afterPeek tm k update)
        continuation hcontinuation
  | context, pop k update continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      transitionStmtLinearResult tm (context.afterPop tm k update)
        continuation hcontinuation
  | _, branch _ _ _, _ => none

/-- The result normalizer is defined on exactly the branch-free terminal
spines recognized by the established terminal layout. -/
theorem transitionStmtLinearResult_isSome_iff_terminal
    (tm : _root_.Turing.FinTM2)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (transitionStmtLinearResult tm context q hsupport).isSome ↔
      (transitionStmtTerminalLayout tm q).isSome := by
  induction q generalizing context with
  | halt => simp [transitionStmtLinearResult, transitionStmtTerminalLayout]
  | goto jump =>
      simp [transitionStmtLinearResult, transitionStmtTerminalLayout]
  | load update continuation ih =>
      simp [transitionStmtLinearResult, transitionStmtTerminalLayout, ih]
  | push k emit continuation ih =>
      simp [transitionStmtLinearResult, transitionStmtTerminalLayout, ih]
  | peek k update continuation ih =>
      simp [transitionStmtLinearResult, transitionStmtTerminalLayout, ih]
  | pop k update continuation ih =>
      simp [transitionStmtLinearResult, transitionStmtTerminalLayout, ih]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtLinearResult, transitionStmtTerminalLayout]

/-- Interpret the normalized terminal on the row denoted by its final
context. -/
def TransitionStmtLinearResult.outputWires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (result : TransitionStmtLinearResult tm) : CfgWires tm height :=
  let current := result.context.wires tm originStart height falseWire trueWire
    source
  current.replaceStatus
    (result.terminal.haltedWire tm falseWire trueWire)
    (result.terminal.labelWires tm falseWire trueWire
      (originStart + result.context.gateOffset.eval height))

/-- Static context normalization computes the literal semantic output of
every branch-free statement at positive workspace height. -/
theorem transitionStmtLinearResult_outputWires
    (tm : _root_.Turing.FinTM2) (height : Nat) (hheight : 0 < height)
    (originStart falseWire trueWire : Nat) (source : CfgWires tm height)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (result : TransitionStmtLinearResult tm)
    (hresult : transitionStmtLinearResult tm context q hsupport =
      some result) :
    transitionStmtOutputWires tm height falseWire trueWire
        (originStart + context.gateOffset.eval height)
        (context.wires tm originStart height falseWire trueWire source)
        q hsupport =
      result.outputWires tm originStart height falseWire trueWire source := by
  induction q generalizing context result with
  | halt =>
      simp [transitionStmtLinearResult] at hresult
      subst result
      rfl
  | goto jump =>
      simp [transitionStmtLinearResult] at hresult
      subst result
      simp only [transitionStmtOutputWires,
        TransitionStmtLinearResult.outputWires]
      rw [oneHotMapGateTrace_wires_eq_offset]
      rfl
  | load update continuation ih =>
      let hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearResult] at hresult
      have htail := ih (context.afterLoad tm update) hcontinuation result hresult
      rw [context.afterLoad_gateOffset_eval] at htail
      rw [context.afterLoad_wires tm originStart height falseWire trueWire
        source update] at htail
      simpa [transitionStmtOutputWires, Nat.add_assoc] using htail
  | push k emit continuation ih =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      simp only [transitionStmtLinearResult] at hresult
      change transitionStmtLinearResult tm (context.afterPush tm k table)
          continuation hcontinuation = some result at hresult
      have htail := ih (context.afterPush tm k table) hcontinuation result
        hresult
      rw [context.afterPush_gateOffset_eval] at htail
      rw [context.afterPush_wires tm originStart height falseWire trueWire
        source k table] at htail
      simpa [transitionStmtOutputWires, symbolAt, table, Nat.add_assoc] using
        htail
  | peek k update continuation ih =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearResult] at hresult
      have htail := ih (context.afterPeek tm k update) hcontinuation result
        hresult
      rw [context.afterPeek_gateOffset_eval] at htail
      rw [context.afterPeek_wires tm originStart height falseWire trueWire
        source k update] at htail
      simpa [transitionStmtOutputWires, Nat.add_assoc] using htail
  | pop k update continuation ih =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearResult] at hresult
      have htail := ih (context.afterPop tm k update) hcontinuation result
        hresult
      rw [context.afterPop_gateOffset_eval] at htail
      rw [context.afterPop_wires tm originStart height falseWire trueWire
        source k update] at htail
      have hpopCost : popStackWireGateCost height = 1 := by
        cases height with
        | zero => omega
        | succ height => rfl
      simpa [transitionStmtOutputWires, hpopCost, Nat.add_assoc] using htail
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtLinearResult] at hresult

end CLRS.Chapter34.Turing.CookLevin
