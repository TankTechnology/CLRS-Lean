import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalStack

/-!
# Complete row normal form for terminal-ending statements

This module assembles the independently normalized status, state, and stack
components into one complete builder-free output row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- All fixed data needed to reconstruct a terminal statement output row. -/
structure TransitionStmtTerminalRowLayout (tm : _root_.Turing.FinTM2) where
  terminal : TransitionStmtTerminalLayout tm
  state : TransitionStmtStateLayout tm
  stackActions : List (TransitionStmtStackAction tm)

/-- Collect the three component normal forms. -/
noncomputable def transitionStmtTerminalRowLayout
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    Option (TransitionStmtTerminalRowLayout tm) :=
  match transitionStmtTerminalLayout tm q,
      transitionStmtTerminalStateLayout tm q,
      transitionStmtTerminalStackActions tm q hsupport with
  | some terminal, some state, some stackActions =>
      some { terminal, state, stackActions }
  | _, _, _ => none

private theorem
    transitionStmtTerminalStackActionsFrom_isSome_iff_terminal
    (tm : _root_.Turing.FinTM2)
    (gateOffset : TransitionAffineNat)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    ∀ hsupport : ∀ k,
        stmtPushSet tm q k ⊆ reachableAlphabet tm k,
      (transitionStmtTerminalStackActionsFrom tm gateOffset q
        hsupport).isSome ↔
        (transitionStmtTerminalLayout tm q).isSome := by
  induction q generalizing gateOffset with
  | halt =>
      intro hsupport
      simp [transitionStmtTerminalStackActionsFrom,
        transitionStmtTerminalLayout]
  | goto jump =>
      intro hsupport
      simp [transitionStmtTerminalStackActionsFrom,
        transitionStmtTerminalLayout]
  | load update continuation ih =>
      intro hsupport
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simpa [transitionStmtTerminalStackActionsFrom,
        transitionStmtTerminalLayout] using
        ih (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + stateCount tm))) hcontinuation
  | push k emit continuation ih =>
      intro hsupport
      have hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      simpa [transitionStmtTerminalStackActionsFrom,
        transitionStmtTerminalLayout] using
        ih (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + (reachableAlphabet tm k).card))) hcontinuation
  | peek k update continuation ih =>
      intro hsupport
      have hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simpa [transitionStmtTerminalStackActionsFrom,
        transitionStmtTerminalLayout] using
        ih (gateOffset.add (TransitionAffineNat.const
          (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
            stateCount tm))) hcontinuation
  | pop k update continuation ih =>
      intro hsupport
      have hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simpa [transitionStmtTerminalStackActionsFrom,
        transitionStmtTerminalLayout] using
        ih (gateOffset.add (TransitionAffineNat.const
          (1 + 2 * stateCount tm *
            ((reachableAlphabet tm k).card + 1) + stateCount tm)))
          hcontinuation
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport
      simp [transitionStmtTerminalStackActionsFrom,
        transitionStmtTerminalLayout]

/-- The stack-action extractor is defined on exactly the terminal-ending
statement spines. -/
theorem transitionStmtTerminalStackActions_isSome_iff_terminal
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (transitionStmtTerminalStackActions tm q hsupport).isSome ↔
      (transitionStmtTerminalLayout tm q).isSome := by
  exact transitionStmtTerminalStackActionsFrom_isSome_iff_terminal tm
    (TransitionAffineNat.const 0) q hsupport

/-- The complete terminal row normal form is available exactly when the
statement spine does not end in a branch. -/
theorem transitionStmtTerminalRowLayout_isSome_iff_terminal
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (transitionStmtTerminalRowLayout tm q hsupport).isSome ↔
      (transitionStmtTerminalLayout tm q).isSome := by
  cases hterminal : transitionStmtTerminalLayout tm q with
  | none => simp [transitionStmtTerminalRowLayout, hterminal]
  | some terminal =>
      have hterminalSome :
          (transitionStmtTerminalLayout tm q).isSome := by
        simp [hterminal]
      have hstateSome :=
        (transitionStmtTerminalStateLayout_isSome_iff_terminal tm q).2
          hterminalSome
      have hstackSome :=
        (transitionStmtTerminalStackActions_isSome_iff_terminal tm q
          hsupport).2 hterminalSome
      rcases Option.isSome_iff_exists.mp hstateSome with ⟨state, hstate⟩
      rcases Option.isSome_iff_exists.mp hstackSome with
        ⟨stackActions, hstack⟩
      simp [transitionStmtTerminalRowLayout, hterminal, hstate, hstack]

/-- Evaluate a complete terminal row normal form. -/
def TransitionStmtTerminalRowLayout.wires
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) : CfgWires tm height :=
  let stackCfg := transitionStmtStackActions_eval tm start height falseWire
    trueWire source layout.stackActions
  let withState := stackCfg.replaceState
    (layout.state.wires tm start height source)
  withState.replaceStatus
    (layout.terminal.terminal.haltedWire tm falseWire trueWire)
    (layout.terminal.terminal.labelWires tm falseWire trueWire
      (start + layout.terminal.offset.eval height))

/-- The recursive statement layout equals the assembled complete terminal
row normal form at every positive workspace height. -/
theorem transitionStmtOutputWires_terminal_row
    (tm : _root_.Turing.FinTM2) (height : Nat) (hheight : 0 < height)
    (falseWire trueWire start : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (layout : TransitionStmtTerminalRowLayout tm)
    (hlayout : transitionStmtTerminalRowLayout tm q hsupport = some layout) :
    transitionStmtOutputWires tm height falseWire trueWire start source q
        hsupport =
      layout.wires tm start height falseWire trueWire source := by
  unfold transitionStmtTerminalRowLayout at hlayout
  cases hterminal : transitionStmtTerminalLayout tm q with
  | none => simp [hterminal] at hlayout
  | some terminal =>
      cases hstate : transitionStmtTerminalStateLayout tm q with
      | none => simp [hterminal, hstate] at hlayout
      | some state =>
          cases hstack : transitionStmtTerminalStackActions tm q hsupport with
          | none => simp [hterminal, hstate, hstack] at hlayout
          | some stackActions =>
              simp [hterminal, hstate, hstack] at hlayout
              subst layout
              have hstatus := transitionStmtOutputWires_terminal_status tm
                height hheight falseWire trueWire start source q hsupport
                terminal hterminal
              have hstateWires := transitionStmtOutputWires_terminal_state tm
                height hheight falseWire trueWire start source q hsupport
                state hstate
              have hstackWires := transitionStmtOutputWires_terminal_stack tm
                height hheight falseWire trueWire start source q hsupport
                stackActions hstack
              funext slot
              rcases slot with (_ | label | stateSlot | ⟨k, coordinates⟩)
              · exact hstatus.1
              · exact congrFun hstatus.2 label
              · exact congrFun hstateWires stateSlot
              · rcases coordinates with heightSlot | cellSlot
                · exact congrArg (fun stack => stack.height heightSlot)
                    (hstackWires k)
                · exact congrArg
                    (fun stack => stack.cell cellSlot.1 cellSlot.2)
                    (hstackWires k)

end CLRS.Chapter34.Turing.CookLevin
