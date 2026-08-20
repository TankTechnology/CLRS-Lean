import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalState

/-!
# Stack actions of terminal-ending transition statements

The stack effect of a fixed linear statement spine is a fixed action table.
Each push stores the affine coordinates of its freshly mapped symbol, and
each pop stores the affine coordinate of its fresh height wire.  This removes
all runtime state-wire dependence from the final stack layout.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- One fixed action on a selected verifier stack. -/
inductive TransitionStmtStackActionKind
    (tm : _root_.Turing.FinTM2) (k : tm.K)
  | push (symbolOffsets :
      Fin (reachableAlphabet tm k).card → TransitionAffineNat)
  | pop (heightWireOffset : TransitionAffineNat)

/-- Dependently packaged stack action. -/
structure TransitionStmtStackAction (tm : _root_.Turing.FinTM2) where
  k : tm.K
  kind : TransitionStmtStackActionKind tm k

/-- Evaluate one static stack action at a runtime statement start and height. -/
def TransitionStmtStackAction.eval (tm : _root_.Turing.FinTM2)
    (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) :
    TransitionStmtStackAction tm → CfgWires tm height
  | ⟨k, .push symbolOffsets⟩ =>
      arithmeticPushCfgWires tm height k falseWire
        (fun target => originStart + (symbolOffsets target).eval height) source
  | ⟨k, .pop heightWireOffset⟩ =>
      arithmeticPopCfgWires tm height k falseWire trueWire
        (originStart + heightWireOffset.eval height) source

/-- Sequential evaluation of a fixed stack-action table. -/
def transitionStmtStackActions_eval (tm : _root_.Turing.FinTM2)
    (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (actions : List (TransitionStmtStackAction tm)) : CfgWires tm height :=
  actions.foldl
    (fun current action =>
      action.eval tm originStart height falseWire trueWire current)
    source

/-- Extract the fixed stack-action table, with every action coordinate
relative to the enclosing statement start. -/
noncomputable def transitionStmtTerminalStackActionsFrom
    (tm : _root_.Turing.FinTM2) :
    (gateOffset : TransitionAffineNat) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      Option (List (TransitionStmtStackAction tm))
  | _, halt, _ => some []
  | _, goto _, _ => some []
  | gateOffset, load _ continuation, hsupport =>
      let hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + stateCount tm)))
        continuation hcontinuation
  | gateOffset, push k emit continuation, hsupport =>
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
      let action : TransitionStmtStackAction tm :=
        { k := k
          kind := .push fun target =>
            gateOffset.add (TransitionAffineNat.const
              (oneHotMapWireOffset
                (fun code => encodeSupportedSymbol (symbolAt code)) target)) }
      (transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + (reachableAlphabet tm k).card)))
        continuation hcontinuation).map (action :: ·)
  | gateOffset, peek k _ continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
            stateCount tm)))
        continuation hcontinuation
  | gateOffset, pop k _ continuation, hsupport =>
      let hcontinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let action : TransitionStmtStackAction tm :=
        { k := k
          kind := .pop gateOffset }
      (transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (1 + 2 * stateCount tm *
            ((reachableAlphabet tm k).card + 1) + stateCount tm)))
        continuation hcontinuation).map (action :: ·)
  | _, branch _ _ _, _ => none

/-- Public stack-action table from the statement's initial gate start. -/
noncomputable def transitionStmtTerminalStackActions
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    Option (List (TransitionStmtStackAction tm)) :=
  transitionStmtTerminalStackActionsFrom tm
    (TransitionAffineNat.const 0) q hsupport

private theorem TransitionStmtStackAction.eval_stack_eq_of_stack_eq
    (tm : _root_.Turing.FinTM2)
    (originStart height falseWire trueWire : Nat)
    (left right : CfgWires tm height)
    (hstack : ∀ k, left.stack k = right.stack k)
    (action : TransitionStmtStackAction tm) :
    ∀ k,
      (action.eval tm originStart height falseWire trueWire left).stack k =
        (action.eval tm originStart height falseWire trueWire right).stack k := by
  rcases action with ⟨selected, kind⟩
  cases kind with
  | push symbolOffsets =>
      intro k
      by_cases hselected : k = selected
      · subst k
        simp [TransitionStmtStackAction.eval, arithmeticPushCfgWires,
          hstack selected]
      · rw [show (TransitionStmtStackAction.eval tm originStart height
            falseWire trueWire left ⟨selected, .push symbolOffsets⟩).stack k =
            left.stack k by
          apply CfgBundle.replaceStack_stack_other
          exact hselected]
        rw [show (TransitionStmtStackAction.eval tm originStart height
            falseWire trueWire right ⟨selected, .push symbolOffsets⟩).stack k =
            right.stack k by
          apply CfgBundle.replaceStack_stack_other
          exact hselected]
        exact hstack k
  | pop heightWireOffset =>
      intro k
      by_cases hselected : k = selected
      · subst k
        simp [TransitionStmtStackAction.eval, arithmeticPopCfgWires,
          hstack selected]
      · rw [show (TransitionStmtStackAction.eval tm originStart height
            falseWire trueWire left ⟨selected, .pop heightWireOffset⟩).stack k =
            left.stack k by
          apply CfgBundle.replaceStack_stack_other
          exact hselected]
        rw [show (TransitionStmtStackAction.eval tm originStart height
            falseWire trueWire right ⟨selected, .pop heightWireOffset⟩).stack k =
            right.stack k by
          apply CfgBundle.replaceStack_stack_other
          exact hselected]
        exact hstack k

private theorem transitionStmtStackActions_eval_stack_eq_of_stack_eq
    (tm : _root_.Turing.FinTM2)
    (originStart height falseWire trueWire : Nat)
    (left right : CfgWires tm height)
    (hstack : ∀ k, left.stack k = right.stack k) :
    ∀ actions : List (TransitionStmtStackAction tm), ∀ k,
      (transitionStmtStackActions_eval tm originStart height falseWire trueWire
        left actions).stack k =
      (transitionStmtStackActions_eval tm originStart height falseWire trueWire
        right actions).stack k := by
  intro actions
  induction actions generalizing left right with
  | nil => exact hstack
  | cons action rest ih =>
      apply ih
      exact action.eval_stack_eq_of_stack_eq tm originStart height
        falseWire trueWire left right hstack

private theorem transitionStmtOutputWires_terminal_stack_from
    (tm : _root_.Turing.FinTM2) (height : Nat) (hheight : 0 < height)
    (falseWire trueWire originStart currentStart : Nat)
    (gateOffset : TransitionAffineNat)
    (hstart : currentStart = originStart + gateOffset.eval height)
    (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (actions : List (TransitionStmtStackAction tm))
    (hactions : transitionStmtTerminalStackActionsFrom tm gateOffset q
      hsupport = some actions) :
    ∀ k,
      (transitionStmtOutputWires tm height falseWire trueWire currentStart
        source q hsupport).stack k =
      (transitionStmtStackActions_eval tm originStart height falseWire trueWire
        source actions).stack k := by
  induction q generalizing currentStart gateOffset source actions with
  | halt =>
      simp [transitionStmtTerminalStackActionsFrom] at hactions
      subst actions
      intro k
      rfl
  | goto jump =>
      simp [transitionStmtTerminalStackActionsFrom] at hactions
      subst actions
      intro k
      rfl
  | load update continuation ih =>
      have hsupportContinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtTerminalStackActionsFrom] at hactions
      have hnextStart :
          currentStart + stateCount tm + stateCount tm =
            originStart +
              (gateOffset.add (TransitionAffineNat.const
                (stateCount tm + stateCount tm))).eval height := by
        simp [TransitionAffineNat.eval_add, hstart, Nat.add_assoc]
      intro k
      calc
        (transitionStmtOutputWires tm height falseWire trueWire currentStart
            source (load update continuation) hsupport).stack k =
          (transitionStmtStackActions_eval tm originStart height falseWire
            trueWire
            (source.replaceState
              (oneHotMapGateTrace currentStart source.state
                (stmtStateTable tm update)).wires)
            actions).stack k := by
              simp only [transitionStmtOutputWires]
              exact ih
                (currentStart := currentStart + stateCount tm + stateCount tm)
                (gateOffset := gateOffset.add (TransitionAffineNat.const
                  (stateCount tm + stateCount tm)))
                hnextStart
                (source := source.replaceState
                  (oneHotMapGateTrace currentStart source.state
                    (stmtStateTable tm update)).wires)
                (hsupport := hsupportContinuation)
                (actions := actions) hactions k
        _ = (transitionStmtStackActions_eval tm originStart height falseWire
            trueWire source actions).stack k :=
          transitionStmtStackActions_eval_stack_eq_of_stack_eq tm originStart
            height falseWire trueWire _ _
            (fun j => CfgBundle.replaceState_stack source _ j) actions k
  | push selected emit continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm selected :=
        fun code =>
          ⟨emit ((stateEquivFin tm).symm code), by
            apply hsupport selected
            simp [stmtPushSet]⟩
      let action : TransitionStmtStackAction tm :=
        { k := selected
          kind := .push fun target =>
            gateOffset.add (TransitionAffineNat.const
              (oneHotMapWireOffset
                (fun code => encodeSupportedSymbol (symbolAt code)) target)) }
      change (transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + (reachableAlphabet tm selected).card)))
        continuation hsupportContinuation).map (action :: ·) =
          some actions at hactions
      cases hrest : transitionStmtTerminalStackActionsFrom tm
          (gateOffset.add (TransitionAffineNat.const
            (stateCount tm + (reachableAlphabet tm selected).card)))
          continuation hsupportContinuation with
      | none => simp [hrest] at hactions
      | some rest =>
          rw [hrest] at hactions
          simp only [Option.map_some, Option.some.injEq] at hactions
          subst actions
          have hnextStart :
              currentStart + stateCount tm +
                  (reachableAlphabet tm selected).card =
                originStart +
                  (gateOffset.add (TransitionAffineNat.const
                    (stateCount tm +
                      (reachableAlphabet tm selected).card))).eval height := by
            simp [TransitionAffineNat.eval_add, hstart, Nat.add_assoc]
          have hsymbol :
              (oneHotMapGateTrace currentStart source.state
                (fun code => encodeSupportedSymbol (symbolAt code))).wires =
              fun target => originStart +
                ((gateOffset.add (TransitionAffineNat.const
                  (oneHotMapWireOffset
                    (fun code => encodeSupportedSymbol (symbolAt code))
                    target))).eval height) := by
            funext target
            rw [oneHotMapGateTrace_wire_eq_start_add_offset]
            simp [TransitionAffineNat.eval_add, hstart, Nat.add_assoc]
          have haction :
              action.eval tm originStart height falseWire trueWire source =
                arithmeticPushCfgWires tm height selected falseWire
                  (oneHotMapGateTrace currentStart source.state
                    (fun code =>
                      encodeSupportedSymbol (symbolAt code))).wires source := by
            simp [action, TransitionStmtStackAction.eval, hsymbol]
          intro k
          simp only [transitionStmtOutputWires]
          rw [ih (currentStart := currentStart + stateCount tm +
                (reachableAlphabet tm selected).card)
              (gateOffset := gateOffset.add (TransitionAffineNat.const
                (stateCount tm + (reachableAlphabet tm selected).card)))
              hnextStart
              (source := arithmeticPushCfgWires tm height selected falseWire
                (oneHotMapGateTrace currentStart source.state
                  (fun code =>
                    encodeSupportedSymbol (symbolAt code))).wires source)
              (hsupport := hsupportContinuation)
              (actions := rest) hrest k]
          simp [transitionStmtStackActions_eval, action, haction]
  | peek selected update continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtTerminalStackActionsFrom] at hactions
      have hnextStart :
          currentStart +
              2 * stateCount tm *
                ((reachableAlphabet tm selected).card + 1) + stateCount tm =
            originStart +
              (gateOffset.add (TransitionAffineNat.const
                (2 * stateCount tm *
                  ((reachableAlphabet tm selected).card + 1) +
                    stateCount tm))).eval height := by
        simp [TransitionAffineNat.eval_add, hstart, Nat.add_assoc]
      intro k
      calc
        (transitionStmtOutputWires tm height falseWire trueWire currentStart
            source (peek selected update continuation) hsupport).stack k =
          (transitionStmtStackActions_eval tm originStart height falseWire
            trueWire
            (source.replaceState
              (oneHotPairMapGateTrace currentStart source.state
                (arithmeticPeekCfgWires tm height falseWire trueWire source
                  selected)
                (stmtHeadStateTable tm selected update)).wires)
            actions).stack k := by
              simp only [transitionStmtOutputWires]
              exact ih
                (currentStart := currentStart +
                  2 * stateCount tm *
                    ((reachableAlphabet tm selected).card + 1) +
                      stateCount tm)
                (gateOffset := gateOffset.add (TransitionAffineNat.const
                  (2 * stateCount tm *
                    ((reachableAlphabet tm selected).card + 1) +
                      stateCount tm)))
                hnextStart
                (source := source.replaceState
                  (oneHotPairMapGateTrace currentStart source.state
                    (arithmeticPeekCfgWires tm height falseWire trueWire source
                      selected)
                    (stmtHeadStateTable tm selected update)).wires)
                (hsupport := hsupportContinuation)
                (actions := actions) hactions k
        _ = (transitionStmtStackActions_eval tm originStart height falseWire
            trueWire source actions).stack k :=
          transitionStmtStackActions_eval_stack_eq_of_stack_eq tm originStart
            height falseWire trueWire _ _
            (fun j => CfgBundle.replaceState_stack source _ j) actions k
  | pop selected update continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      let action : TransitionStmtStackAction tm :=
        { k := selected
          kind := .pop gateOffset }
      simp only [transitionStmtTerminalStackActionsFrom] at hactions
      cases hrest : transitionStmtTerminalStackActionsFrom tm
          (gateOffset.add (TransitionAffineNat.const
            (1 + 2 * stateCount tm *
              ((reachableAlphabet tm selected).card + 1) + stateCount tm)))
          continuation hsupportContinuation with
      | none => simp [hrest] at hactions
      | some rest =>
          rw [hrest] at hactions
          simp only [Option.map_some, Option.some.injEq] at hactions
          subst actions
          cases height with
          | zero => omega
          | succ height =>
              have hpopStart : originStart + gateOffset.eval (height + 1) =
                  currentStart := hstart.symm
              have hnextStart :
                  currentStart + popStackWireGateCost (height + 1) +
                      (2 * stateCount tm *
                        ((reachableAlphabet tm selected).card + 1) +
                          stateCount tm) =
                    originStart +
                      (gateOffset.add (TransitionAffineNat.const
                        (1 + 2 * stateCount tm *
                          ((reachableAlphabet tm selected).card + 1) +
                            stateCount tm))).eval (height + 1) := by
                simp [TransitionAffineNat.eval_add, hstart,
                  popStackWireGateCost, Nat.add_assoc]
              let popped := arithmeticPopCfgWires tm (height + 1) selected
                falseWire trueWire currentStart source
              let mapped := (oneHotPairMapGateTrace (currentStart + 1)
                popped.state
                (arithmeticPopHeadWires tm selected falseWire trueWire
                  (height + 1) (source.stack selected))
                (stmtHeadStateTable tm selected update)).wires
              have haction :
                  action.eval tm originStart (height + 1) falseWire trueWire
                      source = popped := by
                simp [action, TransitionStmtStackAction.eval, popped, hpopStart]
              intro k
              calc
                (transitionStmtOutputWires tm (height + 1) falseWire trueWire
                    currentStart source (pop selected update continuation)
                    hsupport).stack k =
                  (transitionStmtStackActions_eval tm originStart (height + 1)
                    falseWire trueWire (popped.replaceState mapped) rest).stack k := by
                      simp only [transitionStmtOutputWires,
                        popStackWireGateCost, popped, mapped]
                      exact ih
                        (currentStart := currentStart + 1 +
                          (2 * stateCount tm *
                            ((reachableAlphabet tm selected).card + 1) +
                              stateCount tm))
                        (gateOffset := gateOffset.add
                          (TransitionAffineNat.const
                            (1 + 2 * stateCount tm *
                              ((reachableAlphabet tm selected).card + 1) +
                                stateCount tm)))
                        hnextStart
                        (source := popped.replaceState mapped)
                        (hsupport := hsupportContinuation)
                        (actions := rest) hrest k
                _ = (transitionStmtStackActions_eval tm originStart
                    (height + 1) falseWire trueWire popped rest).stack k :=
                  transitionStmtStackActions_eval_stack_eq_of_stack_eq tm
                    originStart (height + 1) falseWire trueWire _ _
                    (fun j => CfgBundle.replaceState_stack popped mapped j)
                    rest k
                _ = (transitionStmtStackActions_eval tm originStart
                    (height + 1) falseWire trueWire source
                    (action :: rest)).stack k := by
                  simp [transitionStmtStackActions_eval, haction]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtTerminalStackActionsFrom] at hactions

/-- Exact stack-family equation for the public action table. -/
theorem transitionStmtOutputWires_terminal_stack
    (tm : _root_.Turing.FinTM2) (height : Nat) (hheight : 0 < height)
    (falseWire trueWire start : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (actions : List (TransitionStmtStackAction tm))
    (hactions : transitionStmtTerminalStackActions tm q hsupport =
      some actions) :
    ∀ k,
      (transitionStmtOutputWires tm height falseWire trueWire start source q
        hsupport).stack k =
      (transitionStmtStackActions_eval tm start height falseWire trueWire
        source actions).stack k := by
  apply transitionStmtOutputWires_terminal_stack_from tm height hheight
    falseWire trueWire start start (TransitionAffineNat.const 0)
  · simp [TransitionAffineNat.eval, TransitionAffineNat.const]
  · exact hactions

end CLRS.Chapter34.Turing.CookLevin
