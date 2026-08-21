import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextFrontSemantics

/-!
# Primitive evolution of affine statement contexts

This file records the exact context obtained after each non-branching
statement primitive.  Keeping these updates separate from the recursive
compiler makes the later induction small: the context remembers the fresh
state coordinates, the accumulated stack action, and the next gate offset.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact cost of a unary state lookup. -/
def transitionStmtLoadCost (tm : _root_.Turing.FinTM2) : TransitionAffineNat :=
  TransitionAffineNat.const (stateCount tm + stateCount tm)

/-- Exact cost of the symbol lookup preceding a push. -/
def transitionStmtPushCost (tm : _root_.Turing.FinTM2) (k : tm.K) :
    TransitionAffineNat :=
  TransitionAffineNat.const
    (stateCount tm + (reachableAlphabet tm k).card)

/-- Exact cost of a state/head pair lookup. -/
def transitionStmtPeekCost (tm : _root_.Turing.FinTM2) (k : tm.K) :
    TransitionAffineNat :=
  TransitionAffineNat.const
    (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) + stateCount tm)

/-- At positive workspace height a pop contributes one gate before the pair
lookup. -/
def transitionStmtPopCost (tm : _root_.Turing.FinTM2) (k : tm.K) :
    TransitionAffineNat :=
  TransitionAffineNat.const
    (1 + 2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
      stateCount tm)

/-- Context after a `load` primitive. -/
def TransitionStmtAffineContext.afterLoad
    (tm : _root_.Turing.FinTM2) (context : TransitionStmtAffineContext tm)
    (update : tm.σ → tm.σ) : TransitionStmtAffineContext tm :=
  (context.replaceStateByMap tm (stmtStateTable tm update)).advance
    (transitionStmtLoadCost tm)

/-- Context after the symbol lookup and zero-gate stack push. -/
def TransitionStmtAffineContext.afterPush
    (tm : _root_.Turing.FinTM2) (context : TransitionStmtAffineContext tm)
    (k : tm.K)
    (table : Fin (stateCount tm) → Fin (reachableAlphabet tm k).card) :
    TransitionStmtAffineContext tm :=
  (context.recordPush tm k table).advance (transitionStmtPushCost tm k)

/-- Context after a `peek` pair lookup. -/
def TransitionStmtAffineContext.afterPeek
    (tm : _root_.Turing.FinTM2) (context : TransitionStmtAffineContext tm)
    (k : tm.K) (update : tm.σ → Option (tm.Γ k) → tm.σ) :
    TransitionStmtAffineContext tm :=
  (context.replaceStateByPairMap tm 0
    (stmtHeadStateTable tm k update)).advance (transitionStmtPeekCost tm k)

/-- Context after the one-gate positive-height pop and its pair lookup. -/
def TransitionStmtAffineContext.afterPop
    (tm : _root_.Turing.FinTM2) (context : TransitionStmtAffineContext tm)
    (k : tm.K) (update : tm.σ → Option (tm.Γ k) → tm.σ) :
    TransitionStmtAffineContext tm :=
  ((context.recordPop tm k).replaceStateByPairMap tm 1
    (stmtHeadStateTable tm k update)).advance (transitionStmtPopCost tm k)

@[simp] theorem TransitionStmtAffineContext.advance_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (cost : TransitionAffineNat) :
    (context.advance cost).wires tm originStart height falseWire trueWire
        source =
      context.wires tm originStart height falseWire trueWire source := by
  rfl

/-- Recording a unary lookup result has exactly the ordinary pure-trace state
semantics at the current context start. -/
theorem TransitionStmtAffineContext.replaceStateByMap_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (table : Fin (stateCount tm) → Fin (stateCount tm)) :
    (context.replaceStateByMap tm table).wires tm originStart height
        falseWire trueWire source =
      CfgBundle.replaceState
        (context.wires tm originStart height falseWire trueWire source)
          (oneHotMapGateTrace
            (originStart + context.gateOffset.eval height)
            (context.wires tm originStart height falseWire trueWire source).state
            table).wires := by
  rw [oneHotMapGateTrace_wires_eq_offset]
  funext slot
  rcases slot with (_ | label | state | ⟨k, coordinate⟩)
  · rfl
  · rfl
  · simp only [TransitionStmtAffineContext.wires,
      CfgBundle.replaceState, TransitionStmtStateLayout.wires,
      TransitionStmtAffineContext.replaceStateByMap,
      TransitionAffineNat.eval_add, TransitionAffineNat.eval_const]
    simp [Nat.add_assoc]
  · rfl

/-- Pair lookups have the analogous context-state semantics, including the
one-gate prefix used by `pop`. -/
theorem TransitionStmtAffineContext.replaceStateByPairMap_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (pairPrefix : Nat) {p : Nat}
    (table : Fin (stateCount tm) → Fin p → Fin (stateCount tm))
    (right : Fin p → CircuitBuilder.Wire) :
    (context.replaceStateByPairMap tm pairPrefix table).wires tm originStart
        height falseWire trueWire source =
      CfgBundle.replaceState
        (context.wires tm originStart height falseWire trueWire source)
          (oneHotPairMapGateTrace
            (originStart + context.gateOffset.eval height + pairPrefix)
            (context.wires tm originStart height falseWire trueWire source).state
            right table).wires := by
  rw [oneHotPairMapGateTrace_wires_eq_offset]
  funext slot
  rcases slot with (_ | label | state | ⟨k, coordinate⟩)
  · rfl
  · rfl
  · simp only [TransitionStmtAffineContext.wires,
      CfgBundle.replaceState, TransitionStmtStateLayout.wires,
      TransitionStmtAffineContext.replaceStateByPairMap,
      TransitionAffineNat.eval_add, TransitionAffineNat.eval_const]
    simp [Nat.add_assoc]
  · rfl

/-- Stack actions commute with replacing the independent state family. -/
theorem TransitionStmtStackAction.eval_replaceState
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (replacement : StateWires tm)
    (action : TransitionStmtStackAction tm) :
    action.eval tm originStart height falseWire trueWire
        (source.replaceState replacement) =
      CfgBundle.replaceState
        (action.eval tm originStart height falseWire trueWire source)
        replacement := by
  rcases action with ⟨k, kind⟩
  cases kind <;> funext slot <;>
    rcases slot with (_ | label | state | ⟨other, coordinate⟩)
  all_goals
    simp [TransitionStmtStackAction.eval, arithmeticPushCfgWires,
      arithmeticPopCfgWires, CfgBundle.replaceState, CfgBundle.replaceStack,
      CfgSlot.halted, CfgSlot.label, CfgSlot.state]

/-- Appending one recorded action executes it after the existing prefix. -/
theorem transitionStmtStackActions_eval_append_singleton
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (actions : List (TransitionStmtStackAction tm))
    (action : TransitionStmtStackAction tm) :
    transitionStmtStackActions_eval tm originStart height falseWire trueWire
        source (actions ++ [action]) =
      action.eval tm originStart height falseWire trueWire
        (transitionStmtStackActions_eval tm originStart height falseWire
          trueWire source actions) := by
  simp [transitionStmtStackActions_eval, List.foldl_append]

/-- Recording a push in the context is semantically the corresponding
zero-gate push on the context row. -/
theorem TransitionStmtAffineContext.recordPush_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (k : tm.K)
    (table : Fin (stateCount tm) → Fin (reachableAlphabet tm k).card) :
    (context.recordPush tm k table).wires tm originStart height falseWire
        trueWire source =
      arithmeticPushCfgWires tm height k falseWire
        (fun target => originStart + context.gateOffset.eval height +
          oneHotMapWireOffset table target)
        (context.wires tm originStart height falseWire trueWire source) := by
  unfold TransitionStmtAffineContext.recordPush
    TransitionStmtAffineContext.wires
  rw [transitionStmtStackActions_eval_append_singleton]
  symm
  simpa [TransitionStmtStackAction.eval, Nat.add_assoc] using
    (TransitionStmtStackAction.eval_replaceState tm originStart height
      falseWire trueWire
      (transitionStmtStackActions_eval tm originStart height falseWire
        trueWire source context.stackActions)
      (context.state.wires tm originStart height source)
      ({ k := k
         kind := .push fun target =>
           context.gateOffset.add
             (TransitionAffineNat.const
               (oneHotMapWireOffset table target)) } :
        TransitionStmtStackAction tm))

/-- Recording a pop in the context is semantically the corresponding
positive- or zero-height arithmetic pop on the context row. -/
theorem TransitionStmtAffineContext.recordPop_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (k : tm.K) :
    (context.recordPop tm k).wires tm originStart height falseWire trueWire
        source =
      arithmeticPopCfgWires tm height k falseWire trueWire
        (originStart + context.gateOffset.eval height)
        (context.wires tm originStart height falseWire trueWire source) := by
  unfold TransitionStmtAffineContext.recordPop
    TransitionStmtAffineContext.wires
  rw [transitionStmtStackActions_eval_append_singleton]
  symm
  simpa [TransitionStmtStackAction.eval] using
    (TransitionStmtStackAction.eval_replaceState tm originStart height
      falseWire trueWire
      (transitionStmtStackActions_eval tm originStart height falseWire
        trueWire source context.stackActions)
      (context.state.wires tm originStart height source)
      ({ k := k, kind := .pop context.gateOffset } :
        TransitionStmtStackAction tm))

/-- `afterLoad` is the exact continuation source of the ordinary recursive
statement compiler. -/
theorem TransitionStmtAffineContext.afterLoad_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
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
  unfold TransitionStmtAffineContext.afterLoad
  rw [TransitionStmtAffineContext.advance_wires]
  exact context.replaceStateByMap_wires tm originStart height falseWire
    trueWire source (stmtStateTable tm update)

/-- `afterPush` is the exact continuation source after the symbol lookup and
zero-gate stack rewiring. -/
theorem TransitionStmtAffineContext.afterPush_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (k : tm.K)
    (table : Fin (stateCount tm) → Fin (reachableAlphabet tm k).card) :
    (context.afterPush tm k table).wires tm originStart height falseWire
        trueWire source =
      arithmeticPushCfgWires tm height k falseWire
        (oneHotMapGateTrace
          (originStart + context.gateOffset.eval height)
          (context.wires tm originStart height falseWire trueWire source).state
          table).wires
        (context.wires tm originStart height falseWire trueWire source) := by
  unfold TransitionStmtAffineContext.afterPush
  rw [TransitionStmtAffineContext.advance_wires,
    context.recordPush_wires tm originStart height falseWire trueWire source]
  rw [oneHotMapGateTrace_wires_eq_offset]

/-- `afterPeek` is the exact continuation source after the state/head lookup. -/
theorem TransitionStmtAffineContext.afterPeek_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height) (context : TransitionStmtAffineContext tm)
    (k : tm.K) (update : tm.σ → Option (tm.Γ k) → tm.σ) :
    (context.afterPeek tm k update).wires tm originStart height falseWire
        trueWire source =
      CfgBundle.replaceState
        (context.wires tm originStart height falseWire trueWire source)
          (oneHotPairMapGateTrace
            (originStart + context.gateOffset.eval height)
            (context.wires tm originStart height falseWire trueWire source).state
            (arithmeticPeekCfgWires tm height falseWire trueWire
              (context.wires tm originStart height falseWire trueWire source) k)
            (stmtHeadStateTable tm k update)).wires := by
  unfold TransitionStmtAffineContext.afterPeek
  rw [TransitionStmtAffineContext.advance_wires]
  exact context.replaceStateByPairMap_wires tm originStart height falseWire
    trueWire source 0 (stmtHeadStateTable tm k update)
      (arithmeticPeekCfgWires tm height falseWire trueWire
        (context.wires tm originStart height falseWire trueWire source) k)

/-- `afterPop` is the exact continuation source after the arithmetic pop and
the following state/head lookup. -/
theorem TransitionStmtAffineContext.afterPop_wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
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
  unfold TransitionStmtAffineContext.afterPop
  rw [TransitionStmtAffineContext.advance_wires]
  have hpair := (context.recordPop tm k).replaceStateByPairMap_wires tm
    originStart height falseWire trueWire source 1
      (stmtHeadStateTable tm k update)
      (arithmeticPopHeadWires tm k falseWire trueWire height
        ((context.wires tm originStart height falseWire trueWire source).stack k))
  rw [context.recordPop_wires tm originStart height falseWire trueWire source]
    at hpair
  simpa [TransitionStmtAffineContext.recordPop] using hpair

end CLRS.Chapter34.Turing.CookLevin
