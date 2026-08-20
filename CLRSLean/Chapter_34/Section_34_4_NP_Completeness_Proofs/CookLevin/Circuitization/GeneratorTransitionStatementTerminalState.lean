import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionOneHotPairMapCoordinates

/-!
# State layout of terminal-ending transition statements

Every state update in a linear statement spine emits a fresh, table-fixed
one-hot family.  This module normalizes the final state family to either the
original source state or a fixed affine coordinate family, and proves that
normal form against the recursive semantic statement layout.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Normal form for a terminal statement's final state family. -/
inductive TransitionStmtStateLayout (tm : _root_.Turing.FinTM2)
  | source
  | fixed (offsets : Fin (stateCount tm) → TransitionAffineNat)

/-- Evaluate a normalized state family from the statement's initial start
and source row. -/
def TransitionStmtStateLayout.wires (tm : _root_.Turing.FinTM2)
    (start height : Nat) (source : CfgWires tm height) :
    TransitionStmtStateLayout tm → StateWires tm
  | .source => source.state
  | .fixed offsets => fun target => start + (offsets target).eval height

/-- Substitute an updated source state into a continuation layout and shift
fresh continuation outputs back to the enclosing statement start. -/
def TransitionStmtStateLayout.after (tm : _root_.Turing.FinTM2)
    (phaseCost : TransitionAffineNat)
    (replacement continuation : TransitionStmtStateLayout tm) :
    TransitionStmtStateLayout tm :=
  match continuation with
  | .source => replacement
  | .fixed offsets => .fixed fun target => phaseCost.add (offsets target)

/-- Final normalized state layout of a statement whose linear spine ends in
`halt` or `goto`.  Branch-ending spines return `none`. -/
noncomputable def transitionStmtTerminalStateLayout
    (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      Option (TransitionStmtStateLayout tm)
  | halt => some .source
  | goto _ => some .source
  | load update continuation =>
      let phaseCost := TransitionAffineNat.const
        (stateCount tm + stateCount tm)
      let replacement : TransitionStmtStateLayout tm := .fixed fun target =>
        TransitionAffineNat.const
          (oneHotMapWireOffset (stmtStateTable tm update) target)
      (transitionStmtTerminalStateLayout tm continuation).map
        (replacement.after tm phaseCost)
  | push k _ continuation =>
      let phaseCost := TransitionAffineNat.const
        (stateCount tm + (reachableAlphabet tm k).card)
      (transitionStmtTerminalStateLayout tm continuation).map
        ((TransitionStmtStateLayout.source).after tm phaseCost)
  | peek k update continuation =>
      let phaseCost := TransitionAffineNat.const
        (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
          stateCount tm)
      let replacement : TransitionStmtStateLayout tm := .fixed fun target =>
        TransitionAffineNat.const
          (oneHotPairMapWireOffset (stmtHeadStateTable tm k update) target)
      (transitionStmtTerminalStateLayout tm continuation).map
        (replacement.after tm phaseCost)
  | pop k update continuation =>
      let phaseCost := TransitionAffineNat.const
        (1 + 2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
          stateCount tm)
      let replacement : TransitionStmtStateLayout tm := .fixed fun target =>
        TransitionAffineNat.const
          (1 + oneHotPairMapWireOffset
            (stmtHeadStateTable tm k update) target)
      (transitionStmtTerminalStateLayout tm continuation).map
        (replacement.after tm phaseCost)
  | branch _ _ _ => none

/-- State normalization is defined on exactly the terminal-ending spines. -/
theorem transitionStmtTerminalStateLayout_isSome_iff_terminal
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (transitionStmtTerminalStateLayout tm q).isSome ↔
      (transitionStmtTerminalLayout tm q).isSome := by
  induction q with
  | halt => simp [transitionStmtTerminalStateLayout,
      transitionStmtTerminalLayout]
  | goto jump => simp [transitionStmtTerminalStateLayout,
      transitionStmtTerminalLayout]
  | load update continuation ih =>
      simp [transitionStmtTerminalStateLayout,
        transitionStmtTerminalLayout, ih]
  | push k emit continuation ih =>
      simp [transitionStmtTerminalStateLayout,
        transitionStmtTerminalLayout, ih]
  | peek k update continuation ih =>
      simp [transitionStmtTerminalStateLayout,
        transitionStmtTerminalLayout, ih]
  | pop k update continuation ih =>
      simp [transitionStmtTerminalStateLayout,
        transitionStmtTerminalLayout, ih]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtTerminalStateLayout,
        transitionStmtTerminalLayout]

/-- Exact state-family equation for every terminal-ending statement. -/
theorem transitionStmtOutputWires_terminal_state
    (tm : _root_.Turing.FinTM2) (height : Nat) (hheight : 0 < height)
    (falseWire trueWire start : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (layout : TransitionStmtStateLayout tm)
    (hlayout : transitionStmtTerminalStateLayout tm q = some layout) :
    (transitionStmtOutputWires tm height falseWire trueWire start source q
      hsupport).state = layout.wires tm start height source := by
  induction q generalizing start source layout with
  | halt =>
      simp [transitionStmtTerminalStateLayout] at hlayout
      subst layout
      rfl
  | goto jump =>
      simp [transitionStmtTerminalStateLayout] at hlayout
      subst layout
      rfl
  | load update continuation ih =>
      have hsupportContinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtTerminalStateLayout] at hlayout
      cases hcontinuation :
          transitionStmtTerminalStateLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          simp only [transitionStmtOutputWires]
          rw [ih (start := start + stateCount tm + stateCount tm)
            (source := source.replaceState
              (oneHotMapGateTrace start source.state
                (stmtStateTable tm update)).wires)
            (hsupport := hsupportContinuation)
            (layout := continuationLayout) hcontinuation]
          cases continuationLayout with
          | source =>
              change (oneHotMapGateTrace start source.state
                (stmtStateTable tm update)).wires = _
              simpa [TransitionStmtStateLayout.after,
                TransitionStmtStateLayout.wires,
                TransitionAffineNat.eval, TransitionAffineNat.const] using
                oneHotMapGateTrace_wires_eq_offset start source.state
                  (stmtStateTable tm update)
          | fixed offsets =>
              funext target
              simp [TransitionStmtStateLayout.after,
                TransitionStmtStateLayout.wires,
                TransitionAffineNat.eval_add, Nat.add_assoc]
  | push k emit continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      simp only [transitionStmtTerminalStateLayout] at hlayout
      cases hcontinuation :
          transitionStmtTerminalStateLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          simp only [transitionStmtOutputWires]
          rw [ih
            (start := start + stateCount tm + (reachableAlphabet tm k).card)
            (source := arithmeticPushCfgWires tm height k falseWire
              (oneHotMapGateTrace start source.state
                (fun code => encodeSupportedSymbol
                  ⟨emit ((stateEquivFin tm).symm code), by
                    apply hsupport k
                    simp [stmtPushSet]⟩)).wires source)
            (hsupport := hsupportContinuation)
            (layout := continuationLayout) hcontinuation]
          cases continuationLayout with
          | source =>
              funext target
              rfl
          | fixed offsets =>
              funext target
              simp [TransitionStmtStateLayout.after,
                TransitionStmtStateLayout.wires,
                TransitionAffineNat.eval_add, Nat.add_assoc]
  | peek k update continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtTerminalStateLayout] at hlayout
      cases hcontinuation :
          transitionStmtTerminalStateLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          simp only [transitionStmtOutputWires]
          rw [ih
            (start := start +
              2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
                stateCount tm)
            (source := source.replaceState
              (oneHotPairMapGateTrace start source.state
                (arithmeticPeekCfgWires tm height falseWire trueWire source k)
                (stmtHeadStateTable tm k update)).wires)
            (hsupport := hsupportContinuation)
            (layout := continuationLayout) hcontinuation]
          cases continuationLayout with
          | source =>
              change (oneHotPairMapGateTrace start source.state
                (arithmeticPeekCfgWires tm height falseWire trueWire source k)
                (stmtHeadStateTable tm k update)).wires = _
              simpa [TransitionStmtStateLayout.after,
                TransitionStmtStateLayout.wires,
                TransitionAffineNat.eval, TransitionAffineNat.const] using
                oneHotPairMapGateTrace_wires_eq_offset start source.state
                  (arithmeticPeekCfgWires tm height falseWire trueWire source k)
                  (stmtHeadStateTable tm k update)
          | fixed offsets =>
              funext target
              simp [TransitionStmtStateLayout.after,
                TransitionStmtStateLayout.wires,
                TransitionAffineNat.eval_add, Nat.add_assoc]
  | pop k update continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtTerminalStateLayout] at hlayout
      cases hcontinuation :
          transitionStmtTerminalStateLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          simp only [transitionStmtOutputWires]
          cases height with
          | zero => omega
          | succ height =>
              rw [ih
                (start := start + popStackWireGateCost (height + 1) +
                  (2 * stateCount tm *
                    ((reachableAlphabet tm k).card + 1) + stateCount tm))
                (source :=
                  (arithmeticPopCfgWires tm (height + 1) k falseWire trueWire
                    start source).replaceState
                    (oneHotPairMapGateTrace
                      (start + popStackWireGateCost (height + 1))
                      (arithmeticPopCfgWires tm (height + 1) k falseWire
                        trueWire start source).state
                      (arithmeticPopHeadWires tm k falseWire trueWire
                        (height + 1) (source.stack k))
                      (stmtHeadStateTable tm k update)).wires)
                (hsupport := hsupportContinuation)
                (layout := continuationLayout) hcontinuation]
              cases continuationLayout with
              | source =>
                  change (oneHotPairMapGateTrace (start + 1)
                    (arithmeticPopCfgWires tm (height + 1) k falseWire
                      trueWire start source).state
                    (arithmeticPopHeadWires tm k falseWire trueWire
                      (height + 1) (source.stack k))
                    (stmtHeadStateTable tm k update)).wires = _
                  simpa [TransitionStmtStateLayout.after,
                    TransitionStmtStateLayout.wires,
                    TransitionAffineNat.eval, TransitionAffineNat.const,
                    popStackWireGateCost, Nat.add_assoc] using
                    oneHotPairMapGateTrace_wires_eq_offset (start + 1)
                      (arithmeticPopCfgWires tm (height + 1) k falseWire
                        trueWire start source).state
                      (arithmeticPopHeadWires tm k falseWire trueWire
                        (height + 1) (source.stack k))
                      (stmtHeadStateTable tm k update)
              | fixed offsets =>
                  funext target
                  simp [TransitionStmtStateLayout.after,
                    TransitionStmtStateLayout.wires,
                    TransitionAffineNat.eval_add, popStackWireGateCost,
                    Nat.add_assoc]
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtTerminalStateLayout] at hlayout

end CLRS.Chapter34.Turing.CookLevin
