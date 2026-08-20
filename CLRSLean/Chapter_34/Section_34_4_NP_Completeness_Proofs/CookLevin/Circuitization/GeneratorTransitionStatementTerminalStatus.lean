import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionOneHotMapCoordinates

/-!
# Status coordinates of terminal-ending transition statements

For a linear statement spine ending in `halt` or `goto`, the halted bit and
label family have a closed layout.  Earlier state and stack operations cannot
change these status coordinates; they only advance the terminal gate start.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Pool-backed halted coordinate selected by the fixed terminal. -/
def TransitionStmtTerminal.haltedWire (tm : _root_.Turing.FinTM2)
    (falseWire trueWire : Nat) : TransitionStmtTerminal tm → Nat
  | .halt => arithmeticLabelHaltedWire falseWire trueWire
      (labelHalted (none : Option tm.Λ))
  | .goto jump => arithmeticLabelHaltedWire falseWire trueWire
      (labelHalted (some (jump default)))

/-- Complete label family selected by the fixed terminal.  A halt is wired
from the Boolean pool, while a goto uses the table-fixed lookup offsets. -/
def TransitionStmtTerminal.labelWires (tm : _root_.Turing.FinTM2)
    (falseWire trueWire terminalStart : Nat) :
    TransitionStmtTerminal tm → LabelWires tm
  | .halt => arithmeticLabelWires tm falseWire trueWire
      (none : Option tm.Λ)
  | .goto jump => fun target =>
      terminalStart + oneHotMapWireOffset (stmtLabelTable tm jump) target

/-- Exact halted and label coordinates of every terminal-ending statement.
The positive-height assumption is needed only to make each preceding `pop`
contribute its unique OR gate to the affine terminal offset. -/
theorem transitionStmtOutputWires_terminal_status
    (tm : _root_.Turing.FinTM2) (height : Nat) (hheight : 0 < height)
    (falseWire trueWire start : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (layout : TransitionStmtTerminalLayout tm)
    (hlayout : transitionStmtTerminalLayout tm q = some layout) :
    let output := transitionStmtOutputWires tm height falseWire trueWire
      start source q hsupport
    output.halted = layout.terminal.haltedWire tm falseWire trueWire ∧
      output.label = layout.terminal.labelWires tm falseWire trueWire
        (start + layout.offset.eval height) := by
  induction q generalizing start source layout with
  | halt =>
      simp [transitionStmtTerminalLayout] at hlayout
      subst layout
      constructor
      · rfl
      · funext target
        rfl
  | goto jump =>
      simp [transitionStmtTerminalLayout] at hlayout
      subst layout
      constructor
      · rfl
      · change (oneHotMapGateTrace start source.state
          (stmtLabelTable tm jump)).wires = _
        simpa [TransitionStmtTerminal.labelWires,
          TransitionAffineNat.eval, TransitionAffineNat.const] using
          oneHotMapGateTrace_wires_eq_offset start source.state
            (stmtLabelTable tm jump)
  | load update continuation ih =>
      have hsupportContinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtTerminalLayout] at hlayout
      cases hcontinuation : transitionStmtTerminalLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          simp only [transitionStmtOutputWires]
          have hresult := ih (start := start + stateCount tm + stateCount tm)
            (source := source.replaceState
              (oneHotMapGateTrace start source.state
                (stmtStateTable tm update)).wires)
            (hsupport := hsupportContinuation)
            (layout := continuationLayout) hcontinuation
          simpa [TransitionAffineNat.eval_add, Nat.add_assoc] using hresult
  | push k emit continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      simp only [transitionStmtTerminalLayout] at hlayout
      cases hcontinuation : transitionStmtTerminalLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          simp only [transitionStmtOutputWires]
          have hresult := ih
            (start := start + stateCount tm + (reachableAlphabet tm k).card)
            (source := arithmeticPushCfgWires tm height k falseWire
              (oneHotMapGateTrace start source.state
                (fun code => encodeSupportedSymbol
                  ⟨emit ((stateEquivFin tm).symm code), by
                    apply hsupport k
                    simp [stmtPushSet]⟩)).wires source)
            (hsupport := hsupportContinuation)
            (layout := continuationLayout) hcontinuation
          simpa [TransitionAffineNat.eval_add, Nat.add_assoc] using hresult
  | peek k update continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtTerminalLayout] at hlayout
      cases hcontinuation : transitionStmtTerminalLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          simp only [transitionStmtOutputWires]
          have hresult := ih
            (start := start +
              2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
                stateCount tm)
            (source := source.replaceState
              (oneHotPairMapGateTrace start source.state
                (arithmeticPeekCfgWires tm height falseWire trueWire source k)
                (stmtHeadStateTable tm k update)).wires)
            (hsupport := hsupportContinuation)
            (layout := continuationLayout) hcontinuation
          simpa [TransitionAffineNat.eval_add, Nat.add_assoc] using hresult
  | pop k update continuation ih =>
      have hsupportContinuation :
          ∀ j, stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtTerminalLayout] at hlayout
      cases hcontinuation : transitionStmtTerminalLayout tm continuation with
      | none => simp [hcontinuation] at hlayout
      | some continuationLayout =>
          rw [hcontinuation] at hlayout
          simp only [Option.map_some, Option.some.injEq] at hlayout
          subst layout
          simp only [transitionStmtOutputWires]
          cases height with
          | zero => omega
          | succ height =>
              have hresult := ih
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
                (layout := continuationLayout) hcontinuation
              simpa [TransitionAffineNat.eval_add, popStackWireGateCost,
                Nat.add_assoc] using hresult
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [transitionStmtTerminalLayout] at hlayout

end CLRS.Chapter34.Turing.CookLevin
