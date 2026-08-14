import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Core

/-!
# CLRS Section 34.4 - Statement-circuit emitted-gate bounds

Height-independent coefficients bound circuit size for each fixed machine and
statement. These are emitted-gate bounds, not Lean construction-time bounds.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A height-independent coefficient controlling the emitted gate count for a
fixed machine and statement. -/
def compileStmtGateCoefficient (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Nat
  | push k _ continuation =>
      stateCount tm + (reachableAlphabet tm k).card +
        compileStmtGateCoefficient tm continuation
  | peek k _ continuation =>
      2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
        stateCount tm + compileStmtGateCoefficient tm continuation
  | pop k _ continuation =>
      1 + (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
        stateCount tm) + compileStmtGateCoefficient tm continuation
  | load _ continuation =>
      stateCount tm + stateCount tm +
        compileStmtGateCoefficient tm continuation
  | branch test whenTrue whenFalse =>
      (oneHotTruePreimage (stmtPredicateTable tm test)).card + 1 +
        compileStmtGateCoefficient tm whenTrue +
        compileStmtGateCoefficient tm whenFalse + 4
  | goto _ => stateCount tm + (labelCount tm + 1)
  | halt => 0

private theorem local_add_le_coefficient_mul (localCost cost coefficient width : Nat)
    (hwidth : 0 < width) (hcost : cost ≤ coefficient * width) :
    localCost + cost ≤ (localCost + coefficient) * width := by
  calc
    localCost + cost ≤ localCost * width + coefficient * width :=
      Nat.add_le_add (Nat.le_mul_of_pos_right localCost hwidth) hcost
    _ = (localCost + coefficient) * width := by rw [Nat.add_mul]

/-- The exact structural cost is controlled by a fixed statement coefficient
times an affine expression in row width and height. -/
theorem compileStmtGateCost_le (tm : _root_.Turing.FinTM2) (H : Nat)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    compileStmtGateCost tm H q ≤
      compileStmtGateCoefficient tm q * (cfgBitCount tm H + H + 1) := by
  let width := cfgBitCount tm H + H + 1
  have hwidth : 1 ≤ width := by simp [width]
  have hcfg : cfgBitCount tm H ≤ width := by omega
  have hpop : popStackWireGateCost H ≤ width := by
    cases H <;> simp [width, popStackWireGateCost]
  induction q with
  | halt => simp [compileStmtGateCost, compileStmtGateCoefficient]
  | goto jump =>
      simp only [compileStmtGateCost, compileStmtGateCoefficient]
      exact Nat.le_mul_of_pos_right _ (by omega)
  | load update continuation ih =>
      simp only [compileStmtGateCost, compileStmtGateCoefficient]
      exact local_add_le_coefficient_mul _ _ _ _ (by omega) ih
  | push k emit continuation ih =>
      simp only [compileStmtGateCost, compileStmtGateCoefficient]
      exact local_add_le_coefficient_mul _ _ _ _ (by omega) ih
  | peek k update continuation ih =>
      simp only [compileStmtGateCost, compileStmtGateCoefficient]
      exact local_add_le_coefficient_mul _ _ _ _ (by omega) ih
  | pop k update continuation ih =>
      simp only [compileStmtGateCost, compileStmtGateCoefficient]
      let localCost := 2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
        stateCount tm
      have hlocal : popStackWireGateCost H + localCost ≤
          (1 + localCost) * width := by
        calc
          popStackWireGateCost H + localCost ≤ width + localCost * width :=
            Nat.add_le_add hpop (Nat.le_mul_of_pos_right localCost (by omega))
          _ = (1 + localCost) * width := by simp [Nat.add_mul]
      calc
        popStackWireGateCost H + localCost + compileStmtGateCost tm H continuation ≤
            (1 + localCost) * width +
              compileStmtGateCoefficient tm continuation * width :=
          Nat.add_le_add hlocal ih
        _ = (1 + localCost + compileStmtGateCoefficient tm continuation) * width := by
          ring
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp only [compileStmtGateCost, compileStmtGateCoefficient]
      let predicateCost := (oneHotTruePreimage (stmtPredicateTable tm test)).card + 1
      have hpredicate : predicateCost ≤ predicateCost * width :=
        Nat.le_mul_of_pos_right _ (by omega)
      have hmux : 3 * cfgBitCount tm H + 1 ≤ 4 * width := by omega
      calc
        predicateCost + compileStmtGateCost tm H whenTrue +
              compileStmtGateCost tm H whenFalse + (3 * cfgBitCount tm H + 1) ≤
            predicateCost * width +
              compileStmtGateCoefficient tm whenTrue * width +
              compileStmtGateCoefficient tm whenFalse * width + 4 * width :=
          Nat.add_le_add
            (Nat.add_le_add (Nat.add_le_add hpredicate ihTrue) ihFalse) hmux
        _ = (predicateCost + compileStmtGateCoefficient tm whenTrue +
              compileStmtGateCoefficient tm whenFalse + 4) * width := by ring

/-- Statement compilation emits at most a fixed statement coefficient times
{lit}`cfgBitCount tm H + H + 1` gates beyond the input builder.  This is a circuit
size bound only; it makes no claim about Lean host-language construction time. -/
theorem compileStmt_gate_count_le
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm H) (hvalid : source.ValidIn base)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (compileStmt tm H base pool source hvalid q hsupport).builder.gates.length ≤
      base.gates.length + compileStmtGateCoefficient tm q *
        (cfgBitCount tm H + H + 1) := by
  rw [compileStmt_gate_delta]
  exact Nat.add_le_add_left (compileStmtGateCost_le tm H q) _


end

end CLRS.Chapter34.Turing.CookLevin
