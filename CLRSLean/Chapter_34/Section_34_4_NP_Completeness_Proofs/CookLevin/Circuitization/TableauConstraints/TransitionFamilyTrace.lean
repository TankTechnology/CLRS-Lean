import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.TransitionFamily
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Trace

/-!
# Exact whole-tableau transition-family trace

The family trace mirrors the semantic builder's prefix recursion and appends
one explicit local transition trace for each adjacent row pair.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Literal ordered gate trace for all adjacent pairs in a public row family. -/
def transitionCircuitFamilyGateTrace
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder) :
    (T : Nat) → (rows : Fin (T + 1) → CfgWires tm H) →
      (∀ row, (rows row).ValidIn base) → List CircuitGate
  | 0, _, _ => []
  | T + 1, rows, hrows =>
      let prefixRows : Fin (T + 1) → CfgWires tm H :=
        fun row => rows row.castSucc
      let hprefix : ∀ row, (prefixRows row).ValidIn base :=
        fun row => hrows row.castSucc
      let previous := transitionCircuitFamily tm H base prefixRows hprefix
      let currentRow : Fin (T + 2) := (Fin.last T).castSucc
      let nextRow : Fin (T + 2) := Fin.last (T + 1)
      let hcurrent : (rows currentRow).ValidIn previous.builder :=
        (hrows currentRow).mono previous.extension
      let hnext : (rows nextRow).ValidIn previous.builder :=
        (hrows nextRow).mono previous.extension
      transitionCircuitFamilyGateTrace tm H base T prefixRows hprefix ++
        (transitionCircuitGateTrace tm H previous.builder
          (rows currentRow) (rows nextRow) hcurrent hnext).gates

/-- The semantic transition-family builder appends exactly the explicit
adjacent-pair trace. -/
theorem transitionCircuitFamily_gates_eq
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder)
    (T : Nat) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (transitionCircuitFamily tm H base rows hrows).builder.gates =
      base.gates ++ transitionCircuitFamilyGateTrace tm H base T rows hrows := by
  induction T generalizing base with
  | zero => simp [transitionCircuitFamilyGateTrace]
  | succ T ih =>
      simp only [transitionCircuitFamilyGateTrace]
      rw [transitionCircuitFamily_succ_builder]
      rw [transitionCircuit_gates_eq]
      rw [ih]
      simp only [List.append_assoc]

/-- The explicit family trace pays the local exact cost once per step. -/
theorem transitionCircuitFamilyGateTrace_length
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder)
    (T : Nat) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (transitionCircuitFamilyGateTrace tm H base T rows hrows).length =
      T * transitionCircuitGateCost tm H := by
  have hgates := congrArg List.length
    (transitionCircuitFamily_gates_eq tm H base T rows hrows)
  rw [transitionCircuitFamily_gate_delta, List.length_append] at hgates
  omega

end

end CLRS.Chapter34.Turing.CookLevin
