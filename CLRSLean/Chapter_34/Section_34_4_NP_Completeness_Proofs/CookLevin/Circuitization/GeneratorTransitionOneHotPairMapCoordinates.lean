import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalStatus

/-!
# Absolute coordinates of finite one-hot pair-map outputs

The binary lookup used by `peek` and `pop` first emits one AND gate for each
source pair, then performs an ordinary one-hot map.  Consequently its output
coordinates are again a fixed family translated by the current gate start.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Zero-based output coordinate of a fixed binary one-hot lookup. -/
def oneHotPairMapWireOffset {n p m : Nat}
    (f : Fin n → Fin p → Fin m) (target : Fin m) : Nat :=
  n * p + oneHotMapWireOffset (oneHotPairFunction f) target

theorem oneHotPairAndBodyGateTrace_length
    {n p : Nat} (start : Nat) (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) :
    ∀ (k : Nat) (hk : k ≤ n * p),
      (oneHotPairAndBodyGateTrace start left right k hk).gates.length = k := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      simp [oneHotPairAndBodyGateTrace, ih]

theorem oneHotPairAndGateTrace_length
    {n p : Nat} (start : Nat) (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) :
    (oneHotPairAndGateTrace start left right).gates.length = n * p := by
  exact oneHotPairAndBodyGateTrace_length start left right
    (n * p) (Nat.le_refl _)

private theorem oneHotPairAndBodyGateTrace_wire_eq_start_add_val
    {n p : Nat} (start : Nat) (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) :
    ∀ (k : Nat) (hk : k ≤ n * p) (q : Fin k),
      (oneHotPairAndBodyGateTrace start left right k hk).wires q =
        start + q.val := by
  intro k
  induction k with
  | zero =>
      intro hk q
      exact Fin.elim0 q
  | succ k ih =>
      intro hk q
      by_cases hq : q.val < k
      · simp only [oneHotPairAndBodyGateTrace, dif_pos hq]
        exact ih (by omega) ⟨q.val, hq⟩
      · simp only [oneHotPairAndBodyGateTrace, dif_neg hq]
        rw [oneHotPairAndBodyGateTrace_length]
        have hqEq : q.val = k :=
          Nat.le_antisymm (Nat.le_of_lt_succ q.isLt)
            (Nat.le_of_not_gt hq)
        rw [hqEq]

/-- Pair materialization emits one gate per pair in flattened pair order, so
fresh pair wire `q` is exactly `start + q.val`. -/
theorem oneHotPairAndGateTrace_wire_eq_start_add_val
    {n p : Nat} (start : Nat) (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) (q : Fin (n * p)) :
    (oneHotPairAndGateTrace start left right).wires q = start + q.val :=
  oneHotPairAndBodyGateTrace_wire_eq_start_add_val start left right
    (n * p) (Nat.le_refl _) q

theorem oneHotPairAndGateTrace_wires_eq_start_add_val
    {n p : Nat} (start : Nat) (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) :
    (oneHotPairAndGateTrace start left right).wires =
      fun q => start + q.val := by
  funext q
  exact oneHotPairAndGateTrace_wire_eq_start_add_val start left right q

/-- Every binary lookup output coordinate is the gate start plus its fixed
pair-table offset. -/
theorem oneHotPairMapGateTrace_wire_eq_start_add_offset
    {n p m : Nat} (start : Nat)
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m) (target : Fin m) :
    (oneHotPairMapGateTrace start left right f).wires target =
      start + oneHotPairMapWireOffset f target := by
  simp only [oneHotPairMapGateTrace]
  rw [oneHotMapGateTrace_wire_eq_start_add_offset,
    oneHotPairAndGateTrace_length]
  simp [oneHotPairMapWireOffset, Nat.add_assoc]

/-- Function-level pair-map coordinate equation used by state replacement. -/
theorem oneHotPairMapGateTrace_wires_eq_offset
    {n p m : Nat} (start : Nat)
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m) :
    (oneHotPairMapGateTrace start left right f).wires =
      fun target => start + oneHotPairMapWireOffset f target := by
  funext target
  exact oneHotPairMapGateTrace_wire_eq_start_add_offset
    start left right f target

end CLRS.Chapter34.Turing.CookLevin
