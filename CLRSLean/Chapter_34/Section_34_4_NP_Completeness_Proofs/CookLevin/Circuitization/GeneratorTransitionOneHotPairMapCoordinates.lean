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

private theorem oneHotPairAndBodyGateTrace_length
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

private theorem oneHotPairAndGateTrace_length
    {n p : Nat} (start : Nat) (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) :
    (oneHotPairAndGateTrace start left right).gates.length = n * p := by
  exact oneHotPairAndBodyGateTrace_length start left right
    (n * p) (Nat.le_refl _)

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
