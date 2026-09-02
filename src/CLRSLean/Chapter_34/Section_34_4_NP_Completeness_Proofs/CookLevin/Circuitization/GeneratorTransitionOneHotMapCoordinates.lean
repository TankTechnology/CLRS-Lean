import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminal

/-!
# Absolute coordinates of finite one-hot map outputs

Finite one-hot lookup gates consume runtime source wires, but every fresh
output coordinate is fixed by the static lookup table.  This module makes
that separation explicit: changing the gate start translates every output
wire by the same amount, while changing source-wire values leaves all output
coordinates unchanged.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Static zero-based output coordinate of a finite one-hot lookup.  Dummy
source wires are sufficient because source values affect gate operands but
not the fresh output coordinates. -/
def oneHotMapWireOffset {n m : Nat} (f : Fin n → Fin m)
    (target : Fin m) : Nat :=
  (oneHotMapGateTrace 0 (fun _ => 0) f).wires target

private theorem disjunctionGateTrace_wire_eq_start_add_length
    (start : Nat) : ∀ wires : List CircuitBuilder.Wire,
      (CircuitBuilder.disjunctionGateTrace start wires).wire =
        start + wires.length := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [CircuitBuilder.disjunctionGateTrace,
        CircuitBuilder.disjunctionGateTrace_length]

private theorem oneHotMapBodyGateTrace_length_source_independent
    {n m : Nat} (start : Nat) (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Fin m) : ∀ (k : Nat) (hk : k ≤ m),
      (oneHotMapBodyGateTrace start source f k hk).gates.length =
        (oneHotMapBodyGateTrace 0 (fun _ => 0) f k hk).gates.length := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      simp only [oneHotMapBodyGateTrace, List.length_append,
        CircuitBuilder.disjunctionGateTrace_length,
        oneHotPreimageWires_length]
      rw [ih]

private theorem oneHotMapBodyGateTrace_wire_eq_start_add_offset
    {n m : Nat} (start : Nat) (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Fin m) : ∀ (k : Nat) (hk : k ≤ m) (target : Fin k),
      (oneHotMapBodyGateTrace start source f k hk).wires target =
        start +
          (oneHotMapBodyGateTrace 0 (fun _ => 0) f k hk).wires target := by
  intro k
  induction k with
  | zero =>
      intro hk target
      exact Fin.elim0 target
  | succ k ih =>
      intro hk target
      by_cases htarget : target.val < k
      · simp only [oneHotMapBodyGateTrace, dif_pos htarget]
        exact ih (by omega) ⟨target.val, htarget⟩
      · simp only [oneHotMapBodyGateTrace, dif_neg htarget]
        rw [disjunctionGateTrace_wire_eq_start_add_length,
          disjunctionGateTrace_wire_eq_start_add_length,
          oneHotPreimageWires_length, oneHotPreimageWires_length,
          oneHotMapBodyGateTrace_length_source_independent start source f k
            (by omega)]
        simp [Nat.add_assoc]

/-- Every output coordinate is the gate start plus a table-fixed offset. -/
theorem oneHotMapGateTrace_wire_eq_start_add_offset
    {n m : Nat} (start : Nat) (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Fin m) (target : Fin m) :
    (oneHotMapGateTrace start source f).wires target =
      start + oneHotMapWireOffset f target := by
  exact oneHotMapBodyGateTrace_wire_eq_start_add_offset
    start source f m (Nat.le_refl m) target

/-- Function-level form used when replacing an entire state or label family. -/
theorem oneHotMapGateTrace_wires_eq_offset
    {n m : Nat} (start : Nat) (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Fin m) :
    (oneHotMapGateTrace start source f).wires =
      fun target => start + oneHotMapWireOffset f target := by
  funext target
  exact oneHotMapGateTrace_wire_eq_start_add_offset start source f target

end CLRS.Chapter34.Turing.CookLevin
