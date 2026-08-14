import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout.Core

/-!
# Proof-carrying whole-tableau row allocation

Rows are allocated serially with `allocateCfgInputs`.  No static wires or
tableau constraints are introduced here.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Result of serially allocating `n` consecutive configuration rows. -/
structure TableauRowsAllocation (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (base n : Nat) where
  builder : CircuitBuilder
  extension : start.Extends builder
  rows : Fin n → CfgWires tm H
  rowValid : ∀ row, (rows row).ValidIn builder
  gate_delta : builder.gates.length =
    start.gates.length + n * cfgBitCount tm H
  wire_eq : ∀ row slot, rows row slot =
    start.gates.length + row.val * cfgBitCount tm H +
      (cfgSlotEquivFin tm H slot).val
  eval_slot : ∀ inputs row slot,
    builder.evalWire inputs (rows row slot) =
      inputs ((tableauRowLayoutAt tm H base row.val).index slot).val

/-- Serial allocation at an arbitrary offset and builder.  The fit premise is
exactly the endpoint of the complete `n`-row external-input interval. -/
def allocateTableauRowsAt (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (base : Nat) :
    (n : Nat) → base + n * cfgBitCount tm H ≤ start.inputCount →
      TableauRowsAllocation tm H start base n
  | 0, _ =>
      { builder := start
        extension := CircuitBuilder.Extends.refl start
        rows := Fin.elim0
        rowValid := fun row => Fin.elim0 row
        gate_delta := by simp
        wire_eq := fun row => Fin.elim0 row
        eval_slot := fun _ row => Fin.elim0 row }
  | n + 1, hfit => by
      have hprefix : base + n * cfgBitCount tm H ≤ start.inputCount := by
        apply le_trans ?_ hfit
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right _ (Nat.le_succ n)) base
      let previous := allocateTableauRowsAt tm H start base n hprefix
      let layout := tableauRowLayoutAt tm H base n
      have hlayout : layout.Fits previous.builder.inputCount := by
        change layout.finish ≤ previous.builder.inputCount
        rw [previous.extension.1]
        simpa [layout] using hfit
      let current := allocateCfgInputs previous.builder layout hlayout
      let rows : Fin (n + 1) → CfgWires tm H := fun row =>
        if hrow : row.val < n then
          previous.rows ⟨row.val, hrow⟩
        else current.wires
      exact
        { builder := current.builder
          extension := previous.extension.trans current.extension
          rows := rows
          rowValid := by
            intro row
            simp only [rows]
            split
            next hrow =>
              exact (previous.rowValid ⟨row.val, hrow⟩).mono
                current.extension
            next => exact current.valid
          gate_delta := by
            rw [current.gate_delta, previous.gate_delta]
            simp [Nat.succ_mul, Nat.add_assoc]
          wire_eq := by
            intro row slot
            simp only [rows]
            split
            next hrow => exact previous.wire_eq ⟨row.val, hrow⟩ slot
            next hrow =>
              have hlast : row.val = n := by omega
              rw [current.wire_eq, previous.gate_delta, hlast]
          eval_slot := by
            intro inputs row slot
            simp only [rows]
            split
            next hrow =>
              rw [current.extension.evalWire_eq inputs
                (previous.rowValid ⟨row.val, hrow⟩ slot)]
              exact previous.eval_slot inputs ⟨row.val, hrow⟩ slot
            next hrow =>
              have hlast : row.val = n := by omega
              rw [current.eval_slot]
              simp [layout, hlast] }

/-- Allocation is independent of the proof term establishing interval fit. -/
theorem allocateTableauRowsAt_proof_irrel
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (base n : Nat)
    (hfit₁ hfit₂ : base + n * cfgBitCount tm H ≤ start.inputCount) :
    allocateTableauRowsAt tm H start base n hfit₁ =
      allocateTableauRowsAt tm H start base n hfit₂ := by
  congr

/-- Empty builder with exactly the external-input arity of all tableau rows. -/
def tableauStart (tm : _root_.Turing.FinTM2) (H T : Nat) : CircuitBuilder :=
  CircuitBuilder.empty (tableauInputCount tm H T)

/-- Canonical proof-carrying serial allocation of all `T + 1` rows. -/
def allocateTableauRows (tm : _root_.Turing.FinTM2) (H T : Nat) :
    TableauRowsAllocation tm H (tableauStart tm H T) 0 (tableauRowCount T) :=
  allocateTableauRowsAt tm H (tableauStart tm H T) 0 (tableauRowCount T)
    (by simp [tableauStart, tableauInputCount, CircuitBuilder.empty])

/-- Whole-tableau row allocation preserves its exact declared input arity. -/
theorem allocateTableauRows_inputCount (tm : _root_.Turing.FinTM2)
    (H T : Nat) :
    (allocateTableauRows tm H T).builder.inputCount =
      tableauInputCount tm H T := by
  exact (allocateTableauRows tm H T).extension.1.trans rfl

/-- Serial row allocation emits exactly one input gate per row coordinate. -/
theorem allocateTableauRows_gate_delta (tm : _root_.Turing.FinTM2)
    (H T : Nat) :
    (allocateTableauRows tm H T).builder.gates.length =
      tableauInputCount tm H T := by
  simpa [tableauStart, tableauInputCount, CircuitBuilder.empty] using
    (allocateTableauRows tm H T).gate_delta

/-- Every allocated row is valid in the common final builder. -/
theorem allocateTableauRows_row_valid (tm : _root_.Turing.FinTM2)
    (H T : Nat) (row : Fin (tableauRowCount T)) :
    ((allocateTableauRows tm H T).rows row).ValidIn
      (allocateTableauRows tm H T).builder :=
  (allocateTableauRows tm H T).rowValid row

/-- Wires belonging to distinct allocated rows never alias. -/
theorem allocateTableauRows_wire_ne (tm : _root_.Turing.FinTM2)
    (H T : Nat) {left right : Fin (tableauRowCount T)}
    (hne : left ≠ right) (leftSlot rightSlot : CfgSlot tm H) :
    (allocateTableauRows tm H T).rows left leftSlot ≠
      (allocateTableauRows tm H T).rows right rightSlot := by
  rw [(allocateTableauRows tm H T).wire_eq,
    (allocateTableauRows tm H T).wire_eq]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · intro heq
    apply tableauRowLayout_index_ne tm H 0 hlt leftSlot rightSlot
    rw [CfgInputIndex.mk.injEq]
    simpa [tableauStart, tableauRowLayout, tableauRowLayoutAt,
      CfgInputLayout.index, CircuitBuilder.empty, Nat.add_assoc] using heq
  · intro heq
    apply tableauRowLayout_index_ne tm H 0 hgt rightSlot leftSlot
    rw [CfgInputIndex.mk.injEq]
    simpa [tableauStart, tableauRowLayout, tableauRowLayoutAt,
      CfgInputLayout.index, CircuitBuilder.empty, Nat.add_assoc] using heq.symm

/-- Every row evaluates pointwise to its external-input interval. -/
theorem TableauRowsAllocation.evalCfgBits_eq_inputs
    {tm : _root_.Turing.FinTM2} {H : Nat}
    {start : CircuitBuilder} {base n : Nat}
    (allocation : TableauRowsAllocation tm H start base n)
    (inputs : Nat → Bool) (row : Fin n) :
    evalCfgBits allocation.builder inputs (allocation.rows row) =
      fun slot => inputs
        ((tableauRowLayoutAt tm H base row.val).index slot).val := by
  funext slot
  exact allocation.eval_slot inputs row slot

end

end CLRS.Chapter34.Turing.CookLevin
