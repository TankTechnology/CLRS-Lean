import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout.Allocation

/-!
# Whole-tableau external-input assignments

The functions below patch concrete row bits into all consecutive row intervals
and connect those assignments to the serially allocated wire bundles.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Patch `n` consecutive rows, beginning at `base`, into an arbitrary total
external-input assignment. -/
def writeTableauBitsAt (tm : _root_.Turing.FinTM2) (H base : Nat) :
    (n : Nat) → (Nat → Bool) → (Fin n → CfgBits tm H) → Nat → Bool
  | 0, assignment, _ => assignment
  | n + 1, assignment, bits =>
      (tableauRowLayoutAt tm H base n).writeCfgBits
        (writeTableauBitsAt tm H base n assignment
          (fun row => bits row.castSucc))
        (bits (Fin.last n))

/-- Every coordinate of every patched row reads back exactly its supplied
bit, including the initial-only `n = 1` case. -/
theorem writeTableauBitsAt_at (tm : _root_.Turing.FinTM2) (H base : Nat)
    (n : Nat) (assignment : Nat → Bool) (bits : Fin n → CfgBits tm H)
    (row : Fin n) (slot : CfgSlot tm H) :
    writeTableauBitsAt tm H base n assignment bits
        ((tableauRowLayoutAt tm H base row.val).index slot).val =
      bits row slot := by
  induction n with
  | zero => exact Fin.elim0 row
  | succ n ih =>
      unfold writeTableauBitsAt
      by_cases hrow : row.val < n
      · rw [CfgInputLayout.writeCfgBits_outside]
        exact ih (fun i : Fin n => bits i.castSucc) ⟨row.val, hrow⟩
        rcases tableauRowLayout_disjoint tm H base hrow with hbefore | hbefore
        · exact Or.inl (lt_of_lt_of_le
            ((tableauRowLayoutAt tm H base row.val).index_lt slot) hbefore)
        · exact Or.inr (le_trans hbefore (by
            simp [CfgInputLayout.index]))
      · have hlast : row = Fin.last n := Fin.ext (by
          rw [Fin.val_last]
          omega)
        subst row
        simpa only [Fin.val_last] using
          CfgInputLayout.writeCfgBits_at
            (tableauRowLayoutAt tm H base n)
            (writeTableauBitsAt tm H base n assignment
              (fun row => bits row.castSucc))
            (bits (Fin.last n)) slot

/-- Patching a tableau preserves every external input outside the complete
half-open tableau interval. -/
theorem writeTableauBitsAt_outside (tm : _root_.Turing.FinTM2)
    (H base n : Nat) (assignment : Nat → Bool)
    (bits : Fin n → CfgBits tm H) {inputIndex : Nat}
    (houtside : inputIndex < base ∨
      base + n * cfgBitCount tm H ≤ inputIndex) :
    writeTableauBitsAt tm H base n assignment bits inputIndex =
      assignment inputIndex := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold writeTableauBitsAt
      rw [CfgInputLayout.writeCfgBits_outside]
      · apply ih (fun i => bits i.castSucc)
        rcases houtside with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (le_trans (by
            exact Nat.add_le_add_left
              (Nat.mul_le_mul_right _ (Nat.le_succ n)) base) hafter)
      · rcases houtside with hbefore | hafter
        · exact Or.inl (lt_of_lt_of_le hbefore (Nat.le_add_right _ _))
        · exact Or.inr (by
            rw [tableauRowLayoutAt_finish]
            exact hafter)

/-- Patch all rows of the canonical zero-offset `T`-transition tableau. -/
def writeTableauBits (tm : _root_.Turing.FinTM2) (H T : Nat)
    (assignment : Nat → Bool)
    (bits : Fin (tableauRowCount T) → CfgBits tm H) : Nat → Bool :=
  writeTableauBitsAt tm H 0 (tableauRowCount T) assignment bits

/-- Under the all-row assignment, every allocated row evaluates exactly to
the corresponding supplied row bits. -/
theorem TableauRowsAllocation.evalCfgBits_writeTableau
    {tm : _root_.Turing.FinTM2} {H : Nat}
    {start : CircuitBuilder} {base n : Nat}
    (allocation : TableauRowsAllocation tm H start base n)
    (assignment : Nat → Bool) (bits : Fin n → CfgBits tm H)
    (row : Fin n) :
    evalCfgBits allocation.builder
        (writeTableauBitsAt tm H base n assignment bits)
        (allocation.rows row) = bits row := by
  funext slot
  rw [evalCfgBits, allocation.eval_slot,
    writeTableauBitsAt_at tm H base n assignment bits row slot]

end

end CLRS.Chapter34.Turing.CookLevin
