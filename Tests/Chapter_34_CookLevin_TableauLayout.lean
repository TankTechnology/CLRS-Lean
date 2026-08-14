import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization

namespace CLRS.Chapter34.Turing.CookLevin

#check tableauRowCount
#check tableauInputCount
#check tableauRowLayoutAt
#check tableauRowLayout
#check tableauRowLayout_finish
#check tableauRowLayout_fits
#check tableauRowLayout_disjoint
#check tableauRowLayout_index_ne
#check TableauRowsAllocation
#check allocateTableauRowsAt
#check allocateTableauRowsAt_proof_irrel
#check tableauStart
#check allocateTableauRows
#check allocateTableauRows_inputCount
#check allocateTableauRows_gate_delta
#check allocateTableauRows_row_valid
#check allocateTableauRows_wire_ne
#check writeTableauBitsAt
#check writeTableauBitsAt_at
#check writeTableauBitsAt_outside
#check writeTableauBits
#check TableauRowsAllocation.evalCfgBits_writeTableau

/-! ## Concrete zero- and positive-horizon regressions -/

/-- One stack with empty reachable alphabet keeps the exact row width small
enough that the tests below expose the complete arithmetic. -/
private abbrev LayoutMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Empty
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .halt

-- `H = 0`, `T = 0`: the tableau still contains its initial row.
example : tableauRowCount 0 = 1 := by decide

example : cfgBitCount LayoutMachine 0 = 5 := by
  simp [cfgBitCount, LayoutMachine, labelCount, stateCount,
    reachableAlphabet, stmtPushSet]

example : tableauInputCount LayoutMachine 0 0 = 5 := by
  simp [tableauInputCount, tableauRowCount, cfgBitCount, LayoutMachine,
    labelCount, stateCount, reachableAlphabet, stmtPushSet]

example : (allocateTableauRows LayoutMachine 0 0).builder.inputCount = 5 := by
  rw [allocateTableauRows_inputCount]
  simp [tableauInputCount, tableauRowCount, cfgBitCount, LayoutMachine,
    labelCount, stateCount, reachableAlphabet, stmtPushSet]

example : (allocateTableauRows LayoutMachine 0 0).builder.gates.length = 5 := by
  rw [allocateTableauRows_gate_delta]
  simp [tableauInputCount, tableauRowCount, cfgBitCount, LayoutMachine,
    labelCount, stateCount, reachableAlphabet, stmtPushSet]

-- `H > 0`, `T > 1`: three independently allocated rows of width seven.
example : tableauRowCount 2 = 3 := by decide

example : cfgBitCount LayoutMachine 1 = 7 := by
  simp [cfgBitCount, LayoutMachine, labelCount, stateCount,
    reachableAlphabet, stmtPushSet]

example : tableauInputCount LayoutMachine 1 2 = 21 := by
  simp [tableauInputCount, tableauRowCount, cfgBitCount, LayoutMachine,
    labelCount, stateCount, reachableAlphabet, stmtPushSet]

example : (allocateTableauRows LayoutMachine 1 2).builder.gates.length = 21 := by
  rw [allocateTableauRows_gate_delta]
  simp [tableauInputCount, tableauRowCount, cfgBitCount, LayoutMachine,
    labelCount, stateCount, reachableAlphabet, stmtPushSet]

private def firstRow : Fin (tableauRowCount 2) := ⟨0, by decide⟩

private def middleRow : Fin (tableauRowCount 2) := ⟨1, by decide⟩

private def lastRow : Fin (tableauRowCount 2) := ⟨2, by decide⟩

-- A deliberately nonuniform assignment: rows zero and two are true while
-- row one is false at every coordinate.
private def layoutBits (row : Fin (tableauRowCount 2)) :
    CfgBits LayoutMachine 1 :=
  fun _ => decide (row.val % 2 = 0)

private def backgroundInputs (inputIndex : Nat) : Bool :=
  decide (inputIndex = 100)

-- Every row, not merely a selected sample coordinate, evaluates to its own
-- supplied bit bundle after serial allocation.
example (row : Fin (tableauRowCount 2)) :
    evalCfgBits (allocateTableauRows LayoutMachine 1 2).builder
        (writeTableauBits LayoutMachine 1 2 backgroundInputs layoutBits)
        ((allocateTableauRows LayoutMachine 1 2).rows row) =
      layoutBits row := by
  exact (allocateTableauRows LayoutMachine 1 2).evalCfgBits_writeTableau
    backgroundInputs layoutBits row

example :
    (evalCfgBits (allocateTableauRows LayoutMachine 1 2).builder
      (writeTableauBits LayoutMachine 1 2 backgroundInputs layoutBits)
      ((allocateTableauRows LayoutMachine 1 2).rows firstRow))
        (CfgSlot.halted LayoutMachine 1) = true := by
  change _ = layoutBits firstRow (CfgSlot.halted LayoutMachine 1)
  simpa only [writeTableauBits] using congrFun
    ((allocateTableauRows LayoutMachine 1 2).evalCfgBits_writeTableau
      backgroundInputs layoutBits firstRow)
    (CfgSlot.halted LayoutMachine 1)

example :
    (evalCfgBits (allocateTableauRows LayoutMachine 1 2).builder
      (writeTableauBits LayoutMachine 1 2 backgroundInputs layoutBits)
      ((allocateTableauRows LayoutMachine 1 2).rows middleRow))
        (CfgSlot.halted LayoutMachine 1) = false := by
  change _ = layoutBits middleRow (CfgSlot.halted LayoutMachine 1)
  simpa only [writeTableauBits] using congrFun
    ((allocateTableauRows LayoutMachine 1 2).evalCfgBits_writeTableau
      backgroundInputs layoutBits middleRow)
    (CfgSlot.halted LayoutMachine 1)

example :
    (evalCfgBits (allocateTableauRows LayoutMachine 1 2).builder
      (writeTableauBits LayoutMachine 1 2 backgroundInputs layoutBits)
      ((allocateTableauRows LayoutMachine 1 2).rows lastRow))
        (CfgSlot.halted LayoutMachine 1) = true := by
  change _ = layoutBits lastRow (CfgSlot.halted LayoutMachine 1)
  simpa only [writeTableauBits] using congrFun
    ((allocateTableauRows LayoutMachine 1 2).evalCfgBits_writeTableau
      backgroundInputs layoutBits lastRow)
    (CfgSlot.halted LayoutMachine 1)

-- The first and last rows are physically distinct allocations.
example :
    (allocateTableauRows LayoutMachine 1 2).rows firstRow
        (CfgSlot.halted LayoutMachine 1) ≠
      (allocateTableauRows LayoutMachine 1 2).rows lastRow
        (CfgSlot.halted LayoutMachine 1) := by
  apply allocateTableauRows_wire_ne
  decide

-- An offset write preserves assignments on both sides of the reserved block.
example :
    writeTableauBitsAt LayoutMachine 1 7 (tableauRowCount 2)
        backgroundInputs layoutBits 2 = backgroundInputs 2 := by
  apply writeTableauBitsAt_outside
  exact Or.inl (by decide)

example :
    writeTableauBitsAt LayoutMachine 1 7 (tableauRowCount 2)
        backgroundInputs layoutBits 100 = backgroundInputs 100 := by
  apply writeTableauBitsAt_outside
  right
  simp [tableauRowCount, cfgBitCount, LayoutMachine, labelCount,
    stateCount, reachableAlphabet, stmtPushSet]

end CLRS.Chapter34.Turing.CookLevin
