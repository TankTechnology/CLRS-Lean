import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalStack
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSlotEnumeration

/-!
# Flattened wire values of transition-statement stack actions

The concrete transition source machine consumes and emits unary frames in
canonical row order.  This file is the small representation bridge between
the typed `StackWires` push/pop operations and that flat runtime order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Height wires of one stack in increasing height-coordinate order. -/
def transitionStackHeightWireValues
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    (stack : StackWires tm height k) : List Nat :=
  List.ofFn stack.height

/-- Cell-symbol wires grouped first by cell and then by symbol coordinate. -/
def transitionStackCellWireRows
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    (stack : StackWires tm height k) : List (List Nat) :=
  List.ofFn fun cell : Fin height => List.ofFn (stack.cell cell)

/-- Complete flat wire block of one stack in canonical tableau order. -/
def transitionStackWireValues
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    (stack : StackWires tm height k) : List Nat :=
  transitionStackHeightWireValues stack ++
    (transitionStackCellWireRows stack).flatten

/-- The explicit stack block is exactly the corresponding slice of the
canonical public-row slot enumeration. -/
theorem transitionStackWireValues_eq_slot_map
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) (k : tm.K) :
    transitionStackWireValues (source.stack k) =
      (transitionEqStackSlots tm height k).map source := by
  unfold transitionStackWireValues transitionStackHeightWireValues
    transitionStackCellWireRows transitionEqStackSlots
  rw [List.map_append, List.map_flatten, List.map_ofFn, List.map_ofFn]
  simp [CfgBundle.stack, CfgBundle.stackHeight, CfgBundle.stackCell,
    Function.comp_def]

/-- Fixed one-hot symbol row inserted at the top by a push. -/
def transitionPushedSymbolWireRow
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire : Nat) (symbol : SymbolWires tm k) : List Nat :=
  List.ofFn fun code : Fin ((reachableAlphabet tm k).card + 1) =>
    if h : code.val < (reachableAlphabet tm k).card then
      symbol ⟨code.val, h⟩
    else falseWire

/-- Fixed blank-symbol row appended at the bottom by a pop. -/
def transitionBlankSymbolWireRow
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire trueWire : Nat) : List Nat :=
  List.ofFn (arithmeticBlankHeadWires tm k falseWire trueWire)

/-- At positive capacity, push prepends the false height wire and drops the
old final height coordinate. -/
theorem arithmeticPushStackWires_height_values
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire : Nat) (symbol : SymbolWires tm k) (height : Nat)
    (source : StackWires tm height.succ k) :
    transitionStackHeightWireValues
        (arithmeticPushStackWires tm k falseWire symbol height.succ source) =
      falseWire ::
        List.ofFn (fun index : Fin height.succ =>
          source.height index.castSucc) := by
  cases height <;>
    simp [transitionStackHeightWireValues, arithmeticPushStackWires,
      List.ofFn_succ]

/-- At positive capacity, push prepends its mapped symbol row and drops the
old final physical cell. -/
theorem arithmeticPushStackWires_cell_rows
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire : Nat) (symbol : SymbolWires tm k) (height : Nat)
    (source : StackWires tm height.succ k) :
    transitionStackCellWireRows
        (arithmeticPushStackWires tm k falseWire symbol height.succ source) =
      transitionPushedSymbolWireRow tm k falseWire symbol ::
        List.ofFn (fun cell : Fin height =>
          List.ofFn (source.cell cell.castSucc)) := by
  cases height <;>
    simp [transitionStackCellWireRows, arithmeticPushStackWires,
      transitionPushedSymbolWireRow, List.ofFn_succ]

/-- At positive capacity, pop installs its fresh top-height wire, shifts all
remaining source heights by two, and ends with the false wire. -/
theorem arithmeticPopStackWires_height_values
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire trueWire start height : Nat)
    (source : StackWires tm height.succ k) :
    transitionStackHeightWireValues
        (arithmeticPopStackWires tm k falseWire trueWire start
          height.succ source) =
      start ::
        (List.ofFn (fun index : Fin height =>
          source.height ⟨index.val + 2, by omega⟩)).concat falseWire := by
  cases height with
  | zero =>
      simp [transitionStackHeightWireValues, arithmeticPopStackWires,
        List.ofFn_succ]
  | succ height =>
      unfold transitionStackHeightWireValues
      simp only [arithmeticPopStackWires]
      rw [List.ofFn_succ, List.ofFn_succ']
      simp only [Fin.val_zero, ↓reduceIte]
      congr 1
      congr 1
      · apply List.ofFn_inj.mpr
        funext index
        have hindex : index.val ≤ height := Nat.lt_succ_iff.mp index.isLt
        simp [hindex]
      · simp

/-- At positive capacity, pop shifts every surviving cell row toward the
top and appends the fixed blank-symbol row. -/
theorem arithmeticPopStackWires_cell_rows
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire trueWire start height : Nat)
    (source : StackWires tm height.succ k) :
    transitionStackCellWireRows
        (arithmeticPopStackWires tm k falseWire trueWire start
          height.succ source) =
      (List.ofFn (fun cell : Fin height =>
        List.ofFn (source.cell cell.succ))).concat
          (transitionBlankSymbolWireRow tm k falseWire trueWire) := by
  cases height with
  | zero =>
      simp [transitionStackCellWireRows, arithmeticPopStackWires,
        transitionBlankSymbolWireRow, List.ofFn_succ]
  | succ height =>
      unfold transitionStackCellWireRows transitionBlankSymbolWireRow
      simp only [arithmeticPopStackWires]
      rw [List.ofFn_succ']
      congr 1
      · apply List.ofFn_inj.mpr
        funext cell
        apply List.ofFn_inj.mpr
        funext symbol
        have hcell : cell.val ≤ height := Nat.lt_succ_iff.mp cell.isLt
        rw [dif_pos (by
          change cell.val + 1 < height + 1 + 1
          omega)]
        apply congrArg (fun position => source.cell position symbol)
        apply Fin.ext
        rfl
      · apply List.ofFn_inj.mpr
        funext symbol
        simp

end CLRS.Chapter34.Turing.CookLevin
