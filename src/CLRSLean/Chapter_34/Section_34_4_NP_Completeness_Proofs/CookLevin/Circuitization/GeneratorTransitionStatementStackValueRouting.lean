import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouting
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackValues
import Mathlib.Data.Fin.Tuple.Take

/-!
# List-valued routing of terminal statement stacks

After the heterogeneous action table has been split by stack, the remaining
push/pop semantics can be stated using ordinary lists.  This module records a
stack as its height-wire list and its cell-row list, defines the exact list
transformations for push and pop, and proves agreement with the typed
`StackWires` operations and their sequential fold.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Ordinary list representation of one stack's complete wire block. -/
@[ext] structure TransitionStackValueBlock where
  heightValues : List Nat
  cellRows : List (List Nat)
deriving DecidableEq, Repr

/-- Read the list representation from typed stack wires. -/
def TransitionStackValueBlock.ofWires
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    (source : StackWires tm height k) : TransitionStackValueBlock :=
  { heightValues := transitionStackHeightWireValues source
    cellRows := transitionStackCellWireRows source }

/-- Flatten a list-valued stack block in canonical tableau order. -/
def TransitionStackValueBlock.flatten
    (block : TransitionStackValueBlock) : List Nat :=
  block.heightValues ++ block.cellRows.flatten

@[simp] theorem TransitionStackValueBlock.flatten_ofWires
    {tm : _root_.Turing.FinTM2} {height : Nat} {k : tm.K}
    (source : StackWires tm height k) :
    (TransitionStackValueBlock.ofWires source).flatten =
      transitionStackWireValues source := by
  rfl

/-- Exact fixed-capacity list transformation performed by a push. -/
def TransitionStackValueBlock.push
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire : Nat) (symbol : SymbolWires tm k)
    (source : TransitionStackValueBlock) : TransitionStackValueBlock :=
  match height with
  | 0 =>
      { heightValues := [falseWire]
        cellRows := [] }
  | previous + 1 =>
      { heightValues := falseWire :: source.heightValues.take (previous + 1)
        cellRows := transitionPushedSymbolWireRow tm k falseWire symbol ::
          source.cellRows.take previous }

/-- Exact fixed-capacity list transformation performed by a pop. -/
def TransitionStackValueBlock.pop
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire trueWire start : Nat)
    (source : TransitionStackValueBlock) : TransitionStackValueBlock :=
  match height with
  | 0 => source
  | _ + 1 =>
      { heightValues := start :: source.heightValues.drop 2 ++ [falseWire]
        cellRows := source.cellRows.drop 1 ++
          [transitionBlankSymbolWireRow tm k falseWire trueWire] }

private theorem transitionStackHeightWireValues_take_castSucc
    (tm : _root_.Turing.FinTM2) (k : tm.K) (height : Nat)
    (source : StackWires tm height.succ k) :
    (transitionStackHeightWireValues source).take height.succ =
      List.ofFn (fun index : Fin height.succ =>
        source.height index.castSucc) := by
  unfold transitionStackHeightWireValues
  rw [← Fin.ofFn_take_eq_take_ofFn (m := height.succ) (by omega)
    source.height]
  apply List.ofFn_inj.mpr
  funext index
  rfl

private theorem transitionStackCellWireRows_take
    (tm : _root_.Turing.FinTM2) (k : tm.K) (height : Nat)
    (source : StackWires tm height.succ k) :
    (transitionStackCellWireRows source).take height =
      List.ofFn (fun cell : Fin height =>
        List.ofFn (source.cell cell.castSucc)) := by
  unfold transitionStackCellWireRows
  rw [← Fin.ofFn_take_eq_take_ofFn (m := height) (by omega)
    (fun cell : Fin height.succ => List.ofFn (source.cell cell))]
  apply List.ofFn_inj.mpr
  funext cell
  rfl

private theorem transitionStackHeightWireValues_drop_two
    (tm : _root_.Turing.FinTM2) (k : tm.K) (height : Nat)
    (source : StackWires tm height.succ k) :
    (transitionStackHeightWireValues source).drop 2 =
      List.ofFn (fun index : Fin height =>
        source.height ⟨index.val + 2, by omega⟩) := by
  apply List.ext_get
  · simp [transitionStackHeightWireValues]
  · intro index hleft hright
    simp [transitionStackHeightWireValues]

private theorem transitionStackCellWireRows_drop_one
    (tm : _root_.Turing.FinTM2) (k : tm.K) (height : Nat)
    (source : StackWires tm height.succ k) :
    (transitionStackCellWireRows source).drop 1 =
      List.ofFn (fun cell : Fin height =>
        List.ofFn (source.cell cell.succ)) := by
  apply List.ext_get
  · simp [transitionStackCellWireRows]
  · intro index hleft hright
    simp [transitionStackCellWireRows]

/-- The typed push operation is exactly the ordinary list transformation. -/
theorem TransitionStackValueBlock.ofWires_push
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire : Nat) (symbol : SymbolWires tm k)
    (source : StackWires tm height k) :
    TransitionStackValueBlock.ofWires
        (arithmeticPushStackWires tm k falseWire symbol height source) =
      (TransitionStackValueBlock.ofWires source).push tm k height falseWire
        symbol := by
  cases height with
  | zero =>
      apply TransitionStackValueBlock.ext <;>
        simp [TransitionStackValueBlock.ofWires,
          TransitionStackValueBlock.push,
          transitionStackHeightWireValues, transitionStackCellWireRows,
          arithmeticPushStackWires]
  | succ height =>
      apply TransitionStackValueBlock.ext
      · simp only [TransitionStackValueBlock.ofWires,
          TransitionStackValueBlock.push]
        rw [arithmeticPushStackWires_height_values]
        rw [transitionStackHeightWireValues_take_castSucc]
      · simp only [TransitionStackValueBlock.ofWires,
          TransitionStackValueBlock.push]
        rw [arithmeticPushStackWires_cell_rows]
        rw [transitionStackCellWireRows_take]

/-- The typed pop operation is exactly the ordinary list transformation. -/
theorem TransitionStackValueBlock.ofWires_pop
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire trueWire start : Nat)
    (source : StackWires tm height k) :
    TransitionStackValueBlock.ofWires
        (arithmeticPopStackWires tm k falseWire trueWire start height source) =
      (TransitionStackValueBlock.ofWires source).pop tm k height falseWire
        trueWire start := by
  cases height with
  | zero => rfl
  | succ height =>
      apply TransitionStackValueBlock.ext
      · simp only [TransitionStackValueBlock.ofWires,
          TransitionStackValueBlock.pop]
        rw [arithmeticPopStackWires_height_values]
        rw [transitionStackHeightWireValues_drop_two]
        simp [List.concat_eq_append]
      · simp only [TransitionStackValueBlock.ofWires,
          TransitionStackValueBlock.pop]
        rw [arithmeticPopStackWires_cell_rows]
        rw [transitionStackCellWireRows_drop_one]
        simp [List.concat_eq_append]

/-- List-valued semantics of one selected-stack action. -/
def TransitionStmtSelectedStackAction.evalValues
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : TransitionStackValueBlock) :
    TransitionStmtSelectedStackAction tm k → TransitionStackValueBlock
  | .push symbolOffsets =>
      source.push tm k height falseWire
        (fun target => originStart + (symbolOffsets target).eval height)
  | .pop heightWireOffset =>
      source.pop tm k height falseWire trueWire
        (originStart + heightWireOffset.eval height)

/-- One selected action commutes with erasing typed wires to ordinary lists. -/
theorem TransitionStmtSelectedStackAction.ofWires_eval
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : StackWires tm height k)
    (action : TransitionStmtSelectedStackAction tm k) :
    TransitionStackValueBlock.ofWires
        (action.eval tm k originStart height falseWire trueWire source) =
      action.evalValues tm k originStart height falseWire trueWire
        (TransitionStackValueBlock.ofWires source) := by
  cases action with
  | push symbolOffsets =>
      exact TransitionStackValueBlock.ofWires_push tm k height falseWire _
        source
  | pop heightWireOffset =>
      exact TransitionStackValueBlock.ofWires_pop tm k height falseWire
        trueWire _ source

/-- Sequential list-valued execution of one stack's action subsequence. -/
def transitionStmtSelectedStackActionValues_eval
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : TransitionStackValueBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    TransitionStackValueBlock :=
  actions.foldl
    (fun current action =>
      action.evalValues tm k originStart height falseWire trueWire current)
    source

/-- Erasing typed stack wires commutes with the complete selected action fold. -/
theorem transitionStmtSelectedStackActions_eval_values
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : StackWires tm height k)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    TransitionStackValueBlock.ofWires
        (transitionStmtSelectedStackActions_eval tm k originStart height
          falseWire trueWire source actions) =
      transitionStmtSelectedStackActionValues_eval tm k originStart height
        falseWire trueWire (TransitionStackValueBlock.ofWires source)
        actions := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih =>
      change TransitionStackValueBlock.ofWires
          (transitionStmtSelectedStackActions_eval tm k originStart height
            falseWire trueWire
            (action.eval tm k originStart height falseWire trueWire source)
            rest) = _
      rw [ih]
      rw [action.ofWires_eval tm k originStart height falseWire trueWire
        source]
      rfl

/-- Canonical flat values of a projected global action fold are exactly the
flattened result of its independent list-valued stack route. -/
theorem transitionStmtStackActions_eval_stack_values
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (actions : List (TransitionStmtStackAction tm)) :
    transitionStackWireValues
        ((transitionStmtStackActions_eval tm originStart height falseWire
          trueWire source actions).stack target) =
      (transitionStmtSelectedStackActionValues_eval tm target originStart
        height falseWire trueWire
        (TransitionStackValueBlock.ofWires (source.stack target))
        (transitionStmtStackActionsFor tm target actions)).flatten := by
  rw [transitionStmtStackActions_eval_stack_eq_selected]
  rw [← TransitionStackValueBlock.flatten_ofWires]
  rw [transitionStmtSelectedStackActions_eval_values]

end CLRS.Chapter34.Turing.CookLevin
