import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackValueRouting

/-!
# Shape invariants for list-valued terminal stack routes

The ordinary-list stack representation is useful to a source compiler only
when every intermediate push/pop route keeps the canonical fixed-capacity
shape.  This module packages that invariant and proves it for typed source
wires, each primitive action, and the complete selected-action fold.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Canonical list shape of one stack block at a fixed workspace capacity. -/
def TransitionStackValueBlock.HasShape
    (tm : _root_.Turing.FinTM2) (k : tm.K) (height : Nat)
    (block : TransitionStackValueBlock) : Prop :=
  block.heightValues.length = height + 1 ∧
    block.cellRows.length = height ∧
      ∀ row ∈ block.cellRows,
        row.length = (reachableAlphabet tm k).card + 1

/-- Erasing typed stack wires always produces a canonically shaped block. -/
theorem TransitionStackValueBlock.hasShape_ofWires
    (tm : _root_.Turing.FinTM2) (k : tm.K) (height : Nat)
    (source : StackWires tm height k) :
    (TransitionStackValueBlock.ofWires source).HasShape tm k height := by
  simp [TransitionStackValueBlock.HasShape,
    TransitionStackValueBlock.ofWires,
    transitionStackHeightWireValues, transitionStackCellWireRows]

/-- A pushed symbol row has exactly the machine-fixed alphabet width. -/
@[simp] theorem transitionPushedSymbolWireRow_length
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire : Nat) (symbol : SymbolWires tm k) :
    (transitionPushedSymbolWireRow tm k falseWire symbol).length =
      (reachableAlphabet tm k).card + 1 := by
  simp [transitionPushedSymbolWireRow]

/-- A blank row appended by pop has the same machine-fixed alphabet width. -/
@[simp] theorem transitionBlankSymbolWireRow_length
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire trueWire : Nat) :
    (transitionBlankSymbolWireRow tm k falseWire trueWire).length =
      (reachableAlphabet tm k).card + 1 := by
  simp [transitionBlankSymbolWireRow]

/-- Fixed-capacity push preserves the complete list shape. -/
theorem TransitionStackValueBlock.HasShape.push
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire : Nat) (symbol : SymbolWires tm k)
    (source : TransitionStackValueBlock)
    (hsource : source.HasShape tm k height) :
    (source.push tm k height falseWire symbol).HasShape tm k height := by
  rcases hsource with ⟨hheight, hcells, hrows⟩
  cases height with
  | zero =>
      simp [TransitionStackValueBlock.push,
        TransitionStackValueBlock.HasShape]
  | succ height =>
      constructor
      · simp [TransitionStackValueBlock.push, List.length_take, hheight]
      · constructor
        · simp [TransitionStackValueBlock.push, List.length_take, hcells]
        · intro row hrow
          simp only [TransitionStackValueBlock.push, List.mem_cons] at hrow
          rcases hrow with rfl | hrow
          · simp
          · exact hrows row (List.mem_of_mem_take hrow)

/-- Fixed-capacity pop preserves the complete list shape. -/
theorem TransitionStackValueBlock.HasShape.pop
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire trueWire start : Nat)
    (source : TransitionStackValueBlock)
    (hsource : source.HasShape tm k height) :
    (source.pop tm k height falseWire trueWire start).HasShape tm k height := by
  rcases hsource with ⟨hheight, hcells, hrows⟩
  cases height with
  | zero =>
      simpa [TransitionStackValueBlock.pop] using
        ⟨hheight, hcells, hrows⟩
  | succ height =>
      constructor
      · simp [TransitionStackValueBlock.pop, List.length_drop, hheight]
      · constructor
        · simp [TransitionStackValueBlock.pop, hcells]
        · intro row hrow
          simp only [TransitionStackValueBlock.pop, List.mem_append,
            List.mem_singleton] at hrow
          rcases hrow with hrow | rfl
          · exact hrows row (List.mem_of_mem_drop hrow)
          · simp

/-- The list semantics of either selected primitive action preserves shape. -/
theorem TransitionStmtSelectedStackAction.evalValues_hasShape
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : TransitionStackValueBlock)
    (action : TransitionStmtSelectedStackAction tm k)
    (hsource : source.HasShape tm k height) :
    (action.evalValues tm k originStart height falseWire trueWire source).HasShape
      tm k height := by
  cases action with
  | push symbolOffsets => exact hsource.push tm k height falseWire _
  | pop heightWireOffset => exact hsource.pop tm k height falseWire trueWire _

/-- Every intermediate block in the complete fixed action fold has the same
canonical capacity and row width as its source. -/
theorem transitionStmtSelectedStackActionValues_eval_hasShape
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : TransitionStackValueBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k))
    (hsource : source.HasShape tm k height) :
    (transitionStmtSelectedStackActionValues_eval tm k originStart height
      falseWire trueWire source actions).HasShape tm k height := by
  induction actions generalizing source with
  | nil => exact hsource
  | cons action rest ih =>
      apply ih
      exact action.evalValues_hasShape tm k originStart height falseWire
        trueWire source hsource

private theorem sum_map_length_eq_mul_of_forall
    (rows : List (List Nat)) (width : Nat)
    (hrows : ∀ row ∈ rows, row.length = width) :
    (rows.map List.length).sum = rows.length * width := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
      have hrow := hrows row (by simp)
      have hrest : ∀ item ∈ rest, item.length = width := by
        intro item hitem
        exact hrows item (by simp [hitem])
      simp [hrow, ih hrest, Nat.add_mul, Nat.add_comm]

/-- A shaped block has exactly the canonical flattened stack width. -/
theorem TransitionStackValueBlock.HasShape.flatten_length
    (tm : _root_.Turing.FinTM2) (k : tm.K) (height : Nat)
    (block : TransitionStackValueBlock)
    (hshape : block.HasShape tm k height) :
    block.flatten.length =
      height + 1 + height * ((reachableAlphabet tm k).card + 1) := by
  rcases hshape with ⟨hheight, hcells, hrows⟩
  unfold TransitionStackValueBlock.flatten
  rw [List.length_append, List.length_flatten]
  rw [sum_map_length_eq_mul_of_forall block.cellRows
    ((reachableAlphabet tm k).card + 1) hrows]
  rw [hheight, hcells]

/-- The same width stated using the canonical tableau stack-width function. -/
theorem TransitionStackValueBlock.HasShape.flatten_length_eq_cfgStackBitWidth
    (tm : _root_.Turing.FinTM2) (k : tm.K) (height : Nat)
    (block : TransitionStackValueBlock)
    (hshape : block.HasShape tm k height) :
    block.flatten.length = cfgStackBitWidth tm height k := by
  simpa [cfgStackBitWidth] using hshape.flatten_length tm k height block

end CLRS.Chapter34.Turing.CookLevin
