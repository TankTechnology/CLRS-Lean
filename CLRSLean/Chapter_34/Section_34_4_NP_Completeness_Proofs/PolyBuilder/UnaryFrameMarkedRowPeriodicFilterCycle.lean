import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowPeriodicFilter
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-!
# Full-cycle and one-hot semantics for arbitrary marked rows

This file identifies the output of the periodic marked-row controller on
full-width groups and specializes it to a single fixed position per group.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Pair one selection suffix with one row suffix. -/
def selectUnaryFrameMarkedRowsCycle :
    List Bool → List (List UnaryFrameSym) → List (List UnaryFrameSym)
  | keep :: keeps, row :: rows =>
      (if keep then [row] else []) ++
        selectUnaryFrameMarkedRowsCycle keeps rows
  | _, _ => []

/-- Consuming the remainder of a full table cycle returns the selector to
position zero. -/
theorem selectUnaryFrameMarkedRowsFrom_cycle
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (rows rest : List (List UnaryFrameSym))
    (hlength : rows.length = selection.length - position.val) :
    selectUnaryFrameMarkedRowsFrom selection hnonempty position
        (rows ++ rest) =
      selectUnaryFrameMarkedRowsCycle (selection.drop position.val) rows ++
        selectUnaryFrameMarkedRowsFrom selection hnonempty
          ⟨0, hnonempty⟩ rest := by
  induction rows generalizing position with
  | nil =>
      have hpositive : 0 < selection.length - position.val :=
        Nat.sub_pos_of_lt position.isLt
      simp only [List.length_nil] at hlength
      exact (Nat.ne_of_gt hpositive) hlength.symm |>.elim
  | cons row rows ih =>
      rw [List.drop_eq_getElem_cons position.isLt]
      simp only [List.cons_append, selectUnaryFrameMarkedRowsFrom,
        selectUnaryFrameMarkedRowsCycle]
      cases rows with
      | nil =>
          have hlast : ¬position.val + 1 < selection.length := by
            simp only [List.length_cons, List.length_nil] at hlength
            omega
          simp [unaryFramePeriodicMarkedRowFilterNext, hlast,
            selectUnaryFrameMarkedRowsCycle]
      | cons next rows =>
          have hnext : position.val + 1 < selection.length := by
            simp only [List.length_cons] at hlength
            omega
          have htail :
              (next :: rows).length =
                selection.length - (position.val + 1) := by
            simp only [List.length_cons] at hlength ⊢
            omega
          rw [show unaryFramePeriodicMarkedRowFilterNext selection hnonempty
                position = ⟨position.val + 1, hnext⟩ by
              simp [unaryFramePeriodicMarkedRowFilterNext, hnext]]
          rw [ih ⟨position.val + 1, hnext⟩ htail]
          simp [List.append_assoc]

/-- Full-width groups are selected independently. -/
theorem selectUnaryFrameMarkedRows_groups
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (groups : List (List (List UnaryFrameSym)))
    (hlength : ∀ rows ∈ groups, rows.length = selection.length) :
    selectUnaryFrameMarkedRows selection hnonempty groups.flatten =
      groups.flatMap (selectUnaryFrameMarkedRowsCycle selection) := by
  induction groups with
  | nil => rfl
  | cons rows groups ih =>
      unfold selectUnaryFrameMarkedRows
      simp only [List.flatten_cons, List.flatMap_cons]
      have hrows := hlength rows (by simp)
      rw [selectUnaryFrameMarkedRowsFrom_cycle selection hnonempty
        ⟨0, hnonempty⟩ rows groups.flatten (by simpa using hrows)]
      have hgroups : ∀ group ∈ groups,
          group.length = selection.length := by
        intro group hgroup
        exact hlength group (by simp [hgroup])
      have hih := ih hgroups
      unfold selectUnaryFrameMarkedRows at hih
      rw [hih]
      simp

/-- Boolean table retaining only one fixed position in a nonempty cycle. -/
def unaryFrameMarkedRowOneHotSelection
    (width : Nat) (position : Fin width) : List Bool :=
  List.replicate position.val false ++
    true :: List.replicate (width - position.val - 1) false

@[simp] theorem unaryFrameMarkedRowOneHotSelection_length
    (width : Nat) (position : Fin width) :
    (unaryFrameMarkedRowOneHotSelection width position).length = width := by
  simp [unaryFrameMarkedRowOneHotSelection]
  omega

theorem unaryFrameMarkedRowOneHotSelection_nonempty
    (width : Nat) (position : Fin width) :
    0 < (unaryFrameMarkedRowOneHotSelection width position).length := by
  rw [unaryFrameMarkedRowOneHotSelection_length]
  exact Nat.zero_lt_of_lt position.isLt

private theorem selectUnaryFrameMarkedRowsCycle_allFalse
    (rows : List (List UnaryFrameSym)) :
    selectUnaryFrameMarkedRowsCycle
        (List.replicate rows.length false) rows = [] := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change selectUnaryFrameMarkedRowsCycle
        (List.replicate (Nat.succ rows.length) false) (row :: rows) = []
      rw [List.replicate_succ]
      simp only [selectUnaryFrameMarkedRowsCycle]
      exact ih

/-- A one-hot table retains the distinguished row and no other row. -/
theorem selectUnaryFrameMarkedRowsCycle_oneHot
    (before after : List (List UnaryFrameSym))
    (row : List UnaryFrameSym) :
    selectUnaryFrameMarkedRowsCycle
        (List.replicate before.length false ++
          true :: List.replicate after.length false)
        (before ++ row :: after) = [row] := by
  induction before with
  | nil =>
      simp [selectUnaryFrameMarkedRowsCycle,
        selectUnaryFrameMarkedRowsCycle_allFalse]
  | cons head before ih =>
      change selectUnaryFrameMarkedRowsCycle
        (List.replicate (Nat.succ before.length) false ++
          true :: List.replicate after.length false)
        (head :: before ++ row :: after) = [row]
      rw [List.replicate_succ]
      simp only [List.cons_append, selectUnaryFrameMarkedRowsCycle]
      exact ih

/-- In every full-width group, the one-hot table selects its fixed indexed
row. -/
theorem selectUnaryFrameMarkedRowsCycle_oneHot_get
    (width : Nat) (position : Fin width)
    (rows : List (List UnaryFrameSym))
    (hlength : rows.length = width) :
    selectUnaryFrameMarkedRowsCycle
        (unaryFrameMarkedRowOneHotSelection width position) rows =
      [rows.getD position.val []] := by
  have hposition : position.val < rows.length := by omega
  have hsplit :
      rows = rows.take position.val ++
        rows[position.val] :: rows.drop (position.val + 1) := by
    calc
      rows = rows.take position.val ++ rows.drop position.val :=
        (List.take_append_drop position.val rows).symm
      _ = rows.take position.val ++
          rows[position.val] :: rows.drop (position.val + 1) := by
        rw [List.drop_eq_getElem_cons hposition]
  conv_lhs => rw [hsplit]
  have htake : (rows.take position.val).length = position.val := by
    simp [Nat.min_eq_left (Nat.le_of_lt hposition)]
  have hdrop :
      (rows.drop (position.val + 1)).length =
        width - position.val - 1 := by
    simp [hlength]
    omega
  have hselection :
      unaryFrameMarkedRowOneHotSelection width position =
        List.replicate (rows.take position.val).length false ++
          true ::
            List.replicate (rows.drop (position.val + 1)).length false := by
    unfold unaryFrameMarkedRowOneHotSelection
    rw [htake, hdrop]
  rw [hselection]
  rw [selectUnaryFrameMarkedRowsCycle_oneHot]
  rw [List.getD_eq_getElem rows [] hposition]

/-- Selecting one position from every full-width group yields exactly one
row per group, in group order. -/
theorem selectUnaryFrameMarkedRows_groups_oneHot
    (width : Nat) (position : Fin width)
    (groups : List (List (List UnaryFrameSym)))
    (hlength : ∀ rows ∈ groups, rows.length = width) :
    selectUnaryFrameMarkedRows
        (unaryFrameMarkedRowOneHotSelection width position)
        (unaryFrameMarkedRowOneHotSelection_nonempty width position)
        groups.flatten =
      groups.map fun rows => rows.getD position.val [] := by
  rw [selectUnaryFrameMarkedRows_groups]
  · induction groups with
    | nil => rfl
    | cons rows groups ih =>
        simp only [List.flatMap_cons, List.map_cons]
        rw [selectUnaryFrameMarkedRowsCycle_oneHot_get width position rows
          (hlength rows (by simp))]
        rw [ih (by
          intro group hgroup
          exact hlength group (by simp [hgroup]))]
        rfl
  · intro rows hrows
    rw [unaryFrameMarkedRowOneHotSelection_length]
    exact hlength rows hrows

end CLRS.Chapter34.Turing.PolyBuilder
