import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowFilter
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-!
# Full-cycle semantics for periodic marked-row filtering

This file isolates the arithmetic fact needed by Cook--Levin's repeated
transition layout: after exactly one selection-table width of marked rows,
the finite controller returns to table position zero.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Pair one finite selection-table suffix with one equally positioned row
suffix and encode exactly the retained marked rows. -/
def encodeUnaryFramePeriodicSelectedMarkedRows :
    List Bool → List (List Nat) → List UnaryFrameSym
  | keep :: keeps, row :: rows =>
      (if keep then encodeUnaryFrame row ++ [.frameEnd] else []) ++
        encodeUnaryFramePeriodicSelectedMarkedRows keeps rows
  | _, _ => []

/-- Starting at an arbitrary table position, consuming the complete remaining
table suffix returns to position zero before processing the tail. -/
theorem encodeUnaryFramePeriodicMarkedRowOutputFrom_cycle
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (rows rest : List (List Nat))
    (hlength : rows.length = selection.length - position.val) :
    encodeUnaryFramePeriodicMarkedRowOutputFrom selection hnonempty position
        (rows ++ rest) =
      encodeUnaryFramePeriodicSelectedMarkedRows
          (selection.drop position.val) rows ++
        encodeUnaryFramePeriodicMarkedRowOutputFrom selection hnonempty
          ⟨0, hnonempty⟩ rest := by
  induction rows generalizing position with
  | nil =>
      have hpositive : 0 < selection.length - position.val :=
        Nat.sub_pos_of_lt position.isLt
      simp only [List.length_nil] at hlength
      exact (Nat.ne_of_gt hpositive) hlength.symm |>.elim
  | cons row rows ih =>
      rw [List.drop_eq_getElem_cons position.isLt]
      simp only [List.cons_append,
        encodeUnaryFramePeriodicMarkedRowOutputFrom,
        encodeUnaryFramePeriodicSelectedMarkedRows]
      cases rows with
      | nil =>
          have hlast : ¬position.val + 1 < selection.length := by
            simp only [List.length_cons, List.length_nil] at hlength
            omega
          simp [unaryFramePeriodicMarkedRowFilterNext, hlast,
            encodeUnaryFramePeriodicSelectedMarkedRows]
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

/-- A concatenation of full-width row groups is filtered independently with
the same selection table on every group. -/
theorem encodeUnaryFramePeriodicMarkedRowOutput_groups
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (groups : List (List (List Nat)))
    (hlength : ∀ rows ∈ groups, rows.length = selection.length) :
    encodeUnaryFramePeriodicMarkedRowOutput selection hnonempty
        groups.flatten =
      groups.flatMap
        (encodeUnaryFramePeriodicSelectedMarkedRows selection) := by
  induction groups with
  | nil => rfl
  | cons rows groups ih =>
      unfold encodeUnaryFramePeriodicMarkedRowOutput
      simp only [List.flatten_cons, List.flatMap_cons]
      have hrows := hlength rows (by simp)
      rw [encodeUnaryFramePeriodicMarkedRowOutputFrom_cycle
        selection hnonempty ⟨0, hnonempty⟩ rows groups.flatten
        (by simpa using hrows)]
      have hgroups : ∀ group ∈ groups,
          group.length = selection.length := by
        intro group hgroup
        exact hlength group (by simp [hgroup])
      have hih := ih hgroups
      unfold encodeUnaryFramePeriodicMarkedRowOutput at hih
      rw [hih]
      simp

end CLRS.Chapter34.Turing.PolyBuilder
