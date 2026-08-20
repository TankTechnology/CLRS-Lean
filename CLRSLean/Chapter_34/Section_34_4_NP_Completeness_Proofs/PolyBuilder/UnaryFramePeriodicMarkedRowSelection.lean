import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowFilterCycle
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionRowMark
import Mathlib.Tactic

/-!
# Semantic selection for periodic marked rows

The streaming controller uses a finite Boolean table.  This file gives that
table a list-level meaning and proves that the marked unary encoding preserves
the selected rows exactly.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Retain list elements whose corresponding Boolean table entry is true. -/
def selectListByBool {α : Type} : List Bool → List α → List α
  | keep :: keeps, value :: values =>
      if keep then value :: selectListByBool keeps values
      else selectListByBool keeps values
  | _, _ => []

/-- Selected marked-row encoding is the row encoding of list-level selection. -/
theorem encodeUnaryFramePeriodicSelectedMarkedRows_eq
    (selection : List Bool) (rows : List (List Nat)) :
    encodeUnaryFramePeriodicSelectedMarkedRows selection rows =
      (selectListByBool selection rows).flatMap fun row =>
        encodeUnaryFrame row ++ [.frameEnd] := by
  induction selection generalizing rows with
  | nil => rfl
  | cons keep selection ih =>
      cases rows with
      | nil => rfl
      | cons row rows =>
          cases keep <;>
            simp [encodeUnaryFramePeriodicSelectedMarkedRows,
              selectListByBool, ih]

/-- Boolean selection commutes with an elementwise map. -/
theorem selectListByBool_map {α β : Type} (selection : List Bool)
    (values : List α) (f : α → β) :
    selectListByBool selection (values.map f) =
      (selectListByBool selection values).map f := by
  induction selection generalizing values with
  | nil => rfl
  | cons keep selection ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          cases keep <;> simp [selectListByBool, ih]

/-- A selected progression descriptor family has exactly the canonical marked
encoding of the selected progressions. -/
theorem encodeUnaryFramePeriodicSelectedMarkedProgressions
    (selection : List Bool)
    (progressions : List AffineUnaryTripleProgression) :
    encodeUnaryFramePeriodicSelectedMarkedRows selection
        (progressions.map affineUnaryTripleProgressionFields) =
      encodeAffineUnaryTripleProgressionMarkedFamily
        (selectListByBool selection progressions) := by
  rw [encodeUnaryFramePeriodicSelectedMarkedRows_eq]
  rw [selectListByBool_map]
  unfold encodeAffineUnaryTripleProgressionMarkedFamily
  rw [List.flatMap_map]
  rfl

/-- Selection distributes across paired append blocks when the first mask and
value block have the same length. -/
theorem selectListByBool_append {α : Type}
    (leftSelection rightSelection : List Bool)
    (leftValues rightValues : List α)
    (hlength : leftSelection.length = leftValues.length) :
    selectListByBool (leftSelection ++ rightSelection)
        (leftValues ++ rightValues) =
      selectListByBool leftSelection leftValues ++
        selectListByBool rightSelection rightValues := by
  induction leftSelection generalizing leftValues with
  | nil =>
      simp only [List.length_nil] at hlength
      cases leftValues <;> simp_all [selectListByBool]
  | cons keep selection ih =>
      cases leftValues with
      | nil => simp at hlength
      | cons value values =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          cases keep <;>
            simp [selectListByBool, ih values hlength]

/-- An all-false mask selects no values. -/
@[simp] theorem selectListByBool_replicate_false {α : Type}
    (count : Nat) (values : List α) :
    selectListByBool (List.replicate count false) values = [] := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      cases values <;> simp [List.replicate_succ, selectListByBool, ih]

/-- An all-true mask selects the corresponding value prefix. -/
@[simp] theorem selectListByBool_replicate_true {α : Type}
    (count : Nat) (values : List α) :
    selectListByBool (List.replicate count true) values =
      values.take count := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      cases values <;> simp [List.replicate_succ, selectListByBool, ih]

/-- Selection over flattened paired blocks is the flattened family of local
selections. -/
theorem selectListByBool_flatMap {ι α : Type}
    (indices : List ι) (selection : ι → List Bool)
    (values : ι → List α)
    (hlength : ∀ index ∈ indices,
      (selection index).length = (values index).length) :
    selectListByBool (indices.flatMap selection)
        (indices.flatMap values) =
      indices.flatMap fun index =>
        selectListByBool (selection index) (values index) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.flatMap_cons]
      have hhead := hlength index (by simp)
      rw [selectListByBool_append _ _ _ _ hhead]
      apply congrArg (selectListByBool (selection index) (values index) ++ ·)
      apply ih
      intro next hnext
      exact hlength next (by simp [hnext])

end CLRS.Chapter34.Turing.PolyBuilder
