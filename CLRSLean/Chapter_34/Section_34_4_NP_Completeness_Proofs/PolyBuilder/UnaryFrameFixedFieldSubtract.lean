import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import Mathlib.Tactic

/-!
# Saturating subtraction on one fixed unary-frame field

Affine progression descriptors occasionally need a count such as `height - c`,
where `c` is fixed by the verifier.  This module implements that operation as
a streaming finite-state pass: in one fixed field of every row it erases the
first `c` ticks and copies every other symbol.  Unary erasure is exactly
saturating natural subtraction, including all small-height cases.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- A semantic row split immediately before the selected field. -/
structure UnaryFrameFixedFieldSubtractRow (target : Nat) where
  leading : List Nat
  leading_length : leading.length = target
  selected : Nat
  suffix : List Nat
deriving DecidableEq, Repr

/-- Source rows before subtracting from the selected field. -/
def encodeUnaryFrameFixedFieldSubtractInput (target : Nat)
    (rows : List (UnaryFrameFixedFieldSubtractRow target)) :
    List UnaryFrameSym :=
  rows.flatMap fun row =>
    encodeUnaryFrame (row.leading ++ row.selected :: row.suffix) ++
      [.frameEnd]

/-- Target rows after saturating subtraction in the selected field. -/
def encodeUnaryFrameFixedFieldSubtractOutput (target amount : Nat)
    (rows : List (UnaryFrameFixedFieldSubtractRow target)) :
    List UnaryFrameSym :=
  rows.flatMap fun row =>
    encodeUnaryFrame
        (row.leading ++ (row.selected - amount) :: row.suffix) ++
      [.frameEnd]

/-- Finite streaming phase.  `before` exists only while scanning one of the
fixed fields preceding `target`; `selected` stores only the verifier-fixed
number of ticks still to erase. -/
inductive UnaryFrameFixedFieldSubtractMode (target amount : Nat)
  | before (position : Fin target)
  | selected (remaining : Fin (amount + 1))
  | after
deriving DecidableEq, Fintype

def unaryFrameFixedFieldSubtractInitialMode (target amount : Nat) :
    UnaryFrameFixedFieldSubtractMode target amount :=
  if htarget : 0 < target then .before ⟨0, htarget⟩
  else .selected ⟨amount, by omega⟩

private def unaryFrameFixedFieldSubtractRemaining (amount : Nat) :
    Fin (amount + 1) :=
  ⟨amount, by omega⟩

private def unaryFrameFixedFieldSubtractPred {amount : Nat}
    (remaining : Fin (amount + 1)) (_hpositive : remaining.val ≠ 0) :
    Fin (amount + 1) :=
  ⟨remaining.val - 1, by omega⟩

/-- One pure streaming action.  Only selected-field ticks can be erased. -/
def unaryFrameFixedFieldSubtractAction (target amount : Nat)
    (mode : UnaryFrameFixedFieldSubtractMode target amount)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFrameFixedFieldSubtractMode target amount :=
  match mode with
  | .before position =>
      match symbol with
      | .tick => (some .tick, .before position)
      | .separator =>
          if hnext : position.val + 1 < target then
            (some .separator, .before ⟨position.val + 1, hnext⟩)
          else
            (some .separator,
              .selected (unaryFrameFixedFieldSubtractRemaining amount))
      | .frameEnd =>
          (some .frameEnd,
            unaryFrameFixedFieldSubtractInitialMode target amount)
  | .selected remaining =>
      match symbol with
      | .tick =>
          if hzero : remaining.val = 0 then
            (some .tick, .selected remaining)
          else
            (none, .selected
              (unaryFrameFixedFieldSubtractPred remaining hzero))
      | .separator => (some .separator, .after)
      | .frameEnd =>
          (some .frameEnd,
            unaryFrameFixedFieldSubtractInitialMode target amount)
  | .after =>
      match symbol with
      | .frameEnd =>
          (some .frameEnd,
            unaryFrameFixedFieldSubtractInitialMode target amount)
      | other => (some other, .after)

def unaryFrameFixedFieldSubtractSpec (target amount : Nat) :
    UnaryFrameStatefulMapSpec
      (UnaryFrameFixedFieldSubtractMode target amount) :=
  { initial := unaryFrameFixedFieldSubtractInitialMode target amount
    action := unaryFrameFixedFieldSubtractAction target amount }

def rewriteUnaryFrameFixedFieldSubtract (target amount : Nat)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFrameFixedFieldSubtractSpec target amount) input

private theorem fixedFieldSubtract_before_ticks
    (target amount : Nat) (position : Fin target)
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedFieldSubtractSpec target amount)
        (.before position) (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedFieldSubtractSpec target amount)
          (.before position) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedFieldSubtractSpec,
        unaryFrameFixedFieldSubtractAction]
      exact congrArg (List.cons .tick) ih

private theorem fixedFieldSubtract_before_separator
    (target amount : Nat) (position : Fin target)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedFieldSubtractSpec target amount)
        (.before position) (.separator :: tail) =
      .separator ::
        if hnext : position.val + 1 < target then
          rewriteUnaryFrameStatefulFrom
            (unaryFrameFixedFieldSubtractSpec target amount)
            (.before ⟨position.val + 1, hnext⟩) tail
        else
          rewriteUnaryFrameStatefulFrom
            (unaryFrameFixedFieldSubtractSpec target amount)
            (.selected (unaryFrameFixedFieldSubtractRemaining amount))
            tail := by
  simp [rewriteUnaryFrameStatefulFrom,
    unaryFrameFixedFieldSubtractSpec,
    unaryFrameFixedFieldSubtractAction]
  split_ifs <;> rfl

private theorem fixedFieldSubtract_before_values
    (target amount position : Nat) (hposition : position < target)
    (values : List Nat) (tail : List UnaryFrameSym)
    (hfit : position + values.length = target) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedFieldSubtractSpec target amount)
        (.before ⟨position, hposition⟩)
        (encodeUnaryFrame values ++ tail) =
      encodeUnaryFrame values ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedFieldSubtractSpec target amount)
          (.selected (unaryFrameFixedFieldSubtractRemaining amount))
          tail := by
  induction values generalizing position with
  | nil => simp at hfit; omega
  | cons value values ih =>
      have hnextFit : position + 1 + values.length = target := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [fixedFieldSubtract_before_ticks]
      rw [fixedFieldSubtract_before_separator]
      by_cases hnext : position + 1 < target
      · simp only [dif_pos hnext]
        rw [ih (position + 1) hnext hnextFit]
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]
      · simp only [dif_neg hnext]
        have hvalues : values = [] := by
          cases values with
          | nil => rfl
          | cons head rest =>
              simp only [List.length_cons] at hnextFit
              omega
        subst values
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

private theorem fixedFieldSubtract_selected_ticks
    (target amount : Nat) (remaining : Fin (amount + 1))
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedFieldSubtractSpec target amount)
        (.selected remaining)
        (List.replicate count .tick ++ .separator :: tail) =
      List.replicate (count - remaining.val) .tick ++ .separator ::
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedFieldSubtractSpec target amount) .after tail := by
  induction count generalizing remaining with
  | zero =>
      simp [rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedFieldSubtractSpec,
        unaryFrameFixedFieldSubtractAction]
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [rewriteUnaryFrameStatefulFrom]
      by_cases hzero : remaining.val = 0
      · have haction :
            (unaryFrameFixedFieldSubtractSpec target amount).action
                (.selected remaining) .tick =
              (some .tick, .selected remaining) := by
          simp [unaryFrameFixedFieldSubtractSpec,
            unaryFrameFixedFieldSubtractAction, hzero]
        rw [haction]
        simp only
        rw [ih remaining]
        simp only [hzero, Nat.sub_zero]
        rfl
      · let previous := unaryFrameFixedFieldSubtractPred remaining hzero
        have haction :
            (unaryFrameFixedFieldSubtractSpec target amount).action
                (.selected remaining) .tick =
              (none, .selected previous) := by
          simp [unaryFrameFixedFieldSubtractSpec,
            unaryFrameFixedFieldSubtractAction, hzero, previous]
        rw [haction]
        simp only
        have hsub : Nat.succ count - remaining.val =
            count - previous.val := by
          simp [previous, unaryFrameFixedFieldSubtractPred]
          omega
        rw [ih previous]
        rw [hsub]

private theorem fixedFieldSubtract_after_run
    (target amount : Nat) (payload tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ payload, symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedFieldSubtractSpec target amount) .after
        (payload ++ .frameEnd :: tail) =
      payload ++ .frameEnd ::
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedFieldSubtractSpec target amount)
          (unaryFrameFixedFieldSubtractInitialMode target amount) tail := by
  induction payload with
  | nil =>
      simp [rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedFieldSubtractSpec,
        unaryFrameFixedFieldSubtractAction]
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      cases symbol <;>
        simp_all [rewriteUnaryFrameStatefulFrom,
          unaryFrameFixedFieldSubtractSpec,
          unaryFrameFixedFieldSubtractAction]

private theorem encodeUnaryFrame_frameEnd_free (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with (⟨hvalue, rfl⟩ | rfl) <;> simp

private theorem fixedFieldSubtract_selected_value
    (target amount selected : Nat) (suffix : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedFieldSubtractSpec target amount)
        (.selected (unaryFrameFixedFieldSubtractRemaining amount))
        (encodeUnaryFrame (selected :: suffix) ++ .frameEnd :: tail) =
      encodeUnaryFrame ((selected - amount) :: suffix) ++ .frameEnd ::
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedFieldSubtractSpec target amount)
          (unaryFrameFixedFieldSubtractInitialMode target amount) tail := by
  rw [show encodeUnaryFrame (selected :: suffix) ++ .frameEnd :: tail =
      List.replicate selected .tick ++
        (.separator :: (encodeUnaryFrame suffix ++ .frameEnd :: tail)) by
    simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
  rw [fixedFieldSubtract_selected_ticks]
  simp only [unaryFrameFixedFieldSubtractRemaining, Fin.val_mk]
  rw [fixedFieldSubtract_after_run target amount
    (encodeUnaryFrame suffix) tail (encodeUnaryFrame_frameEnd_free suffix)]
  simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

private theorem fixedFieldSubtract_row
    (target amount : Nat) (row : UnaryFrameFixedFieldSubtractRow target)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedFieldSubtractSpec target amount)
        (unaryFrameFixedFieldSubtractInitialMode target amount)
        (encodeUnaryFrame (row.leading ++ row.selected :: row.suffix) ++
          .frameEnd :: tail) =
      encodeUnaryFrame
          (row.leading ++ (row.selected - amount) :: row.suffix) ++
        .frameEnd ::
          rewriteUnaryFrameStatefulFrom
            (unaryFrameFixedFieldSubtractSpec target amount)
            (unaryFrameFixedFieldSubtractInitialMode target amount) tail := by
  cases target with
  | zero =>
      have hprefix : row.leading = [] := by
        exact List.eq_nil_of_length_eq_zero row.leading_length
      have hinitial :
          unaryFrameFixedFieldSubtractInitialMode 0 amount =
            .selected (unaryFrameFixedFieldSubtractRemaining amount) := by
        rw [unaryFrameFixedFieldSubtractInitialMode]
        simp only [Nat.lt_irrefl]
        congr 1
      rw [hprefix, hinitial]
      exact fixedFieldSubtract_selected_value 0 amount row.selected row.suffix tail
  | succ target =>
      have hbefore := fixedFieldSubtract_before_values (target + 1) amount 0
        (by omega) row.leading
        (encodeUnaryFrame (row.selected :: row.suffix) ++ .frameEnd :: tail)
        (by simpa using row.leading_length)
      have hselected := fixedFieldSubtract_selected_value (target + 1) amount
        row.selected row.suffix tail
      rw [show unaryFrameFixedFieldSubtractInitialMode (target + 1) amount =
          .before ⟨0, by omega⟩ by
        simp [unaryFrameFixedFieldSubtractInitialMode]]
      rw [show encodeUnaryFrame
            (row.leading ++ row.selected :: row.suffix) ++ .frameEnd :: tail =
          encodeUnaryFrame row.leading ++
            (encodeUnaryFrame (row.selected :: row.suffix) ++
              .frameEnd :: tail) by
        simp [encodeUnaryFrame, List.append_assoc]]
      rw [hbefore, hselected]
      simp [encodeUnaryFrame, List.append_assoc]
      simp [unaryFrameFixedFieldSubtractInitialMode]

/-- Exact action on every well-formed fixed-field row family. -/
theorem rewriteUnaryFrameFixedFieldSubtract_rows
    (target amount : Nat)
    (rows : List (UnaryFrameFixedFieldSubtractRow target)) :
    rewriteUnaryFrameFixedFieldSubtract target amount
        (encodeUnaryFrameFixedFieldSubtractInput target rows) =
      encodeUnaryFrameFixedFieldSubtractOutput target amount rows := by
  unfold rewriteUnaryFrameFixedFieldSubtract rewriteUnaryFrameStateful
  change rewriteUnaryFrameStatefulFrom
      (unaryFrameFixedFieldSubtractSpec target amount)
      (unaryFrameFixedFieldSubtractInitialMode target amount)
      (encodeUnaryFrameFixedFieldSubtractInput target rows) =
    encodeUnaryFrameFixedFieldSubtractOutput target amount rows
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [encodeUnaryFrameFixedFieldSubtractInput,
        encodeUnaryFrameFixedFieldSubtractOutput, List.flatMap_cons]
      rw [show
          (encodeUnaryFrame (row.leading ++ row.selected :: row.suffix) ++
            [.frameEnd]) ++
              rest.flatMap (fun item =>
                encodeUnaryFrame
                    (item.leading ++ item.selected :: item.suffix) ++
                  [.frameEnd]) =
          encodeUnaryFrame (row.leading ++ row.selected :: row.suffix) ++
            .frameEnd ::
              rest.flatMap (fun item =>
                encodeUnaryFrame
                    (item.leading ++ item.selected :: item.suffix) ++
                  [.frameEnd]) by
        simp [List.append_assoc]]
      rw [fixedFieldSubtract_row]
      change
        encodeUnaryFrame
              (row.leading ++ (row.selected - amount) :: row.suffix) ++
            .frameEnd ::
              rewriteUnaryFrameStatefulFrom
                (unaryFrameFixedFieldSubtractSpec target amount)
                (unaryFrameFixedFieldSubtractInitialMode target amount)
                (encodeUnaryFrameFixedFieldSubtractInput target rest) =
          encodeUnaryFrame
                (row.leading ++ (row.selected - amount) :: row.suffix) ++
              [.frameEnd] ++
                encodeUnaryFrameFixedFieldSubtractOutput target amount rest
      rw [ih]
      simp [List.append_assoc]

/-- Saturating subtraction in one verifier-fixed field is computed by a
concrete linear-time TM2. -/
noncomputable def unaryFrameFixedFieldSubtract_computableInPolyTime
    (target amount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameFixedFieldSubtract target amount) :=
  unaryFrameStatefulMap_computableInPolyTime
    (unaryFrameFixedFieldSubtractSpec target amount)

end CLRS.Chapter34.Turing.PolyBuilder
