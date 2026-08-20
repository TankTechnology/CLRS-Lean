import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import Mathlib.Tactic

/-!
# Zero-tagged fixed-width unary row demultiplexing

Each input row contains one unary tag followed by a fixed number of unary
payload fields.  Positive tags are dropped while their payload is retained;
a zero tag drops its payload and emits one `frameEnd`.  The construction is a
small specialization of the reusable stateful streaming TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

inductive UnaryFrameZeroTagRowMode (fieldCount : Nat)
  | tag (positive : Bool)
  | payload (position : Fin fieldCount)
  | skip (position : Fin fieldCount)
deriving DecidableEq, Fintype

def unaryFrameZeroTagRowAfterTag (fieldCount : Nat)
    (positive : Bool) :
    Option UnaryFrameSym × UnaryFrameZeroTagRowMode fieldCount :=
  if h : 0 < fieldCount then
    if positive then (none, .payload ⟨0, h⟩)
    else (some .frameEnd, .skip ⟨0, h⟩)
  else if positive then (none, .tag false)
    else (some .frameEnd, .tag false)

def unaryFrameZeroTagRowNext (fieldCount : Nat)
    (position : Fin fieldCount)
    (keep : Bool) :
    Option UnaryFrameSym × UnaryFrameZeroTagRowMode fieldCount :=
  let emitted := if keep then some .separator else none
  if hnext : position.val + 1 < fieldCount then
    if keep then (emitted, .payload ⟨position.val + 1, hnext⟩)
    else (emitted, .skip ⟨position.val + 1, hnext⟩)
  else (emitted, .tag false)

def unaryFrameZeroTagRowAction (fieldCount : Nat)
    (mode : UnaryFrameZeroTagRowMode fieldCount)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFrameZeroTagRowMode fieldCount :=
  match mode with
  | .tag positive =>
      match symbol with
      | .tick => (none, .tag true)
      | .separator => unaryFrameZeroTagRowAfterTag fieldCount positive
      | .frameEnd => (none, .tag false)
  | .payload position =>
      match symbol with
      | .tick => (some .tick, .payload position)
      | .separator => unaryFrameZeroTagRowNext fieldCount position true
      | .frameEnd => (some .frameEnd, .tag false)
  | .skip position =>
      match symbol with
      | .tick => (none, .skip position)
      | .separator => unaryFrameZeroTagRowNext fieldCount position false
      | .frameEnd => (none, .tag false)

def unaryFrameZeroTagRowSpec (fieldCount : Nat) :
    UnaryFrameStatefulMapSpec (UnaryFrameZeroTagRowMode fieldCount) :=
  { initial := .tag false
    action := unaryFrameZeroTagRowAction fieldCount }

def rewriteUnaryFrameZeroTagRows (fieldCount : Nat)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful (unaryFrameZeroTagRowSpec fieldCount) input

private theorem zeroTagRow_tag_true_ticks (fieldCount count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.tag true) (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.tag true) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom, unaryFrameZeroTagRowSpec,
        unaryFrameZeroTagRowAction]
      exact ih

private theorem zeroTagRow_tag_positive_ticks (fieldCount count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.tag false) (List.replicate (count + 1) .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.tag true) tail := by
  rw [List.replicate_succ, List.cons_append]
  simp only [rewriteUnaryFrameStatefulFrom,
    unaryFrameZeroTagRowSpec, unaryFrameZeroTagRowAction]
  exact zeroTagRow_tag_true_ticks fieldCount count tail

private theorem zeroTagRow_payload_ticks (fieldCount : Nat)
    (position : Fin fieldCount) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.payload position) (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameZeroTagRowSpec fieldCount) (.payload position) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom, unaryFrameZeroTagRowSpec,
        unaryFrameZeroTagRowAction]
      exact congrArg (List.cons .tick) ih

private theorem zeroTagRow_skip_ticks (fieldCount : Nat)
    (position : Fin fieldCount) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.skip position) (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameZeroTagRowSpec fieldCount) (.skip position) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom, unaryFrameZeroTagRowSpec,
        unaryFrameZeroTagRowAction]
      exact ih

private theorem zeroTagRow_payload_separator
    (fieldCount position : Nat) (hposition : position < fieldCount)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.payload ⟨position, hposition⟩) (.separator :: tail) =
      .separator ::
        if hnext : position + 1 < fieldCount then
          rewriteUnaryFrameStatefulFrom
            (unaryFrameZeroTagRowSpec fieldCount)
            (.payload ⟨position + 1, hnext⟩) tail
        else rewriteUnaryFrameStatefulFrom
          (unaryFrameZeroTagRowSpec fieldCount) (.tag false) tail := by
  simp [rewriteUnaryFrameStatefulFrom, unaryFrameZeroTagRowSpec,
    unaryFrameZeroTagRowAction, unaryFrameZeroTagRowNext]
  split_ifs <;> rfl

private theorem zeroTagRow_skip_separator
    (fieldCount position : Nat) (hposition : position < fieldCount)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.skip ⟨position, hposition⟩) (.separator :: tail) =
      if hnext : position + 1 < fieldCount then
        rewriteUnaryFrameStatefulFrom
          (unaryFrameZeroTagRowSpec fieldCount)
          (.skip ⟨position + 1, hnext⟩) tail
      else rewriteUnaryFrameStatefulFrom
        (unaryFrameZeroTagRowSpec fieldCount) (.tag false) tail := by
  simp [rewriteUnaryFrameStatefulFrom, unaryFrameZeroTagRowSpec,
    unaryFrameZeroTagRowAction, unaryFrameZeroTagRowNext]
  split_ifs <;> rfl

private theorem zeroTagRow_copy_payload
    (fieldCount position : Nat) (values : List Nat)
    (tail : List UnaryFrameSym)
    (hfit : position + values.length = fieldCount)
    (hposition : position < fieldCount) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.payload ⟨position, hposition⟩)
        (encodeUnaryFrame values ++ tail) =
      encodeUnaryFrame values ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameZeroTagRowSpec fieldCount) (.tag false) tail := by
  induction values generalizing position with
  | nil => simp at hfit; omega
  | cons value values ih =>
      have hnextFit : position + 1 + values.length = fieldCount := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [zeroTagRow_payload_ticks]
      rw [zeroTagRow_payload_separator fieldCount position hposition]
      split_ifs with hnext
      · rw [ih (position + 1) hnextFit hnext]
        simp [encodeUnaryFrame, encodeUnaryFrameBlock,
          List.append_assoc]
      · cases values with
        | nil =>
            simp [encodeUnaryFrame, encodeUnaryFrameBlock,
              List.append_assoc]
        | cons head rest =>
            simp only [List.length_cons] at hnextFit
            omega

private theorem zeroTagRow_drop_payload
    (fieldCount position : Nat) (values : List Nat)
    (tail : List UnaryFrameSym)
    (hfit : position + values.length = fieldCount)
    (hposition : position < fieldCount) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.skip ⟨position, hposition⟩)
        (encodeUnaryFrame values ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameZeroTagRowSpec fieldCount) (.tag false) tail := by
  induction values generalizing position with
  | nil => simp at hfit; omega
  | cons value values ih =>
      have hnextFit : position + 1 + values.length = fieldCount := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [zeroTagRow_skip_ticks]
      rw [zeroTagRow_skip_separator fieldCount position hposition]
      split_ifs with hnext
      · exact ih (position + 1) hnextFit hnext
      · cases values with
        | nil => rfl
        | cons head rest =>
            simp only [List.length_cons] at hnextFit
            omega

private theorem zeroTagRow_tag_false_separator
    (fieldCount : Nat) (tail : List UnaryFrameSym)
    (hpositive : 0 < fieldCount) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.tag false) (.separator :: tail) =
      .frameEnd ::
        rewriteUnaryFrameStatefulFrom
          (unaryFrameZeroTagRowSpec fieldCount)
          (.skip ⟨0, hpositive⟩) tail := by
  simp [rewriteUnaryFrameStatefulFrom, unaryFrameZeroTagRowSpec,
    unaryFrameZeroTagRowAction, unaryFrameZeroTagRowAfterTag,
    hpositive]

private theorem zeroTagRow_tag_true_separator
    (fieldCount : Nat) (tail : List UnaryFrameSym)
    (hpositive : 0 < fieldCount) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.tag true) (.separator :: tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameZeroTagRowSpec fieldCount)
        (.payload ⟨0, hpositive⟩) tail := by
  simp [rewriteUnaryFrameStatefulFrom, unaryFrameZeroTagRowSpec,
    unaryFrameZeroTagRowAction, unaryFrameZeroTagRowAfterTag,
    hpositive]

/-- Exact action on one well-formed tagged row followed by an arbitrary row
tail. -/
theorem rewriteUnaryFrameZeroTagRows_one
    (fieldCount tag : Nat) (payload : List Nat)
    (tail : List UnaryFrameSym)
    (hpositive : 0 < fieldCount)
    (hlength : payload.length = fieldCount) :
    rewriteUnaryFrameStatefulFrom (unaryFrameZeroTagRowSpec fieldCount)
        (.tag false)
        (encodeUnaryFrame (tag :: payload) ++ tail) =
      (if tag = 0 then [.frameEnd] else encodeUnaryFrame payload) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameZeroTagRowSpec fieldCount) (.tag false) tail := by
  cases tag with
  | zero =>
      rw [show encodeUnaryFrame (0 :: payload) ++ tail =
          .separator :: (encodeUnaryFrame payload ++ tail) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock]]
      rw [zeroTagRow_tag_false_separator fieldCount
        (encodeUnaryFrame payload ++ tail) hpositive]
      rw [zeroTagRow_drop_payload fieldCount 0 payload tail]
      · simp
      · simpa using hlength
  | succ tag =>
      rw [show encodeUnaryFrame (Nat.succ tag :: payload) ++ tail =
          List.replicate (tag + 1) .tick ++
            (.separator :: (encodeUnaryFrame payload ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc,
          Nat.succ_eq_add_one]]
      rw [zeroTagRow_tag_positive_ticks]
      rw [zeroTagRow_tag_true_separator fieldCount
        (encodeUnaryFrame payload ++ tail) hpositive]
      rw [zeroTagRow_copy_payload fieldCount 0 payload tail]
      · simp
      · simpa using hlength

/-- Typed finite family used by semantic alignment theorems. -/
structure UnaryFrameZeroTagRowFamily (fieldCount : Nat) where
  rows : List (Nat × List Nat)
  payload_lengths : ∀ row ∈ rows, row.2.length = fieldCount

def encodeUnaryFrameZeroTagRowFamily {fieldCount : Nat}
    (family : UnaryFrameZeroTagRowFamily fieldCount) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row => encodeUnaryFrame (row.1 :: row.2)

def encodeUnaryFrameZeroTagRowOutput {fieldCount : Nat}
    (family : UnaryFrameZeroTagRowFamily fieldCount) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    if row.1 = 0 then [.frameEnd] else encodeUnaryFrame row.2

/-- Family-level exact semantics. -/
theorem rewriteUnaryFrameZeroTagRows_family
    {fieldCount : Nat} (family : UnaryFrameZeroTagRowFamily fieldCount)
    (hpositive : 0 < fieldCount) :
    rewriteUnaryFrameZeroTagRows fieldCount
        (encodeUnaryFrameZeroTagRowFamily family) =
      encodeUnaryFrameZeroTagRowOutput family := by
  unfold rewriteUnaryFrameZeroTagRows rewriteUnaryFrameStateful
    encodeUnaryFrameZeroTagRowFamily encodeUnaryFrameZeroTagRowOutput
  generalize hrows : family.rows = rows
  have hlengths : ∀ row ∈ rows, row.2.length = fieldCount := by
    intro row hrow
    apply family.payload_lengths row
    simpa [hrows] using hrow
  clear hrows
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [List.flatMap_cons, List.flatMap_cons]
      change rewriteUnaryFrameStatefulFrom
          (unaryFrameZeroTagRowSpec fieldCount) (.tag false)
          (encodeUnaryFrame (row.1 :: row.2) ++
            rows.flatMap fun item =>
              encodeUnaryFrame (item.1 :: item.2)) = _
      rw [rewriteUnaryFrameZeroTagRows_one fieldCount row.1 row.2
        (rows.flatMap fun item => encodeUnaryFrame (item.1 :: item.2))
        hpositive (hlengths row (by simp))]
      congr 1
      apply ih
      intro item hitem
      exact hlengths item (by simp [hitem])

/-- The raw zero-tag demultiplexer is one fixed linear-time TM2. -/
noncomputable def rewriteUnaryFrameZeroTagRows_computableInPolyTime
    (fieldCount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameZeroTagRows fieldCount) :=
  unaryFrameStatefulMap_computableInPolyTime
    (unaryFrameZeroTagRowSpec fieldCount)

end CLRS.Chapter34.Turing.PolyBuilder
