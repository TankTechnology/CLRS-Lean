import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import Mathlib.Tactic

/-!
# Dropping a fixed value prefix from unary-frame rows

Stack pop routing removes a verifier-fixed number of values from the front of
each runtime row.  This reusable controller performs exactly that operation.
It counts only value separators in finite control, erases the selected prefix,
preserves the outer row marker, and resets for the next row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Row-major input encoding with one outer marker after each value row. -/
def encodeUnaryFrameFixedPrefixDropInput (rows : List (List Nat)) :
    List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

/-- Row-major target after dropping `amount` values from every row. -/
def encodeUnaryFrameFixedPrefixDropOutput (amount : Nat)
    (rows : List (List Nat)) : List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame (row.drop amount) ++ [.frameEnd]

/-- The remaining number of complete value frames to erase. -/
inductive UnaryFrameFixedPrefixDropMode (amount : Nat)
  | dropping (remaining : Fin (amount + 1))
deriving DecidableEq, Fintype

def unaryFrameFixedPrefixDropInitialMode (amount : Nat) :
    UnaryFrameFixedPrefixDropMode amount :=
  .dropping ⟨amount, by omega⟩

private def unaryFrameFixedPrefixDropPred {amount : Nat}
    (remaining : Fin (amount + 1)) (_hpositive : remaining.val ≠ 0) :
    Fin (amount + 1) :=
  ⟨remaining.val - 1, by omega⟩

/-- One streaming action.  While the counter is positive, ticks and the
following separator are erased.  At zero all symbols are copied until the
outer marker resets the counter. -/
def unaryFrameFixedPrefixDropAction (amount : Nat)
    (mode : UnaryFrameFixedPrefixDropMode amount)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFrameFixedPrefixDropMode amount :=
  match mode with
  | .dropping remaining =>
      match symbol with
      | .frameEnd => (some .frameEnd,
          unaryFrameFixedPrefixDropInitialMode amount)
      | .tick =>
          if remaining.val = 0 then (some .tick, .dropping remaining)
          else (none, .dropping remaining)
      | .separator =>
          if hzero : remaining.val = 0 then
            (some .separator, .dropping remaining)
          else
            (none, .dropping
              (unaryFrameFixedPrefixDropPred remaining hzero))

def unaryFrameFixedPrefixDropSpec (amount : Nat) :
    UnaryFrameStatefulMapSpec (UnaryFrameFixedPrefixDropMode amount) :=
  { initial := unaryFrameFixedPrefixDropInitialMode amount
    action := unaryFrameFixedPrefixDropAction amount }

def rewriteUnaryFrameFixedPrefixDrop (amount : Nat)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful (unaryFrameFixedPrefixDropSpec amount) input

private theorem fixedPrefixDrop_zero_ticks (amount count : Nat)
    (remaining : Fin (amount + 1)) (hzero : remaining.val = 0)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameFixedPrefixDropSpec amount)
        (.dropping remaining) (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedPrefixDropSpec amount) (.dropping remaining) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedPrefixDropSpec,
        unaryFrameFixedPrefixDropAction, hzero, ↓reduceIte]
      exact congrArg (List.cons .tick) ih

private theorem fixedPrefixDrop_positive_ticks (amount count : Nat)
    (remaining : Fin (amount + 1)) (hpositive : remaining.val ≠ 0)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameFixedPrefixDropSpec amount)
        (.dropping remaining) (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedPrefixDropSpec amount) (.dropping remaining) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedPrefixDropSpec,
        unaryFrameFixedPrefixDropAction, hpositive, ↓reduceIte]
      exact ih

private theorem fixedPrefixDrop_row_from (amount : Nat)
    (remaining : Fin (amount + 1)) (row : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameFixedPrefixDropSpec amount)
        (.dropping remaining)
        (encodeUnaryFrame row ++ .frameEnd :: tail) =
      encodeUnaryFrame (row.drop remaining.val) ++ .frameEnd ::
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedPrefixDropSpec amount)
          (unaryFrameFixedPrefixDropInitialMode amount) tail := by
  induction row generalizing remaining with
  | nil =>
      simp [encodeUnaryFrame, rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedPrefixDropSpec,
        unaryFrameFixedPrefixDropAction]
  | cons value rest ih =>
      rw [show encodeUnaryFrame (value :: rest) ++ .frameEnd :: tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame rest ++ .frameEnd :: tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      by_cases hzero : remaining.val = 0
      · rw [fixedPrefixDrop_zero_ticks amount value remaining hzero]
        simp only [rewriteUnaryFrameStatefulFrom,
          unaryFrameFixedPrefixDropSpec,
          unaryFrameFixedPrefixDropAction, hzero, ↓reduceDIte]
        have hih := ih remaining
        simp only [unaryFrameFixedPrefixDropSpec] at hih
        rw [hih]
        simp [hzero, encodeUnaryFrame, encodeUnaryFrameBlock,
          List.append_assoc]
      · rw [fixedPrefixDrop_positive_ticks amount value remaining hzero]
        simp only [rewriteUnaryFrameStatefulFrom,
          unaryFrameFixedPrefixDropSpec,
          unaryFrameFixedPrefixDropAction, hzero, ↓reduceDIte]
        have hih := ih (unaryFrameFixedPrefixDropPred remaining hzero)
        simp only [unaryFrameFixedPrefixDropSpec] at hih
        rw [hih]
        have hremaining :
            remaining.val =
              (unaryFrameFixedPrefixDropPred remaining hzero).val + 1 := by
          simp [unaryFrameFixedPrefixDropPred]
          omega
        rw [hremaining]
        simp

private theorem fixedPrefixDrop_row (amount : Nat) (row : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom (unaryFrameFixedPrefixDropSpec amount)
        (unaryFrameFixedPrefixDropInitialMode amount)
        (encodeUnaryFrame row ++ .frameEnd :: tail) =
      encodeUnaryFrame (row.drop amount) ++ .frameEnd ::
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedPrefixDropSpec amount)
          (unaryFrameFixedPrefixDropInitialMode amount) tail := by
  exact fixedPrefixDrop_row_from amount ⟨amount, by omega⟩ row tail

/-- Exact semantics on every row-major unary-frame family. -/
theorem rewriteUnaryFrameFixedPrefixDrop_rows (amount : Nat)
    (rows : List (List Nat)) :
    rewriteUnaryFrameFixedPrefixDrop amount
        (encodeUnaryFrameFixedPrefixDropInput rows) =
      encodeUnaryFrameFixedPrefixDropOutput amount rows := by
  unfold rewriteUnaryFrameFixedPrefixDrop rewriteUnaryFrameStateful
  change rewriteUnaryFrameStatefulFrom
      (unaryFrameFixedPrefixDropSpec amount)
      (unaryFrameFixedPrefixDropInitialMode amount)
      (encodeUnaryFrameFixedPrefixDropInput rows) =
    encodeUnaryFrameFixedPrefixDropOutput amount rows
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [encodeUnaryFrameFixedPrefixDropInput,
        encodeUnaryFrameFixedPrefixDropOutput, List.flatMap_cons]
      rw [show (encodeUnaryFrame row ++ [.frameEnd]) ++
            rest.flatMap (fun item =>
              encodeUnaryFrame item ++ [.frameEnd]) =
          encodeUnaryFrame row ++ .frameEnd ::
            rest.flatMap (fun item =>
              encodeUnaryFrame item ++ [.frameEnd]) by
        simp [List.append_assoc]]
      rw [fixedPrefixDrop_row]
      change encodeUnaryFrame (row.drop amount) ++ .frameEnd ::
          rewriteUnaryFrameStatefulFrom
            (unaryFrameFixedPrefixDropSpec amount)
            (unaryFrameFixedPrefixDropInitialMode amount)
            (encodeUnaryFrameFixedPrefixDropInput rest) =
        encodeUnaryFrame (row.drop amount) ++ [.frameEnd] ++
          encodeUnaryFrameFixedPrefixDropOutput amount rest
      rw [ih]
      simp [List.append_assoc]

/-- Dropping a verifier-fixed value prefix from every marked row is computed
by one concrete linear-time TM2. -/
noncomputable def unaryFrameFixedPrefixDrop_computableInPolyTime
    (amount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameFixedPrefixDrop amount) :=
  unaryFrameStatefulMap_computableInPolyTime
    (unaryFrameFixedPrefixDropSpec amount)

end CLRS.Chapter34.Turing.PolyBuilder
