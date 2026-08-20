import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import Mathlib.Data.List.DropRight
import Mathlib.Tactic

/-!
# Dropping a fixed value suffix from unary-frame rows

Stack push routing removes a verifier-fixed number of values from the end of
each runtime row.  A left-to-right finite-state pass cannot decide that a value
belongs to the suffix until it sees the row boundary.  This controller therefore
reverses the complete family, deletes the fixed value prefix of each reversed
row, and reverses the result again.  The middle pass still uses only finite
control, so the complete construction is polynomial time.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Row-major input encoding with one outer marker after each value row. -/
def encodeUnaryFrameFixedSuffixDropInput (rows : List (List Nat)) :
    List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

/-- Row-major target after deleting `amount` values from the end of every row.
-/
def encodeUnaryFrameFixedSuffixDropOutput (amount : Nat)
    (rows : List (List Nat)) : List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame (row.rdrop amount) ++ [.frameEnd]

/-- Unary values as they occur after reversing an ordinary unary frame: the
separator precedes the ticks and the value order is already reversed. -/
def encodeReversedUnaryFrameValues (values : List Nat) :
    List UnaryFrameSym :=
  values.flatMap fun value => .separator :: List.replicate value .tick

@[simp] theorem encodeUnaryFrame_reverse (values : List Nat) :
    (encodeUnaryFrame values).reverse =
      encodeReversedUnaryFrameValues values.reverse := by
  rw [show (encodeUnaryFrame values).reverse =
      values.reverse.flatMap (List.reverse ∘ encodeUnaryFrameBlock) by
    simp [encodeUnaryFrame, List.reverse_flatMap]]
  unfold encodeReversedUnaryFrameValues
  apply List.flatMap_congr
  intro value hvalue
  simp [encodeUnaryFrameBlock, List.reverse_append]

/-- Reversed row-family representation.  Each row marker now precedes its
separator-first reversed value stream. -/
def encodeUnaryFrameFixedSuffixDropReversed (rows : List (List Nat)) :
    List UnaryFrameSym :=
  rows.flatMap fun row => .frameEnd :: (encodeUnaryFrame row).reverse

theorem encodeUnaryFrameFixedSuffixDropInput_reverse
    (rows : List (List Nat)) :
    (encodeUnaryFrameFixedSuffixDropInput rows).reverse =
      encodeUnaryFrameFixedSuffixDropReversed rows.reverse := by
  rw [show (encodeUnaryFrameFixedSuffixDropInput rows).reverse =
      rows.reverse.flatMap
        (List.reverse ∘ fun row => encodeUnaryFrame row ++ [.frameEnd]) by
    simp [encodeUnaryFrameFixedSuffixDropInput, List.reverse_flatMap]]
  unfold encodeUnaryFrameFixedSuffixDropReversed
  apply List.flatMap_congr
  intro row hrow
  simp [List.reverse_append]

theorem encodeUnaryFrameFixedSuffixDropOutput_reverse
    (amount : Nat) (rows : List (List Nat)) :
    (encodeUnaryFrameFixedSuffixDropOutput amount rows).reverse =
      encodeUnaryFrameFixedSuffixDropReversed
        ((rows.map fun row => row.rdrop amount).reverse) := by
  rw [show (encodeUnaryFrameFixedSuffixDropOutput amount rows).reverse =
      rows.reverse.flatMap
        (List.reverse ∘ fun row =>
          encodeUnaryFrame (row.rdrop amount) ++ [.frameEnd]) by
    simp [encodeUnaryFrameFixedSuffixDropOutput, List.reverse_flatMap]]
  unfold encodeUnaryFrameFixedSuffixDropReversed
  rw [← List.map_reverse]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro row hrow
  simp [List.reverse_append]

/-- Finite-control modes for the separator-first middle pass. -/
inductive UnaryFrameReversedPrefixDropMode (amount : Nat)
  | boundary
  | dropping (remaining : Fin (amount + 1))
  | droppingTicks (remaining : Fin (amount + 1))
  | preserving
deriving DecidableEq, Fintype

def unaryFrameReversedPrefixDropInitialRemaining (amount : Nat) :
    Fin (amount + 1) :=
  ⟨amount, by omega⟩

private def unaryFrameReversedPrefixDropPred {amount : Nat}
    (remaining : Fin (amount + 1)) (_hpositive : remaining.val ≠ 0) :
    Fin (amount + 1) :=
  ⟨remaining.val - 1, by omega⟩

/-- One middle-pass action.  A row boundary resets the fixed counter.  While
the counter is positive, separators and the ticks following them are erased.
After the last deleted value, the remaining reversed row is copied exactly. -/
def unaryFrameReversedPrefixDropAction (amount : Nat)
    (mode : UnaryFrameReversedPrefixDropMode amount)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFrameReversedPrefixDropMode amount :=
  match symbol with
  | .frameEnd =>
      (some .frameEnd,
        .dropping (unaryFrameReversedPrefixDropInitialRemaining amount))
  | .tick =>
      match mode with
      | .boundary => (some .tick, .boundary)
      | .dropping remaining =>
          if remaining.val = 0 then (some .tick, .preserving)
          else (none, .dropping remaining)
      | .droppingTicks remaining => (none, .droppingTicks remaining)
      | .preserving => (some .tick, .preserving)
  | .separator =>
      match mode with
      | .boundary => (some .separator, .boundary)
      | .dropping remaining =>
          if hzero : remaining.val = 0 then
            (some .separator, .preserving)
          else
            (none, .droppingTicks
              (unaryFrameReversedPrefixDropPred remaining hzero))
      | .droppingTicks remaining =>
          if hzero : remaining.val = 0 then
            (some .separator, .preserving)
          else
            (none, .droppingTicks
              (unaryFrameReversedPrefixDropPred remaining hzero))
      | .preserving => (some .separator, .preserving)

def unaryFrameReversedPrefixDropSpec (amount : Nat) :
    UnaryFrameStatefulMapSpec (UnaryFrameReversedPrefixDropMode amount) :=
  { initial := .boundary
    action := unaryFrameReversedPrefixDropAction amount }

def rewriteUnaryFrameReversedPrefixDrop (amount : Nat)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful (unaryFrameReversedPrefixDropSpec amount) input

private def IsUnaryFrameBoundaryTail : List UnaryFrameSym → Prop
  | [] => True
  | .frameEnd :: _ => True
  | _ => False

private theorem reversedPrefixDrop_mode_eq_boundary
    (amount : Nat) (mode : UnaryFrameReversedPrefixDropMode amount)
    (tail : List UnaryFrameSym) (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) mode tail =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) .boundary tail := by
  cases tail with
  | nil => rfl
  | cons symbol rest =>
      cases symbol <;>
        simp_all [IsUnaryFrameBoundaryTail,
          rewriteUnaryFrameStatefulFrom,
          unaryFrameReversedPrefixDropSpec,
          unaryFrameReversedPrefixDropAction]

private theorem reversedPrefixDrop_preserving_ticks
    (amount count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) .preserving
        (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameReversedPrefixDropSpec amount) .preserving tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameReversedPrefixDropSpec,
        unaryFrameReversedPrefixDropAction]
      exact congrArg (List.cons .tick) ih

private theorem reversedPrefixDrop_dropping_ticks
    (amount count : Nat) (remaining : Fin (amount + 1))
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) (.droppingTicks remaining)
        (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) (.droppingTicks remaining)
        tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameReversedPrefixDropSpec,
        unaryFrameReversedPrefixDropAction]
      exact ih

private theorem reversedPrefixDrop_preserving_values
    (amount : Nat) (values : List Nat) (tail : List UnaryFrameSym)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) .preserving
        (encodeReversedUnaryFrameValues values ++ tail) =
      encodeReversedUnaryFrameValues values ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameReversedPrefixDropSpec amount) .boundary tail := by
  induction values with
  | nil =>
      simpa [encodeReversedUnaryFrameValues] using
        reversedPrefixDrop_mode_eq_boundary amount .preserving tail htail
  | cons value rest ih =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons]
      simp only [unaryFrameReversedPrefixDropSpec]
      change .separator ::
          rewriteUnaryFrameStatefulFrom
            (unaryFrameReversedPrefixDropSpec amount) .preserving
            (List.replicate value .tick ++
              encodeReversedUnaryFrameValues rest ++ tail) = _
      rw [show List.replicate value UnaryFrameSym.tick ++
            encodeReversedUnaryFrameValues rest ++ tail =
          List.replicate value UnaryFrameSym.tick ++
            (encodeReversedUnaryFrameValues rest ++ tail) by
        simp [List.append_assoc]]
      rw [reversedPrefixDrop_preserving_ticks amount value
        (encodeReversedUnaryFrameValues rest ++ tail)]
      rw [ih]
      simp [encodeReversedUnaryFrameValues,
        unaryFrameReversedPrefixDropSpec, List.append_assoc]

private theorem reversedPrefixDrop_droppingTicks_values_eq
    (amount : Nat) (remaining : Fin (amount + 1))
    (values : List Nat) (tail : List UnaryFrameSym)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) (.droppingTicks remaining)
        (encodeReversedUnaryFrameValues values ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) (.dropping remaining)
        (encodeReversedUnaryFrameValues values ++ tail) := by
  cases values with
  | nil =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_nil,
        List.nil_append]
      rw [reversedPrefixDrop_mode_eq_boundary amount
        (.droppingTicks remaining) tail htail]
      rw [reversedPrefixDrop_mode_eq_boundary amount
        (.dropping remaining) tail htail]
  | cons value rest =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons,
        List.cons_append, rewriteUnaryFrameStatefulFrom,
        unaryFrameReversedPrefixDropSpec,
        unaryFrameReversedPrefixDropAction]

private theorem reversedPrefixDrop_values
    (amount : Nat) (remaining : Fin (amount + 1))
    (values : List Nat) (tail : List UnaryFrameSym)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameReversedPrefixDropSpec amount) (.dropping remaining)
        (encodeReversedUnaryFrameValues values ++ tail) =
      encodeReversedUnaryFrameValues (values.drop remaining.val) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameReversedPrefixDropSpec amount) .boundary tail := by
  induction values generalizing remaining with
  | nil =>
      simpa [encodeReversedUnaryFrameValues] using
        reversedPrefixDrop_mode_eq_boundary amount
          (.dropping remaining) tail htail
  | cons value rest ih =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons]
      by_cases hzero : remaining.val = 0
      · simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
          unaryFrameReversedPrefixDropSpec,
          unaryFrameReversedPrefixDropAction, hzero, ↓reduceDIte]
        change .separator ::
            rewriteUnaryFrameStatefulFrom
              (unaryFrameReversedPrefixDropSpec amount) .preserving
              (List.replicate value .tick ++
                encodeReversedUnaryFrameValues rest ++ tail) = _
        rw [show List.replicate value UnaryFrameSym.tick ++
              encodeReversedUnaryFrameValues rest ++ tail =
            List.replicate value UnaryFrameSym.tick ++
              (encodeReversedUnaryFrameValues rest ++ tail) by
          simp [List.append_assoc]]
        rw [reversedPrefixDrop_preserving_ticks amount value
          (encodeReversedUnaryFrameValues rest ++ tail)]
        rw [reversedPrefixDrop_preserving_values amount rest tail htail]
        simp only [List.drop_zero]
        simp [encodeReversedUnaryFrameValues,
          unaryFrameReversedPrefixDropSpec, List.append_assoc]
      · simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
          unaryFrameReversedPrefixDropSpec,
          unaryFrameReversedPrefixDropAction, hzero, ↓reduceDIte]
        change rewriteUnaryFrameStatefulFrom
            (unaryFrameReversedPrefixDropSpec amount)
            (.droppingTicks
              (unaryFrameReversedPrefixDropPred remaining hzero))
            (List.replicate value .tick ++
              encodeReversedUnaryFrameValues rest ++ tail) = _
        rw [show List.replicate value UnaryFrameSym.tick ++
              encodeReversedUnaryFrameValues rest ++ tail =
            List.replicate value UnaryFrameSym.tick ++
              (encodeReversedUnaryFrameValues rest ++ tail) by
          simp [List.append_assoc]]
        rw [reversedPrefixDrop_dropping_ticks amount value
          (unaryFrameReversedPrefixDropPred remaining hzero)
          (encodeReversedUnaryFrameValues rest ++ tail)]
        rw [reversedPrefixDrop_droppingTicks_values_eq amount
          (unaryFrameReversedPrefixDropPred remaining hzero) rest tail htail]
        rw [ih (unaryFrameReversedPrefixDropPred remaining hzero)]
        have hremaining :
            remaining.val =
              (unaryFrameReversedPrefixDropPred remaining hzero).val + 1 := by
          simp [unaryFrameReversedPrefixDropPred]
          omega
        rw [hremaining]
        simp only [List.drop_succ_cons]
        simp only [encodeReversedUnaryFrameValues,
          unaryFrameReversedPrefixDropSpec]

private theorem suffixDrop_reversed_family
    (amount : Nat) (rows : List (List Nat)) :
    rewriteUnaryFrameReversedPrefixDrop amount
        (encodeUnaryFrameFixedSuffixDropReversed rows) =
      encodeUnaryFrameFixedSuffixDropReversed
        (rows.map fun row => row.rdrop amount) := by
  unfold rewriteUnaryFrameReversedPrefixDrop rewriteUnaryFrameStateful
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [encodeUnaryFrameFixedSuffixDropReversed, List.flatMap_cons,
        List.map_cons]
      rw [show
        (.frameEnd :: (encodeUnaryFrame row).reverse) ++
            rest.flatMap (fun item =>
              .frameEnd :: (encodeUnaryFrame item).reverse) =
          .frameEnd :: ((encodeUnaryFrame row).reverse ++
            rest.flatMap (fun item =>
              .frameEnd :: (encodeUnaryFrame item).reverse)) by simp]
      simp only [rewriteUnaryFrameStatefulFrom,
        unaryFrameReversedPrefixDropSpec,
        unaryFrameReversedPrefixDropAction]
      rw [encodeUnaryFrame_reverse]
      change .frameEnd ::
          rewriteUnaryFrameStatefulFrom
            (unaryFrameReversedPrefixDropSpec amount)
            (.dropping
              (unaryFrameReversedPrefixDropInitialRemaining amount))
            (encodeReversedUnaryFrameValues row.reverse ++
              encodeUnaryFrameFixedSuffixDropReversed rest) = _
      rw [reversedPrefixDrop_values amount
        (unaryFrameReversedPrefixDropInitialRemaining amount) row.reverse
        (encodeUnaryFrameFixedSuffixDropReversed rest)]
      · change .frameEnd ::
            (encodeReversedUnaryFrameValues (row.reverse.drop amount) ++
              rewriteUnaryFrameStatefulFrom
                (unaryFrameReversedPrefixDropSpec amount) .boundary
                (encodeUnaryFrameFixedSuffixDropReversed rest)) = _
        rw [show row.reverse.drop amount = (row.rdrop amount).reverse by
          simp [List.rdrop_eq_reverse_drop_reverse]]
        rw [← encodeUnaryFrame_reverse]
        have ih' :
            rewriteUnaryFrameStatefulFrom
                (unaryFrameReversedPrefixDropSpec amount) .boundary
                (encodeUnaryFrameFixedSuffixDropReversed rest) =
              encodeUnaryFrameFixedSuffixDropReversed
                (rest.map fun item => item.rdrop amount) := by
          simpa [unaryFrameReversedPrefixDropSpec] using ih
        rw [ih']
        simp [encodeUnaryFrameFixedSuffixDropReversed]
      · cases rest <;> simp [IsUnaryFrameBoundaryTail,
          encodeUnaryFrameFixedSuffixDropReversed]

/-- Delete a fixed suffix from every row by reverse/filter/reverse. -/
def rewriteUnaryFrameFixedSuffixDrop (amount : Nat)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  (rewriteUnaryFrameReversedPrefixDrop amount input.reverse).reverse

/-- Exact semantics on every row-major unary-frame family. -/
theorem rewriteUnaryFrameFixedSuffixDrop_rows (amount : Nat)
    (rows : List (List Nat)) :
    rewriteUnaryFrameFixedSuffixDrop amount
        (encodeUnaryFrameFixedSuffixDropInput rows) =
      encodeUnaryFrameFixedSuffixDropOutput amount rows := by
  unfold rewriteUnaryFrameFixedSuffixDrop
  rw [encodeUnaryFrameFixedSuffixDropInput_reverse]
  rw [suffixDrop_reversed_family]
  rw [show (rows.reverse.map fun row => row.rdrop amount) =
      (rows.map fun row => row.rdrop amount).reverse by simp]
  rw [← encodeUnaryFrameFixedSuffixDropOutput_reverse]
  simp

/-- Dropping a verifier-fixed value suffix from every marked row is computed
by a concrete polynomial-time TM2. -/
noncomputable def unaryFrameFixedSuffixDrop_computableInPolyTime
    (amount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameFixedSuffixDrop amount) := by
  let reversed := reverse_computableInPolyTime (Γ := UnaryFrameSym)
  let filtered := unaryFrameStatefulMap_computableInPolyTime
    (unaryFrameReversedPrefixDropSpec amount)
  let first := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    reversed filtered
  let second := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (Classical.choice first)
    (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  let result := Classical.choice second
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [id_eq, Function.comp_apply,
          rewriteUnaryFrameFixedSuffixDrop,
          rewriteUnaryFrameReversedPrefixDrop] using run }

end CLRS.Chapter34.Turing.PolyBuilder
