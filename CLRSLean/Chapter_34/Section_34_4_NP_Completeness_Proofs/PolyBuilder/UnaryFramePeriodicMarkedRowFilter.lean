import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import Mathlib.Tactic

/-!
# Periodic filtering of marked unary-frame rows

Many Cook--Levin descriptor sources repeat one machine-fixed segment layout
for every runtime seed.  This controller keeps or erases each complete marked
row according to a nonempty Boolean table and advances the table only at the
outer `frameEnd` boundary.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- One finite-control position in the periodic selection table. -/
abbrev UnaryFramePeriodicMarkedRowFilterMode
    (selection : List Bool) := Fin selection.length

/-- Advance cyclically in an arbitrary nonempty selection table. -/
def unaryFramePeriodicMarkedRowFilterNext
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection) :
    UnaryFramePeriodicMarkedRowFilterMode selection :=
  if hnext : position.val + 1 < selection.length then
    ⟨position.val + 1, hnext⟩
  else ⟨0, hnonempty⟩

/-- Copy or erase the current row; only its outer boundary advances the
periodic position. -/
def unaryFramePeriodicMarkedRowFilterAction
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFramePeriodicMarkedRowFilterMode selection :=
  let keep := selection.get position
  match symbol with
  | .frameEnd =>
      (if keep then some .frameEnd else none,
        unaryFramePeriodicMarkedRowFilterNext selection hnonempty position)
  | .tick => (if keep then some .tick else none, position)
  | .separator => (if keep then some .separator else none, position)

def unaryFramePeriodicMarkedRowFilterSpec
    (selection : List Bool) (hnonempty : 0 < selection.length) :
    UnaryFrameStatefulMapSpec
      (UnaryFramePeriodicMarkedRowFilterMode selection) :=
  { initial := ⟨0, hnonempty⟩
    action := unaryFramePeriodicMarkedRowFilterAction selection hnonempty }

/-- Pure stream rewrite implemented by the fixed controller. -/
def rewriteUnaryFramePeriodicMarkedRows
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty) input

/-- Canonical marked input rows. -/
def encodeUnaryFramePeriodicMarkedRowInput (rows : List (List Nat)) :
    List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

/-- Exact selected output starting at an arbitrary periodic position. -/
def encodeUnaryFramePeriodicMarkedRowOutputFrom
    (selection : List Bool) (hnonempty : 0 < selection.length) :
    UnaryFramePeriodicMarkedRowFilterMode selection →
      List (List Nat) → List UnaryFrameSym
  | _, [] => []
  | position, row :: rest =>
      (if selection.get position then
          encodeUnaryFrame row ++ [.frameEnd]
        else []) ++
        encodeUnaryFramePeriodicMarkedRowOutputFrom selection hnonempty
          (unaryFramePeriodicMarkedRowFilterNext selection hnonempty position)
          rest

/-- Selected output from table position zero. -/
def encodeUnaryFramePeriodicMarkedRowOutput
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (rows : List (List Nat)) : List UnaryFrameSym :=
  encodeUnaryFramePeriodicMarkedRowOutputFrom selection hnonempty
    ⟨0, hnonempty⟩ rows

/-- A delimiter-free payload is either copied or erased without advancing
the periodic table.  This public form lets typed marked-row families reuse
the same verified controller. -/
theorem periodicMarkedRow_prefix
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (rowSymbols tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ rowSymbols,
      symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)
        position (rowSymbols ++ tail) =
      (if selection.get position then rowSymbols else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)
          position tail := by
  induction rowSymbols with
  | nil => simp
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      have ih' := ih hrest
      cases symbol with
      | tick =>
          by_cases hkeep : selection.get position = true
          · simp only [List.cons_append,
              rewriteUnaryFrameStatefulFrom,
              unaryFramePeriodicMarkedRowFilterSpec,
              unaryFramePeriodicMarkedRowFilterAction]
            rw [hkeep]
            simp only [if_true]
            have hih := ih'
            simp only [unaryFramePeriodicMarkedRowFilterSpec, hkeep,
              if_true] at hih
            rw [hih]
            rfl
          · have hfalse : selection.get position = false :=
              Bool.eq_false_of_not_eq_true hkeep
            simp only [List.cons_append,
              rewriteUnaryFrameStatefulFrom,
              unaryFramePeriodicMarkedRowFilterSpec,
              unaryFramePeriodicMarkedRowFilterAction]
            rw [hfalse]
            simp only [Bool.false_eq]
            have hih := ih'
            simp only [unaryFramePeriodicMarkedRowFilterSpec, hfalse,
              Bool.false_eq] at hih
            exact hih
      | separator =>
          by_cases hkeep : selection.get position = true
          · simp only [List.cons_append,
              rewriteUnaryFrameStatefulFrom,
              unaryFramePeriodicMarkedRowFilterSpec,
              unaryFramePeriodicMarkedRowFilterAction]
            rw [hkeep]
            simp only [if_true]
            have hih := ih'
            simp only [unaryFramePeriodicMarkedRowFilterSpec, hkeep,
              if_true] at hih
            rw [hih]
            rfl
          · have hfalse : selection.get position = false :=
              Bool.eq_false_of_not_eq_true hkeep
            simp only [List.cons_append,
              rewriteUnaryFrameStatefulFrom,
              unaryFramePeriodicMarkedRowFilterSpec,
              unaryFramePeriodicMarkedRowFilterAction]
            rw [hfalse]
            simp only [Bool.false_eq]
            have hih := ih'
            simp only [unaryFramePeriodicMarkedRowFilterSpec, hfalse,
              Bool.false_eq] at hih
            exact hih
      | frameEnd => exact (hsymbol rfl).elim

private theorem encodeUnaryFrame_frameEnd_free (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  unfold encodeUnaryFrame at hsymbol
  rw [List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with ⟨_, rfl⟩ | rfl <;> simp

private theorem periodicMarkedRow_one
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (row : List Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)
        position (encodeUnaryFrame row ++ .frameEnd :: tail) =
      (if selection.get position then
          encodeUnaryFrame row ++ [.frameEnd]
        else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)
          (unaryFramePeriodicMarkedRowFilterNext selection hnonempty position)
          tail := by
  rw [periodicMarkedRow_prefix selection hnonempty position
    (encodeUnaryFrame row) (.frameEnd :: tail)
    (encodeUnaryFrame_frameEnd_free row)]
  by_cases hkeep : selection.get position = true
  · simp only [hkeep, if_true]
    simp only [rewriteUnaryFrameStatefulFrom,
      unaryFramePeriodicMarkedRowFilterSpec,
      unaryFramePeriodicMarkedRowFilterAction]
    rw [hkeep]
    simp [List.append_assoc]
  · have hfalse : selection.get position = false :=
      Bool.eq_false_of_not_eq_true hkeep
    simp only [hfalse, Bool.false_eq]
    simp only [rewriteUnaryFrameStatefulFrom,
      unaryFramePeriodicMarkedRowFilterSpec,
      unaryFramePeriodicMarkedRowFilterAction]
    rw [hfalse]
    rfl

private theorem periodicMarkedRows_from
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (rows : List (List Nat)) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)
        position (encodeUnaryFramePeriodicMarkedRowInput rows) =
      encodeUnaryFramePeriodicMarkedRowOutputFrom selection hnonempty
        position rows := by
  induction rows generalizing position with
  | nil => rfl
  | cons row rest ih =>
      simp only [encodeUnaryFramePeriodicMarkedRowInput,
        List.flatMap_cons]
      rw [show (encodeUnaryFrame row ++ [.frameEnd]) ++
            rest.flatMap (fun item => encodeUnaryFrame item ++ [.frameEnd]) =
          encodeUnaryFrame row ++ .frameEnd ::
            encodeUnaryFramePeriodicMarkedRowInput rest by
        simp [encodeUnaryFramePeriodicMarkedRowInput, List.append_assoc]]
      rw [periodicMarkedRow_one]
      rw [ih]
      rfl

/-- Exact periodic filtering semantics on every marked unary-value row. -/
theorem rewriteUnaryFramePeriodicMarkedRows_encode
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (rows : List (List Nat)) :
    rewriteUnaryFramePeriodicMarkedRows selection hnonempty
        (encodeUnaryFramePeriodicMarkedRowInput rows) =
      encodeUnaryFramePeriodicMarkedRowOutput selection hnonempty rows := by
  exact periodicMarkedRows_from selection hnonempty ⟨0, hnonempty⟩ rows

/-- For every fixed nonempty selection table, periodic marked-row filtering
is computed by one concrete linear-time TM2. -/
noncomputable def
    unaryFramePeriodicMarkedRowFilter_computableInPolyTime
    (selection : List Bool) (hnonempty : 0 < selection.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFramePeriodicMarkedRows selection hnonempty) :=
  unaryFrameStatefulMap_computableInPolyTime
    (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)

end CLRS.Chapter34.Turing.PolyBuilder
