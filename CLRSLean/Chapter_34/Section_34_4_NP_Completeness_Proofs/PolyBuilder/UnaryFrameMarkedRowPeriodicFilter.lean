import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowFilter
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveFamily

/-!
# Periodic selection of arbitrary marked rows

The low-level periodic controller works on delimiter-safe symbol rows, not
only unary encodings of natural-number rows.  This module exposes that typed
family interface and a same-input polynomial-time composition theorem.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Rows retained from an arbitrary starting table position. -/
def selectUnaryFrameMarkedRowsFrom
    (selection : List Bool) (hnonempty : 0 < selection.length) :
    UnaryFramePeriodicMarkedRowFilterMode selection →
      List (List UnaryFrameSym) → List (List UnaryFrameSym)
  | _, [] => []
  | position, row :: rows =>
      (if selection.get position then [row] else []) ++
        selectUnaryFrameMarkedRowsFrom selection hnonempty
          (unaryFramePeriodicMarkedRowFilterNext selection hnonempty position)
          rows

/-- Rows retained when the periodic table starts at position zero. -/
def selectUnaryFrameMarkedRows
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (rows : List (List UnaryFrameSym)) : List (List UnaryFrameSym) :=
  selectUnaryFrameMarkedRowsFrom selection hnonempty ⟨0, hnonempty⟩ rows

theorem mem_selectUnaryFrameMarkedRowsFrom
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (rows : List (List UnaryFrameSym)) (row : List UnaryFrameSym)
    (hrow : row ∈ selectUnaryFrameMarkedRowsFrom selection hnonempty
      position rows) :
    row ∈ rows := by
  induction rows generalizing position with
  | nil => simp [selectUnaryFrameMarkedRowsFrom] at hrow
  | cons head tail ih =>
      simp only [selectUnaryFrameMarkedRowsFrom] at hrow
      by_cases hkeep : selection.get position = true
      · simp only [hkeep, if_true, List.singleton_append,
          List.mem_cons] at hrow
        exact hrow.elim (fun h => h ▸ List.mem_cons_self) fun h =>
          List.mem_cons_of_mem _ (ih _ h)
      · have hfalse : selection.get position = false :=
          Bool.eq_false_of_not_eq_true hkeep
        simp only [hfalse, Bool.false_eq] at hrow
        exact List.mem_cons_of_mem _ (ih _ hrow)

/-- Typed selected family. -/
def UnaryFrameMarkedRowFamily.periodicallySelected
    (family : UnaryFrameMarkedRowFamily)
    (selection : List Bool) (hnonempty : 0 < selection.length) :
    UnaryFrameMarkedRowFamily where
  rows := selectUnaryFrameMarkedRows selection hnonempty family.rows
  frameEnd_free := by
    intro row hrow symbol hsymbol
    apply family.frameEnd_free row
    · exact mem_selectUnaryFrameMarkedRowsFrom selection hnonempty
        ⟨0, hnonempty⟩ family.rows row hrow
    · exact hsymbol

/-- One delimiter-safe symbol row is copied or erased as one unit, and its
outer boundary advances the periodic position exactly once. -/
theorem periodicMarkedSymbolRow_one
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (row tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ row, symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)
        position (row ++ .frameEnd :: tail) =
      (if selection.get position then row ++ [.frameEnd] else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)
          (unaryFramePeriodicMarkedRowFilterNext selection hnonempty position)
          tail := by
  rw [periodicMarkedRow_prefix selection hnonempty position row
    (.frameEnd :: tail) hfree]
  by_cases hkeep : selection.get position = true
  · simp only [hkeep, if_true, rewriteUnaryFrameStatefulFrom,
      unaryFramePeriodicMarkedRowFilterSpec,
      unaryFramePeriodicMarkedRowFilterAction]
    simp [List.append_assoc]
  · have hfalse : selection.get position = false :=
      Bool.eq_false_of_not_eq_true hkeep
    simp only [hfalse, Bool.false_eq, rewriteUnaryFrameStatefulFrom,
      unaryFramePeriodicMarkedRowFilterSpec,
      unaryFramePeriodicMarkedRowFilterAction]
    rfl

theorem rewriteUnaryFramePeriodicMarkedRows_marked_from
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (rows : List (List UnaryFrameSym))
    (hfree : ∀ row ∈ rows, ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicMarkedRowFilterSpec selection hnonempty)
        position (encodeUnaryFrameMarkedRows rows) =
      encodeUnaryFrameMarkedRows
        (selectUnaryFrameMarkedRowsFrom selection hnonempty position rows) := by
  induction rows generalizing position with
  | nil => rfl
  | cons row rows ih =>
      rw [encodeUnaryFrameMarkedRows_cons]
      rw [periodicMarkedSymbolRow_one selection hnonempty position row _
        (fun symbol hsymbol => hfree row (by simp) symbol hsymbol)]
      rw [ih (unaryFramePeriodicMarkedRowFilterNext selection hnonempty
        position) (by
          intro tail htail symbol hsymbol
          exact hfree tail (by simp [htail]) symbol hsymbol)]
      by_cases hkeep : selection.get position = true
      · rw [selectUnaryFrameMarkedRowsFrom]
        rw [hkeep]
        simp only [if_true, List.singleton_append,
          encodeUnaryFrameMarkedRows_cons]
        simp [List.append_assoc]
      · have hfalse : selection.get position = false :=
          Bool.eq_false_of_not_eq_true hkeep
        rw [selectUnaryFrameMarkedRowsFrom]
        rw [hfalse]
        rfl

/-- Exact low-level rewrite on an arbitrary typed marked-row family. -/
theorem rewriteUnaryFramePeriodicMarkedRows_family
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (family : UnaryFrameMarkedRowFamily) :
    rewriteUnaryFramePeriodicMarkedRows selection hnonempty
        (encodeUnaryFrameMarkedRowFamily family) =
      encodeUnaryFrameMarkedRowFamily
        (family.periodicallySelected selection hnonempty) := by
  exact rewriteUnaryFramePeriodicMarkedRows_marked_from selection hnonempty
    ⟨0, hnonempty⟩ family.rows family.frameEnd_free

namespace UnaryFrameMarkedRowPeriodicFilter

variable {Γ : Type} [Fintype Γ]
variable {family : List Γ → UnaryFrameMarkedRowFamily}

/-- Same-input typed output family of the fixed periodic selector. -/
def selectedFamily
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (family input).periodicallySelected selection hnonempty

/-- Composing any concrete marked-row source with the fixed periodic
controller gives a concrete polynomial-time source for the selected rows. -/
noncomputable def computableInPolyTime
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (source : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily family) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (selectedFamily (family := family) selection hnonempty) := by
  let raw : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrameMarkedRowFamily (family input)) :=
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa only [id_eq] using source.outputsFun input }
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    raw
    (unaryFramePeriodicMarkedRowFilter_computableInPolyTime selection
      hnonempty)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_apply, id_eq] at run
        rw [rewriteUnaryFramePeriodicMarkedRows_family selection hnonempty
          (family input)] at run
        simpa only [Function.comp_def, id_eq, selectedFamily] using run }

end UnaryFrameMarkedRowPeriodicFilter

end CLRS.Chapter34.Turing.PolyBuilder
