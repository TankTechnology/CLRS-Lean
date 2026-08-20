import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePeriodicMarkedRowFilter

/-!
# Periodic filtering of unary-frame row boundaries

This finite-state pass preserves every tick and ordinary separator while
selectively retaining `frameEnd` markers according to a fixed nonempty cyclic
Boolean table.  It merges adjacent descriptor rows without discarding their
payloads and keeps the chosen structural boundaries needed by stack routing.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Copy every payload symbol and advance only when a row boundary is read. -/
def unaryFramePeriodicBoundaryFilterAction
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFramePeriodicMarkedRowFilterMode selection :=
  match symbol with
  | .frameEnd =>
      (if selection.get position then some .frameEnd else none,
        unaryFramePeriodicMarkedRowFilterNext selection hnonempty position)
  | .tick => (some .tick, position)
  | .separator => (some .separator, position)

def unaryFramePeriodicBoundaryFilterSpec
    (selection : List Bool) (hnonempty : 0 < selection.length) :
    UnaryFrameStatefulMapSpec
      (UnaryFramePeriodicMarkedRowFilterMode selection) :=
  { initial := ⟨0, hnonempty⟩
    action := unaryFramePeriodicBoundaryFilterAction selection hnonempty }

/-- Pure boundary-filtering rewrite. -/
def rewriteUnaryFramePeriodicBoundaries
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFramePeriodicBoundaryFilterSpec selection hnonempty) input

/-- Exact output from an arbitrary cyclic table position. -/
def encodeUnaryFramePeriodicBoundaryOutputFrom
    (selection : List Bool) (hnonempty : 0 < selection.length) :
    UnaryFramePeriodicMarkedRowFilterMode selection →
      List (List Nat) → List UnaryFrameSym
  | _, [] => []
  | position, row :: rest =>
      encodeUnaryFrame row ++
        (if selection.get position then [.frameEnd] else []) ++
        encodeUnaryFramePeriodicBoundaryOutputFrom selection hnonempty
          (unaryFramePeriodicMarkedRowFilterNext selection hnonempty position)
          rest

/-- Exact output starting at the first table position. -/
def encodeUnaryFramePeriodicBoundaryOutput
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (rows : List (List Nat)) : List UnaryFrameSym :=
  encodeUnaryFramePeriodicBoundaryOutputFrom selection hnonempty
    ⟨0, hnonempty⟩ rows

private theorem periodicBoundary_copy_free
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (symbols tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ symbols, symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicBoundaryFilterSpec selection hnonempty)
        position (symbols ++ tail) =
      symbols ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicBoundaryFilterSpec selection hnonempty)
          position tail := by
  induction symbols with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      cases symbol <;>
        simp_all [rewriteUnaryFrameStatefulFrom,
          unaryFramePeriodicBoundaryFilterSpec,
          unaryFramePeriodicBoundaryFilterAction]

private theorem periodicBoundary_encodeUnaryFrame_free (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  unfold encodeUnaryFrame at hsymbol
  rw [List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with ⟨_, rfl⟩ | rfl <;> simp

private theorem periodicBoundary_one
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (row : List Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicBoundaryFilterSpec selection hnonempty)
        position (encodeUnaryFrame row ++ .frameEnd :: tail) =
      encodeUnaryFrame row ++
        (if selection.get position then [.frameEnd] else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicBoundaryFilterSpec selection hnonempty)
          (unaryFramePeriodicMarkedRowFilterNext selection hnonempty position)
          tail := by
  rw [periodicBoundary_copy_free selection hnonempty position
    (encodeUnaryFrame row) (.frameEnd :: tail)
    (periodicBoundary_encodeUnaryFrame_free row)]
  by_cases hkeep : selection.get position = true
  · simp only [hkeep, if_true, rewriteUnaryFrameStatefulFrom,
      unaryFramePeriodicBoundaryFilterSpec,
      unaryFramePeriodicBoundaryFilterAction]
    simp
  · have hfalse : selection.get position = false :=
      Bool.eq_false_of_not_eq_true hkeep
    simp only [hfalse, Bool.false_eq, rewriteUnaryFrameStatefulFrom,
      unaryFramePeriodicBoundaryFilterSpec,
      unaryFramePeriodicBoundaryFilterAction]
    simp

private theorem periodicBoundaries_from
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (rows : List (List Nat)) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicBoundaryFilterSpec selection hnonempty)
        position (encodeUnaryFramePeriodicMarkedRowInput rows) =
      encodeUnaryFramePeriodicBoundaryOutputFrom selection hnonempty
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
      rw [periodicBoundary_one]
      rw [ih]
      rfl

/-- Exact semantics on a family with one input marker after every row. -/
theorem rewriteUnaryFramePeriodicBoundaries_encode
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (rows : List (List Nat)) :
    rewriteUnaryFramePeriodicBoundaries selection hnonempty
        (encodeUnaryFramePeriodicMarkedRowInput rows) =
      encodeUnaryFramePeriodicBoundaryOutput selection hnonempty rows := by
  exact periodicBoundaries_from selection hnonempty ⟨0, hnonempty⟩ rows

/-- Pair one table suffix with equally positioned rows, retaining all row
payloads and only the selected boundaries. -/
def encodeUnaryFramePeriodicSelectedBoundaries :
    List Bool → List (List Nat) → List UnaryFrameSym
  | keep :: keeps, row :: rows =>
      encodeUnaryFrame row ++ (if keep then [.frameEnd] else []) ++
        encodeUnaryFramePeriodicSelectedBoundaries keeps rows
  | _, _ => []

/-- Consuming the remaining suffix of one complete table cycle returns the
boundary filter to position zero on the tail. -/
theorem encodeUnaryFramePeriodicBoundaryOutputFrom_cycle
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (position : UnaryFramePeriodicMarkedRowFilterMode selection)
    (rows rest : List (List Nat))
    (hlength : rows.length = selection.length - position.val) :
    encodeUnaryFramePeriodicBoundaryOutputFrom selection hnonempty position
        (rows ++ rest) =
      encodeUnaryFramePeriodicSelectedBoundaries
          (selection.drop position.val) rows ++
        encodeUnaryFramePeriodicBoundaryOutputFrom selection hnonempty
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
        encodeUnaryFramePeriodicBoundaryOutputFrom,
        encodeUnaryFramePeriodicSelectedBoundaries]
      cases rows with
      | nil =>
          have hlast : ¬position.val + 1 < selection.length := by
            simp only [List.length_cons, List.length_nil] at hlength
            omega
          simp [unaryFramePeriodicMarkedRowFilterNext, hlast,
            encodeUnaryFramePeriodicSelectedBoundaries, List.append_assoc]
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

/-- Full-width row groups are boundary-filtered independently with the same
table on every group. -/
theorem encodeUnaryFramePeriodicBoundaryOutput_groups
    (selection : List Bool) (hnonempty : 0 < selection.length)
    (groups : List (List (List Nat)))
    (hlength : ∀ rows ∈ groups, rows.length = selection.length) :
    encodeUnaryFramePeriodicBoundaryOutput selection hnonempty
        groups.flatten =
      groups.flatMap
        (encodeUnaryFramePeriodicSelectedBoundaries selection) := by
  induction groups with
  | nil => rfl
  | cons rows groups ih =>
      unfold encodeUnaryFramePeriodicBoundaryOutput
      simp only [List.flatten_cons, List.flatMap_cons]
      have hrows := hlength rows (by simp)
      rw [encodeUnaryFramePeriodicBoundaryOutputFrom_cycle
        selection hnonempty ⟨0, hnonempty⟩ rows groups.flatten
        (by simpa using hrows)]
      have hgroups : ∀ group ∈ groups,
          group.length = selection.length := by
        intro group hgroup
        exact hlength group (by simp [hgroup])
      have hih := ih hgroups
      unfold encodeUnaryFramePeriodicBoundaryOutput at hih
      rw [hih]
      simp

/-- Every fixed nonempty periodic boundary filter is a concrete linear-time
TM2. -/
noncomputable def unaryFramePeriodicBoundaryFilter_computableInPolyTime
    (selection : List Bool) (hnonempty : 0 < selection.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFramePeriodicBoundaries selection hnonempty) :=
  unaryFrameStatefulMap_computableInPolyTime
    (unaryFramePeriodicBoundaryFilterSpec selection hnonempty)

end CLRS.Chapter34.Turing.PolyBuilder
