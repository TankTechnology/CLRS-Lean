import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedSuffixDrop
import Mathlib.Data.List.DropRight
import Mathlib.Tactic

/-!
# Periodic suffix drops preserving unary-row boundaries

For a nonempty verifier-fixed table `drops`, this controller removes a
possibly different number of whole unary values from the end of every row in
one fixed-size period.  It reverses the complete stream, cycles through the
reversed table in finite control, and reverses the result again.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Row transformation in the order encountered by the reversed stream. -/
def unaryFramePeriodicReversedDropValues :
    List Nat → List (List Nat) → List (List Nat)
  | amount :: amounts, row :: rows =>
      row.rdrop amount :: unaryFramePeriodicReversedDropValues amounts rows
  | _, _ => []

/-- Apply corresponding suffix drops in the original row order.  The
definition exposes the reverse/filter/reverse implementation directly. -/
def unaryFramePeriodicSuffixDropValues
    (drops : List Nat) (rows : List (List Nat)) : List (List Nat) :=
  (unaryFramePeriodicReversedDropValues drops.reverse rows.reverse).reverse

def encodeUnaryFramePeriodicSuffixDropInput
    (groups : List (List (List Nat))) : List UnaryFrameSym :=
  groups.flatMap fun group =>
    group.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

def encodeUnaryFramePeriodicSuffixDropOutput
    (drops : List Nat) (groups : List (List (List Nat))) :
    List UnaryFrameSym :=
  groups.flatMap fun group =>
    (unaryFramePeriodicSuffixDropValues drops group).flatMap fun row =>
      encodeUnaryFrame row ++ [.frameEnd]

/-- Reversed representation: every row boundary precedes its
separator-first reversed value stream. -/
def encodeUnaryFramePeriodicSuffixDropReversed
    (groups : List (List (List Nat))) : List UnaryFrameSym :=
  groups.flatMap fun group =>
    group.flatMap fun row => .frameEnd :: (encodeUnaryFrame row).reverse

/-- Group family encountered after reversing an ordinary group stream. -/
def unaryFramePeriodicSuffixDropReverseGroups
    (groups : List (List (List Nat))) : List (List (List Nat)) :=
  groups.reverse.map List.reverse

/-- Reversed transformed family encountered after suffix deletion. -/
def unaryFramePeriodicSuffixDropReverseOutputGroups
    (drops : List Nat) (groups : List (List (List Nat))) :
    List (List (List Nat)) :=
  groups.reverse.map fun group =>
    unaryFramePeriodicReversedDropValues drops.reverse group.reverse

theorem encodeUnaryFramePeriodicSuffixDropInput_reverse
    (groups : List (List (List Nat))) :
    (encodeUnaryFramePeriodicSuffixDropInput groups).reverse =
      encodeUnaryFramePeriodicSuffixDropReversed
        (unaryFramePeriodicSuffixDropReverseGroups groups) := by
  unfold encodeUnaryFramePeriodicSuffixDropInput
    encodeUnaryFramePeriodicSuffixDropReversed
    unaryFramePeriodicSuffixDropReverseGroups
  rw [show
      (groups.flatMap fun group =>
        group.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]).reverse =
        groups.reverse.flatMap
          (List.reverse ∘ fun group =>
            group.flatMap fun row =>
              encodeUnaryFrame row ++ [.frameEnd]) by
    simp [List.reverse_flatMap]]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro group hgroup
  simp [List.reverse_flatMap, List.reverse_append,
    Function.comp_def]

theorem encodeUnaryFramePeriodicSuffixDropOutput_reverse
    (drops : List Nat) (groups : List (List (List Nat))) :
    (encodeUnaryFramePeriodicSuffixDropOutput drops groups).reverse =
      encodeUnaryFramePeriodicSuffixDropReversed
        (unaryFramePeriodicSuffixDropReverseOutputGroups drops groups) := by
  unfold encodeUnaryFramePeriodicSuffixDropOutput
    encodeUnaryFramePeriodicSuffixDropReversed
    unaryFramePeriodicSuffixDropReverseOutputGroups
    unaryFramePeriodicSuffixDropValues
  rw [show
      (groups.flatMap fun group =>
        (unaryFramePeriodicReversedDropValues drops.reverse group.reverse).reverse.flatMap
          fun row => encodeUnaryFrame row ++ [.frameEnd]).reverse =
        groups.reverse.flatMap
          (List.reverse ∘ fun group =>
            (unaryFramePeriodicReversedDropValues drops.reverse
              group.reverse).reverse.flatMap
              fun row => encodeUnaryFrame row ++ [.frameEnd]) by
    simp [List.reverse_flatMap]]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro group hgroup
  simp [List.reverse_flatMap, List.reverse_append,
    Function.comp_def]

/-- Finite control for the separator-first reversed pass.  `position` is the
table entry used at the next boundary; the remaining modes store its successor
while the current row is processed. -/
inductive UnaryFramePeriodicReversedDropMode (drops : List Nat)
  | boundary (position : Fin drops.length)
  | dropping (next : Fin drops.length) (remaining : Fin (drops.sum + 1))
  | droppingTicks (next : Fin drops.length)
      (remaining : Fin (drops.sum + 1))
  | preserving (next : Fin drops.length)
deriving DecidableEq, Fintype

def unaryFramePeriodicReversedDropNext
    {drops : List Nat} :
    UnaryFramePeriodicReversedDropMode drops → Fin drops.length
  | .boundary position => position
  | .dropping next _ => next
  | .droppingTicks next _ => next
  | .preserving next => next

def unaryFramePeriodicReversedDropAdvance
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) : Fin drops.length :=
  if hnext : position.val + 1 < drops.length then
    ⟨position.val + 1, hnext⟩
  else
    ⟨0, hnonempty⟩

def unaryFramePeriodicReversedDropRemaining
    (drops : List Nat) (position : Fin drops.length) :
    Fin (drops.sum + 1) :=
  ⟨drops.get position, by
    have hmem : drops.get position ∈ drops := List.get_mem drops position
    have hle : drops.get position ≤ drops.sum := List.le_sum_of_mem hmem
    omega⟩

private def unaryFramePeriodicReversedDropPred {drops : List Nat}
    (remaining : Fin (drops.sum + 1))
    (_hpositive : remaining.val ≠ 0) : Fin (drops.sum + 1) :=
  ⟨remaining.val - 1, by omega⟩

def unaryFramePeriodicReversedDropBegin
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) :
    UnaryFramePeriodicReversedDropMode drops :=
  .dropping (unaryFramePeriodicReversedDropAdvance drops hnonempty position)
    (unaryFramePeriodicReversedDropRemaining drops position)

def unaryFramePeriodicReversedDropInitial
    (drops : List Nat) (hnonempty : 0 < drops.length) :
    UnaryFramePeriodicReversedDropMode drops :=
  .boundary ⟨0, hnonempty⟩

def unaryFramePeriodicReversedDropAction
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (mode : UnaryFramePeriodicReversedDropMode drops)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFramePeriodicReversedDropMode drops :=
  match symbol with
  | .frameEnd =>
      (some .frameEnd,
        unaryFramePeriodicReversedDropBegin drops hnonempty
          (unaryFramePeriodicReversedDropNext mode))
  | .tick =>
      match mode with
      | .boundary position => (some .tick, .boundary position)
      | .dropping next remaining =>
          if remaining.val = 0 then
            (some .tick, .preserving next)
          else
            (none, .dropping next remaining)
      | .droppingTicks next remaining =>
          (none, .droppingTicks next remaining)
      | .preserving next => (some .tick, .preserving next)
  | .separator =>
      match mode with
      | .boundary position => (some .separator, .boundary position)
      | .dropping next remaining =>
          if hzero : remaining.val = 0 then
            (some .separator, .preserving next)
          else
            (none, .droppingTicks next
              (unaryFramePeriodicReversedDropPred remaining hzero))
      | .droppingTicks next remaining =>
          if hzero : remaining.val = 0 then
            (some .separator, .preserving next)
          else
            (none, .droppingTicks next
              (unaryFramePeriodicReversedDropPred remaining hzero))
      | .preserving next => (some .separator, .preserving next)

def unaryFramePeriodicReversedDropSpec
    (drops : List Nat) (hnonempty : 0 < drops.length) :
    UnaryFrameStatefulMapSpec (UnaryFramePeriodicReversedDropMode drops) :=
  { initial := unaryFramePeriodicReversedDropInitial drops hnonempty
    action := unaryFramePeriodicReversedDropAction drops hnonempty }

def rewriteUnaryFramePeriodicReversedDrop
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFramePeriodicReversedDropSpec drops hnonempty) input

private def IsUnaryFrameBoundaryTail : List UnaryFrameSym → Prop
  | [] => True
  | .frameEnd :: _ => True
  | _ => False

private theorem periodicReversedDrop_mode_eq_boundary
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (mode : UnaryFramePeriodicReversedDropMode drops)
    (position : Fin drops.length)
    (hposition : unaryFramePeriodicReversedDropNext mode = position)
    (tail : List UnaryFrameSym) (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty) mode tail =
      rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.boundary position) tail := by
  cases tail with
  | nil => rfl
  | cons symbol rest =>
      cases symbol <;>
        simp_all [IsUnaryFrameBoundaryTail,
          rewriteUnaryFrameStatefulFrom,
          unaryFramePeriodicReversedDropSpec,
          unaryFramePeriodicReversedDropAction,
          unaryFramePeriodicReversedDropNext]

private theorem periodicReversedDrop_preserving_ticks
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (next : Fin drops.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.preserving next) (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicReversedDropSpec drops hnonempty)
          (.preserving next) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFramePeriodicReversedDropSpec,
        unaryFramePeriodicReversedDropAction]
      exact congrArg (List.cons .tick) ih

private theorem periodicReversedDrop_dropping_ticks
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (next : Fin drops.length) (remaining : Fin (drops.sum + 1))
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.droppingTicks next remaining)
        (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.droppingTicks next remaining) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFramePeriodicReversedDropSpec,
        unaryFramePeriodicReversedDropAction]
      exact ih

private theorem periodicReversedDrop_preserving_values
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (next : Fin drops.length) (values : List Nat)
    (tail : List UnaryFrameSym) (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.preserving next)
        (encodeReversedUnaryFrameValues values ++ tail) =
      encodeReversedUnaryFrameValues values ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicReversedDropSpec drops hnonempty)
          (.boundary next) tail := by
  induction values with
  | nil =>
      simpa [encodeReversedUnaryFrameValues] using
        periodicReversedDrop_mode_eq_boundary drops hnonempty
          (.preserving next) next rfl tail htail
  | cons value rest ih =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons]
      simp only [unaryFramePeriodicReversedDropSpec]
      change .separator ::
          rewriteUnaryFrameStatefulFrom
            (unaryFramePeriodicReversedDropSpec drops hnonempty)
            (.preserving next)
            (List.replicate value .tick ++
              encodeReversedUnaryFrameValues rest ++ tail) = _
      rw [show List.replicate value UnaryFrameSym.tick ++
            encodeReversedUnaryFrameValues rest ++ tail =
          List.replicate value UnaryFrameSym.tick ++
            (encodeReversedUnaryFrameValues rest ++ tail) by
        simp [List.append_assoc]]
      rw [periodicReversedDrop_preserving_ticks drops hnonempty next value
        (encodeReversedUnaryFrameValues rest ++ tail)]
      rw [ih]
      simp [encodeReversedUnaryFrameValues,
        unaryFramePeriodicReversedDropSpec, List.append_assoc]

private theorem periodicReversedDrop_droppingTicks_values_eq
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (next : Fin drops.length) (remaining : Fin (drops.sum + 1))
    (values : List Nat) (tail : List UnaryFrameSym)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.droppingTicks next remaining)
        (encodeReversedUnaryFrameValues values ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.dropping next remaining)
        (encodeReversedUnaryFrameValues values ++ tail) := by
  cases values with
  | nil =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_nil,
        List.nil_append]
      rw [periodicReversedDrop_mode_eq_boundary drops hnonempty
        (.droppingTicks next remaining) next rfl tail htail]
      rw [periodicReversedDrop_mode_eq_boundary drops hnonempty
        (.dropping next remaining) next rfl tail htail]
  | cons value rest =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons,
        List.cons_append, rewriteUnaryFrameStatefulFrom,
        unaryFramePeriodicReversedDropSpec,
        unaryFramePeriodicReversedDropAction]

private theorem periodicReversedDrop_values
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (next : Fin drops.length) (remaining : Fin (drops.sum + 1))
    (values : List Nat) (tail : List UnaryFrameSym)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.dropping next remaining)
        (encodeReversedUnaryFrameValues values ++ tail) =
      encodeReversedUnaryFrameValues (values.drop remaining.val) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicReversedDropSpec drops hnonempty)
          (.boundary next) tail := by
  induction values generalizing remaining with
  | nil =>
      simpa [encodeReversedUnaryFrameValues] using
        periodicReversedDrop_mode_eq_boundary drops hnonempty
          (.dropping next remaining) next rfl tail htail
  | cons value rest ih =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons]
      by_cases hzero : remaining.val = 0
      · simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
          unaryFramePeriodicReversedDropSpec,
          unaryFramePeriodicReversedDropAction, hzero, ↓reduceDIte]
        change .separator ::
            rewriteUnaryFrameStatefulFrom
              (unaryFramePeriodicReversedDropSpec drops hnonempty)
              (.preserving next)
              (List.replicate value .tick ++
                encodeReversedUnaryFrameValues rest ++ tail) = _
        rw [show List.replicate value UnaryFrameSym.tick ++
              encodeReversedUnaryFrameValues rest ++ tail =
            List.replicate value UnaryFrameSym.tick ++
              (encodeReversedUnaryFrameValues rest ++ tail) by
          simp [List.append_assoc]]
        rw [periodicReversedDrop_preserving_ticks drops hnonempty next value
          (encodeReversedUnaryFrameValues rest ++ tail)]
        rw [periodicReversedDrop_preserving_values drops hnonempty next rest
          tail htail]
        simp only [List.drop_zero]
        simp [encodeReversedUnaryFrameValues,
          unaryFramePeriodicReversedDropSpec, List.append_assoc]
      · simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
          unaryFramePeriodicReversedDropSpec,
          unaryFramePeriodicReversedDropAction, hzero, ↓reduceDIte]
        change rewriteUnaryFrameStatefulFrom
            (unaryFramePeriodicReversedDropSpec drops hnonempty)
            (.droppingTicks next
              (unaryFramePeriodicReversedDropPred remaining hzero))
            (List.replicate value .tick ++
              encodeReversedUnaryFrameValues rest ++ tail) = _
        rw [show List.replicate value UnaryFrameSym.tick ++
              encodeReversedUnaryFrameValues rest ++ tail =
            List.replicate value UnaryFrameSym.tick ++
              (encodeReversedUnaryFrameValues rest ++ tail) by
          simp [List.append_assoc]]
        rw [periodicReversedDrop_dropping_ticks drops hnonempty next
          (unaryFramePeriodicReversedDropPred remaining hzero) value
          (encodeReversedUnaryFrameValues rest ++ tail)]
        rw [periodicReversedDrop_droppingTicks_values_eq drops hnonempty next
          (unaryFramePeriodicReversedDropPred remaining hzero)
          rest tail htail]
        rw [ih (unaryFramePeriodicReversedDropPred remaining hzero)]
        have hremaining :
            remaining.val =
              (unaryFramePeriodicReversedDropPred remaining hzero).val + 1 := by
          simp [unaryFramePeriodicReversedDropPred]
          omega
        rw [hremaining]
        simp only [List.drop_succ_cons]
        simp only [encodeReversedUnaryFrameValues,
          unaryFramePeriodicReversedDropSpec]

private theorem periodicReversedDrop_rows
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (amounts : List Nat)
    (rows : List (List Nat)) (tail : List UnaryFrameSym)
    (hdrops : drops.drop position.val = amounts)
    (hlength : position.val + rows.length = drops.length)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicReversedDropSpec drops hnonempty)
        (.boundary position)
        ((rows.flatMap fun row =>
          .frameEnd :: (encodeUnaryFrame row).reverse) ++ tail) =
      (unaryFramePeriodicReversedDropValues amounts rows).flatMap
          (fun row => .frameEnd :: (encodeUnaryFrame row).reverse) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicReversedDropSpec drops hnonempty)
          (unaryFramePeriodicReversedDropInitial drops hnonempty) tail := by
  induction rows generalizing position amounts with
  | nil =>
      simp only [List.length_nil, Nat.add_zero] at hlength
      omega
  | cons row rows ih =>
      have hposition : position.val < drops.length := position.isLt
      have hamounts : amounts ≠ [] := by
        intro hnil
        have := congrArg List.length hdrops
        simp [hnil] at this
        omega
      obtain ⟨amount, restAmounts, rfl⟩ := List.exists_cons_of_ne_nil hamounts
      have hamount : drops.get position = amount := by
        have hdrop := List.drop_eq_getElem_cons hposition
        rw [hdrops] at hdrop
        simpa using (congrArg List.head? hdrop).symm
      simp only [List.flatMap_cons]
      rw [show
        (.frameEnd :: (encodeUnaryFrame row).reverse) ++
              rows.flatMap
                (fun item => .frameEnd :: (encodeUnaryFrame item).reverse) ++
              tail =
            .frameEnd :: ((encodeUnaryFrame row).reverse ++
              (rows.flatMap
                (fun item => .frameEnd :: (encodeUnaryFrame item).reverse) ++
                tail)) by simp [List.append_assoc]]
      simp only [rewriteUnaryFrameStatefulFrom,
        unaryFramePeriodicReversedDropSpec,
        unaryFramePeriodicReversedDropAction,
        unaryFramePeriodicReversedDropNext]
      unfold unaryFramePeriodicReversedDropBegin
      rw [encodeUnaryFrame_reverse]
      change .frameEnd ::
          rewriteUnaryFrameStatefulFrom
            (unaryFramePeriodicReversedDropSpec drops hnonempty)
            (.dropping
              (unaryFramePeriodicReversedDropAdvance drops hnonempty position)
              (unaryFramePeriodicReversedDropRemaining drops position))
            (encodeReversedUnaryFrameValues row.reverse ++
              (rows.flatMap
                (fun item =>
                  .frameEnd :: (encodeUnaryFrame item).reverse) ++ tail)) = _
      rw [periodicReversedDrop_values drops hnonempty
        (unaryFramePeriodicReversedDropAdvance drops hnonempty position)
        (unaryFramePeriodicReversedDropRemaining drops position)
        row.reverse
        (rows.flatMap
          (fun item => .frameEnd :: (encodeUnaryFrame item).reverse) ++ tail)]
      · have hremaining :
            (unaryFramePeriodicReversedDropRemaining drops position).val =
              amount := hamount
        rw [hremaining]
        rw [show row.reverse.drop amount = (row.rdrop amount).reverse by
          simp [List.rdrop_eq_reverse_drop_reverse]]
        rw [← encodeUnaryFrame_reverse]
        simp only [unaryFramePeriodicReversedDropValues, List.flatMap_cons]
        by_cases hlast : position.val + 1 = drops.length
        · have hrows : rows = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_cons] at hlength
            omega
          subst rows
          have hrest : restAmounts = [] := by
            have hdropLength := congrArg List.length hdrops
            simp only [List.length_cons, List.length_drop] at hdropLength
            apply List.eq_nil_of_length_eq_zero
            omega
          subst restAmounts
          have hadvance :
              unaryFramePeriodicReversedDropAdvance drops hnonempty position =
                (⟨0, hnonempty⟩ : Fin drops.length) := by
            unfold unaryFramePeriodicReversedDropAdvance
            simp only [show ¬ position.val + 1 < drops.length by omega,
              ↓reduceDIte]
          rw [hadvance]
          simp [unaryFramePeriodicReversedDropInitial,
            unaryFramePeriodicReversedDropSpec,
            unaryFramePeriodicReversedDropValues]
        · let next : Fin drops.length :=
            unaryFramePeriodicReversedDropAdvance drops hnonempty position
          have hnextVal : next.val = position.val + 1 := by
            unfold next unaryFramePeriodicReversedDropAdvance
            simp only [show position.val + 1 < drops.length by omega,
              ↓reduceDIte]
          have hnextLength : next.val + rows.length = drops.length := by
            rw [hnextVal]
            simp only [List.length_cons] at hlength
            omega
          have hnextDrop : drops.drop next.val = restAmounts := by
            have hdrop := List.drop_eq_getElem_cons hposition
            rw [hdrops] at hdrop
            rw [hnextVal]
            simpa [hamount] using (congrArg List.tail hdrop).symm
          rw [show unaryFramePeriodicReversedDropAdvance drops hnonempty
              position = next by rfl]
          rw [ih next restAmounts hnextDrop hnextLength]
          simp [unaryFramePeriodicReversedDropSpec, List.append_assoc]
      · cases rows with
        | nil => exact htail
        | cons next rest => simp [IsUnaryFrameBoundaryTail]

/-- Exact separator-first action on complete reversed row periods. -/
theorem rewriteUnaryFramePeriodicReversedDrop_groups
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (groups : List (List (List Nat)))
    (hlength : ∀ group ∈ groups, group.length = drops.length) :
    rewriteUnaryFramePeriodicReversedDrop drops hnonempty
        (encodeUnaryFramePeriodicSuffixDropReversed groups) =
      encodeUnaryFramePeriodicSuffixDropReversed
        (groups.map fun group =>
          unaryFramePeriodicReversedDropValues drops group) := by
  unfold rewriteUnaryFramePeriodicReversedDrop rewriteUnaryFrameStateful
    encodeUnaryFramePeriodicSuffixDropReversed
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      have hgroup := hlength group (by simp)
      have hrest : ∀ other ∈ groups,
          other.length = drops.length := by
        intro other hother
        exact hlength other (by simp [hother])
      simp only [List.flatMap_cons, List.map_cons]
      have hrun := periodicReversedDrop_rows drops hnonempty
        (⟨0, hnonempty⟩ : Fin drops.length) drops group
        (groups.flatMap fun rows =>
          rows.flatMap fun row =>
            .frameEnd :: (encodeUnaryFrame row).reverse)
        (by simp) (by simpa using hgroup)
        (by
          cases groups with
          | nil => simp [IsUnaryFrameBoundaryTail]
          | cons next rest =>
              have hnext : next.length = drops.length :=
                hrest next (by simp)
              have hne : next ≠ [] := by
                apply List.ne_nil_of_length_pos
                omega
              obtain ⟨row, rows, rfl⟩ := List.exists_cons_of_ne_nil hne
              simp [IsUnaryFrameBoundaryTail])
      change rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicReversedDropSpec drops hnonempty)
          (.boundary ⟨0, hnonempty⟩)
          (group.flatMap
              (fun row => .frameEnd :: (encodeUnaryFrame row).reverse) ++
            groups.flatMap
              (fun rows => rows.flatMap fun row =>
                .frameEnd :: (encodeUnaryFrame row).reverse)) = _
      rw [hrun]
      have ih' := ih hrest
      change rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicReversedDropSpec drops hnonempty)
          (unaryFramePeriodicReversedDropInitial drops hnonempty)
          (groups.flatMap
            (fun rows => rows.flatMap fun row =>
              .frameEnd :: (encodeUnaryFrame row).reverse)) = _ at ih'
      rw [ih']

/-- Delete periodic fixed suffixes by reverse/filter/reverse. -/
def rewriteUnaryFramePeriodicSuffixDrop
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  (rewriteUnaryFramePeriodicReversedDrop drops.reverse
    (by simpa using hnonempty) input.reverse).reverse

private theorem reverseGroups_length
    (drops : List Nat) (groups : List (List (List Nat)))
    (hlength : ∀ group ∈ groups, group.length = drops.length) :
    ∀ group ∈ unaryFramePeriodicSuffixDropReverseGroups groups,
      group.length = drops.reverse.length := by
  intro group hgroup
  unfold unaryFramePeriodicSuffixDropReverseGroups at hgroup
  rw [List.mem_map] at hgroup
  rcases hgroup with ⟨source, hsource, rfl⟩
  simp only [List.length_reverse]
  exact hlength source (List.mem_reverse.mp hsource)

/-- Exact semantics on every family of complete fixed-size row periods. -/
theorem rewriteUnaryFramePeriodicSuffixDrop_groups
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (groups : List (List (List Nat)))
    (hlength : ∀ group ∈ groups, group.length = drops.length) :
    rewriteUnaryFramePeriodicSuffixDrop drops hnonempty
        (encodeUnaryFramePeriodicSuffixDropInput groups) =
      encodeUnaryFramePeriodicSuffixDropOutput drops groups := by
  unfold rewriteUnaryFramePeriodicSuffixDrop
  rw [encodeUnaryFramePeriodicSuffixDropInput_reverse]
  rw [rewriteUnaryFramePeriodicReversedDrop_groups drops.reverse
    (by simpa using hnonempty)
    (unaryFramePeriodicSuffixDropReverseGroups groups)
    (reverseGroups_length drops groups hlength)]
  rw [show
      (unaryFramePeriodicSuffixDropReverseGroups groups).map
          (fun group =>
            unaryFramePeriodicReversedDropValues drops.reverse group) =
        unaryFramePeriodicSuffixDropReverseOutputGroups drops groups by
    unfold unaryFramePeriodicSuffixDropReverseGroups
      unaryFramePeriodicSuffixDropReverseOutputGroups
    simp [List.map_map, Function.comp_def]]
  rw [← encodeUnaryFramePeriodicSuffixDropOutput_reverse]
  simp

/-- Periodic fixed suffix deletion is computed by a concrete polynomial-time
TM2. -/
noncomputable def unaryFramePeriodicSuffixDrop_computableInPolyTime
    (drops : List Nat) (hnonempty : 0 < drops.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFramePeriodicSuffixDrop drops hnonempty) := by
  let reversed := reverse_computableInPolyTime (Γ := UnaryFrameSym)
  let filtered := unaryFrameStatefulMap_computableInPolyTime
    (unaryFramePeriodicReversedDropSpec drops.reverse
      (by simpa using hnonempty))
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
          rewriteUnaryFramePeriodicSuffixDrop,
          rewriteUnaryFramePeriodicReversedDrop] using run }

end CLRS.Chapter34.Turing.PolyBuilder
