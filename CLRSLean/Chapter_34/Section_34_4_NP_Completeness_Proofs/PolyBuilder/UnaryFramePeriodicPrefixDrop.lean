import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedGroupPrefixDrop
import Mathlib.Tactic

/-!
# Periodic prefix drops preserving unary-row boundaries

For a nonempty verifier-fixed table `drops`, this streaming controller cycles
through the table and removes `drops[i]` whole unary values from row `i`.
Unlike `UnaryFrameFixedGroupPrefixDrop`, every input `frameEnd` is retained.
This is the routing primitive needed when one duplicated descriptor packet is
split into several independently executable physical rows.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Apply the corresponding prefix drop to every row in one complete period. -/
def unaryFramePeriodicPrefixDropValues :
    List Nat → List (List Nat) → List (List Nat)
  | amount :: amounts, row :: rows =>
      row.drop amount :: unaryFramePeriodicPrefixDropValues amounts rows
  | _, _ => []

/-- Mark every row in every complete source period. -/
def encodeUnaryFramePeriodicPrefixDropInput
    (groups : List (List (List Nat))) : List UnaryFrameSym :=
  groups.flatMap fun group =>
    group.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

/-- Mark every independently transformed row. -/
def encodeUnaryFramePeriodicPrefixDropOutput
    (drops : List Nat) (groups : List (List (List Nat))) :
    List UnaryFrameSym :=
  groups.flatMap fun group =>
    (unaryFramePeriodicPrefixDropValues drops group).flatMap fun row =>
      encodeUnaryFrame row ++ [.frameEnd]

private def unaryFramePeriodicPrefixDropPred {drops : List Nat}
    (remaining : Fin (drops.sum + 1))
    (_hpositive : remaining.val ≠ 0) : Fin (drops.sum + 1) :=
  ⟨remaining.val - 1, by omega⟩

/-- One action of the periodic controller.  The existing fixed-group mode and
bounded counters are reused, but every boundary is emitted. -/
def unaryFramePeriodicPrefixDropAction
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (mode : UnaryFrameFixedGroupPrefixDropMode drops)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFrameFixedGroupPrefixDropMode drops :=
  let position := unaryFrameFixedGroupPrefixDropPosition mode
  match symbol with
  | .frameEnd =>
      if hlast : position.val + 1 = drops.length then
        (some .frameEnd,
          unaryFrameFixedGroupPrefixDropInitial drops hnonempty)
      else
        (some .frameEnd, unaryFrameFixedGroupPrefixDropBegin drops
          ⟨position.val + 1, by omega⟩)
  | .tick =>
      match mode with
      | .dropping position remaining =>
          if remaining.val = 0 then
            (some .tick, .preserving position)
          else
            (none, .dropping position remaining)
      | .preserving position => (some .tick, .preserving position)
  | .separator =>
      match mode with
      | .dropping position remaining =>
          if hzero : remaining.val = 0 then
            (some .separator, .preserving position)
          else
            (none, .dropping position
              (unaryFramePeriodicPrefixDropPred remaining hzero))
      | .preserving position =>
          (some .separator, .preserving position)

def unaryFramePeriodicPrefixDropSpec
    (drops : List Nat) (hnonempty : 0 < drops.length) :
    UnaryFrameStatefulMapSpec
      (UnaryFrameFixedGroupPrefixDropMode drops) :=
  { initial := unaryFrameFixedGroupPrefixDropInitial drops hnonempty
    action := unaryFramePeriodicPrefixDropAction drops hnonempty }

def rewriteUnaryFramePeriodicPrefixDrop
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFramePeriodicPrefixDropSpec drops hnonempty) input

private def unaryFramePeriodicPrefixDropAfterBoundary
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (tail : List UnaryFrameSym) :
    List UnaryFrameSym :=
  .frameEnd ::
    if hlast : position.val + 1 = drops.length then
      rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (unaryFrameFixedGroupPrefixDropInitial drops hnonempty) tail
    else
      rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (unaryFrameFixedGroupPrefixDropBegin drops
          ⟨position.val + 1, by omega⟩) tail

private theorem periodicPrefixDrop_preserving_ticks
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (.preserving position) (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicPrefixDropSpec drops hnonempty)
          (.preserving position) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFramePeriodicPrefixDropSpec,
        unaryFramePeriodicPrefixDropAction]
      exact congrArg (List.cons .tick) ih

private theorem periodicPrefixDrop_preserving_values
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (values : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (.preserving position)
        (encodeUnaryFrame values ++ .frameEnd :: tail) =
      encodeUnaryFrame values ++
        unaryFramePeriodicPrefixDropAfterBoundary
          drops hnonempty position tail := by
  induction values with
  | nil =>
      simp only [encodeUnaryFrame, List.flatMap_nil, List.nil_append]
      unfold unaryFramePeriodicPrefixDropAfterBoundary
      by_cases hlast : position.val + 1 = drops.length <;>
        simp [rewriteUnaryFrameStatefulFrom,
          unaryFramePeriodicPrefixDropSpec,
          unaryFramePeriodicPrefixDropAction,
          unaryFrameFixedGroupPrefixDropPosition, hlast]
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) ++ .frameEnd :: tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ .frameEnd :: tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [periodicPrefixDrop_preserving_ticks]
      change List.replicate value .tick ++
          (.separator :: rewriteUnaryFrameStatefulFrom
            (unaryFramePeriodicPrefixDropSpec drops hnonempty)
            (.preserving position)
            (encodeUnaryFrame values ++ .frameEnd :: tail)) = _
      rw [ih]
      simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

private theorem periodicPrefixDrop_dropping_ticks
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length)
    (remaining : Fin (drops.sum + 1))
    (hpositive : remaining.val ≠ 0) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (.dropping position remaining)
        (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (.dropping position remaining) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFramePeriodicPrefixDropSpec,
        unaryFramePeriodicPrefixDropAction]
      simp only [hpositive, ↓reduceIte]
      exact ih

private theorem periodicPrefixDrop_dropping_zero_block
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length)
    (remaining : Fin (drops.sum + 1)) (hzero : remaining.val = 0)
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (.dropping position remaining)
        (List.replicate count .tick ++ .separator :: tail) =
      List.replicate count .tick ++
        .separator :: rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicPrefixDropSpec drops hnonempty)
          (.preserving position) tail := by
  cases count with
  | zero =>
      simp [rewriteUnaryFrameStatefulFrom,
        unaryFramePeriodicPrefixDropSpec,
        unaryFramePeriodicPrefixDropAction, hzero]
  | succ count =>
      rw [List.replicate_succ, List.cons_append]
      simp only [rewriteUnaryFrameStatefulFrom,
        unaryFramePeriodicPrefixDropSpec,
        unaryFramePeriodicPrefixDropAction, hzero, ↓reduceIte]
      congr 1
      change rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicPrefixDropSpec drops hnonempty)
          (.preserving position)
          (List.replicate count .tick ++ .separator :: tail) = _
      rw [periodicPrefixDrop_preserving_ticks
        drops hnonempty position count (.separator :: tail)]
      rfl

private theorem periodicPrefixDrop_dropping_values
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length)
    (remaining : Fin (drops.sum + 1)) (values : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (.dropping position remaining)
        (encodeUnaryFrame values ++ .frameEnd :: tail) =
      encodeUnaryFrame (values.drop remaining.val) ++
        unaryFramePeriodicPrefixDropAfterBoundary
          drops hnonempty position tail := by
  induction values generalizing remaining with
  | nil =>
      simp only [encodeUnaryFrame, List.flatMap_nil, List.nil_append,
        List.drop_nil]
      unfold unaryFramePeriodicPrefixDropAfterBoundary
      by_cases hlast : position.val + 1 = drops.length <;>
        simp [rewriteUnaryFrameStatefulFrom,
          unaryFramePeriodicPrefixDropSpec,
          unaryFramePeriodicPrefixDropAction,
          unaryFrameFixedGroupPrefixDropPosition, hlast]
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) ++ .frameEnd :: tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ .frameEnd :: tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      by_cases hzero : remaining.val = 0
      · rw [periodicPrefixDrop_dropping_zero_block
          drops hnonempty position remaining hzero]
        rw [periodicPrefixDrop_preserving_values]
        simp [hzero, encodeUnaryFrame, encodeUnaryFrameBlock,
          List.append_assoc]
      · rw [periodicPrefixDrop_dropping_ticks
          drops hnonempty position remaining hzero]
        simp only [rewriteUnaryFrameStatefulFrom,
          unaryFramePeriodicPrefixDropSpec,
          unaryFramePeriodicPrefixDropAction, hzero]
        change rewriteUnaryFrameStatefulFrom
            (unaryFramePeriodicPrefixDropSpec drops hnonempty)
            (.dropping position
              (unaryFramePeriodicPrefixDropPred remaining hzero))
            (encodeUnaryFrame values ++ .frameEnd :: tail) = _
        rw [ih (unaryFramePeriodicPrefixDropPred remaining hzero)]
        congr 1
        have hsucc : remaining.val = (remaining.val - 1) + 1 := by omega
        rw [hsucc]
        simp [unaryFramePeriodicPrefixDropPred]

private theorem periodicPrefixDrop_rows
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (amounts : List Nat)
    (rows : List (List Nat)) (tail : List UnaryFrameSym)
    (hdrops : drops.drop position.val = amounts)
    (hlength : position.val + rows.length = drops.length) :
    rewriteUnaryFrameStatefulFrom
        (unaryFramePeriodicPrefixDropSpec drops hnonempty)
        (unaryFrameFixedGroupPrefixDropBegin drops position)
        ((rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) ++
          tail) =
      (unaryFramePeriodicPrefixDropValues amounts rows).flatMap
          (fun row => encodeUnaryFrame row ++ [.frameEnd]) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicPrefixDropSpec drops hnonempty)
          (unaryFrameFixedGroupPrefixDropInitial drops hnonempty) tail := by
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
        (encodeUnaryFrame row ++ [.frameEnd]) ++
              rows.flatMap
                (fun item => encodeUnaryFrame item ++ [.frameEnd]) ++ tail =
            encodeUnaryFrame row ++ .frameEnd ::
              (rows.flatMap
                (fun item => encodeUnaryFrame item ++ [.frameEnd]) ++ tail) by
        simp [List.append_assoc]]
      unfold unaryFrameFixedGroupPrefixDropBegin
      rw [periodicPrefixDrop_dropping_values]
      have hremaining :
          (unaryFrameFixedGroupPrefixDropRemaining drops position).val =
            amount := hamount
      rw [hremaining]
      simp only [unaryFramePeriodicPrefixDropValues, List.flatMap_cons]
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
        simp [unaryFramePeriodicPrefixDropAfterBoundary, hlast,
          unaryFramePeriodicPrefixDropValues, List.append_assoc]
      · let next : Fin drops.length := ⟨position.val + 1, by omega⟩
        have hnextLength : next.val + rows.length = drops.length := by
          simp only [List.length_cons] at hlength
          dsimp only [next]
          omega
        have hnextDrop : drops.drop next.val = restAmounts := by
          have hdrop := List.drop_eq_getElem_cons hposition
          rw [hdrops] at hdrop
          simp only [next]
          simpa [hamount] using (congrArg List.tail hdrop).symm
        rw [unaryFramePeriodicPrefixDropAfterBoundary]
        simp only [hlast, ↓reduceDIte]
        rw [show (⟨position.val + 1, by omega⟩ : Fin drops.length) =
            next by apply Fin.ext; rfl]
        rw [ih next restAmounts hnextDrop hnextLength]
        simp [List.append_assoc]

/-- Exact action on every family of complete fixed-size row periods. -/
theorem rewriteUnaryFramePeriodicPrefixDrop_groups
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (groups : List (List (List Nat)))
    (hlength : ∀ group ∈ groups, group.length = drops.length) :
    rewriteUnaryFramePeriodicPrefixDrop drops hnonempty
        (encodeUnaryFramePeriodicPrefixDropInput groups) =
      encodeUnaryFramePeriodicPrefixDropOutput drops groups := by
  unfold rewriteUnaryFramePeriodicPrefixDrop rewriteUnaryFrameStateful
    encodeUnaryFramePeriodicPrefixDropInput
    encodeUnaryFramePeriodicPrefixDropOutput
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      have hgroup := hlength group (by simp)
      have hrest : ∀ other ∈ groups,
          other.length = drops.length := by
        intro other hother
        exact hlength other (by simp [hother])
      simp only [List.flatMap_cons]
      have hrun := periodicPrefixDrop_rows drops hnonempty
        (⟨0, hnonempty⟩ : Fin drops.length) drops group
        (groups.flatMap fun rows =>
          rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd])
        (by simp) (by simpa using hgroup)
      change rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicPrefixDropSpec drops hnonempty)
          (unaryFrameFixedGroupPrefixDropBegin drops ⟨0, hnonempty⟩)
          (group.flatMap
              (fun row => encodeUnaryFrame row ++ [.frameEnd]) ++
            groups.flatMap
              (fun rows => rows.flatMap fun row =>
                encodeUnaryFrame row ++ [.frameEnd])) = _
      rw [hrun]
      have ih' := ih hrest
      change rewriteUnaryFrameStatefulFrom
          (unaryFramePeriodicPrefixDropSpec drops hnonempty)
          (unaryFrameFixedGroupPrefixDropInitial drops hnonempty)
          (groups.flatMap
            (fun rows => rows.flatMap fun row =>
              encodeUnaryFrame row ++ [.frameEnd])) = _ at ih'
      rw [ih']

/-- The periodic boundary-preserving prefix-drop pass is a concrete
linear-time TM2. -/
noncomputable def unaryFramePeriodicPrefixDrop_computableInPolyTime
    (drops : List Nat) (hnonempty : 0 < drops.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFramePeriodicPrefixDrop drops hnonempty) :=
  unaryFrameStatefulMap_computableInPolyTime
    (unaryFramePeriodicPrefixDropSpec drops hnonempty)

end CLRS.Chapter34.Turing.PolyBuilder
