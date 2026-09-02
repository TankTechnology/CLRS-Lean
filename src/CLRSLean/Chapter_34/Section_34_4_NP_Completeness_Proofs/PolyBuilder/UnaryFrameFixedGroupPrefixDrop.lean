import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import Mathlib.Tactic

/-!
# Fixed-position prefix drops inside groups of unary rows

For a nonempty verifier-fixed table `drops`, this streaming controller reads
groups of exactly `drops.length` unary-frame rows.  At position `i` it removes
the first `drops[i]` unary values, erases the internal row boundary, and emits
one `frameEnd` only after the last position.  Thus the transformed rows are
concatenated into one output row per input group.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Apply corresponding prefix drops and concatenate the resulting rows. -/
def unaryFrameFixedGroupPrefixDropValues :
    List Nat → List (List Nat) → List Nat
  | amount :: amounts, row :: rows =>
      row.drop amount ++ unaryFrameFixedGroupPrefixDropValues amounts rows
  | _, _ => []

/-- Separate every source segment with `frameEnd`. -/
def encodeUnaryFrameFixedGroupPrefixDropInput
    (groups : List (List (List Nat))) : List UnaryFrameSym :=
  groups.flatMap fun group =>
    group.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

/-- One concatenated marked row per transformed segment group. -/
def encodeUnaryFrameFixedGroupPrefixDropOutput
    (drops : List Nat) (groups : List (List (List Nat))) :
    List UnaryFrameSym :=
  groups.flatMap fun group =>
    encodeUnaryFrame (unaryFrameFixedGroupPrefixDropValues drops group) ++
      [.frameEnd]

/-- Finite control remembers the segment position and the bounded number of
whole unary values still to erase in that segment. -/
inductive UnaryFrameFixedGroupPrefixDropMode (drops : List Nat)
  | dropping (position : Fin drops.length)
      (remaining : Fin (drops.sum + 1))
  | preserving (position : Fin drops.length)
deriving DecidableEq, Fintype

def unaryFrameFixedGroupPrefixDropPosition {drops : List Nat} :
    UnaryFrameFixedGroupPrefixDropMode drops → Fin drops.length
  | .dropping position _ => position
  | .preserving position => position

def unaryFrameFixedGroupPrefixDropRemaining
    (drops : List Nat) (position : Fin drops.length) :
    Fin (drops.sum + 1) :=
  ⟨drops.get position, by
    have hmem : drops.get position ∈ drops := List.get_mem drops position
    have hle : drops.get position ≤ drops.sum := List.le_sum_of_mem hmem
    omega⟩

private def unaryFrameFixedGroupPrefixDropPred {drops : List Nat}
    (remaining : Fin (drops.sum + 1))
    (_hpositive : remaining.val ≠ 0) : Fin (drops.sum + 1) :=
  ⟨remaining.val - 1, by omega⟩

def unaryFrameFixedGroupPrefixDropBegin
    (drops : List Nat) (position : Fin drops.length) :
    UnaryFrameFixedGroupPrefixDropMode drops :=
  .dropping position
    (unaryFrameFixedGroupPrefixDropRemaining drops position)

def unaryFrameFixedGroupPrefixDropInitial
    (drops : List Nat) (hnonempty : 0 < drops.length) :
    UnaryFrameFixedGroupPrefixDropMode drops :=
  unaryFrameFixedGroupPrefixDropBegin drops ⟨0, hnonempty⟩

/-- One streaming action.  Internal `frameEnd`s are erased; the last one in
each fixed-size group is retained and resets the position. -/
def unaryFrameFixedGroupPrefixDropAction
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
        (none, unaryFrameFixedGroupPrefixDropBegin drops
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
              (unaryFrameFixedGroupPrefixDropPred remaining hzero))
      | .preserving position =>
          (some .separator, .preserving position)

def unaryFrameFixedGroupPrefixDropSpec
    (drops : List Nat) (hnonempty : 0 < drops.length) :
    UnaryFrameStatefulMapSpec
      (UnaryFrameFixedGroupPrefixDropMode drops) :=
  { initial := unaryFrameFixedGroupPrefixDropInitial drops hnonempty
    action := unaryFrameFixedGroupPrefixDropAction drops hnonempty }

def rewriteUnaryFrameFixedGroupPrefixDrop
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFrameFixedGroupPrefixDropSpec drops hnonempty) input

private def unaryFrameFixedGroupPrefixDropAfterBoundary
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (tail : List UnaryFrameSym) :
    List UnaryFrameSym :=
  if hlast : position.val + 1 = drops.length then
    .frameEnd :: rewriteUnaryFrameStatefulFrom
      (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
      (unaryFrameFixedGroupPrefixDropInitial drops hnonempty) tail
  else
    rewriteUnaryFrameStatefulFrom
      (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
      (unaryFrameFixedGroupPrefixDropBegin drops
        ⟨position.val + 1, by omega⟩) tail

private theorem fixedGroupPrefixDrop_preserving_ticks
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
        (.preserving position) (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
          (.preserving position) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedGroupPrefixDropSpec,
        unaryFrameFixedGroupPrefixDropAction]
      exact congrArg (List.cons .tick) ih

private theorem fixedGroupPrefixDrop_preserving_values
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (values : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
        (.preserving position)
        (encodeUnaryFrame values ++ .frameEnd :: tail) =
      encodeUnaryFrame values ++
        unaryFrameFixedGroupPrefixDropAfterBoundary
          drops hnonempty position tail := by
  induction values with
  | nil =>
      simp only [encodeUnaryFrame, List.flatMap_nil, List.nil_append]
      unfold unaryFrameFixedGroupPrefixDropAfterBoundary
      by_cases hlast : position.val + 1 = drops.length <;>
        simp [rewriteUnaryFrameStatefulFrom,
          unaryFrameFixedGroupPrefixDropSpec,
          unaryFrameFixedGroupPrefixDropAction,
          unaryFrameFixedGroupPrefixDropPosition, hlast]
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) ++ .frameEnd :: tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ .frameEnd :: tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [fixedGroupPrefixDrop_preserving_ticks]
      change List.replicate value .tick ++
          (.separator :: rewriteUnaryFrameStatefulFrom
            (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
            (.preserving position)
            (encodeUnaryFrame values ++ .frameEnd :: tail)) = _
      rw [ih]
      simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

private theorem fixedGroupPrefixDrop_dropping_ticks
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length)
    (remaining : Fin (drops.sum + 1))
    (hpositive : remaining.val ≠ 0) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
        (.dropping position remaining)
        (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
        (.dropping position remaining) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedGroupPrefixDropSpec,
        unaryFrameFixedGroupPrefixDropAction]
      simp only [hpositive, ↓reduceIte]
      exact ih

private theorem fixedGroupPrefixDrop_dropping_zero_block
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length)
    (remaining : Fin (drops.sum + 1)) (hzero : remaining.val = 0)
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
        (.dropping position remaining)
        (List.replicate count .tick ++ .separator :: tail) =
      List.replicate count .tick ++
        .separator :: rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
          (.preserving position) tail := by
  cases count with
  | zero =>
      simp [rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedGroupPrefixDropSpec,
        unaryFrameFixedGroupPrefixDropAction, hzero]
  | succ count =>
      rw [List.replicate_succ, List.cons_append]
      simp only [rewriteUnaryFrameStatefulFrom,
        unaryFrameFixedGroupPrefixDropSpec,
        unaryFrameFixedGroupPrefixDropAction, hzero, ↓reduceIte]
      congr 1
      change rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
          (.preserving position)
          (List.replicate count .tick ++ .separator :: tail) = _
      rw [fixedGroupPrefixDrop_preserving_ticks
        drops hnonempty position count (.separator :: tail)]
      rfl

private theorem fixedGroupPrefixDrop_dropping_values
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length)
    (remaining : Fin (drops.sum + 1)) (values : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
        (.dropping position remaining)
        (encodeUnaryFrame values ++ .frameEnd :: tail) =
      encodeUnaryFrame (values.drop remaining.val) ++
        unaryFrameFixedGroupPrefixDropAfterBoundary
          drops hnonempty position tail := by
  induction values generalizing remaining with
  | nil =>
      simp only [encodeUnaryFrame, List.flatMap_nil, List.nil_append,
        List.drop_nil]
      unfold unaryFrameFixedGroupPrefixDropAfterBoundary
      by_cases hlast : position.val + 1 = drops.length <;>
        simp [rewriteUnaryFrameStatefulFrom,
          unaryFrameFixedGroupPrefixDropSpec,
          unaryFrameFixedGroupPrefixDropAction,
          unaryFrameFixedGroupPrefixDropPosition, hlast]
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) ++ .frameEnd :: tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ .frameEnd :: tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      by_cases hzero : remaining.val = 0
      · rw [fixedGroupPrefixDrop_dropping_zero_block
          drops hnonempty position remaining hzero]
        rw [fixedGroupPrefixDrop_preserving_values]
        simp [hzero, encodeUnaryFrame, encodeUnaryFrameBlock,
          List.append_assoc]
      · rw [fixedGroupPrefixDrop_dropping_ticks
          drops hnonempty position remaining hzero]
        simp only [rewriteUnaryFrameStatefulFrom,
          unaryFrameFixedGroupPrefixDropSpec,
          unaryFrameFixedGroupPrefixDropAction, hzero]
        change rewriteUnaryFrameStatefulFrom
            (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
            (.dropping position
              (unaryFrameFixedGroupPrefixDropPred remaining hzero))
            (encodeUnaryFrame values ++ .frameEnd :: tail) = _
        rw [ih (unaryFrameFixedGroupPrefixDropPred remaining hzero)]
        congr 1
        have hsucc : remaining.val = (remaining.val - 1) + 1 := by omega
        rw [hsucc]
        simp [unaryFrameFixedGroupPrefixDropPred]

private theorem fixedGroupPrefixDrop_rows
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (position : Fin drops.length) (amounts : List Nat)
    (rows : List (List Nat)) (tail : List UnaryFrameSym)
    (hdrops : drops.drop position.val = amounts)
    (hlength : position.val + rows.length = drops.length) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
        (unaryFrameFixedGroupPrefixDropBegin drops position)
        ((rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) ++
          tail) =
      encodeUnaryFrame
          (unaryFrameFixedGroupPrefixDropValues amounts rows) ++
        .frameEnd :: rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
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
      rw [fixedGroupPrefixDrop_dropping_values]
      have hremaining :
          (unaryFrameFixedGroupPrefixDropRemaining drops position).val =
            amount := by
        exact hamount
      rw [hremaining]
      simp only [unaryFrameFixedGroupPrefixDropValues]
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
        simp [unaryFrameFixedGroupPrefixDropAfterBoundary, hlast,
          unaryFrameFixedGroupPrefixDropValues]
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
        rw [unaryFrameFixedGroupPrefixDropAfterBoundary]
        simp only [hlast, ↓reduceDIte]
        rw [show (⟨position.val + 1, by omega⟩ : Fin drops.length) =
            next by apply Fin.ext; rfl]
        rw [ih next restAmounts hnextDrop hnextLength]
        simp [encodeUnaryFrame, List.append_assoc]

/-- Exact action on every family of complete fixed-size segment groups. -/
theorem rewriteUnaryFrameFixedGroupPrefixDrop_groups
    (drops : List Nat) (hnonempty : 0 < drops.length)
    (groups : List (List (List Nat)))
    (hlength : ∀ group ∈ groups, group.length = drops.length) :
    rewriteUnaryFrameFixedGroupPrefixDrop drops hnonempty
        (encodeUnaryFrameFixedGroupPrefixDropInput groups) =
      encodeUnaryFrameFixedGroupPrefixDropOutput drops groups := by
  unfold rewriteUnaryFrameFixedGroupPrefixDrop
    rewriteUnaryFrameStateful
    encodeUnaryFrameFixedGroupPrefixDropInput
    encodeUnaryFrameFixedGroupPrefixDropOutput
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      have hgroup := hlength group (by simp)
      have hrest : ∀ other ∈ groups,
          other.length = drops.length := by
        intro other hother
        exact hlength other (by simp [hother])
      simp only [List.flatMap_cons]
      rw [show group.flatMap
            (fun row => encodeUnaryFrame row ++ [.frameEnd]) ++
              groups.flatMap
                (fun rows => rows.flatMap fun row =>
                  encodeUnaryFrame row ++ [.frameEnd]) =
          group.flatMap (fun row => encodeUnaryFrame row ++ [.frameEnd]) ++
            groups.flatMap
              (fun rows => rows.flatMap fun row =>
                encodeUnaryFrame row ++ [.frameEnd]) by rfl]
      have hrun := fixedGroupPrefixDrop_rows drops hnonempty
        (⟨0, hnonempty⟩ : Fin drops.length) drops group
        (groups.flatMap fun rows =>
          rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd])
        (by simp) (by simpa using hgroup)
      change rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
          (unaryFrameFixedGroupPrefixDropBegin drops ⟨0, hnonempty⟩)
          (group.flatMap
              (fun row => encodeUnaryFrame row ++ [.frameEnd]) ++
            groups.flatMap
              (fun rows => rows.flatMap fun row =>
                encodeUnaryFrame row ++ [.frameEnd])) = _
      rw [hrun]
      have ih' := ih hrest
      change rewriteUnaryFrameStatefulFrom
          (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)
          (unaryFrameFixedGroupPrefixDropInitial drops hnonempty)
          (groups.flatMap
            (fun rows => rows.flatMap fun row =>
              encodeUnaryFrame row ++ [.frameEnd])) = _ at ih'
      rw [ih']
      simp [List.append_assoc]

/-- The fixed group prefix-drop pass is a concrete linear-time TM2. -/
noncomputable def unaryFrameFixedGroupPrefixDrop_computableInPolyTime
    (drops : List Nat) (hnonempty : 0 < drops.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameFixedGroupPrefixDrop drops hnonempty) :=
  unaryFrameStatefulMap_computableInPolyTime
    (unaryFrameFixedGroupPrefixDropSpec drops hnonempty)

end CLRS.Chapter34.Turing.PolyBuilder
