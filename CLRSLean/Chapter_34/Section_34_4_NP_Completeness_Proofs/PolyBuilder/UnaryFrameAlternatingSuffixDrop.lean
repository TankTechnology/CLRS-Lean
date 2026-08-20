import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedSuffixDrop
import Mathlib.Data.List.DropRight
import Mathlib.Tactic

/-!
# Dropping alternating fixed suffixes from pairs of unary-frame rows

Stack push routing stores a height row followed by a flattened cell row.  The
two rows lose different verifier-fixed suffix widths.  This controller reverses
the complete pair family, alternates the two fixed counters in finite control,
and reverses the result again.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Row-major encoding of pairs of unary-frame rows. -/
def encodeUnaryFrameAlternatingSuffixDropInput
    (pairs : List (List Nat × List Nat)) : List UnaryFrameSym :=
  pairs.flatMap fun pair =>
    encodeUnaryFrame pair.1 ++ [.frameEnd] ++
      encodeUnaryFrame pair.2 ++ [.frameEnd]

/-- Target encoding after deleting the two fixed suffix widths. -/
def encodeUnaryFrameAlternatingSuffixDropOutput
    (firstAmount secondAmount : Nat)
    (pairs : List (List Nat × List Nat)) : List UnaryFrameSym :=
  pairs.flatMap fun pair =>
    encodeUnaryFrame (pair.1.rdrop firstAmount) ++ [.frameEnd] ++
      encodeUnaryFrame (pair.2.rdrop secondAmount) ++ [.frameEnd]

/-- After whole-stream reversal, the second row of each pair occurs first. -/
def encodeUnaryFrameAlternatingSuffixDropReversed
    (pairs : List (List Nat × List Nat)) : List UnaryFrameSym :=
  pairs.flatMap fun pair =>
    .frameEnd :: (encodeUnaryFrame pair.2).reverse ++
      .frameEnd :: (encodeUnaryFrame pair.1).reverse

theorem encodeUnaryFrameAlternatingSuffixDropInput_reverse
    (pairs : List (List Nat × List Nat)) :
    (encodeUnaryFrameAlternatingSuffixDropInput pairs).reverse =
      encodeUnaryFrameAlternatingSuffixDropReversed pairs.reverse := by
  rw [show (encodeUnaryFrameAlternatingSuffixDropInput pairs).reverse =
      pairs.reverse.flatMap
        (List.reverse ∘ fun pair =>
          encodeUnaryFrame pair.1 ++ [.frameEnd] ++
            encodeUnaryFrame pair.2 ++ [.frameEnd]) by
    simp [encodeUnaryFrameAlternatingSuffixDropInput,
      List.reverse_flatMap]]
  unfold encodeUnaryFrameAlternatingSuffixDropReversed
  apply List.flatMap_congr
  intro pair hpair
  simp [List.reverse_append]

theorem encodeUnaryFrameAlternatingSuffixDropOutput_reverse
    (firstAmount secondAmount : Nat)
    (pairs : List (List Nat × List Nat)) :
    (encodeUnaryFrameAlternatingSuffixDropOutput
        firstAmount secondAmount pairs).reverse =
      encodeUnaryFrameAlternatingSuffixDropReversed
        ((pairs.map fun pair =>
          (pair.1.rdrop firstAmount, pair.2.rdrop secondAmount)).reverse) := by
  rw [show
      (encodeUnaryFrameAlternatingSuffixDropOutput
        firstAmount secondAmount pairs).reverse =
        pairs.reverse.flatMap
          (List.reverse ∘ fun pair =>
            encodeUnaryFrame (pair.1.rdrop firstAmount) ++ [.frameEnd] ++
              encodeUnaryFrame (pair.2.rdrop secondAmount) ++ [.frameEnd]) by
    simp [encodeUnaryFrameAlternatingSuffixDropOutput,
      List.reverse_flatMap]]
  unfold encodeUnaryFrameAlternatingSuffixDropReversed
  rw [← List.map_reverse, List.flatMap_map]
  apply List.flatMap_congr
  intro pair hpair
  simp [List.reverse_append]

/-- Finite-control modes.  The Boolean records which counter the next row
boundary must start: `true` for the first row, `false` for the second. -/
inductive UnaryFrameAlternatingReversedDropMode
    (firstAmount secondAmount : Nat)
  | boundary (useFirst : Bool)
  | dropping (nextUseFirst : Bool)
      (remaining : Fin (firstAmount + secondAmount + 1))
  | droppingTicks (nextUseFirst : Bool)
      (remaining : Fin (firstAmount + secondAmount + 1))
  | preserving (nextUseFirst : Bool)
deriving DecidableEq, Fintype

def unaryFrameAlternatingReversedDropNext
    {firstAmount secondAmount : Nat} :
    UnaryFrameAlternatingReversedDropMode firstAmount secondAmount → Bool
  | .boundary useFirst => useFirst
  | .dropping nextUseFirst _ => nextUseFirst
  | .droppingTicks nextUseFirst _ => nextUseFirst
  | .preserving nextUseFirst => nextUseFirst

def unaryFrameAlternatingReversedDropInitialRemaining
    (firstAmount secondAmount : Nat) (useFirst : Bool) :
    Fin (firstAmount + secondAmount + 1) :=
  if useFirst then
    ⟨firstAmount, by omega⟩
  else
    ⟨secondAmount, by omega⟩

private def unaryFrameAlternatingReversedDropPred
    {firstAmount secondAmount : Nat}
    (remaining : Fin (firstAmount + secondAmount + 1))
    (_hpositive : remaining.val ≠ 0) :
    Fin (firstAmount + secondAmount + 1) :=
  ⟨remaining.val - 1, by omega⟩

def unaryFrameAlternatingReversedDropBegin
    (firstAmount secondAmount : Nat) (useFirst : Bool) :
    UnaryFrameAlternatingReversedDropMode firstAmount secondAmount :=
  .dropping (!useFirst)
    (unaryFrameAlternatingReversedDropInitialRemaining
      firstAmount secondAmount useFirst)

/-- One action of the separator-first middle pass. -/
def unaryFrameAlternatingReversedDropAction
    (firstAmount secondAmount : Nat)
    (mode : UnaryFrameAlternatingReversedDropMode firstAmount secondAmount)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym ×
      UnaryFrameAlternatingReversedDropMode firstAmount secondAmount :=
  match symbol with
  | .frameEnd =>
      (some .frameEnd,
        unaryFrameAlternatingReversedDropBegin firstAmount secondAmount
          (unaryFrameAlternatingReversedDropNext mode))
  | .tick =>
      match mode with
      | .boundary useFirst => (some .tick, .boundary useFirst)
      | .dropping nextUseFirst remaining =>
          if remaining.val = 0 then
            (some .tick, .preserving nextUseFirst)
          else
            (none, .dropping nextUseFirst remaining)
      | .droppingTicks nextUseFirst remaining =>
          (none, .droppingTicks nextUseFirst remaining)
      | .preserving nextUseFirst =>
          (some .tick, .preserving nextUseFirst)
  | .separator =>
      match mode with
      | .boundary useFirst => (some .separator, .boundary useFirst)
      | .dropping nextUseFirst remaining =>
          if hzero : remaining.val = 0 then
            (some .separator, .preserving nextUseFirst)
          else
            (none, .droppingTicks nextUseFirst
              (unaryFrameAlternatingReversedDropPred remaining hzero))
      | .droppingTicks nextUseFirst remaining =>
          if hzero : remaining.val = 0 then
            (some .separator, .preserving nextUseFirst)
          else
            (none, .droppingTicks nextUseFirst
              (unaryFrameAlternatingReversedDropPred remaining hzero))
      | .preserving nextUseFirst =>
          (some .separator, .preserving nextUseFirst)

def unaryFrameAlternatingReversedDropSpec
    (firstAmount secondAmount : Nat) :
    UnaryFrameStatefulMapSpec
      (UnaryFrameAlternatingReversedDropMode firstAmount secondAmount) :=
  { initial := .boundary false
    action := unaryFrameAlternatingReversedDropAction
      firstAmount secondAmount }

def rewriteUnaryFrameAlternatingReversedDrop
    (firstAmount secondAmount : Nat) (input : List UnaryFrameSym) :
    List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount) input

private def IsUnaryFrameBoundaryTail : List UnaryFrameSym → Prop
  | [] => True
  | .frameEnd :: _ => True
  | _ => False

private theorem alternatingDrop_mode_eq_boundary
    (firstAmount secondAmount : Nat)
    (mode : UnaryFrameAlternatingReversedDropMode firstAmount secondAmount)
    (nextUseFirst : Bool)
    (hnext : unaryFrameAlternatingReversedDropNext mode = nextUseFirst)
    (tail : List UnaryFrameSym) (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        mode tail =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        (.boundary nextUseFirst) tail := by
  cases tail with
  | nil => rfl
  | cons symbol rest =>
      cases symbol <;>
        simp_all [IsUnaryFrameBoundaryTail,
          rewriteUnaryFrameStatefulFrom,
          unaryFrameAlternatingReversedDropSpec,
          unaryFrameAlternatingReversedDropAction,
          unaryFrameAlternatingReversedDropNext]

private theorem alternatingDrop_preserving_ticks
    (firstAmount secondAmount count : Nat) (nextUseFirst : Bool)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        (.preserving nextUseFirst)
        (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
          (.preserving nextUseFirst) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameAlternatingReversedDropSpec,
        unaryFrameAlternatingReversedDropAction]
      exact congrArg (List.cons .tick) ih

private theorem alternatingDrop_dropping_ticks
    (firstAmount secondAmount count : Nat) (nextUseFirst : Bool)
    (remaining : Fin (firstAmount + secondAmount + 1))
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        (.droppingTicks nextUseFirst remaining)
        (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        (.droppingTicks nextUseFirst remaining) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameAlternatingReversedDropSpec,
        unaryFrameAlternatingReversedDropAction]
      exact ih

private theorem alternatingDrop_preserving_values
    (firstAmount secondAmount : Nat) (nextUseFirst : Bool)
    (values : List Nat) (tail : List UnaryFrameSym)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        (.preserving nextUseFirst)
        (encodeReversedUnaryFrameValues values ++ tail) =
      encodeReversedUnaryFrameValues values ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
          (.boundary nextUseFirst) tail := by
  induction values with
  | nil =>
      simpa [encodeReversedUnaryFrameValues] using
        alternatingDrop_mode_eq_boundary firstAmount secondAmount
          (.preserving nextUseFirst) nextUseFirst rfl tail htail
  | cons value rest ih =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons]
      simp only [unaryFrameAlternatingReversedDropSpec]
      change .separator ::
          rewriteUnaryFrameStatefulFrom
            (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
            (.preserving nextUseFirst)
            (List.replicate value .tick ++
              encodeReversedUnaryFrameValues rest ++ tail) = _
      rw [show List.replicate value UnaryFrameSym.tick ++
            encodeReversedUnaryFrameValues rest ++ tail =
          List.replicate value UnaryFrameSym.tick ++
            (encodeReversedUnaryFrameValues rest ++ tail) by
        simp [List.append_assoc]]
      rw [alternatingDrop_preserving_ticks firstAmount secondAmount value
        nextUseFirst (encodeReversedUnaryFrameValues rest ++ tail)]
      rw [ih]
      simp [encodeReversedUnaryFrameValues,
        unaryFrameAlternatingReversedDropSpec, List.append_assoc]

private theorem alternatingDrop_droppingTicks_values_eq
    (firstAmount secondAmount : Nat) (nextUseFirst : Bool)
    (remaining : Fin (firstAmount + secondAmount + 1))
    (values : List Nat) (tail : List UnaryFrameSym)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        (.droppingTicks nextUseFirst remaining)
        (encodeReversedUnaryFrameValues values ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        (.dropping nextUseFirst remaining)
        (encodeReversedUnaryFrameValues values ++ tail) := by
  cases values with
  | nil =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_nil,
        List.nil_append]
      rw [alternatingDrop_mode_eq_boundary firstAmount secondAmount
        (.droppingTicks nextUseFirst remaining) nextUseFirst rfl tail htail]
      rw [alternatingDrop_mode_eq_boundary firstAmount secondAmount
        (.dropping nextUseFirst remaining) nextUseFirst rfl tail htail]
  | cons value rest =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons,
        List.cons_append, rewriteUnaryFrameStatefulFrom,
        unaryFrameAlternatingReversedDropSpec,
        unaryFrameAlternatingReversedDropAction]

private theorem alternatingDrop_values
    (firstAmount secondAmount : Nat) (nextUseFirst : Bool)
    (remaining : Fin (firstAmount + secondAmount + 1))
    (values : List Nat) (tail : List UnaryFrameSym)
    (htail : IsUnaryFrameBoundaryTail tail) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
        (.dropping nextUseFirst remaining)
        (encodeReversedUnaryFrameValues values ++ tail) =
      encodeReversedUnaryFrameValues (values.drop remaining.val) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
          (.boundary nextUseFirst) tail := by
  induction values generalizing remaining with
  | nil =>
      simpa [encodeReversedUnaryFrameValues] using
        alternatingDrop_mode_eq_boundary firstAmount secondAmount
          (.dropping nextUseFirst remaining) nextUseFirst rfl tail htail
  | cons value rest ih =>
      simp only [encodeReversedUnaryFrameValues, List.flatMap_cons]
      by_cases hzero : remaining.val = 0
      · simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
          unaryFrameAlternatingReversedDropSpec,
          unaryFrameAlternatingReversedDropAction, hzero, ↓reduceDIte]
        change .separator ::
            rewriteUnaryFrameStatefulFrom
              (unaryFrameAlternatingReversedDropSpec
                firstAmount secondAmount)
              (.preserving nextUseFirst)
              (List.replicate value .tick ++
                encodeReversedUnaryFrameValues rest ++ tail) = _
        rw [show List.replicate value UnaryFrameSym.tick ++
              encodeReversedUnaryFrameValues rest ++ tail =
            List.replicate value UnaryFrameSym.tick ++
              (encodeReversedUnaryFrameValues rest ++ tail) by
          simp [List.append_assoc]]
        rw [alternatingDrop_preserving_ticks firstAmount secondAmount value
          nextUseFirst (encodeReversedUnaryFrameValues rest ++ tail)]
        rw [alternatingDrop_preserving_values firstAmount secondAmount
          nextUseFirst rest tail htail]
        simp only [List.drop_zero]
        simp [encodeReversedUnaryFrameValues,
          unaryFrameAlternatingReversedDropSpec, List.append_assoc]
      · simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
          unaryFrameAlternatingReversedDropSpec,
          unaryFrameAlternatingReversedDropAction, hzero, ↓reduceDIte]
        change rewriteUnaryFrameStatefulFrom
            (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
            (.droppingTicks nextUseFirst
              (unaryFrameAlternatingReversedDropPred remaining hzero))
            (List.replicate value .tick ++
              encodeReversedUnaryFrameValues rest ++ tail) = _
        rw [show List.replicate value UnaryFrameSym.tick ++
              encodeReversedUnaryFrameValues rest ++ tail =
            List.replicate value UnaryFrameSym.tick ++
              (encodeReversedUnaryFrameValues rest ++ tail) by
          simp [List.append_assoc]]
        rw [alternatingDrop_dropping_ticks firstAmount secondAmount value
          nextUseFirst
          (unaryFrameAlternatingReversedDropPred remaining hzero)
          (encodeReversedUnaryFrameValues rest ++ tail)]
        rw [alternatingDrop_droppingTicks_values_eq firstAmount secondAmount
          nextUseFirst
          (unaryFrameAlternatingReversedDropPred remaining hzero)
          rest tail htail]
        rw [ih (unaryFrameAlternatingReversedDropPred remaining hzero)]
        have hremaining :
            remaining.val =
              (unaryFrameAlternatingReversedDropPred remaining hzero).val +
                1 := by
          simp [unaryFrameAlternatingReversedDropPred]
          omega
        rw [hremaining]
        simp only [List.drop_succ_cons]
        simp only [encodeReversedUnaryFrameValues,
          unaryFrameAlternatingReversedDropSpec]

private theorem alternatingSuffixDrop_reversed_pairs
    (firstAmount secondAmount : Nat)
    (pairs : List (List Nat × List Nat)) :
    rewriteUnaryFrameAlternatingReversedDrop firstAmount secondAmount
        (encodeUnaryFrameAlternatingSuffixDropReversed pairs) =
      encodeUnaryFrameAlternatingSuffixDropReversed
        (pairs.map fun pair =>
          (pair.1.rdrop firstAmount, pair.2.rdrop secondAmount)) := by
  unfold rewriteUnaryFrameAlternatingReversedDrop rewriteUnaryFrameStateful
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      simp only [encodeUnaryFrameAlternatingSuffixDropReversed,
        List.flatMap_cons, List.map_cons]
      rw [show
        (.frameEnd :: (encodeUnaryFrame pair.2).reverse ++
            .frameEnd :: (encodeUnaryFrame pair.1).reverse) ++
            rest.flatMap (fun item =>
              .frameEnd :: (encodeUnaryFrame item.2).reverse ++
                .frameEnd :: (encodeUnaryFrame item.1).reverse) =
          .frameEnd :: ((encodeUnaryFrame pair.2).reverse ++
            .frameEnd :: ((encodeUnaryFrame pair.1).reverse ++
              encodeUnaryFrameAlternatingSuffixDropReversed rest)) by
        simp [encodeUnaryFrameAlternatingSuffixDropReversed,
          List.append_assoc]]
      simp only [rewriteUnaryFrameStatefulFrom,
        unaryFrameAlternatingReversedDropSpec,
        unaryFrameAlternatingReversedDropAction,
        unaryFrameAlternatingReversedDropNext,
        unaryFrameAlternatingReversedDropBegin]
      rw [encodeUnaryFrame_reverse]
      change .frameEnd ::
          rewriteUnaryFrameStatefulFrom
            (unaryFrameAlternatingReversedDropSpec
              firstAmount secondAmount)
            (.dropping true
              (unaryFrameAlternatingReversedDropInitialRemaining
                firstAmount secondAmount false))
            (encodeReversedUnaryFrameValues pair.2.reverse ++
              .frameEnd :: ((encodeUnaryFrame pair.1).reverse ++
                encodeUnaryFrameAlternatingSuffixDropReversed rest)) = _
      rw [alternatingDrop_values firstAmount secondAmount true
        (unaryFrameAlternatingReversedDropInitialRemaining
          firstAmount secondAmount false)
        pair.2.reverse
        (.frameEnd :: ((encodeUnaryFrame pair.1).reverse ++
          encodeUnaryFrameAlternatingSuffixDropReversed rest))]
      · simp only [unaryFrameAlternatingReversedDropInitialRemaining,
          Bool.false_eq_true, ↓reduceIte]
        rw [show pair.2.reverse.drop secondAmount =
            (pair.2.rdrop secondAmount).reverse by
          simp [List.rdrop_eq_reverse_drop_reverse]]
        simp only [rewriteUnaryFrameStatefulFrom,
          unaryFrameAlternatingReversedDropSpec,
          unaryFrameAlternatingReversedDropAction,
          unaryFrameAlternatingReversedDropNext,
          unaryFrameAlternatingReversedDropBegin, Bool.not_true]
        rw [encodeUnaryFrame_reverse pair.1]
        change .frameEnd ::
            (encodeReversedUnaryFrameValues
                (pair.2.rdrop secondAmount).reverse ++
              .frameEnd ::
                rewriteUnaryFrameStatefulFrom
                  (unaryFrameAlternatingReversedDropSpec
                    firstAmount secondAmount)
                  (.dropping false
                    (unaryFrameAlternatingReversedDropInitialRemaining
                      firstAmount secondAmount true))
                  (encodeReversedUnaryFrameValues pair.1.reverse ++
                    encodeUnaryFrameAlternatingSuffixDropReversed rest)) = _
        rw [alternatingDrop_values firstAmount secondAmount false
          (unaryFrameAlternatingReversedDropInitialRemaining
            firstAmount secondAmount true)
          pair.1.reverse
          (encodeUnaryFrameAlternatingSuffixDropReversed rest)]
        · simp only [unaryFrameAlternatingReversedDropInitialRemaining,
              ↓reduceIte]
          rw [show pair.1.reverse.drop firstAmount =
              (pair.1.rdrop firstAmount).reverse by
            simp [List.rdrop_eq_reverse_drop_reverse]]
          rw [← encodeUnaryFrame_reverse]
          have ih' :
              rewriteUnaryFrameStatefulFrom
                  (unaryFrameAlternatingReversedDropSpec
                    firstAmount secondAmount)
                  (.boundary false)
                  (encodeUnaryFrameAlternatingSuffixDropReversed rest) =
                encodeUnaryFrameAlternatingSuffixDropReversed
                  (rest.map fun item =>
                    (item.1.rdrop firstAmount,
                      item.2.rdrop secondAmount)) := by
            simpa [unaryFrameAlternatingReversedDropSpec] using ih
          rw [ih']
          simp [encodeUnaryFrameAlternatingSuffixDropReversed,
            List.append_assoc]
        · cases rest <;> simp [IsUnaryFrameBoundaryTail,
              encodeUnaryFrameAlternatingSuffixDropReversed]
      · simp [IsUnaryFrameBoundaryTail]

/-- Delete two alternating fixed suffixes by reverse/filter/reverse. -/
def rewriteUnaryFrameAlternatingSuffixDrop
    (firstAmount secondAmount : Nat) (input : List UnaryFrameSym) :
    List UnaryFrameSym :=
  (rewriteUnaryFrameAlternatingReversedDrop
    firstAmount secondAmount input.reverse).reverse

/-- Exact semantics for every row-pair family. -/
theorem rewriteUnaryFrameAlternatingSuffixDrop_pairs
    (firstAmount secondAmount : Nat)
    (pairs : List (List Nat × List Nat)) :
    rewriteUnaryFrameAlternatingSuffixDrop firstAmount secondAmount
        (encodeUnaryFrameAlternatingSuffixDropInput pairs) =
      encodeUnaryFrameAlternatingSuffixDropOutput
        firstAmount secondAmount pairs := by
  unfold rewriteUnaryFrameAlternatingSuffixDrop
  rw [encodeUnaryFrameAlternatingSuffixDropInput_reverse]
  rw [alternatingSuffixDrop_reversed_pairs]
  rw [show
      (pairs.reverse.map fun pair =>
        (pair.1.rdrop firstAmount, pair.2.rdrop secondAmount)) =
        (pairs.map fun pair =>
          (pair.1.rdrop firstAmount,
            pair.2.rdrop secondAmount)).reverse by simp]
  rw [← encodeUnaryFrameAlternatingSuffixDropOutput_reverse]
  simp

/-- Alternating fixed suffix deletion is computed by a concrete
polynomial-time TM2. -/
noncomputable def unaryFrameAlternatingSuffixDrop_computableInPolyTime
    (firstAmount secondAmount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameAlternatingSuffixDrop firstAmount secondAmount) := by
  let reversed := reverse_computableInPolyTime (Γ := UnaryFrameSym)
  let filtered := unaryFrameStatefulMap_computableInPolyTime
    (unaryFrameAlternatingReversedDropSpec firstAmount secondAmount)
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
          rewriteUnaryFrameAlternatingSuffixDrop,
          rewriteUnaryFrameAlternatingReversedDrop] using run }

end CLRS.Chapter34.Turing.PolyBuilder
