import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixSplice
import Mathlib.Tactic

/-!
# Three-way routing of fixed-width tagged unary rows

Each source row contains a unary tag followed by three candidate fixed-width
payloads.  Tag zero selects the first payload, tag one selects the second,
and every larger tag selects the third.  Unselected payloads are erased, while
the selected payload receives its own fixed delimiter table.

The implementation is a finite-state streaming specialization of
`UnaryFrameStatefulMap`; in particular, it is a concrete linear-time TM2 and
does not appeal to an abstract computability closure principle.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The three tag classes distinguished by the router. -/
inductive UnaryFrameThreeWayTag
  | zero
  | one
  | many
deriving DecidableEq, Fintype

def unaryFrameThreeWayTagNext :
    UnaryFrameThreeWayTag → UnaryFrameThreeWayTag
  | .zero => .one
  | .one => .many
  | .many => .many

def unaryFrameThreeWayTagOfNat : Nat → UnaryFrameThreeWayTag
  | 0 => .zero
  | 1 => .one
  | _ + 2 => .many

@[simp] theorem unaryFrameThreeWayTagOfNat_add_two (count : Nat) :
    unaryFrameThreeWayTagOfNat (count + 2) = .many := by
  cases count <;> rfl

/-- Finite streaming modes: scan the tag, then visit all three candidate
segments in their source order. -/
inductive UnaryFrameThreeWayTaggedRowMode
    (zeroCount oneCount manyCount : Nat)
  | tag (selection : UnaryFrameThreeWayTag)
  | zeroPayload (selection : UnaryFrameThreeWayTag)
      (position : Fin zeroCount)
  | onePayload (selection : UnaryFrameThreeWayTag)
      (position : Fin oneCount)
  | manyPayload (selection : UnaryFrameThreeWayTag)
      (position : Fin manyCount)
deriving DecidableEq, Fintype

/-- One router action.  Source separators are either erased or replaced by
the selected segment's verifier-fixed delimiter. -/
def unaryFrameThreeWayTaggedRowAction
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (mode : UnaryFrameThreeWayTaggedRowMode
      zeroDelimiters.length oneDelimiters.length manyDelimiters.length)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFrameThreeWayTaggedRowMode
      zeroDelimiters.length oneDelimiters.length manyDelimiters.length :=
  match mode with
  | .tag selection =>
      match symbol with
      | .tick => (none, .tag (unaryFrameThreeWayTagNext selection))
      | .separator => (none, .zeroPayload selection ⟨0, hzero⟩)
      | .frameEnd => (none, .tag .zero)
  | .zeroPayload selection position =>
      match symbol with
      | .tick =>
          (if selection = .zero then some .tick
            else none, .zeroPayload selection position)
      | .separator =>
          let emitted :=
            if selection = .zero then
              some (zeroDelimiters.get position)
            else none
          if hnext : position.val + 1 < zeroDelimiters.length then
            (emitted, .zeroPayload selection ⟨position.val + 1, hnext⟩)
          else (emitted, .onePayload selection ⟨0, hone⟩)
      | .frameEnd => (some .frameEnd, .tag .zero)
  | .onePayload selection position =>
      match symbol with
      | .tick =>
          (if selection = .one then some .tick
            else none, .onePayload selection position)
      | .separator =>
          let emitted :=
            if selection = .one then
              some (oneDelimiters.get position)
            else none
          if hnext : position.val + 1 < oneDelimiters.length then
            (emitted, .onePayload selection ⟨position.val + 1, hnext⟩)
          else (emitted, .manyPayload selection ⟨0, hmany⟩)
      | .frameEnd => (some .frameEnd, .tag .zero)
  | .manyPayload selection position =>
      match symbol with
      | .tick =>
          (if selection = .many then some .tick
            else none, .manyPayload selection position)
      | .separator =>
          let emitted :=
            if selection = .many then
              some (manyDelimiters.get position)
            else none
          if hnext : position.val + 1 < manyDelimiters.length then
            (emitted, .manyPayload selection ⟨position.val + 1, hnext⟩)
          else (emitted, .tag .zero)
      | .frameEnd => (some .frameEnd, .tag .zero)

def unaryFrameThreeWayTaggedRowSpec
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length) :
    UnaryFrameStatefulMapSpec
      (UnaryFrameThreeWayTaggedRowMode
        zeroDelimiters.length oneDelimiters.length manyDelimiters.length) :=
  { initial := .tag .zero
    action := unaryFrameThreeWayTaggedRowAction
      zeroDelimiters oneDelimiters manyDelimiters hzero hone hmany }

def rewriteUnaryFrameThreeWayTaggedRows
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameStateful
    (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
      manyDelimiters hzero hone hmany) input

private theorem threeWay_tag_many_ticks
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.tag .many) (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.tag .many) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameStatefulFrom,
        unaryFrameThreeWayTaggedRowSpec,
        unaryFrameThreeWayTaggedRowAction,
        unaryFrameThreeWayTagNext]
      exact ih

private theorem threeWay_tag_field
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (tag : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.tag .zero)
        (List.replicate tag .tick ++ .separator :: tail) =
      rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.zeroPayload (unaryFrameThreeWayTagOfNat tag) ⟨0, hzero⟩)
        tail := by
  cases tag with
  | zero => rfl
  | succ tag =>
      cases tag with
      | zero => rfl
      | succ tag =>
          rw [show List.replicate (Nat.succ (Nat.succ tag)) .tick ++
                .separator :: tail =
              [.tick, .tick] ++
                (List.replicate tag .tick ++ .separator :: tail) by
            simp [List.replicate_succ, List.append_assoc]]
          simp only [List.cons_append,
            rewriteUnaryFrameStatefulFrom,
            unaryFrameThreeWayTaggedRowSpec,
            unaryFrameThreeWayTaggedRowAction,
            unaryFrameThreeWayTagNext]
          simp only [List.nil_append]
          have hticks := threeWay_tag_many_ticks zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany tag (.separator :: tail)
          simp only [unaryFrameThreeWayTaggedRowSpec] at hticks
          rw [hticks]
          change rewriteUnaryFrameStatefulFrom
              { initial := .tag .zero
                action := unaryFrameThreeWayTaggedRowAction zeroDelimiters
                  oneDelimiters manyDelimiters hzero hone hmany }
              (.tag .many) (.separator :: tail) = _
          rfl

private theorem threeWay_zero_ticks
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag)
    (position : Fin zeroDelimiters.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.zeroPayload selection position)
        (List.replicate count .tick ++ tail) =
      (if selection = .zero then List.replicate count .tick else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.zeroPayload selection position) tail := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [rewriteUnaryFrameStatefulFrom,
        unaryFrameThreeWayTaggedRowSpec,
        unaryFrameThreeWayTaggedRowAction]
      split_ifs with hselected
      · have ih' := ih
        simp only [unaryFrameThreeWayTaggedRowSpec] at ih'
        simp only
        rw [ih']
        simp [hselected]
      · have ih' := ih
        simp only [unaryFrameThreeWayTaggedRowSpec] at ih'
        simp only
        rw [ih']
        simp [hselected]

private theorem threeWay_zero_separator
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag)
    (position : Fin zeroDelimiters.length)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.zeroPayload selection position) (.separator :: tail) =
      (if selection = .zero then [zeroDelimiters.get position] else []) ++
        if hnext : position.val + 1 < zeroDelimiters.length then
          rewriteUnaryFrameStatefulFrom
            (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
              manyDelimiters hzero hone hmany)
            (.zeroPayload selection ⟨position.val + 1, hnext⟩) tail
        else rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.onePayload selection ⟨0, hone⟩) tail := by
  simp [rewriteUnaryFrameStatefulFrom,
    unaryFrameThreeWayTaggedRowSpec,
    unaryFrameThreeWayTaggedRowAction]
  split_ifs <;> rfl

private theorem threeWay_zero_values
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag) (position : Nat)
    (hposition : position < zeroDelimiters.length)
    (values : List Nat) (tail : List UnaryFrameSym)
    (hfit : position + values.length = zeroDelimiters.length) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.zeroPayload selection ⟨position, hposition⟩)
        (encodeUnaryFrame values ++ tail) =
      (if selection = .zero then
          encodeUnaryFrameWithFixedDelimiters values
            (zeroDelimiters.drop position)
        else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.onePayload selection ⟨0, hone⟩) tail := by
  induction values generalizing position with
  | nil => simp only [List.length_nil, Nat.add_zero] at hfit; omega
  | cons value values ih =>
      have htailFit : position + 1 + values.length =
          zeroDelimiters.length := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [threeWay_zero_ticks zeroDelimiters oneDelimiters
        manyDelimiters hzero hone hmany]
      rw [threeWay_zero_separator zeroDelimiters oneDelimiters
        manyDelimiters hzero hone hmany]
      by_cases hselected : selection = .zero
      · simp only [if_pos hselected, List.singleton_append]
        by_cases hnext : position + 1 < zeroDelimiters.length
        · simp only [dif_pos hnext]
          rw [ih (position + 1) hnext htailFit]
          have hdrop : zeroDelimiters.drop position =
              zeroDelimiters.get ⟨position, hposition⟩ ::
                zeroDelimiters.drop (position + 1) := by
            simpa using List.drop_eq_getElem_cons hposition
          rw [hdrop]
          simp only [encodeUnaryFrameWithFixedDelimiters,
            if_pos hselected, List.cons_append, List.append_assoc]
        · simp only [dif_neg hnext]
          have hvalues : values = [] := by
            cases values with
            | nil => rfl
            | cons head rest =>
                simp only [List.length_cons] at htailFit
                omega
          subst values
          have hdrop : zeroDelimiters.drop position =
              [zeroDelimiters[position]] := by
            rw [List.drop_eq_getElem_cons hposition]
            rw [List.drop_eq_nil_of_le (by omega)]
          rw [hdrop, List.get_eq_getElem]
          simp only [encodeUnaryFrame, List.flatMap_nil,
            encodeUnaryFrameWithFixedDelimiters, List.nil_append,
            List.singleton_append, List.append_nil, List.append_assoc]
      · simp only [if_neg hselected, List.nil_append]
        by_cases hnext : position + 1 < zeroDelimiters.length
        · simp only [dif_pos hnext]
          rw [ih (position + 1) hnext htailFit]
          simp only [if_neg hselected, List.nil_append]
        · simp only [dif_neg hnext]
          have hvalues : values = [] := by
            cases values with
            | nil => rfl
            | cons head rest =>
                simp only [List.length_cons] at htailFit
                omega
          subst values
          simp only [if_neg hselected, encodeUnaryFrame,
            List.flatMap_nil, encodeUnaryFrameWithFixedDelimiters,
            List.nil_append]

private theorem threeWay_one_ticks
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag)
    (position : Fin oneDelimiters.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.onePayload selection position)
        (List.replicate count .tick ++ tail) =
      (if selection = .one then List.replicate count .tick else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.onePayload selection position) tail := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [rewriteUnaryFrameStatefulFrom,
        unaryFrameThreeWayTaggedRowSpec,
        unaryFrameThreeWayTaggedRowAction]
      split_ifs with hselected
      · have ih' := ih
        simp only [unaryFrameThreeWayTaggedRowSpec] at ih'
        simp only
        rw [ih']
        simp [hselected]
      · have ih' := ih
        simp only [unaryFrameThreeWayTaggedRowSpec] at ih'
        simp only
        rw [ih']
        simp [hselected]

private theorem threeWay_one_separator
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag)
    (position : Fin oneDelimiters.length)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.onePayload selection position) (.separator :: tail) =
      (if selection = .one then [oneDelimiters.get position] else []) ++
        if hnext : position.val + 1 < oneDelimiters.length then
          rewriteUnaryFrameStatefulFrom
            (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
              manyDelimiters hzero hone hmany)
            (.onePayload selection ⟨position.val + 1, hnext⟩) tail
        else rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.manyPayload selection ⟨0, hmany⟩) tail := by
  simp [rewriteUnaryFrameStatefulFrom,
    unaryFrameThreeWayTaggedRowSpec,
    unaryFrameThreeWayTaggedRowAction]
  split_ifs <;> rfl

private theorem threeWay_one_values
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag) (position : Nat)
    (hposition : position < oneDelimiters.length)
    (values : List Nat) (tail : List UnaryFrameSym)
    (hfit : position + values.length = oneDelimiters.length) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.onePayload selection ⟨position, hposition⟩)
        (encodeUnaryFrame values ++ tail) =
      (if selection = .one then
          encodeUnaryFrameWithFixedDelimiters values
            (oneDelimiters.drop position)
        else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.manyPayload selection ⟨0, hmany⟩) tail := by
  induction values generalizing position with
  | nil => simp only [List.length_nil, Nat.add_zero] at hfit; omega
  | cons value values ih =>
      have htailFit : position + 1 + values.length =
          oneDelimiters.length := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [threeWay_one_ticks zeroDelimiters oneDelimiters
        manyDelimiters hzero hone hmany]
      rw [threeWay_one_separator zeroDelimiters oneDelimiters
        manyDelimiters hzero hone hmany]
      by_cases hselected : selection = .one
      · simp only [if_pos hselected, List.singleton_append]
        by_cases hnext : position + 1 < oneDelimiters.length
        · simp only [dif_pos hnext]
          rw [ih (position + 1) hnext htailFit]
          have hdrop : oneDelimiters.drop position =
              oneDelimiters.get ⟨position, hposition⟩ ::
                oneDelimiters.drop (position + 1) := by
            simpa using List.drop_eq_getElem_cons hposition
          rw [hdrop]
          simp only [encodeUnaryFrameWithFixedDelimiters,
            if_pos hselected, List.cons_append, List.append_assoc]
        · simp only [dif_neg hnext]
          have hvalues : values = [] := by
            cases values with
            | nil => rfl
            | cons head rest =>
                simp only [List.length_cons] at htailFit
                omega
          subst values
          have hdrop : oneDelimiters.drop position =
              [oneDelimiters[position]] := by
            rw [List.drop_eq_getElem_cons hposition]
            rw [List.drop_eq_nil_of_le (by omega)]
          rw [hdrop, List.get_eq_getElem]
          simp only [encodeUnaryFrame, List.flatMap_nil,
            encodeUnaryFrameWithFixedDelimiters, List.nil_append,
            List.singleton_append, List.append_nil, List.append_assoc]
      · simp only [if_neg hselected, List.nil_append]
        by_cases hnext : position + 1 < oneDelimiters.length
        · simp only [dif_pos hnext]
          rw [ih (position + 1) hnext htailFit]
          simp only [if_neg hselected, List.nil_append]
        · simp only [dif_neg hnext]
          have hvalues : values = [] := by
            cases values with
            | nil => rfl
            | cons head rest =>
                simp only [List.length_cons] at htailFit
                omega
          subst values
          simp only [if_neg hselected, encodeUnaryFrame,
            List.flatMap_nil, encodeUnaryFrameWithFixedDelimiters,
            List.nil_append]

private theorem threeWay_many_ticks
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag)
    (position : Fin manyDelimiters.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.manyPayload selection position)
        (List.replicate count .tick ++ tail) =
      (if selection = .many then List.replicate count .tick else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.manyPayload selection position) tail := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      simp only [rewriteUnaryFrameStatefulFrom,
        unaryFrameThreeWayTaggedRowSpec,
        unaryFrameThreeWayTaggedRowAction]
      split_ifs with hselected
      · have ih' := ih
        simp only [unaryFrameThreeWayTaggedRowSpec] at ih'
        simp only
        rw [ih']
        simp [hselected]
      · have ih' := ih
        simp only [unaryFrameThreeWayTaggedRowSpec] at ih'
        simp only
        rw [ih']
        simp [hselected]

private theorem threeWay_many_separator
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag)
    (position : Fin manyDelimiters.length)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.manyPayload selection position) (.separator :: tail) =
      (if selection = .many then [manyDelimiters.get position] else []) ++
        if hnext : position.val + 1 < manyDelimiters.length then
          rewriteUnaryFrameStatefulFrom
            (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
              manyDelimiters hzero hone hmany)
            (.manyPayload selection ⟨position.val + 1, hnext⟩) tail
        else rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.tag .zero) tail := by
  simp [rewriteUnaryFrameStatefulFrom,
    unaryFrameThreeWayTaggedRowSpec,
    unaryFrameThreeWayTaggedRowAction]
  split_ifs <;> rfl

private theorem threeWay_many_values
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (selection : UnaryFrameThreeWayTag) (position : Nat)
    (hposition : position < manyDelimiters.length)
    (values : List Nat) (tail : List UnaryFrameSym)
    (hfit : position + values.length = manyDelimiters.length) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.manyPayload selection ⟨position, hposition⟩)
        (encodeUnaryFrame values ++ tail) =
      (if selection = .many then
          encodeUnaryFrameWithFixedDelimiters values
            (manyDelimiters.drop position)
        else []) ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.tag .zero) tail := by
  induction values generalizing position with
  | nil => simp only [List.length_nil, Nat.add_zero] at hfit; omega
  | cons value values ih =>
      have htailFit : position + 1 + values.length =
          manyDelimiters.length := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [threeWay_many_ticks zeroDelimiters oneDelimiters
        manyDelimiters hzero hone hmany]
      rw [threeWay_many_separator zeroDelimiters oneDelimiters
        manyDelimiters hzero hone hmany]
      by_cases hselected : selection = .many
      · simp only [if_pos hselected, List.singleton_append]
        by_cases hnext : position + 1 < manyDelimiters.length
        · simp only [dif_pos hnext]
          rw [ih (position + 1) hnext htailFit]
          have hdrop : manyDelimiters.drop position =
              manyDelimiters.get ⟨position, hposition⟩ ::
                manyDelimiters.drop (position + 1) := by
            simpa using List.drop_eq_getElem_cons hposition
          rw [hdrop]
          simp only [encodeUnaryFrameWithFixedDelimiters,
            if_pos hselected, List.cons_append, List.append_assoc]
        · simp only [dif_neg hnext]
          have hvalues : values = [] := by
            cases values with
            | nil => rfl
            | cons head rest =>
                simp only [List.length_cons] at htailFit
                omega
          subst values
          have hdrop : manyDelimiters.drop position =
              [manyDelimiters[position]] := by
            rw [List.drop_eq_getElem_cons hposition]
            rw [List.drop_eq_nil_of_le (by omega)]
          rw [hdrop, List.get_eq_getElem]
          simp only [encodeUnaryFrame, List.flatMap_nil,
            encodeUnaryFrameWithFixedDelimiters, List.nil_append,
            List.singleton_append, List.append_nil, List.append_assoc]
      · simp only [if_neg hselected, List.nil_append]
        by_cases hnext : position + 1 < manyDelimiters.length
        · simp only [dif_pos hnext]
          rw [ih (position + 1) hnext htailFit]
          simp only [if_neg hselected, List.nil_append]
        · simp only [dif_neg hnext]
          have hvalues : values = [] := by
            cases values with
            | nil => rfl
            | cons head rest =>
                simp only [List.length_cons] at htailFit
                omega
          subst values
          simp only [if_neg hselected, encodeUnaryFrame,
            List.flatMap_nil, encodeUnaryFrameWithFixedDelimiters,
            List.nil_append]

/-- One well-typed source row. -/
structure UnaryFrameThreeWayTaggedRow
    (zeroCount oneCount manyCount : Nat) where
  tag : Nat
  zeroValues : List Nat
  oneValues : List Nat
  manyValues : List Nat
  zero_length : zeroValues.length = zeroCount
  one_length : oneValues.length = oneCount
  many_length : manyValues.length = manyCount

def encodeUnaryFrameThreeWayTaggedRow
    {zeroCount oneCount manyCount : Nat}
    (row : UnaryFrameThreeWayTaggedRow zeroCount oneCount manyCount) :
    List UnaryFrameSym :=
  encodeUnaryFrame
    (row.tag :: row.zeroValues ++ row.oneValues ++ row.manyValues)

def encodeUnaryFrameThreeWayTaggedRowOutput
    {zeroCount oneCount manyCount : Nat}
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (row : UnaryFrameThreeWayTaggedRow zeroCount oneCount manyCount) :
    List UnaryFrameSym :=
  if row.tag = 0 then
    encodeUnaryFrameWithFixedDelimiters row.zeroValues zeroDelimiters
  else if row.tag = 1 then
    encodeUnaryFrameWithFixedDelimiters row.oneValues oneDelimiters
  else encodeUnaryFrameWithFixedDelimiters row.manyValues manyDelimiters

/-- Exact routing semantics for one source row and an arbitrary following
row stream. -/
theorem rewriteUnaryFrameThreeWayTaggedRows_one
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (row : UnaryFrameThreeWayTaggedRow zeroDelimiters.length
      oneDelimiters.length manyDelimiters.length)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom
        (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
          manyDelimiters hzero hone hmany)
        (.tag .zero)
        (encodeUnaryFrameThreeWayTaggedRow row ++ tail) =
      encodeUnaryFrameThreeWayTaggedRowOutput zeroDelimiters oneDelimiters
          manyDelimiters row ++
        rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.tag .zero) tail := by
  unfold encodeUnaryFrameThreeWayTaggedRow
  rw [show encodeUnaryFrame
          (row.tag :: row.zeroValues ++ row.oneValues ++ row.manyValues) ++
        tail =
      List.replicate row.tag .tick ++ .separator ::
        (encodeUnaryFrame row.zeroValues ++
          encodeUnaryFrame row.oneValues ++
            encodeUnaryFrame row.manyValues ++ tail) by
    simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
  rw [threeWay_tag_field zeroDelimiters oneDelimiters manyDelimiters
    hzero hone hmany]
  rw [show encodeUnaryFrame row.zeroValues ++
          encodeUnaryFrame row.oneValues ++
            encodeUnaryFrame row.manyValues ++ tail =
        encodeUnaryFrame row.zeroValues ++
          (encodeUnaryFrame row.oneValues ++
            encodeUnaryFrame row.manyValues ++ tail) by
      simp only [List.append_assoc]]
  rw [threeWay_zero_values zeroDelimiters oneDelimiters manyDelimiters
    hzero hone hmany (unaryFrameThreeWayTagOfNat row.tag) 0
    hzero row.zeroValues
    (encodeUnaryFrame row.oneValues ++
      encodeUnaryFrame row.manyValues ++ tail) (by simpa using row.zero_length)]
  rw [show encodeUnaryFrame row.oneValues ++
          encodeUnaryFrame row.manyValues ++ tail =
        encodeUnaryFrame row.oneValues ++
          (encodeUnaryFrame row.manyValues ++ tail) by
      simp only [List.append_assoc]]
  rw [threeWay_one_values zeroDelimiters oneDelimiters manyDelimiters
    hzero hone hmany (unaryFrameThreeWayTagOfNat row.tag) 0
    hone row.oneValues (encodeUnaryFrame row.manyValues ++ tail)
    (by simpa using row.one_length)]
  rw [threeWay_many_values zeroDelimiters oneDelimiters manyDelimiters
    hzero hone hmany (unaryFrameThreeWayTagOfNat row.tag) 0
    hmany row.manyValues tail (by simpa using row.many_length)]
  unfold encodeUnaryFrameThreeWayTaggedRowOutput
  cases row.tag with
  | zero => simp [unaryFrameThreeWayTagOfNat]
  | succ tag =>
      cases tag with
      | zero => simp [unaryFrameThreeWayTagOfNat]
      | succ tag => simp [unaryFrameThreeWayTagOfNat]

def encodeUnaryFrameThreeWayTaggedRowFamily
    {zeroCount oneCount manyCount : Nat}
    (rows : List
      (UnaryFrameThreeWayTaggedRow zeroCount oneCount manyCount)) :
    List UnaryFrameSym :=
  rows.flatMap encodeUnaryFrameThreeWayTaggedRow

def encodeUnaryFrameThreeWayTaggedRowOutputFamily
    {zeroCount oneCount manyCount : Nat}
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (rows : List
      (UnaryFrameThreeWayTaggedRow zeroCount oneCount manyCount)) :
    List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrameThreeWayTaggedRowOutput
    zeroDelimiters oneDelimiters manyDelimiters row

/-- Family-level exact semantics. -/
theorem rewriteUnaryFrameThreeWayTaggedRows_family
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length)
    (rows : List (UnaryFrameThreeWayTaggedRow zeroDelimiters.length
      oneDelimiters.length manyDelimiters.length)) :
    rewriteUnaryFrameThreeWayTaggedRows zeroDelimiters oneDelimiters
        manyDelimiters hzero hone hmany
        (encodeUnaryFrameThreeWayTaggedRowFamily rows) =
      encodeUnaryFrameThreeWayTaggedRowOutputFamily zeroDelimiters
        oneDelimiters manyDelimiters rows := by
  unfold rewriteUnaryFrameThreeWayTaggedRows rewriteUnaryFrameStateful
    encodeUnaryFrameThreeWayTaggedRowFamily
    encodeUnaryFrameThreeWayTaggedRowOutputFamily
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [List.flatMap_cons, List.flatMap_cons]
      change rewriteUnaryFrameStatefulFrom
          (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
            manyDelimiters hzero hone hmany)
          (.tag .zero)
          (encodeUnaryFrameThreeWayTaggedRow row ++
            rows.flatMap encodeUnaryFrameThreeWayTaggedRow) = _
      rw [rewriteUnaryFrameThreeWayTaggedRows_one zeroDelimiters
        oneDelimiters manyDelimiters hzero hone hmany row]
      simpa only [unaryFrameThreeWayTaggedRowSpec] using congrArg
        (fun rest => encodeUnaryFrameThreeWayTaggedRowOutput zeroDelimiters
          oneDelimiters manyDelimiters row ++ rest) ih

/-- The router is one fixed linear-time TM2 for every fixed delimiter triple. -/
noncomputable def rewriteUnaryFrameThreeWayTaggedRows_computableInPolyTime
    (zeroDelimiters oneDelimiters manyDelimiters : List UnaryFrameSym)
    (hzero : 0 < zeroDelimiters.length)
    (hone : 0 < oneDelimiters.length)
    (hmany : 0 < manyDelimiters.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameThreeWayTaggedRows zeroDelimiters oneDelimiters
        manyDelimiters hzero hone hmany) :=
  unaryFrameStatefulMap_computableInPolyTime
    (unaryFrameThreeWayTaggedRowSpec zeroDelimiters oneDelimiters
      manyDelimiters hzero hone hmany)

end CLRS.Chapter34.Turing.PolyBuilder
