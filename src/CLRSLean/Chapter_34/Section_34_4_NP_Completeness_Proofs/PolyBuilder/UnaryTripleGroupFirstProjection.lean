import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionFixedGroups
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap

/-!
# First-coordinate projection for group-marked unary triples

The fixed-group progression executor emits ordinary three-field rows and one
`frameEnd` after each descriptor group.  This finite-state streaming pass
keeps the first field of every triple, erases the other two fields, and
preserves each outer group marker.  It is the representation bridge from
executed affine descriptors to the value rows consumed by stack routing.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Current field inside an ordinary three-field row. -/
inductive UnaryTripleGroupFirstMode
  | first | second | third
deriving DecidableEq, Fintype

/-- Keep the first field, erase the second and third, and reset at an outer
group boundary. -/
def unaryTripleGroupFirstAction
    (mode : UnaryTripleGroupFirstMode) (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryTripleGroupFirstMode :=
  match symbol with
  | .frameEnd => (some .frameEnd, .first)
  | .tick =>
      match mode with
      | .first => (some .tick, .first)
      | .second => (none, .second)
      | .third => (none, .third)
  | .separator =>
      match mode with
      | .first => (some .separator, .second)
      | .second => (none, .third)
      | .third => (none, .first)

def unaryTripleGroupFirstSpec :
    UnaryFrameStatefulMapSpec UnaryTripleGroupFirstMode :=
  { initial := .first
    action := unaryTripleGroupFirstAction }

/-- Pure first-coordinate projection. -/
def projectUnaryTripleGroupFirst (input : List UnaryFrameSym) :
    List UnaryFrameSym :=
  rewriteUnaryFrameStateful unaryTripleGroupFirstSpec input

@[simp] theorem projectUnaryTripleGroupFirst_frameEnd
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
        (.frameEnd :: tail) =
      .frameEnd ::
        rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
          tail := rfl

/-- Semantic first-coordinate stream with the same fixed descriptor-group
cursor as the concrete progression controller. -/
def affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom
    (groupLast : Nat) :
    Fin (groupLast + 1) → List AffineUnaryTripleProgression →
      List UnaryFrameSym
  | _, [] => []
  | position, progression :: rest =>
      encodeUnaryFrame
          ((affineUnaryTripleProgressionRows progression).map fun row =>
            row.1) ++
        if hlast : position.val = groupLast then
          .frameEnd ::
            affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom
              groupLast ⟨0, by omega⟩ rest
        else
          affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom
            groupLast ⟨position.val + 1, by omega⟩ rest

def affineUnaryTripleProgressionFixedGroupFirstFrameStream
    (groupLast : Nat) (progressions : List AffineUnaryTripleProgression) :
    List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom groupLast
    ⟨0, by omega⟩ progressions

private theorem projectUnaryTripleGroupFirst_firstTicks
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
        (List.replicate count .tick ++ .separator :: tail) =
      List.replicate count .tick ++ .separator ::
        rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .second
          tail := by
  induction count with
  | zero =>
      change .separator ::
          rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .second
            tail = _
      rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      change .tick ::
          rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
            (List.replicate count .tick ++ .separator :: tail) =
        .tick :: (List.replicate count .tick ++ .separator ::
          rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .second
            tail)
      rw [ih]

private theorem projectUnaryTripleGroupFirst_secondTicks
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .second
        (List.replicate count .tick ++ .separator :: tail) =
      rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .third tail := by
  induction count with
  | zero =>
      simp [rewriteUnaryFrameStatefulFrom, unaryTripleGroupFirstSpec,
        unaryTripleGroupFirstAction]
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      change rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .second
          (List.replicate count .tick ++ .separator :: tail) = _
      exact ih

private theorem projectUnaryTripleGroupFirst_thirdTicks
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .third
        (List.replicate count .tick ++ .separator :: tail) =
      rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first tail := by
  induction count with
  | zero =>
      simp [rewriteUnaryFrameStatefulFrom, unaryTripleGroupFirstSpec,
        unaryTripleGroupFirstAction]
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      change rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .third
          (List.replicate count .tick ++ .separator :: tail) = _
      exact ih

private theorem projectUnaryTripleGroupFirst_row
    (first second third : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
        (encodeUnaryFrame [first, second, third] ++ tail) =
      encodeUnaryFrame [first] ++
        rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
          tail := by
  simp only [encodeUnaryFrame, encodeUnaryFrameBlock, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  simp only [List.append_assoc, List.cons_append, List.singleton_append,
    List.nil_append]
  rw [projectUnaryTripleGroupFirst_firstTicks,
    projectUnaryTripleGroupFirst_secondTicks,
    projectUnaryTripleGroupFirst_thirdTicks]

private theorem projectUnaryTripleGroupFirst_rows
    (rows : List (Nat × Nat × Nat)) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
        (rows.flatMap (fun row =>
          encodeUnaryFrame [row.1, row.2.1, row.2.2]) ++ tail) =
      encodeUnaryFrame (rows.map fun row => row.1) ++
        rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
          tail := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rcases row with ⟨first, second, third⟩
      simp only [List.flatMap_cons, List.map_cons, List.cons_append]
      rw [List.append_assoc, projectUnaryTripleGroupFirst_row, ih]
      simp [encodeUnaryFrame, List.append_assoc]

/-- The projector converts the concrete group-marked triple stream to its
first-coordinate semantic stream, from any valid group cursor. -/
theorem projectUnaryTripleGroupFirst_fixedGroupStreamFrom
    (groupLast : Nat) (position : Fin (groupLast + 1))
    (progressions : List AffineUnaryTripleProgression) :
    rewriteUnaryFrameStatefulFrom unaryTripleGroupFirstSpec .first
        (affineUnaryTripleProgressionFixedGroupFrameStreamFrom groupLast
          position progressions) =
      affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom groupLast
        position progressions := by
  induction progressions generalizing position with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFixedGroupFrameStreamFrom,
        affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom,
        affineUnaryTripleProgressionFrameStream,
        affineUnaryTripleRowValues]
      rw [projectUnaryTripleGroupFirst_rows]
      by_cases hlast : position.val = groupLast
      · rw [dif_pos hlast, projectUnaryTripleGroupFirst_frameEnd,
          ih]
        simp only [dif_pos hlast]
      · rw [dif_neg hlast, ih]
        simp only [dif_neg hlast]

/-- Exact action on a complete fixed-group progression stream. -/
theorem projectUnaryTripleGroupFirst_fixedGroupStream
    (groupLast : Nat)
    (progressions : List AffineUnaryTripleProgression) :
    projectUnaryTripleGroupFirst
        (affineUnaryTripleProgressionFixedGroupFrameStream groupLast
          progressions) =
      affineUnaryTripleProgressionFixedGroupFirstFrameStream groupLast
        progressions := by
  exact projectUnaryTripleGroupFirst_fixedGroupStreamFrom groupLast
    ⟨0, by omega⟩ progressions

/-- A descriptor block that exactly fills the remaining group positions is
projected to one ordinary first-coordinate value row followed by one outer
marker.  The cursor then restarts at zero on the suffix. -/
theorem affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom_append_group
    (groupLast : Nat) (position : Fin (groupLast + 1))
    (group rest : List AffineUnaryTripleProgression)
    (hlength : position.val + group.length = groupLast + 1) :
    affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom groupLast
        position (group ++ rest) =
      encodeUnaryFrame
          ((group.flatMap affineUnaryTripleProgressionRows).map fun row =>
            row.1) ++
        .frameEnd ::
          affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom
            groupLast ⟨0, by omega⟩ rest := by
  induction group generalizing position with
  | nil =>
      have hposition := position.isLt
      simp only [List.length_nil, Nat.add_zero] at hlength
      omega
  | cons progression group ih =>
      by_cases hlast : position.val = groupLast
      · have hgroupLength : group.length = 0 := by
          simp only [List.length_cons] at hlength
          omega
        have hgroup : group = [] := List.eq_nil_of_length_eq_zero hgroupLength
        subst group
        simp only [List.cons_append,
          affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom,
          dif_pos hlast, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.map_append, List.map_nil]
        simp [encodeUnaryFrame, List.append_assoc]
      · let nextPosition : Fin (groupLast + 1) :=
          ⟨position.val + 1, by omega⟩
        have hnext : nextPosition.val + group.length = groupLast + 1 := by
          simp only [List.length_cons] at hlength
          dsimp only [nextPosition]
          omega
        have hrest := ih nextPosition hnext
        simp only [List.cons_append,
          affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom,
          dif_neg hlast, List.flatMap_cons, List.map_append]
        rw [show (⟨position.val + 1, by omega⟩ : Fin (groupLast + 1)) =
            nextPosition by apply Fin.ext; rfl]
        rw [hrest]
        simp [encodeUnaryFrame, List.append_assoc]

/-- Starting at zero, every exact group of `groupLast + 1` descriptors has
the canonical marked first-coordinate row representation. -/
theorem affineUnaryTripleProgressionFixedGroupFirstFrameStream_append_group
    (groupLast : Nat) (group rest : List AffineUnaryTripleProgression)
    (hlength : group.length = groupLast + 1) :
    affineUnaryTripleProgressionFixedGroupFirstFrameStream groupLast
        (group ++ rest) =
      encodeUnaryFrame
          ((group.flatMap affineUnaryTripleProgressionRows).map fun row =>
            row.1) ++
        .frameEnd ::
          affineUnaryTripleProgressionFixedGroupFirstFrameStream groupLast
            rest := by
  exact
    affineUnaryTripleProgressionFixedGroupFirstFrameStreamFrom_append_group
      groupLast ⟨0, by omega⟩ group rest (by simpa using hlength)

/-- The first-coordinate projection is a concrete fixed linear-time TM2. -/
noncomputable def projectUnaryTripleGroupFirst_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      projectUnaryTripleGroupFirst :=
  unaryFrameStatefulMap_computableInPolyTime unaryTripleGroupFirstSpec

end CLRS.Chapter34.Turing.PolyBuilder
