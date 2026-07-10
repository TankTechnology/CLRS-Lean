import Mathlib

/-!
# CLRS Section 21.1 - Disjoint-set operations

This section gives the representation-independent semantics for disjoint-set
data structures.  A state is a partition, presented by its equivalence
relation.  Merging two sets replaces the two old equivalence classes by their
union and leaves every other class unchanged.

Main results:

- Theorem {lit}`Partition.merge_sameSet_iff`: exact relational semantics of
  union.
- Theorem {lit}`stepSpec_union_sameSet_iff`: the abstract {lit}`UNION`
  operation implements that merge.
- Theorem {lit}`runSpec_append`: operation traces compose.
- Theorem {lit}`runSpec_preserves_sameSet`: disjoint-set traces only merge
  classes; they never split an existing class.
-/

namespace CLRS
namespace Chapter21

/-- A representation-independent disjoint-set state. -/
structure Partition (α : Type*) where
  sameSet : α → α → Prop
  refl : ∀ x, sameSet x x
  symm : ∀ {x y}, sameSet x y → sameSet y x
  trans : ∀ {x y z}, sameSet x y → sameSet y z → sameSet x z

namespace Partition

variable {α : Type*}

/-- The initial partition in which every element is a singleton. -/
def discrete : Partition α where
  sameSet := (· = ·)
  refl := Eq.refl
  symm := Eq.symm
  trans := Eq.trans

@[simp]
theorem discrete_sameSet_iff {x y : α} :
    (discrete : Partition α).sameSet x y ↔ x = y :=
  Iff.rfl

/-- An element belongs to one of the two classes selected for a merge. -/
def touches (P : Partition α) (x y a : α) : Prop :=
  P.sameSet a x ∨ P.sameSet a y

private theorem touches_of_sameSet_left (P : Partition α) {x y a b : α}
    (hab : P.sameSet a b) (hb : P.touches x y b) :
    P.touches x y a := by
  rcases hb with hbx | hby
  · exact Or.inl (P.trans hab hbx)
  · exact Or.inr (P.trans hab hby)

/-- Merge the equivalence classes containing {lit}`x` and {lit}`y`. -/
def merge (P : Partition α) (x y : α) : Partition α where
  sameSet a b :=
    P.sameSet a b ∨ (P.touches x y a ∧ P.touches x y b)
  refl a := Or.inl (P.refl a)
  symm := by
    intro a b hab
    rcases hab with hab | ⟨ha, hb⟩
    · exact Or.inl (P.symm hab)
    · exact Or.inr ⟨hb, ha⟩
  trans := by
    intro a b c hab hbc
    rcases hab with hab | ⟨ha, hb⟩
    · rcases hbc with hbc | ⟨hb', hc⟩
      · exact Or.inl (P.trans hab hbc)
      · exact Or.inr ⟨P.touches_of_sameSet_left hab hb', hc⟩
    · rcases hbc with hbc | ⟨_, hc⟩
      · exact Or.inr ⟨ha,
          P.touches_of_sameSet_left (P.symm hbc) hb⟩
      · exact Or.inr ⟨ha, hc⟩

/-- The CLRS union formula: exactly the two selected classes become one. -/
theorem merge_sameSet_iff (P : Partition α) (x y a b : α) :
    (P.merge x y).sameSet a b ↔
      P.sameSet a b ∨
        (P.sameSet a x ∧ P.sameSet y b) ∨
        (P.sameSet a y ∧ P.sameSet x b) := by
  constructor
  · intro h
    rcases h with hab | ⟨ha, hb⟩
    · exact Or.inl hab
    · rcases ha with hax | hay <;> rcases hb with hbx | hby
      · exact Or.inl (P.trans hax (P.symm hbx))
      · exact Or.inr (Or.inl ⟨hax, P.symm hby⟩)
      · exact Or.inr (Or.inr ⟨hay, P.symm hbx⟩)
      · exact Or.inl (P.trans hay (P.symm hby))
  · intro h
    rcases h with hab | ⟨⟨hax, hyb⟩ | ⟨hay, hxb⟩⟩
    · exact Or.inl hab
    · exact Or.inr ⟨Or.inl hax, Or.inr (P.symm hyb)⟩
    · exact Or.inr ⟨Or.inr hay, Or.inl (P.symm hxb)⟩

/-- Merging a class with itself leaves the represented partition unchanged. -/
theorem merge_self_sameSet_iff (P : Partition α) (x a b : α) :
    (P.merge x x).sameSet a b ↔ P.sameSet a b := by
  rw [merge_sameSet_iff]
  constructor
  · intro h
    rcases h with hab | ⟨⟨hax, hxb⟩ | ⟨hax, hxb⟩⟩
    · exact hab
    · exact P.trans hax hxb
    · exact P.trans hax hxb
  · exact Or.inl

/-- Merging two elements already in one class leaves the partition unchanged. -/
theorem merge_related_sameSet_iff (P : Partition α) {x y a b : α}
    (hxy : P.sameSet x y) :
    (P.merge x y).sameSet a b ↔ P.sameSet a b := by
  rw [merge_sameSet_iff]
  constructor
  · intro h
    rcases h with hab | ⟨⟨hax, hyb⟩ | ⟨hay, hxb⟩⟩
    · exact hab
    · exact P.trans (P.trans hax hxy) hyb
    · exact P.trans (P.trans hay (P.symm hxy)) hxb
  · exact Or.inl

/-- A merge preserves every equivalence that already held. -/
theorem sameSet_merge_of_sameSet (P : Partition α) {x y a b : α}
    (h : P.sameSet a b) :
    (P.merge x y).sameSet a b :=
  Or.inl h

end Partition

/-- The two observable CLRS disjoint-set operations. -/
inductive Operation (α : Type*) where
  | find (x : α)
  | union (x y : α)
deriving Repr

/-- Abstract state transition for one disjoint-set operation. -/
def stepSpec {α : Type*} (P : Partition α) : Operation α → Partition α
  | .find _ => P
  | .union x y => P.merge x y

/-- Execute an abstract sequence of disjoint-set operations. -/
def runSpec {α : Type*} : Partition α → List (Operation α) → Partition α
  | P, [] => P
  | P, op :: ops => runSpec (stepSpec P op) ops

@[simp]
theorem stepSpec_find {α : Type*} (P : Partition α) (x : α) :
    stepSpec P (.find x) = P :=
  rfl

theorem stepSpec_union_sameSet_iff {α : Type*} (P : Partition α)
    (x y a b : α) :
    (stepSpec P (.union x y)).sameSet a b ↔
      P.sameSet a b ∨
        (P.sameSet a x ∧ P.sameSet y b) ∨
        (P.sameSet a y ∧ P.sameSet x b) :=
  P.merge_sameSet_iff x y a b

@[simp]
theorem runSpec_nil {α : Type*} (P : Partition α) :
    runSpec P [] = P :=
  rfl

@[simp]
theorem runSpec_cons {α : Type*} (P : Partition α)
    (op : Operation α) (ops : List (Operation α)) :
    runSpec P (op :: ops) = runSpec (stepSpec P op) ops :=
  rfl

/-- Running concatenated traces is the same as running them successively. -/
theorem runSpec_append {α : Type*} (P : Partition α)
    (xs ys : List (Operation α)) :
    runSpec P (xs ++ ys) = runSpec (runSpec P xs) ys := by
  induction xs generalizing P with
  | nil => rfl
  | cons op xs ih =>
      simp only [List.cons_append, runSpec_cons]
      exact ih (stepSpec P op)

/-- An operation trace may merge classes, but it never splits one. -/
theorem runSpec_preserves_sameSet {α : Type*} (P : Partition α)
    (ops : List (Operation α)) {a b : α} (h : P.sameSet a b) :
    (runSpec P ops).sameSet a b := by
  induction ops generalizing P with
  | nil => exact h
  | cons op ops ih =>
      cases op with
      | find x => exact ih P h
      | union x y => exact ih (P.merge x y) (Or.inl h)

end Chapter21
end CLRS
