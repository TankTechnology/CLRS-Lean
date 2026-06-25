import CLRSLean.Chapter_20.Section_20_1_VEB_Universe

/-!
# CLRS Section 20.2 - van Emde Boas tree specification

This first-pass section represents a van Emde Boas tree by the finite set of
keys it contains, together with a universe bound.  The model gives precise
query/update specifications before introducing recursive summary and cluster
storage.

Main results:

- Theorem {lit}`VEB.member_correct`: membership queries match the represented
  set.
- Theorems {lit}`VEB.minimum_correct` and {lit}`VEB.maximum_correct`: returned
  extrema are represented keys with the expected order property.
- Theorems {lit}`VEB.minimum_none_iff` and {lit}`VEB.maximum_none_iff`:
  extrema queries return no key exactly when the represented set is empty.
- Theorem {lit}`VEB.successor_correct`: a returned successor is represented,
  greater than the query, and no larger than any represented greater key.
- Theorem {lit}`VEB.successor_none_iff`: no successor is returned exactly when
  no represented key is greater than the query.
- Theorem {lit}`VEB.predecessor_correct`: a returned predecessor is
  represented, less than the query, and no smaller than any represented smaller
  key.
- Theorem {lit}`VEB.predecessor_none_iff`: no predecessor is returned exactly
  when no represented key is smaller than the query.
- Theorems {lit}`VEB.insert_correct` and {lit}`VEB.delete_correct`: updates
  match finite-set insertion and deletion.
- Theorems {lit}`VEB.insert_member_iff` and {lit}`VEB.delete_member_iff`:
  membership queries after updates match the expected finite-set update.
- Theorem {lit}`VEB.operationDepth_linear`: the first-pass recurrence-depth
  wrapper is linear in the universe exponent.

Current gaps:

- Recursive summary/cluster storage and word-RAM base cases are future
  refinement targets.
-/

namespace CLRS
namespace Chapter20
namespace VEB

/-- First-pass vEB tree state: a universe size and a finite represented set. -/
structure Tree where
  univSize : Nat
  elems : Finset Nat

/-- A tree represents exactly a finite set whose elements fit in the universe. -/
def Represents (t : Tree) (s : Finset Nat) : Prop :=
  t.elems = s ∧ forall x, x ∈ s -> x < t.univSize

/-- Boolean membership query. -/
def member (x : Nat) (t : Tree) : Bool :=
  decide (x ∈ t.elems)

/-- Membership queries match the represented set. -/
theorem member_correct {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) :
    member x t = true <-> x ∈ s := by
  simp [member, hrep.1]

/-- Minimum represented key, if the tree is nonempty. -/
def minimum (t : Tree) : Option Nat :=
  if h : t.elems.Nonempty then
    some (t.elems.min' h)
  else
    none

/-- Maximum represented key, if the tree is nonempty. -/
def maximum (t : Tree) : Option Nat :=
  if h : t.elems.Nonempty then
    some (t.elems.max' h)
  else
    none

/-- The returned minimum is represented and is a lower bound for all keys. -/
theorem minimum_correct {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hmin : minimum t = some x) :
    x ∈ s ∧ forall y, y ∈ s -> x <= y := by
  unfold minimum at hmin
  by_cases hne : t.elems.Nonempty
  · simp [hne] at hmin
    subst x
    constructor
    · simpa [hrep.1] using Finset.min'_mem t.elems hne
    · intro y hy
      have hyt : y ∈ t.elems := by
        simpa [hrep.1] using hy
      exact Finset.min'_le t.elems y hyt
  · simp [hne] at hmin

/-- No minimum is returned exactly when the represented set is empty. -/
theorem minimum_none_iff {t : Tree} {s : Finset Nat}
    (hrep : Represents t s) :
    minimum t = none <-> s = ∅ := by
  unfold minimum
  constructor
  · intro hnone
    by_cases hne : t.elems.Nonempty
    · simp [hne] at hnone
    · have helemsEmpty : t.elems = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      simpa [hrep.1] using helemsEmpty
  · intro hs
    have helemsEmpty : t.elems = ∅ := by
      simpa [hrep.1] using hs
    have hne : ¬ t.elems.Nonempty :=
      Finset.not_nonempty_iff_eq_empty.mpr helemsEmpty
    simp [hne]

/-- The returned maximum is represented and is an upper bound for all keys. -/
theorem maximum_correct {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hmax : maximum t = some x) :
    x ∈ s ∧ forall y, y ∈ s -> y <= x := by
  unfold maximum at hmax
  by_cases hne : t.elems.Nonempty
  · simp [hne] at hmax
    subst x
    constructor
    · simpa [hrep.1] using Finset.max'_mem t.elems hne
    · intro y hy
      have hyt : y ∈ t.elems := by
        simpa [hrep.1] using hy
      exact Finset.le_max' t.elems y hyt
  · simp [hne] at hmax

/-- No maximum is returned exactly when the represented set is empty. -/
theorem maximum_none_iff {t : Tree} {s : Finset Nat}
    (hrep : Represents t s) :
    maximum t = none <-> s = ∅ := by
  unfold maximum
  constructor
  · intro hnone
    by_cases hne : t.elems.Nonempty
    · simp [hne] at hnone
    · have helemsEmpty : t.elems = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      simpa [hrep.1] using helemsEmpty
  · intro hs
    have helemsEmpty : t.elems = ∅ := by
      simpa [hrep.1] using hs
    have hne : ¬ t.elems.Nonempty :=
      Finset.not_nonempty_iff_eq_empty.mpr helemsEmpty
    simp [hne]

/-- Candidate successor set for query {lit}`x`. -/
def successorCandidates (x : Nat) (t : Tree) : Finset Nat :=
  t.elems.filter (fun y => x < y)

/-- Least represented key greater than {lit}`x`, if one exists. -/
def successor (x : Nat) (t : Tree) : Option Nat :=
  if h : (successorCandidates x t).Nonempty then
    some ((successorCandidates x t).min' h)
  else
    none

/--
A returned successor is represented, greater than the query, and no larger than
any represented key that is also greater than the query.
-/
theorem successor_correct {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hsucc : successor x t = some y) :
    y ∈ s ∧ x < y ∧ forall z, z ∈ s -> x < z -> y <= z := by
  unfold successor at hsucc
  by_cases hne : (successorCandidates x t).Nonempty
  · simp [hne] at hsucc
    subst y
    have hmem := Finset.min'_mem (successorCandidates x t) hne
    have hmem' : (successorCandidates x t).min' hne ∈ t.elems ∧
        x < (successorCandidates x t).min' hne := by
      simpa [successorCandidates] using hmem
    refine ⟨?_, hmem'.2, ?_⟩
    · simpa [hrep.1] using hmem'.1
    · intro z hz hxz
      have hzCand : z ∈ successorCandidates x t := by
        simp [successorCandidates, hrep.1, hz, hxz]
      exact Finset.min'_le (successorCandidates x t) z hzCand
  · simp [hne] at hsucc

/-- No successor is returned exactly when no represented key is greater. -/
theorem successor_none_iff {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) :
    successor x t = none <-> forall y, y ∈ s -> ¬ x < y := by
  unfold successor
  constructor
  · intro hnone y hy hxy
    have hyCand : y ∈ successorCandidates x t := by
      simp [successorCandidates, hrep.1, hy, hxy]
    have hne : (successorCandidates x t).Nonempty := ⟨y, hyCand⟩
    simp [hne] at hnone
  · intro hnone
    by_cases hne : (successorCandidates x t).Nonempty
    · rcases hne with ⟨y, hyCand⟩
      have hy : y ∈ s ∧ x < y := by
        simpa [successorCandidates, hrep.1] using hyCand
      exact False.elim ((hnone y hy.1) hy.2)
    · simp [hne]

/-- Candidate predecessor set for query {lit}`x`. -/
def predecessorCandidates (x : Nat) (t : Tree) : Finset Nat :=
  t.elems.filter (fun y => y < x)

/-- Greatest represented key less than {lit}`x`, if one exists. -/
def predecessor (x : Nat) (t : Tree) : Option Nat :=
  if h : (predecessorCandidates x t).Nonempty then
    some ((predecessorCandidates x t).max' h)
  else
    none

/--
A returned predecessor is represented, less than the query, and no smaller than
any represented key that is also less than the query.
-/
theorem predecessor_correct {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hpred : predecessor x t = some y) :
    y ∈ s ∧ y < x ∧ forall z, z ∈ s -> z < x -> z <= y := by
  unfold predecessor at hpred
  by_cases hne : (predecessorCandidates x t).Nonempty
  · simp [hne] at hpred
    subst y
    have hmem := Finset.max'_mem (predecessorCandidates x t) hne
    have hmem' : (predecessorCandidates x t).max' hne ∈ t.elems ∧
        (predecessorCandidates x t).max' hne < x := by
      simpa [predecessorCandidates] using hmem
    refine ⟨?_, hmem'.2, ?_⟩
    · simpa [hrep.1] using hmem'.1
    · intro z hz hzx
      have hzCand : z ∈ predecessorCandidates x t := by
        simp [predecessorCandidates, hrep.1, hz, hzx]
      exact Finset.le_max' (predecessorCandidates x t) z hzCand
  · simp [hne] at hpred

/-- No predecessor is returned exactly when no represented key is smaller. -/
theorem predecessor_none_iff {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) :
    predecessor x t = none <-> forall y, y ∈ s -> ¬ y < x := by
  unfold predecessor
  constructor
  · intro hnone y hy hyx
    have hyCand : y ∈ predecessorCandidates x t := by
      simp [predecessorCandidates, hrep.1, hy, hyx]
    have hne : (predecessorCandidates x t).Nonempty := ⟨y, hyCand⟩
    simp [hne] at hnone
  · intro hnone
    by_cases hne : (predecessorCandidates x t).Nonempty
    · rcases hne with ⟨y, hyCand⟩
      have hy : y ∈ s ∧ y < x := by
        simpa [predecessorCandidates, hrep.1] using hyCand
      exact False.elim ((hnone y hy.1) hy.2)
    · simp [hne]

/-- Insert a key into the represented set. -/
def insert (x : Nat) (t : Tree) : Tree :=
  { t with elems := Insert.insert x t.elems }

/-- Insertion matches finite-set insertion when the inserted key is in universe. -/
theorem insert_correct {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    Represents (insert x t) (Insert.insert x s) := by
  constructor
  · simp [insert, hrep.1]
  · intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with hy | hy
    · simpa [insert, hy] using hx
    · simpa [insert] using hrep.2 y hy

/-- Membership after insertion succeeds exactly for the inserted or old keys. -/
theorem insert_member_iff {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    member y (insert x t) = true <-> y = x ∨ member y t = true := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  rw [member_correct (t := insert x t) (s := Insert.insert x s) (x := y) hinsert]
  rw [Finset.mem_insert]
  rw [← member_correct (t := t) (s := s) (x := y) hrep]

/-- Delete a key from the represented set. -/
def delete (x : Nat) (t : Tree) : Tree :=
  { t with elems := t.elems.erase x }

/-- Deletion matches finite-set deletion. -/
theorem delete_correct {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) :
    Represents (delete x t) (s.erase x) := by
  constructor
  · simp [delete, hrep.1]
  · intro y hy
    have hys : y ∈ s := Finset.mem_of_mem_erase hy
    exact hrep.2 y hys

/-- Membership after deletion succeeds exactly for old keys different from the deleted key. -/
theorem delete_member_iff {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) :
    member y (delete x t) = true <-> y ≠ x ∧ member y t = true := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  rw [member_correct (t := delete x t) (s := s.erase x) (x := y) hdelete]
  rw [Finset.mem_erase]
  rw [← member_correct (t := t) (s := s) (x := y) hrep]

/-- First-pass operation-depth recurrence over a tower exponent. -/
def operationDepth (k : Nat) : Nat :=
  k + 1

/-- The first-pass recurrence-depth wrapper is linear in {lit}`k`. -/
theorem operationDepth_linear (k : Nat) :
    operationDepth k <= k + 1 := by
  rfl

end VEB
end Chapter20
end CLRS
