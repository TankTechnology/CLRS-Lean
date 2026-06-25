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
- Theorem {lit}`VEB.successor_correct`: a returned successor is represented,
  greater than the query, and no larger than any represented greater key.
- Theorems {lit}`VEB.insert_correct` and {lit}`VEB.delete_correct`: updates
  match finite-set insertion and deletion.
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
