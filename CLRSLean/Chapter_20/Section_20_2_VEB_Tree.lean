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
- Theorems {lit}`VEB.minimum_mem`, {lit}`VEB.minimum_le`,
  {lit}`VEB.maximum_mem`, and {lit}`VEB.le_maximum`: direct membership and
  lower/upper-bound corollaries for returned extrema.
- Theorems {lit}`VEB.member_lt_univ`, {lit}`VEB.minimum_lt_univ`,
  {lit}`VEB.maximum_lt_univ`, {lit}`VEB.successor_lt_univ`, and
  {lit}`VEB.predecessor_lt_univ`: successful queries return keys inside the
  represented universe.
- Theorems {lit}`VEB.minimum_none_iff` and {lit}`VEB.maximum_none_iff`:
  extrema queries return no key exactly when the represented set is empty.
- Theorem {lit}`VEB.successor_correct`: a returned successor is represented,
  greater than the query, and no larger than any represented greater key.
- Theorems {lit}`VEB.successor_mem`, {lit}`VEB.successor_gt`,
  {lit}`VEB.successor_le`, {lit}`VEB.predecessor_mem`,
  {lit}`VEB.predecessor_lt`, and {lit}`VEB.le_predecessor`: direct membership
  and order corollaries for returned neighbors.
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
- Theorems {lit}`VEB.insert_member_self`, {lit}`VEB.insert_member_old`,
  {lit}`VEB.delete_member_deleted_false`, and
  {lit}`VEB.delete_member_of_ne`: direct member-query corollaries for the
  updated key and preserved old keys after insertion and deletion.
- Theorems {lit}`VEB.insert_member_false_iff` and
  {lit}`VEB.delete_member_false_iff`: exact failed member-query specifications
  after insertion and deletion.
- Theorems {lit}`VEB.insert_member_false_of_ne`,
  {lit}`VEB.delete_member_false_old`, and
  {lit}`VEB.delete_member_false_of_eq`: direct failed member-query preservation
  wrappers after insertion and deletion.
- Theorems {lit}`VEB.insert_minimum_correct`,
  {lit}`VEB.insert_maximum_correct`, {lit}`VEB.delete_minimum_correct`, and
  {lit}`VEB.delete_maximum_correct`: extrema returned after updates are
  exactly extrema of the updated finite set.
- Theorems {lit}`VEB.insert_minimum_mem`,
  {lit}`VEB.insert_minimum_mem_old_of_ne`,
  {lit}`VEB.insert_minimum_le_inserted`, {lit}`VEB.insert_minimum_le_old`,
  {lit}`VEB.insert_maximum_mem`,
  {lit}`VEB.insert_maximum_mem_old_of_ne`,
  {lit}`VEB.insert_maximum_inserted_le`, and
  {lit}`VEB.insert_maximum_old_le`: direct membership and order corollaries
  for extrema returned after insertion, including old-key membership when the
  returned extremum is not the inserted key.
- Theorems {lit}`VEB.delete_minimum_ne`, {lit}`VEB.delete_minimum_mem`,
  {lit}`VEB.delete_minimum_le_old`, {lit}`VEB.delete_maximum_ne`,
  {lit}`VEB.delete_maximum_mem`, and {lit}`VEB.delete_maximum_old_le`:
  direct membership and order corollaries for extrema returned after deletion.
- Theorems {lit}`VEB.insert_minimum_none_iff`,
  {lit}`VEB.insert_maximum_none_iff`, {lit}`VEB.delete_minimum_none_iff`, and
  {lit}`VEB.delete_maximum_none_iff`: empty extrema results after updates
  match whether the updated finite set is empty.
- Theorems {lit}`VEB.minimum_none_of_empty`,
  {lit}`VEB.maximum_none_of_empty`,
  {lit}`VEB.insert_minimum_ne_none`,
  {lit}`VEB.insert_maximum_ne_none`,
  {lit}`VEB.delete_minimum_none_of_all_eq`, and
  {lit}`VEB.delete_maximum_none_of_all_eq`: direct extrema empty-result
  wrappers for base and updated trees.
- Theorems {lit}`VEB.minimum_ne_none_of_nonempty` and
  {lit}`VEB.maximum_ne_none_of_nonempty`: direct nonempty-result wrappers for
  base extrema queries.
- Theorems {lit}`VEB.delete_minimum_ne_none_of_remaining` and
  {lit}`VEB.delete_maximum_ne_none_of_remaining`: direct nonempty-result
  wrappers for extrema queries after deletion leaves a remaining old key.
- Theorems {lit}`VEB.insert_successor_correct`,
  {lit}`VEB.insert_predecessor_correct`, {lit}`VEB.delete_successor_correct`,
  and {lit}`VEB.delete_predecessor_correct`: successor and predecessor queries
  after updates are extrema of the updated filtered finite set.
- Theorems {lit}`VEB.insert_successor_mem`,
  {lit}`VEB.insert_successor_mem_old_of_ne`,
  {lit}`VEB.insert_successor_gt`, {lit}`VEB.insert_successor_le`,
  {lit}`VEB.insert_predecessor_mem`,
  {lit}`VEB.insert_predecessor_mem_old_of_ne`,
  {lit}`VEB.insert_predecessor_lt`, and {lit}`VEB.insert_le_predecessor`:
  direct membership and order corollaries for returned neighbors after
  insertion, including old-key membership when the returned neighbor is not the
  inserted key.
- Theorems {lit}`VEB.delete_successor_mem`, {lit}`VEB.delete_successor_gt`,
  {lit}`VEB.delete_successor_le`, {lit}`VEB.delete_predecessor_mem`,
  {lit}`VEB.delete_predecessor_lt`, and {lit}`VEB.delete_le_predecessor`:
  direct membership and order corollaries for returned neighbors after
  deletion.
- Theorems {lit}`VEB.insert_member_lt_univ`,
  {lit}`VEB.insert_minimum_lt_univ`, {lit}`VEB.insert_maximum_lt_univ`,
  {lit}`VEB.insert_successor_lt_univ`,
  {lit}`VEB.insert_predecessor_lt_univ`, {lit}`VEB.delete_member_lt_univ`,
  {lit}`VEB.delete_minimum_lt_univ`, {lit}`VEB.delete_maximum_lt_univ`,
  {lit}`VEB.delete_successor_lt_univ`, and
  {lit}`VEB.delete_predecessor_lt_univ`: successful queries after updates
  still return keys inside the represented universe.
- Theorems {lit}`VEB.insert_successor_none_iff`,
  {lit}`VEB.insert_predecessor_none_iff`,
  {lit}`VEB.delete_successor_none_iff`, and
  {lit}`VEB.delete_predecessor_none_iff`: no-neighbor query results after
  updates match the absence of updated keys on the corresponding side.
- Theorems {lit}`VEB.successor_none_of_no_gt`,
  {lit}`VEB.predecessor_none_of_no_lt`,
  {lit}`VEB.insert_successor_none_of_no_gt`,
  {lit}`VEB.insert_predecessor_none_of_no_lt`,
  {lit}`VEB.delete_successor_none_of_no_gt`, and
  {lit}`VEB.delete_predecessor_none_of_no_lt`: direct no-neighbor query
  wrappers for base and updated trees.
- Theorems {lit}`VEB.successor_ne_none_of_exists_gt` and
  {lit}`VEB.predecessor_ne_none_of_exists_lt`: direct existing-neighbor
  wrappers for base successor and predecessor queries.
- Theorems {lit}`VEB.insert_successor_ne_none_of_insert_gt`,
  {lit}`VEB.insert_successor_ne_none_of_old_gt`,
  {lit}`VEB.insert_predecessor_ne_none_of_insert_lt`,
  {lit}`VEB.insert_predecessor_ne_none_of_old_lt`,
  {lit}`VEB.delete_successor_ne_none_of_remaining_gt`, and
  {lit}`VEB.delete_predecessor_ne_none_of_remaining_lt`: direct
  existing-neighbor wrappers for updated successor and predecessor queries.
- Theorems {lit}`VEB.insert_successor_none_of_insert_le_old_no_gt`,
  {lit}`VEB.insert_predecessor_none_of_query_le_insert_old_no_lt`,
  {lit}`VEB.delete_successor_none_of_old_no_gt`, and
  {lit}`VEB.delete_predecessor_none_of_old_no_lt`: premise-light
  no-neighbor wrappers stated against the old represented set.
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

/-- A successful membership query returns a key inside the represented universe. -/
theorem member_lt_univ {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hmem : member x t = true) :
    x < t.univSize := by
  exact hrep.2 x ((member_correct (t := t) (s := s) (x := x) hrep).mp hmem)

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

/-- A returned minimum belongs to the represented key set. -/
theorem minimum_mem {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hmin : minimum t = some x) :
    x ∈ s := by
  exact (minimum_correct (t := t) (s := s) (x := x) hrep hmin).1

/-- A returned minimum is no larger than any represented key. -/
theorem minimum_le {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hmin : minimum t = some x) (hy : y ∈ s) :
    x <= y := by
  exact (minimum_correct (t := t) (s := s) (x := x) hrep hmin).2 y hy

/-- A returned minimum lies inside the represented universe. -/
theorem minimum_lt_univ {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hmin : minimum t = some x) :
    x < t.univSize := by
  exact hrep.2 x (minimum_correct (t := t) (s := s) (x := x) hrep hmin).1

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

/-- If the represented set is empty, no minimum is returned. -/
theorem minimum_none_of_empty {t : Tree} {s : Finset Nat}
    (hrep : Represents t s) (hempty : s = ∅) :
    minimum t = none := by
  exact (minimum_none_iff (t := t) (s := s) hrep).2 hempty

/-- A nonempty represented set forces the minimum query to return a result. -/
theorem minimum_ne_none_of_nonempty {t : Tree} {s : Finset Nat}
    (hrep : Represents t s) (hne : s.Nonempty) :
    minimum t ≠ none := by
  intro hnone
  have hempty : s = ∅ := (minimum_none_iff (t := t) (s := s) hrep).1 hnone
  rcases hne with ⟨x, hx⟩
  rw [hempty] at hx
  simp at hx

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

/-- A returned maximum belongs to the represented key set. -/
theorem maximum_mem {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hmax : maximum t = some x) :
    x ∈ s := by
  exact (maximum_correct (t := t) (s := s) (x := x) hrep hmax).1

/-- Every represented key is no larger than a returned maximum. -/
theorem le_maximum {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hmax : maximum t = some x) (hy : y ∈ s) :
    y <= x := by
  exact (maximum_correct (t := t) (s := s) (x := x) hrep hmax).2 y hy

/-- A returned maximum lies inside the represented universe. -/
theorem maximum_lt_univ {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hmax : maximum t = some x) :
    x < t.univSize := by
  exact hrep.2 x (maximum_correct (t := t) (s := s) (x := x) hrep hmax).1

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

/-- If the represented set is empty, no maximum is returned. -/
theorem maximum_none_of_empty {t : Tree} {s : Finset Nat}
    (hrep : Represents t s) (hempty : s = ∅) :
    maximum t = none := by
  exact (maximum_none_iff (t := t) (s := s) hrep).2 hempty

/-- A nonempty represented set forces the maximum query to return a result. -/
theorem maximum_ne_none_of_nonempty {t : Tree} {s : Finset Nat}
    (hrep : Represents t s) (hne : s.Nonempty) :
    maximum t ≠ none := by
  intro hnone
  have hempty : s = ∅ := (maximum_none_iff (t := t) (s := s) hrep).1 hnone
  rcases hne with ⟨x, hx⟩
  rw [hempty] at hx
  simp at hx

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

/-- A returned successor belongs to the represented key set. -/
theorem successor_mem {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hsucc : successor x t = some y) :
    y ∈ s := by
  exact (successor_correct (t := t) (s := s) (x := x) (y := y) hrep hsucc).1

/-- A returned successor is greater than the query. -/
theorem successor_gt {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hsucc : successor x t = some y) :
    x < y := by
  exact (successor_correct (t := t) (s := s) (x := x) (y := y) hrep hsucc).2.1

/-- A returned successor is no larger than any represented key greater than the query. -/
theorem successor_le {t : Tree} {s : Finset Nat} {x y z : Nat}
    (hrep : Represents t s) (hsucc : successor x t = some y)
    (hz : z ∈ s) (hxz : x < z) :
    y <= z := by
  exact (successor_correct (t := t) (s := s) (x := x) (y := y) hrep hsucc).2.2 z hz hxz

/-- A returned successor lies inside the represented universe. -/
theorem successor_lt_univ {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hsucc : successor x t = some y) :
    y < t.univSize := by
  exact hrep.2 y
    (successor_correct (t := t) (s := s) (x := x) (y := y) hrep hsucc).1

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

/-- If no represented key is greater than the query, no successor is returned. -/
theorem successor_none_of_no_gt {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hnone : forall y, y ∈ s -> ¬ x < y) :
    successor x t = none := by
  exact (successor_none_iff (t := t) (s := s) (x := x) hrep).2 hnone

/-- An existing greater represented key forces successor to return a result. -/
theorem successor_ne_none_of_exists_gt {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hy : y ∈ s) (hxy : x < y) :
    successor x t ≠ none := by
  intro hnone
  have hnoGt : forall z, z ∈ s -> ¬ x < z :=
    (successor_none_iff (t := t) (s := s) (x := x) hrep).1 hnone
  exact (hnoGt y hy) hxy

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

/-- A returned predecessor belongs to the represented key set. -/
theorem predecessor_mem {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hpred : predecessor x t = some y) :
    y ∈ s := by
  exact (predecessor_correct (t := t) (s := s) (x := x) (y := y) hrep hpred).1

/-- A returned predecessor is less than the query. -/
theorem predecessor_lt {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hpred : predecessor x t = some y) :
    y < x := by
  exact (predecessor_correct (t := t) (s := s) (x := x) (y := y) hrep hpred).2.1

/-- Any represented key less than the query is no larger than a returned predecessor. -/
theorem le_predecessor {t : Tree} {s : Finset Nat} {x y z : Nat}
    (hrep : Represents t s) (hpred : predecessor x t = some y)
    (hz : z ∈ s) (hzx : z < x) :
    z <= y := by
  exact (predecessor_correct (t := t) (s := s) (x := x) (y := y) hrep hpred).2.2 z hz hzx

/-- A returned predecessor lies inside the represented universe. -/
theorem predecessor_lt_univ {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hpred : predecessor x t = some y) :
    y < t.univSize := by
  exact hrep.2 y
    (predecessor_correct (t := t) (s := s) (x := x) (y := y) hrep hpred).1

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

/-- If no represented key is smaller than the query, no predecessor is returned. -/
theorem predecessor_none_of_no_lt {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hnone : forall y, y ∈ s -> ¬ y < x) :
    predecessor x t = none := by
  exact (predecessor_none_iff (t := t) (s := s) (x := x) hrep).2 hnone

/-- An existing smaller represented key forces predecessor to return a result. -/
theorem predecessor_ne_none_of_exists_lt {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hy : y ∈ s) (hyx : y < x) :
    predecessor x t ≠ none := by
  intro hnone
  have hnoLt : forall z, z ∈ s -> ¬ z < x :=
    (predecessor_none_iff (t := t) (s := s) (x := x) hrep).1 hnone
  exact (hnoLt y hy) hyx

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

/-- A successful membership query after insertion lies inside the represented universe. -/
theorem insert_member_lt_univ {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmem : member y (insert x t) = true) :
    y < t.univSize := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  exact member_lt_univ
    (t := insert x t) (s := Insert.insert x s) (x := y) hinsert hmem

/-- Membership succeeds for the inserted key after insertion. -/
theorem insert_member_self {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    member x (insert x t) = true := by
  rw [insert_member_iff (t := t) (s := s) (x := x) (y := x) hrep hx]
  exact Or.inl rfl

/-- Old represented keys remain members after insertion. -/
theorem insert_member_old {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hy : member y t = true) :
    member y (insert x t) = true := by
  rw [insert_member_iff (t := t) (s := s) (x := x) (y := y) hrep hx]
  exact Or.inr hy

/-- Membership after insertion fails exactly for noninserted keys absent before insertion. -/
theorem insert_member_false_iff {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    member y (insert x t) = false <-> y ≠ x ∧ member y t = false := by
  constructor
  · intro hfalse
    constructor
    · intro hyx
      have htrue : member y (insert x t) = true :=
        (insert_member_iff (t := t) (s := s) (x := x) (y := y) hrep hx).mpr
          (Or.inl hyx)
      rw [hfalse] at htrue
      contradiction
    · cases hold : member y t
      · rfl
      · have htrue : member y (insert x t) = true :=
          (insert_member_iff (t := t) (s := s) (x := x) (y := y) hrep hx).mpr
            (Or.inr hold)
        rw [hfalse] at htrue
        contradiction
  · intro h
    rcases h with ⟨hyx, holdFalse⟩
    cases hmember : member y (insert x t)
    · rfl
    · have hcases : y = x ∨ member y t = true :=
        (insert_member_iff (t := t) (s := s) (x := x) (y := y) hrep hx).mp
          hmember
      cases hcases with
      | inl hyxEq =>
          exact False.elim (hyx hyxEq)
      | inr holdTrue =>
          rw [holdFalse] at holdTrue
          contradiction

/-- Old failed membership queries different from the inserted key remain false after insertion. -/
theorem insert_member_false_of_ne {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hyx : y ≠ x) (hy : member y t = false) :
    member y (insert x t) = false := by
  rw [insert_member_false_iff (t := t) (s := s) (x := x) (y := y) hrep hx]
  exact ⟨hyx, hy⟩

/-- A returned minimum after insertion is the least key among the inserted key and old set. -/
theorem insert_minimum_correct {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmin : minimum (insert x t) = some m) :
    (m = x ∨ m ∈ s) ∧ m <= x ∧ forall y, y ∈ s -> m <= y := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  have hmin' := minimum_correct
    (t := insert x t) (s := Insert.insert x s) (x := m) hinsert hmin
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.mem_insert] using hmin'.1
  · exact hmin'.2 x (by simp)
  · intro y hy
    exact hmin'.2 y (by simp [hy])

/-- A returned minimum after insertion is the inserted key or an old key. -/
theorem insert_minimum_mem {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmin : minimum (insert x t) = some m) :
    m = x ∨ m ∈ s := by
  exact (insert_minimum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hx hmin).1

/-- A returned minimum after insertion that is not the inserted key is an old key. -/
theorem insert_minimum_mem_old_of_ne {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmin : minimum (insert x t) = some m) (hmx : m ≠ x) :
    m ∈ s := by
  cases insert_minimum_mem
      (t := t) (s := s) (x := x) (m := m) hrep hx hmin with
  | inl hmxEq => exact False.elim (hmx hmxEq)
  | inr hmem => exact hmem

/-- A returned minimum after insertion is no larger than the inserted key. -/
theorem insert_minimum_le_inserted {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmin : minimum (insert x t) = some m) :
    m <= x := by
  exact (insert_minimum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hx hmin).2.1

/-- A returned minimum after insertion is no larger than any old key. -/
theorem insert_minimum_le_old {t : Tree} {s : Finset Nat} {x m y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmin : minimum (insert x t) = some m) (hy : y ∈ s) :
    m <= y := by
  exact (insert_minimum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hx hmin).2.2 y hy

/-- A returned minimum after insertion lies inside the represented universe. -/
theorem insert_minimum_lt_univ {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmin : minimum (insert x t) = some m) :
    m < t.univSize := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  exact minimum_lt_univ
    (t := insert x t) (s := Insert.insert x s) (x := m) hinsert hmin

/-- Insertion makes the updated set nonempty, so no minimum-empty result is possible. -/
theorem insert_minimum_none_iff {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    minimum (insert x t) = none <-> False := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  rw [minimum_none_iff (t := insert x t) (s := Insert.insert x s) hinsert]
  simp

/-- After insertion, a minimum-empty result is impossible. -/
theorem insert_minimum_ne_none {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    minimum (insert x t) ≠ none := by
  intro hnone
  exact (insert_minimum_none_iff (t := t) (s := s) (x := x) hrep hx).1 hnone

/-- A returned maximum after insertion is the greatest key among the inserted key and old set. -/
theorem insert_maximum_correct {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmax : maximum (insert x t) = some m) :
    (m = x ∨ m ∈ s) ∧ x <= m ∧ forall y, y ∈ s -> y <= m := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  have hmax' := maximum_correct
    (t := insert x t) (s := Insert.insert x s) (x := m) hinsert hmax
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.mem_insert] using hmax'.1
  · exact hmax'.2 x (by simp)
  · intro y hy
    exact hmax'.2 y (by simp [hy])

/-- A returned maximum after insertion is the inserted key or an old key. -/
theorem insert_maximum_mem {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmax : maximum (insert x t) = some m) :
    m = x ∨ m ∈ s := by
  exact (insert_maximum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hx hmax).1

/-- A returned maximum after insertion that is not the inserted key is an old key. -/
theorem insert_maximum_mem_old_of_ne {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmax : maximum (insert x t) = some m) (hmx : m ≠ x) :
    m ∈ s := by
  cases insert_maximum_mem
      (t := t) (s := s) (x := x) (m := m) hrep hx hmax with
  | inl hmxEq => exact False.elim (hmx hmxEq)
  | inr hmem => exact hmem

/-- The inserted key is no larger than a returned maximum after insertion. -/
theorem insert_maximum_inserted_le {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmax : maximum (insert x t) = some m) :
    x <= m := by
  exact (insert_maximum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hx hmax).2.1

/-- Any old key is no larger than a returned maximum after insertion. -/
theorem insert_maximum_old_le {t : Tree} {s : Finset Nat} {x m y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmax : maximum (insert x t) = some m) (hy : y ∈ s) :
    y <= m := by
  exact (insert_maximum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hx hmax).2.2 y hy

/-- A returned maximum after insertion lies inside the represented universe. -/
theorem insert_maximum_lt_univ {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hmax : maximum (insert x t) = some m) :
    m < t.univSize := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  exact maximum_lt_univ
    (t := insert x t) (s := Insert.insert x s) (x := m) hinsert hmax

/-- Insertion makes the updated set nonempty, so no maximum-empty result is possible. -/
theorem insert_maximum_none_iff {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    maximum (insert x t) = none <-> False := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  rw [maximum_none_iff (t := insert x t) (s := Insert.insert x s) hinsert]
  simp

/-- After insertion, a maximum-empty result is impossible. -/
theorem insert_maximum_ne_none {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    maximum (insert x t) ≠ none := by
  intro hnone
  exact (insert_maximum_none_iff (t := t) (s := s) (x := x) hrep hx).1 hnone

/-- A returned successor after insertion is the least updated key greater than the query. -/
theorem insert_successor_correct {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hsucc : successor q (insert x t) = some y) :
    (y = x ∨ y ∈ s) ∧ q < y ∧
      forall z, z = x ∨ z ∈ s -> q < z -> y <= z := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  have hsucc' := successor_correct
    (t := insert x t) (s := Insert.insert x s) (x := q) (y := y)
    hinsert hsucc
  refine ⟨?_, hsucc'.2.1, ?_⟩
  · simpa [Finset.mem_insert] using hsucc'.1
  · intro z hz hqz
    exact hsucc'.2.2 z (by simpa [Finset.mem_insert] using hz) hqz

/-- A returned successor after insertion is either the inserted key or an old key. -/
theorem insert_successor_mem {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hsucc : successor q (insert x t) = some y) :
    y = x ∨ y ∈ s := by
  exact (insert_successor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hx hsucc).1

/-- A returned successor after insertion that is not the inserted key is an old key. -/
theorem insert_successor_mem_old_of_ne {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hsucc : successor q (insert x t) = some y) (hyx : y ≠ x) :
    y ∈ s := by
  cases insert_successor_mem
      (t := t) (s := s) (x := x) (q := q) (y := y) hrep hx hsucc with
  | inl hyxEq => exact False.elim (hyx hyxEq)
  | inr hmem => exact hmem

/-- A returned successor after insertion is greater than the query. -/
theorem insert_successor_gt {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hsucc : successor q (insert x t) = some y) :
    q < y := by
  exact (insert_successor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hx hsucc).2.1

/-- A returned successor after insertion is no larger than any updated greater key. -/
theorem insert_successor_le {t : Tree} {s : Finset Nat} {x q y z : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hsucc : successor q (insert x t) = some y)
    (hz : z = x ∨ z ∈ s) (hqz : q < z) :
    y <= z := by
  exact (insert_successor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hx hsucc).2.2 z hz hqz

/-- A returned successor after insertion lies inside the represented universe. -/
theorem insert_successor_lt_univ {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hsucc : successor q (insert x t) = some y) :
    y < t.univSize := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  exact successor_lt_univ
    (t := insert x t) (s := Insert.insert x s) (x := q) (y := y)
    hinsert hsucc

/-- No successor after insertion means no inserted or old key is greater than the query. -/
theorem insert_successor_none_iff {t : Tree} {s : Finset Nat} {x q : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    successor q (insert x t) = none <->
      forall y, y = x ∨ y ∈ s -> ¬ q < y := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  simpa [Finset.mem_insert] using
    (successor_none_iff (t := insert x t) (s := Insert.insert x s)
      (x := q) hinsert)

/-- If no updated key is greater than the query after insertion, no successor is returned. -/
theorem insert_successor_none_of_no_gt {t : Tree} {s : Finset Nat} {x q : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hnone : forall y, y = x ∨ y ∈ s -> ¬ q < y) :
    successor q (insert x t) = none := by
  exact (insert_successor_none_iff
    (t := t) (s := s) (x := x) (q := q) hrep hx).2 hnone

/-- If the inserted key and every old key are no greater than the query, no successor is returned. -/
theorem insert_successor_none_of_insert_le_old_no_gt {t : Tree}
    {s : Finset Nat} {x q : Nat} (hrep : Represents t s)
    (hx : x < t.univSize) (hxq : x <= q)
    (hold : forall y, y ∈ s -> ¬ q < y) :
    successor q (insert x t) = none := by
  exact insert_successor_none_of_no_gt
    (t := t) (s := s) (x := x) (q := q) hrep hx
    (by
      intro y hy
      cases hy with
      | inl hyx =>
          omega
      | inr hys =>
          exact hold y hys)

/-- If the inserted key is greater than the query, successor after insertion exists. -/
theorem insert_successor_ne_none_of_insert_gt {t : Tree} {s : Finset Nat}
    {x q : Nat} (hrep : Represents t s) (hx : x < t.univSize)
    (hqx : q < x) :
    successor q (insert x t) ≠ none := by
  intro hnone
  have hnoGt : forall y, y = x ∨ y ∈ s -> ¬ q < y :=
    (insert_successor_none_iff
      (t := t) (s := s) (x := x) (q := q) hrep hx).1 hnone
  exact (hnoGt x (Or.inl rfl)) hqx

/-- If an old represented key is greater than the query, successor after insertion exists. -/
theorem insert_successor_ne_none_of_old_gt {t : Tree} {s : Finset Nat}
    {x q y : Nat} (hrep : Represents t s) (hx : x < t.univSize)
    (hy : y ∈ s) (hqy : q < y) :
    successor q (insert x t) ≠ none := by
  intro hnone
  have hnoGt : forall z, z = x ∨ z ∈ s -> ¬ q < z :=
    (insert_successor_none_iff
      (t := t) (s := s) (x := x) (q := q) hrep hx).1 hnone
  exact (hnoGt y (Or.inr hy)) hqy

/-- A returned predecessor after insertion is the greatest updated key less than the query. -/
theorem insert_predecessor_correct {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hpred : predecessor q (insert x t) = some y) :
    (y = x ∨ y ∈ s) ∧ y < q ∧
      forall z, z = x ∨ z ∈ s -> z < q -> z <= y := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  have hpred' := predecessor_correct
    (t := insert x t) (s := Insert.insert x s) (x := q) (y := y)
    hinsert hpred
  refine ⟨?_, hpred'.2.1, ?_⟩
  · simpa [Finset.mem_insert] using hpred'.1
  · intro z hz hzq
    exact hpred'.2.2 z (by simpa [Finset.mem_insert] using hz) hzq

/-- A returned predecessor after insertion is either the inserted key or an old key. -/
theorem insert_predecessor_mem {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hpred : predecessor q (insert x t) = some y) :
    y = x ∨ y ∈ s := by
  exact (insert_predecessor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hx hpred).1

/-- A returned predecessor after insertion that is not the inserted key is an old key. -/
theorem insert_predecessor_mem_old_of_ne {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hpred : predecessor q (insert x t) = some y) (hyx : y ≠ x) :
    y ∈ s := by
  cases insert_predecessor_mem
      (t := t) (s := s) (x := x) (q := q) (y := y) hrep hx hpred with
  | inl hyxEq => exact False.elim (hyx hyxEq)
  | inr hmem => exact hmem

/-- A returned predecessor after insertion is less than the query. -/
theorem insert_predecessor_lt {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hpred : predecessor q (insert x t) = some y) :
    y < q := by
  exact (insert_predecessor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hx hpred).2.1

/-- Any updated key less than the query is no larger than a returned predecessor. -/
theorem insert_le_predecessor {t : Tree} {s : Finset Nat} {x q y z : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hpred : predecessor q (insert x t) = some y)
    (hz : z = x ∨ z ∈ s) (hzq : z < q) :
    z <= y := by
  exact (insert_predecessor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hx hpred).2.2 z hz hzq

/-- A returned predecessor after insertion lies inside the represented universe. -/
theorem insert_predecessor_lt_univ {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hpred : predecessor q (insert x t) = some y) :
    y < t.univSize := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  exact predecessor_lt_univ
    (t := insert x t) (s := Insert.insert x s) (x := q) (y := y)
    hinsert hpred

/-- No predecessor after insertion means no inserted or old key is smaller than the query. -/
theorem insert_predecessor_none_iff {t : Tree} {s : Finset Nat} {x q : Nat}
    (hrep : Represents t s) (hx : x < t.univSize) :
    predecessor q (insert x t) = none <->
      forall y, y = x ∨ y ∈ s -> ¬ y < q := by
  have hinsert : Represents (insert x t) (Insert.insert x s) :=
    insert_correct (t := t) (s := s) (x := x) hrep hx
  simpa [Finset.mem_insert] using
    (predecessor_none_iff (t := insert x t) (s := Insert.insert x s)
      (x := q) hinsert)

/-- If no updated key is smaller than the query after insertion, no predecessor is returned. -/
theorem insert_predecessor_none_of_no_lt {t : Tree} {s : Finset Nat} {x q : Nat}
    (hrep : Represents t s) (hx : x < t.univSize)
    (hnone : forall y, y = x ∨ y ∈ s -> ¬ y < q) :
    predecessor q (insert x t) = none := by
  exact (insert_predecessor_none_iff
    (t := t) (s := s) (x := x) (q := q) hrep hx).2 hnone

/-- If the query is no greater than the inserted key and no old key is smaller, no predecessor is returned. -/
theorem insert_predecessor_none_of_query_le_insert_old_no_lt {t : Tree}
    {s : Finset Nat} {x q : Nat} (hrep : Represents t s)
    (hx : x < t.univSize) (hqx : q <= x)
    (hold : forall y, y ∈ s -> ¬ y < q) :
    predecessor q (insert x t) = none := by
  exact insert_predecessor_none_of_no_lt
    (t := t) (s := s) (x := x) (q := q) hrep hx
    (by
      intro y hy
      cases hy with
      | inl hyx =>
          omega
      | inr hys =>
          exact hold y hys)

/-- If the inserted key is smaller than the query, predecessor after insertion exists. -/
theorem insert_predecessor_ne_none_of_insert_lt {t : Tree} {s : Finset Nat}
    {x q : Nat} (hrep : Represents t s) (hx : x < t.univSize)
    (hxq : x < q) :
    predecessor q (insert x t) ≠ none := by
  intro hnone
  have hnoLt : forall y, y = x ∨ y ∈ s -> ¬ y < q :=
    (insert_predecessor_none_iff
      (t := t) (s := s) (x := x) (q := q) hrep hx).1 hnone
  exact (hnoLt x (Or.inl rfl)) hxq

/-- If an old represented key is smaller than the query, predecessor after insertion exists. -/
theorem insert_predecessor_ne_none_of_old_lt {t : Tree} {s : Finset Nat}
    {x q y : Nat} (hrep : Represents t s) (hx : x < t.univSize)
    (hy : y ∈ s) (hyq : y < q) :
    predecessor q (insert x t) ≠ none := by
  intro hnone
  have hnoLt : forall z, z = x ∨ z ∈ s -> ¬ z < q :=
    (insert_predecessor_none_iff
      (t := t) (s := s) (x := x) (q := q) hrep hx).1 hnone
  exact (hnoLt y (Or.inr hy)) hyq

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

/-- A successful membership query after deletion lies inside the represented universe. -/
theorem delete_member_lt_univ {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hmem : member y (delete x t) = true) :
    y < t.univSize := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  exact member_lt_univ
    (t := delete x t) (s := s.erase x) (x := y) hdelete hmem

/-- Membership fails for the deleted key after deletion. -/
theorem delete_member_deleted_false {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) :
    member x (delete x t) = false := by
  cases hmember : member x (delete x t)
  · rfl
  · have hbad :
        x ≠ x ∧ member x t = true :=
        (delete_member_iff (t := t) (s := s) (x := x) (y := x) hrep).mp hmember
    exact False.elim (hbad.1 rfl)

/-- Old keys different from the deleted key remain members after deletion. -/
theorem delete_member_of_ne {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hxy : y ≠ x) (hy : member y t = true) :
    member y (delete x t) = true := by
  rw [delete_member_iff (t := t) (s := s) (x := x) (y := y) hrep]
  exact ⟨hxy, hy⟩

/-- Membership after deletion fails exactly for the deleted key or old absent keys. -/
theorem delete_member_false_iff {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) :
    member y (delete x t) = false <-> y = x ∨ member y t = false := by
  constructor
  · intro hfalse
    by_cases hxy : y = x
    · exact Or.inl hxy
    · right
      cases hold : member y t
      · rfl
      · have htrue : member y (delete x t) = true :=
          (delete_member_iff (t := t) (s := s) (x := x) (y := y) hrep).mpr
            ⟨hxy, hold⟩
        rw [hfalse] at htrue
        contradiction
  · intro h
    cases h with
    | inl hyx =>
        rw [hyx]
        exact delete_member_deleted_false (t := t) (s := s) (x := x) hrep
    | inr holdFalse =>
        cases hmember : member y (delete x t)
        · rfl
        · have hcases : y ≠ x ∧ member y t = true :=
            (delete_member_iff (t := t) (s := s) (x := x) (y := y) hrep).mp
              hmember
          rw [holdFalse] at hcases
          exact hcases.2.symm

/-- Old failed membership queries remain false after deletion. -/
theorem delete_member_false_old {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hy : member y t = false) :
    member y (delete x t) = false := by
  rw [delete_member_false_iff (t := t) (s := s) (x := x) (y := y) hrep]
  exact Or.inr hy

/-- Keys equal to the deleted key are failed membership queries after deletion. -/
theorem delete_member_false_of_eq {t : Tree} {s : Finset Nat} {x y : Nat}
    (hrep : Represents t s) (hyx : y = x) :
    member y (delete x t) = false := by
  rw [delete_member_false_iff (t := t) (s := s) (x := x) (y := y) hrep]
  exact Or.inl hyx

/-- A returned minimum after deletion is the least remaining old key. -/
theorem delete_minimum_correct {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hmin : minimum (delete x t) = some m) :
    m ≠ x ∧ m ∈ s ∧ forall y, y ∈ s -> y ≠ x -> m <= y := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  have hmin' := minimum_correct
    (t := delete x t) (s := s.erase x) (x := m) hdelete hmin
  have hmem : m ≠ x ∧ m ∈ s := by
    simpa [Finset.mem_erase] using hmin'.1
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro y hy hyx
  exact hmin'.2 y (by simp [Finset.mem_erase, hyx, hy])

/-- A returned minimum after deletion is not the deleted key. -/
theorem delete_minimum_ne {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hmin : minimum (delete x t) = some m) :
    m ≠ x := by
  exact (delete_minimum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hmin).1

/-- A returned minimum after deletion is an old key. -/
theorem delete_minimum_mem {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hmin : minimum (delete x t) = some m) :
    m ∈ s := by
  exact (delete_minimum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hmin).2.1

/-- A returned minimum after deletion is no larger than any old remaining key. -/
theorem delete_minimum_le_old {t : Tree} {s : Finset Nat} {x m y : Nat}
    (hrep : Represents t s) (hmin : minimum (delete x t) = some m)
    (hy : y ∈ s) (hyx : y ≠ x) :
    m <= y := by
  exact (delete_minimum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hmin).2.2 y hy hyx

/-- A returned minimum after deletion lies inside the represented universe. -/
theorem delete_minimum_lt_univ {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hmin : minimum (delete x t) = some m) :
    m < t.univSize := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  exact minimum_lt_univ
    (t := delete x t) (s := s.erase x) (x := m) hdelete hmin

/-- No minimum after deletion means every old key was the deleted key. -/
theorem delete_minimum_none_iff {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) :
    minimum (delete x t) = none <-> forall y, y ∈ s -> y = x := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  rw [minimum_none_iff (t := delete x t) (s := s.erase x) hdelete]
  constructor
  · intro hempty y hy
    by_contra hyx
    have hyerase : y ∈ s.erase x := by
      simp [Finset.mem_erase, hyx, hy]
    have hnot : y ∉ s.erase x := by
      simp [hempty]
    exact False.elim (hnot hyerase)
  · intro hall
    ext y
    constructor
    · intro hyerase
      rw [Finset.mem_erase] at hyerase
      exact False.elim (hyerase.1 (hall y hyerase.2))
    · intro hyempty
      simp at hyempty

/-- If every old key equals the deleted key, no minimum remains after deletion. -/
theorem delete_minimum_none_of_all_eq {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hall : forall y, y ∈ s -> y = x) :
    minimum (delete x t) = none := by
  exact (delete_minimum_none_iff (t := t) (s := s) (x := x) hrep).2 hall

/-- If some old key remains after deletion, a minimum still exists. -/
theorem delete_minimum_ne_none_of_remaining {t : Tree} {s : Finset Nat}
    {x y : Nat} (hrep : Represents t s) (hy : y ∈ s) (hyx : y ≠ x) :
    minimum (delete x t) ≠ none := by
  intro hnone
  have hall : forall z, z ∈ s -> z = x :=
    (delete_minimum_none_iff (t := t) (s := s) (x := x) hrep).1 hnone
  exact hyx (hall y hy)

/-- A returned maximum after deletion is the greatest remaining old key. -/
theorem delete_maximum_correct {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hmax : maximum (delete x t) = some m) :
    m ≠ x ∧ m ∈ s ∧ forall y, y ∈ s -> y ≠ x -> y <= m := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  have hmax' := maximum_correct
    (t := delete x t) (s := s.erase x) (x := m) hdelete hmax
  have hmem : m ≠ x ∧ m ∈ s := by
    simpa [Finset.mem_erase] using hmax'.1
  refine ⟨hmem.1, hmem.2, ?_⟩
  intro y hy hyx
  exact hmax'.2 y (by simp [Finset.mem_erase, hyx, hy])

/-- A returned maximum after deletion is not the deleted key. -/
theorem delete_maximum_ne {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hmax : maximum (delete x t) = some m) :
    m ≠ x := by
  exact (delete_maximum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hmax).1

/-- A returned maximum after deletion is an old key. -/
theorem delete_maximum_mem {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hmax : maximum (delete x t) = some m) :
    m ∈ s := by
  exact (delete_maximum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hmax).2.1

/-- Any old remaining key is no larger than a returned maximum after deletion. -/
theorem delete_maximum_old_le {t : Tree} {s : Finset Nat} {x m y : Nat}
    (hrep : Represents t s) (hmax : maximum (delete x t) = some m)
    (hy : y ∈ s) (hyx : y ≠ x) :
    y <= m := by
  exact (delete_maximum_correct
    (t := t) (s := s) (x := x) (m := m) hrep hmax).2.2 y hy hyx

/-- A returned maximum after deletion lies inside the represented universe. -/
theorem delete_maximum_lt_univ {t : Tree} {s : Finset Nat} {x m : Nat}
    (hrep : Represents t s) (hmax : maximum (delete x t) = some m) :
    m < t.univSize := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  exact maximum_lt_univ
    (t := delete x t) (s := s.erase x) (x := m) hdelete hmax

/-- No maximum after deletion means every old key was the deleted key. -/
theorem delete_maximum_none_iff {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) :
    maximum (delete x t) = none <-> forall y, y ∈ s -> y = x := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  rw [maximum_none_iff (t := delete x t) (s := s.erase x) hdelete]
  constructor
  · intro hempty y hy
    by_contra hyx
    have hyerase : y ∈ s.erase x := by
      simp [Finset.mem_erase, hyx, hy]
    have hnot : y ∉ s.erase x := by
      simp [hempty]
    exact False.elim (hnot hyerase)
  · intro hall
    ext y
    constructor
    · intro hyerase
      rw [Finset.mem_erase] at hyerase
      exact False.elim (hyerase.1 (hall y hyerase.2))
    · intro hyempty
      simp at hyempty

/-- If every old key equals the deleted key, no maximum remains after deletion. -/
theorem delete_maximum_none_of_all_eq {t : Tree} {s : Finset Nat} {x : Nat}
    (hrep : Represents t s) (hall : forall y, y ∈ s -> y = x) :
    maximum (delete x t) = none := by
  exact (delete_maximum_none_iff (t := t) (s := s) (x := x) hrep).2 hall

/-- If some old key remains after deletion, a maximum still exists. -/
theorem delete_maximum_ne_none_of_remaining {t : Tree} {s : Finset Nat}
    {x y : Nat} (hrep : Represents t s) (hy : y ∈ s) (hyx : y ≠ x) :
    maximum (delete x t) ≠ none := by
  intro hnone
  have hall : forall z, z ∈ s -> z = x :=
    (delete_maximum_none_iff (t := t) (s := s) (x := x) hrep).1 hnone
  exact hyx (hall y hy)

/-- A returned successor after deletion is the least remaining old key greater than the query. -/
theorem delete_successor_correct {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hsucc : successor q (delete x t) = some y) :
    y ≠ x ∧ y ∈ s ∧ q < y ∧
      forall z, z ∈ s -> z ≠ x -> q < z -> y <= z := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  have hsucc' := successor_correct
    (t := delete x t) (s := s.erase x) (x := q) (y := y) hdelete hsucc
  have hmem : y ≠ x ∧ y ∈ s := by
    simpa [Finset.mem_erase] using hsucc'.1
  refine ⟨hmem.1, hmem.2, hsucc'.2.1, ?_⟩
  intro z hz hzx hqz
  exact hsucc'.2.2 z (by simp [Finset.mem_erase, hzx, hz]) hqz

/-- A returned successor after deletion is a remaining old key. -/
theorem delete_successor_mem {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hsucc : successor q (delete x t) = some y) :
    y ≠ x ∧ y ∈ s := by
  have h := delete_successor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hsucc
  exact ⟨h.1, h.2.1⟩

/-- A returned successor after deletion is greater than the query. -/
theorem delete_successor_gt {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hsucc : successor q (delete x t) = some y) :
    q < y := by
  exact (delete_successor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hsucc).2.2.1

/-- A returned successor after deletion is no larger than any remaining greater key. -/
theorem delete_successor_le {t : Tree} {s : Finset Nat} {x q y z : Nat}
    (hrep : Represents t s) (hsucc : successor q (delete x t) = some y)
    (hz : z ∈ s) (hzx : z ≠ x) (hqz : q < z) :
    y <= z := by
  exact (delete_successor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hsucc).2.2.2 z hz hzx hqz

/-- A returned successor after deletion lies inside the represented universe. -/
theorem delete_successor_lt_univ {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hsucc : successor q (delete x t) = some y) :
    y < t.univSize := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  exact successor_lt_univ
    (t := delete x t) (s := s.erase x) (x := q) (y := y) hdelete hsucc

/-- No successor after deletion means no remaining old key is greater than the query. -/
theorem delete_successor_none_iff {t : Tree} {s : Finset Nat} {x q : Nat}
    (hrep : Represents t s) :
    successor q (delete x t) = none <->
      forall y, y ∈ s -> y ≠ x -> ¬ q < y := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  rw [successor_none_iff (t := delete x t) (s := s.erase x)
    (x := q) hdelete]
  constructor
  · intro hnone y hy hyx hqy
    exact hnone y (by simp [Finset.mem_erase, hyx, hy]) hqy
  · intro hnone y hyerase hqy
    have hy : y ≠ x ∧ y ∈ s := by
      simpa [Finset.mem_erase] using hyerase
    exact hnone y hy.2 hy.1 hqy

/-- If no remaining old key is greater than the query after deletion, no successor is returned. -/
theorem delete_successor_none_of_no_gt {t : Tree} {s : Finset Nat} {x q : Nat}
    (hrep : Represents t s)
    (hnone : forall y, y ∈ s -> y ≠ x -> ¬ q < y) :
    successor q (delete x t) = none := by
  exact (delete_successor_none_iff
    (t := t) (s := s) (x := x) (q := q) hrep).2 hnone

/-- If no old key is greater than the query, deletion returns no successor. -/
theorem delete_successor_none_of_old_no_gt {t : Tree} {s : Finset Nat}
    {x q : Nat} (hrep : Represents t s)
    (hnone : forall y, y ∈ s -> ¬ q < y) :
    successor q (delete x t) = none := by
  exact delete_successor_none_of_no_gt
    (t := t) (s := s) (x := x) (q := q) hrep
    (by
      intro y hy _hyx
      exact hnone y hy)

/-- If a remaining old key is greater than the query, successor after deletion exists. -/
theorem delete_successor_ne_none_of_remaining_gt {t : Tree} {s : Finset Nat}
    {x q y : Nat} (hrep : Represents t s) (hy : y ∈ s)
    (hyx : y ≠ x) (hqy : q < y) :
    successor q (delete x t) ≠ none := by
  intro hnone
  have hnoGt : forall z, z ∈ s -> z ≠ x -> ¬ q < z :=
    (delete_successor_none_iff
      (t := t) (s := s) (x := x) (q := q) hrep).1 hnone
  exact (hnoGt y hy hyx) hqy

/-- A returned predecessor after deletion is the greatest remaining old key less than the query. -/
theorem delete_predecessor_correct {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hpred : predecessor q (delete x t) = some y) :
    y ≠ x ∧ y ∈ s ∧ y < q ∧
      forall z, z ∈ s -> z ≠ x -> z < q -> z <= y := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  have hpred' := predecessor_correct
    (t := delete x t) (s := s.erase x) (x := q) (y := y) hdelete hpred
  have hmem : y ≠ x ∧ y ∈ s := by
    simpa [Finset.mem_erase] using hpred'.1
  refine ⟨hmem.1, hmem.2, hpred'.2.1, ?_⟩
  intro z hz hzx hzq
  exact hpred'.2.2 z (by simp [Finset.mem_erase, hzx, hz]) hzq

/-- A returned predecessor after deletion is a remaining old key. -/
theorem delete_predecessor_mem {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hpred : predecessor q (delete x t) = some y) :
    y ≠ x ∧ y ∈ s := by
  have h := delete_predecessor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hpred
  exact ⟨h.1, h.2.1⟩

/-- A returned predecessor after deletion is less than the query. -/
theorem delete_predecessor_lt {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hpred : predecessor q (delete x t) = some y) :
    y < q := by
  exact (delete_predecessor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hpred).2.2.1

/-- Any remaining old key less than the query is no larger than a returned predecessor. -/
theorem delete_le_predecessor {t : Tree} {s : Finset Nat} {x q y z : Nat}
    (hrep : Represents t s) (hpred : predecessor q (delete x t) = some y)
    (hz : z ∈ s) (hzx : z ≠ x) (hzq : z < q) :
    z <= y := by
  exact (delete_predecessor_correct
    (t := t) (s := s) (x := x) (q := q) (y := y) hrep hpred).2.2.2 z hz hzx hzq

/-- A returned predecessor after deletion lies inside the represented universe. -/
theorem delete_predecessor_lt_univ {t : Tree} {s : Finset Nat} {x q y : Nat}
    (hrep : Represents t s) (hpred : predecessor q (delete x t) = some y) :
    y < t.univSize := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  exact predecessor_lt_univ
    (t := delete x t) (s := s.erase x) (x := q) (y := y) hdelete hpred

/-- No predecessor after deletion means no remaining old key is smaller than the query. -/
theorem delete_predecessor_none_iff {t : Tree} {s : Finset Nat} {x q : Nat}
    (hrep : Represents t s) :
    predecessor q (delete x t) = none <->
      forall y, y ∈ s -> y ≠ x -> ¬ y < q := by
  have hdelete : Represents (delete x t) (s.erase x) :=
    delete_correct (t := t) (s := s) (x := x) hrep
  rw [predecessor_none_iff (t := delete x t) (s := s.erase x)
    (x := q) hdelete]
  constructor
  · intro hnone y hy hyx hyq
    exact hnone y (by simp [Finset.mem_erase, hyx, hy]) hyq
  · intro hnone y hyerase hyq
    have hy : y ≠ x ∧ y ∈ s := by
      simpa [Finset.mem_erase] using hyerase
    exact hnone y hy.2 hy.1 hyq

/-- If no remaining old key is smaller than the query after deletion, no predecessor is returned. -/
theorem delete_predecessor_none_of_no_lt {t : Tree} {s : Finset Nat} {x q : Nat}
    (hrep : Represents t s)
    (hnone : forall y, y ∈ s -> y ≠ x -> ¬ y < q) :
    predecessor q (delete x t) = none := by
  exact (delete_predecessor_none_iff
    (t := t) (s := s) (x := x) (q := q) hrep).2 hnone

/-- If no old key is smaller than the query, deletion returns no predecessor. -/
theorem delete_predecessor_none_of_old_no_lt {t : Tree} {s : Finset Nat}
    {x q : Nat} (hrep : Represents t s)
    (hnone : forall y, y ∈ s -> ¬ y < q) :
    predecessor q (delete x t) = none := by
  exact delete_predecessor_none_of_no_lt
    (t := t) (s := s) (x := x) (q := q) hrep
    (by
      intro y hy _hyx
      exact hnone y hy)

/-- If a remaining old key is smaller than the query, predecessor after deletion exists. -/
theorem delete_predecessor_ne_none_of_remaining_lt {t : Tree} {s : Finset Nat}
    {x q y : Nat} (hrep : Represents t s) (hy : y ∈ s)
    (hyx : y ≠ x) (hyq : y < q) :
    predecessor q (delete x t) ≠ none := by
  intro hnone
  have hnoLt : forall z, z ∈ s -> z ≠ x -> ¬ z < q :=
    (delete_predecessor_none_iff
      (t := t) (s := s) (x := x) (q := q) hrep).1 hnone
  exact (hnoLt y hy hyx) hyq

/-- First-pass operation-depth recurrence over a tower exponent. -/
def operationDepth (k : Nat) : Nat :=
  k + 1

/-- The first-pass operation-depth recurrence starts with one base step. -/
theorem operationDepth_zero :
    operationDepth 0 = 1 := by
  rfl

/-- The first-pass operation-depth recurrence increases by one per exponent level. -/
theorem operationDepth_succ (k : Nat) :
    operationDepth (k + 1) = operationDepth k + 1 := by
  rfl

/-- The first-pass recurrence-depth wrapper is linear in {lit}`k`. -/
theorem operationDepth_linear (k : Nat) :
    operationDepth k <= k + 1 := by
  rfl

/-- The first-pass operation depth is monotone in the exponent level. -/
theorem operationDepth_monotone {a b : Nat} (hab : a <= b) :
    operationDepth a <= operationDepth b := by
  unfold operationDepth
  omega

/-- The first-pass operation depth is strictly monotone in the exponent level. -/
theorem operationDepth_strict_mono {a b : Nat} (hab : a < b) :
    operationDepth a < operationDepth b := by
  unfold operationDepth
  omega

end VEB
end Chapter20
end CLRS
