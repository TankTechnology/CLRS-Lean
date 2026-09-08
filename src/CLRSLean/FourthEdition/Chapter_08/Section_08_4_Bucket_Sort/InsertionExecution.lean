import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Instrumented insertion sorting within a bucket

The same recursive execution constructs the output and records controller work.
One unit pays for each rank comparison and each newly constructed list node;
each outer sorting iteration pays one additional controller unit. Existing
suffixes may be shared. Rank evaluation and list allocation use unit costs;
this is not a bit-level or allocator runtime model.

The public results identify the value with generic insertion sort and prove
permutation, ordering, and the quadratic bound needed by bucket sort.
-/

namespace CLRS.Chapter08.BucketExecution

universe u
variable {α : Type u}

/-- One list result and the work accumulated while constructing that result. -/
structure InsertionExecution (α : Type u) where
  value : List α
  work : Nat
  deriving Repr, DecidableEq

/-- Insert one value into a sorted bucket. The empty branch constructs one
node; the early-stop branch compares ranks and constructs two nodes; a recursive
branch compares ranks and constructs one node after its recursive call. -/
def insertWithCost (rank : α → Nat) (x : α) : List α → InsertionExecution α
  | [] => ⟨[x], 1⟩
  | y :: ys =>
      if rank x ≤ rank y then
        ⟨x :: y :: ys, 3⟩
      else
        let rest := insertWithCost rank x ys
        ⟨y :: rest.value, rest.work + 2⟩

/-- Sort a bucket by recursively sorting its tail and inserting its head.
Each nonempty outer iteration contributes one controller unit in addition to
the insertion work. -/
def insertionWithCost (rank : α → Nat) : List α → InsertionExecution α
  | [] => ⟨[], 0⟩
  | x :: xs =>
      let tail := insertionWithCost rank xs
      let inserted := insertWithCost rank x tail.value
      ⟨inserted.value, tail.work + inserted.work + 1⟩

/-- Erasing insertion work gives the verified generic ordered insertion. -/
theorem insertWithCost_value (rank : α → Nat) (x : α) (xs : List α) :
    (insertWithCost rank x xs).value =
      List.orderedInsert (fun x y => rank x ≤ rank y) x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      simp only [insertWithCost, List.orderedInsert_cons]
      split <;> simp_all

/-- Erasing the accumulated work gives generic insertion sort. -/
theorem insertionWithCost_value (rank : α → Nat) (xs : List α) :
    (insertionWithCost rank xs).value =
      List.insertionSort (fun x y => rank x ≤ rank y) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [insertionWithCost, List.insertionSort_cons, insertWithCost_value, ih]

/-- The executed sorter preserves every payload, including duplicate ranks. -/
theorem insertionWithCost_perm (rank : α → Nat) (xs : List α) :
    (insertionWithCost rank xs).value.Perm xs := by
  rw [insertionWithCost_value]
  exact List.perm_insertionSort _ _

/-- The execution returns a list ordered by its final rank. -/
theorem insertionWithCost_pairwise (rank : α → Nat) (xs : List α) :
    (insertionWithCost rank xs).value.Pairwise (fun x y => rank x ≤ rank y) := by
  rw [insertionWithCost_value]
  exact List.pairwise_insertionSort _ _

/-- The executed output has the same length as the input bucket. -/
theorem insertionWithCost_length (rank : α → Nat) (xs : List α) :
    (insertionWithCost rank xs).value.length = xs.length :=
  (insertionWithCost_perm rank xs).length_eq

/-- Insertion visits at most the existing bucket length, constructing at most
one replacement node per recursive visit and its new final node. -/
theorem insertWithCost_work_le (rank : α → Nat) (x : α) (xs : List α) :
    (insertWithCost rank x xs).work ≤ 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [insertWithCost]
  | cons y ys ih =>
      simp only [insertWithCost, List.length_cons]
      split <;> simp_all
      omega

/-- The actual insertion execution uses at most {lit}`n(n+1)` work. -/
theorem insertionWithCost_work_le (rank : α → Nat) (xs : List α) :
    (insertionWithCost rank xs).work ≤ xs.length * (xs.length + 1) := by
  induction xs with
  | nil => simp [insertionWithCost]
  | cons x xs ih =>
      have hi := insertWithCost_work_le rank x (insertionWithCost rank xs).value
      rw [insertionWithCost_length] at hi
      simp only [insertionWithCost, List.length_cons]
      nlinarith

/-- A uniform quadratic bound, including an empty bucket with zero work. -/
theorem insertionWithCost_work_le_sq (rank : α → Nat) (xs : List α) :
    (insertionWithCost rank xs).work ≤ 2 * xs.length ^ 2 := by
  have h := insertionWithCost_work_le rank xs
  have hn : xs.length ≤ xs.length ^ 2 := by
    cases xs.length with
    | zero => norm_num
    | succ n => nlinarith
  nlinarith

end CLRS.Chapter08.BucketExecution
