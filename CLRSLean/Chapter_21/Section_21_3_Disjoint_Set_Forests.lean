import Batteries.Data.UnionFind
import CLRSLean.Chapter_21.Section_21_1_Disjoint_Set_Operations

/-!
# CLRS Section 21.3 - Disjoint-set forests

This section refines the abstract partition semantics from Section 21.1 to the
executable union-by-rank, path-compressing implementation supplied by
{lit}`Batteries.UnionFind`.

Main results:

- Theorem {lit}`Forest.singletonForest_equiv_iff`: initialization creates only
  singleton classes.
- Theorems {lit}`Forest.find_preserves_sameSet` and
  {lit}`Forest.find_returns_representative`: path compression preserves the
  partition and returns its representative.
- Theorem {lit}`Forest.union_sameSet_iff`: executable union implements the
  exact CLRS merge formula.
- Theorems {lit}`Forest.checkEquiv_correct` and
  {lit}`Forest.checkEquiv_preserves_sameSet`: the executable Boolean query is
  correct and its path compression does not change the partition.
-/

namespace CLRS
namespace Chapter21
namespace Forest

open Batteries

abbrev State := UnionFind

/-- The abstract partition represented by an executable forest. -/
def partition (s : State) : Partition Nat where
  sameSet := s.Equiv
  refl := fun _ => UnionFind.Equiv.rfl
  symm := fun h => UnionFind.Equiv.symm h
  trans := fun hab hbc => UnionFind.Equiv.trans hab hbc

/-- Build a forest containing {lit}`n` singleton nodes. -/
def singletonForest : Nat → State
  | 0 => UnionFind.empty
  | n + 1 => (singletonForest n).push

@[simp]
theorem singletonForest_zero :
    singletonForest 0 = UnionFind.empty :=
  rfl

@[simp]
theorem singletonForest_succ (n : Nat) :
    singletonForest (n + 1) = (singletonForest n).push :=
  rfl

@[simp]
theorem singletonForest_size (n : Nat) :
    (singletonForest n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [singletonForest_succ]
      have hpush :
          (singletonForest n).push.size = (singletonForest n).size + 1 := by
        simp [UnionFind.push, UnionFind.size]
      rw [hpush, ih]

/-- Initially every natural-number node is equivalent only to itself. -/
@[simp]
theorem singletonForest_equiv_iff (n a b : Nat) :
    (singletonForest n).Equiv a b ↔ a = b := by
  induction n with
  | zero => simp [singletonForest]
  | succ n ih => simp [singletonForest, ih]

/-- The executable singleton forest refines the discrete abstract partition. -/
theorem singletonForest_refines_discrete (n a b : Nat) :
    (partition (singletonForest n)).sameSet a b ↔
      (Partition.discrete : Partition Nat).sameSet a b := by
  exact singletonForest_equiv_iff n a b

/-- Path compression does not change any represented equivalence class. -/
theorem find_preserves_sameSet (s : State) (x : Fin s.size) (a b : Nat) :
    (partition (s.find x).1).sameSet a b ↔
      (partition s).sameSet a b := by
  exact UnionFind.equiv_find

/-- The value returned by {lit}`find` is the original canonical root. -/
theorem find_returns_root (s : State) (x : Fin s.size) :
    (s.find x).2.1.1 = s.rootD x :=
  UnionFind.find_root_2 s x

/-- The representative returned by {lit}`find` belongs to the queried class. -/
theorem find_returns_representative (s : State) (x : Fin s.size) :
    (partition s).sameSet x (s.find x).2.1.1 := by
  change s.Equiv x (s.find x).2.1.1
  rw [find_returns_root]
  exact UnionFind.Equiv.symm UnionFind.equiv_rootD

/-- Path compression makes the queried node point directly to its root. -/
theorem find_compresses_path (s : State) (x : Fin s.size) :
    (s.find x).1.parent x = s.rootD x :=
  UnionFind.find_parent_1 s x

/-- The executable union operation has the exact abstract merge semantics. -/
theorem union_sameSet_iff (s : State) (x y : Fin s.size) (a b : Nat) :
    (partition (s.union x y)).sameSet a b ↔
      (partition s).sameSet a b ∨
        ((partition s).sameSet a x ∧ (partition s).sameSet y b) ∨
        ((partition s).sameSet a y ∧ (partition s).sameSet x b) := by
  exact UnionFind.equiv_union

/-- Executable union refines the Section 21.1 partition merge. -/
theorem union_refines_merge (s : State) (x y : Fin s.size) (a b : Nat) :
    (partition (s.union x y)).sameSet a b ↔
      ((partition s).merge x y).sameSet a b := by
  rw [union_sameSet_iff, Partition.merge_sameSet_iff]

/-- Union preserves the number of allocated nodes. -/
@[simp]
theorem union_size (s : State) (x y : Fin s.size) :
    (s.union x y).size = s.size := by
  simp [UnionFind.union, UnionFind.link, UnionFind.size]

/-- The Boolean result of {lit}`checkEquiv` exactly decides class equality. -/
@[simp]
private theorem coe_subst_fin {m n : Nat} (h : m = n) (y : Fin n) :
    ((h ▸ y : Fin m) : Nat) = y := by
  cases h
  rfl

theorem checkEquiv_correct (s : State) (x y : Fin s.size) :
    (s.checkEquiv x y).2 = true ↔ (partition s).sameSet x y := by
  simp [UnionFind.checkEquiv, partition, UnionFind.Equiv]

/-- The path compression performed by {lit}`checkEquiv` preserves all classes. -/
theorem checkEquiv_preserves_sameSet (s : State) (x y : Fin s.size)
    (a b : Nat) :
    (partition (s.checkEquiv x y).1).sameSet a b ↔
      (partition s).sameSet a b := by
  simp [UnionFind.checkEquiv, partition, UnionFind.equiv_find]

/-- The Boolean cycle test rejects exactly pairs already in one class. -/
theorem checkEquiv_eq_false_iff (s : State) (x y : Fin s.size) :
    (s.checkEquiv x y).2 = false ↔
      ¬(partition s).sameSet x y := by
  rw [Bool.eq_false_iff]
  exact not_congr (checkEquiv_correct s x y)

end Forest
end Chapter21
end CLRS
