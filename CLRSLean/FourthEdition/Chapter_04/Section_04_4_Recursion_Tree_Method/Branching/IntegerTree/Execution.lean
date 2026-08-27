import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree.Model

/-!
# Building integer branching trees

A specification contains the termination proof for every rounded child.  The
recurrence equation is stated independently, then strong induction identifies
its solution with the cost of the generated finite tree.
-/

namespace CLRS
namespace Chapter04

open Finset
open scoped BigOperators

/-- Data needed to expand a natural-size recurrence into a finite tree. -/
structure IntegerBranchingSpec (Branch : Type) where
  cutoff : Nat
  childSize : Branch → Nat → Nat
  localCost : Nat → Real
  baseCost : Nat → Real
  decreases : ∀ branch n, cutoff < n → childSize branch n < n

namespace IntegerBranchingSpec

variable {Branch : Type}

/-- The recurrence semantics, stated without referring to the generated tree. -/
structure Satisfies [Fintype Branch] (spec : IntegerBranchingSpec Branch)
    (T : Nat → Real) : Prop where
  base : ∀ n, n ≤ spec.cutoff → T n = spec.baseCost n
  step : ∀ n, spec.cutoff < n →
    T n = spec.localCost n + ∑ branch, T (spec.childSize branch n)

/-- Executably expand all children until their independently certified cutoff. -/
def build (spec : IntegerBranchingSpec Branch) (n : Nat) :
    IntegerBranchingTree Branch :=
  if _h : n ≤ spec.cutoff then
    .leaf n (spec.baseCost n)
  else
    .node n (spec.localCost n) (fun branch => spec.build (spec.childSize branch n))
termination_by n
decreasing_by
  exact spec.decreases _ _ (Nat.lt_of_not_ge _h)

@[simp] theorem build_of_le (spec : IntegerBranchingSpec Branch) (n : Nat)
    (h : n ≤ spec.cutoff) :
    spec.build n = .leaf n (spec.baseCost n) := by
  rw [build]
  simp [h]

@[simp] theorem build_of_lt (spec : IntegerBranchingSpec Branch) (n : Nat)
    (h : spec.cutoff < n) :
    spec.build n = .node n (spec.localCost n)
      (fun branch => spec.build (spec.childSize branch n)) := by
  rw [build]
  simp [Nat.not_le_of_gt h]

/-- Building preserves the requested root subproblem size. -/
@[simp] theorem rootSize_build (spec : IntegerBranchingSpec Branch) (n : Nat) :
    IntegerBranchingTree.rootSize (spec.build n) = n := by
  by_cases h : n ≤ spec.cutoff
  · simp [build_of_le spec n h]
  · simp [build_of_lt spec n (Nat.lt_of_not_ge h)]

/-- Predicate saying that every leaf size satisfies a given property. -/
def EveryLeafSize (P : Nat → Prop) : IntegerBranchingTree Branch → Prop
  | .leaf size _ => P size
  | .node _ _ children => ∀ branch, EveryLeafSize P (children branch)

/-- Predicate saying that every internal-node size satisfies a property. -/
def EveryInternalSize (P : Nat → Prop) : IntegerBranchingTree Branch → Prop
  | .leaf _ _ => True
  | .node size _ children => P size ∧ ∀ branch, EveryInternalSize P (children branch)

/-- Every generated leaf is genuinely in the base-case range. -/
theorem build_everyLeaf_le (spec : IntegerBranchingSpec Branch) (n : Nat) :
    EveryLeafSize (fun size => size ≤ spec.cutoff) (spec.build n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hbase : n ≤ spec.cutoff
      · simp [EveryLeafSize, hbase]
      · have hrec : spec.cutoff < n := Nat.lt_of_not_ge hbase
        rw [build_of_lt spec n hrec]
        simp only [EveryLeafSize]
        intro branch
        exact ih (spec.childSize branch n) (spec.decreases branch n hrec)

/-- Every generated internal node is genuinely above the cutoff. -/
theorem build_everyInternal_gt (spec : IntegerBranchingSpec Branch) (n : Nat) :
    EveryInternalSize (fun size => spec.cutoff < size) (spec.build n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hbase : n ≤ spec.cutoff
      · simp [build_of_le spec n hbase, EveryInternalSize]
      · have hrec : spec.cutoff < n := Nat.lt_of_not_ge hbase
        rw [build_of_lt spec n hrec]
        simp only [EveryInternalSize]
        refine ⟨hrec, fun branch => ?_⟩
        exact ih (spec.childSize branch n) (spec.decreases branch n hrec)

/--
Exact recurrence-tree semantics.  This is not true by definition: {lit}`T` is
specified only by its base and recursive equations, independently of {name}`build`.
-/
theorem build_totalCost_eq [Fintype Branch] (spec : IntegerBranchingSpec Branch)
    (T : Nat → Real) (hT : spec.Satisfies T) (n : Nat) :
    IntegerBranchingTree.totalCost (spec.build n) = T n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hbase : n ≤ spec.cutoff
      · rw [build_of_le spec n hbase]
        simp [hT.base n hbase]
      · have hrec : spec.cutoff < n := Nat.lt_of_not_ge hbase
        rw [build_of_lt spec n hrec]
        simp only [IntegerBranchingTree.totalCost_node]
        have hchildren : ∀ branch,
            IntegerBranchingTree.totalCost
                (spec.build (spec.childSize branch n)) =
              T (spec.childSize branch n) := fun branch =>
          ih (spec.childSize branch n) (spec.decreases branch n hrec)
        simp_rw [hchildren]
        exact (hT.step n hrec).symm

end IntegerBranchingSpec

end Chapter04
end CLRS
