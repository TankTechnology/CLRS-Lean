import Mathlib

/-!
# Finite indexed SUBSET-SUM instances

Items carry stable labels so equal numerical values still represent distinct
copies, as required by the textbook reduction.  A certificate is a finite
subset of those labels whose values add to the target.
-/

namespace CLRS.Chapter34

/-- Uniform labels used by the 3-CNF reduction. -/
inductive SubsetSumItem
  | choice (index : Nat) (truth : Bool)
  | slack (clause : Nat) (slot : Nat)
  deriving DecidableEq, Repr

/-- A finite family of natural numbers with a target sum. -/
structure SubsetSumInstance where
  items : Finset SubsetSumItem
  value : SubsetSumItem → Nat
  target : Nat

namespace SubsetSumInstance

/-- Some subfamily of the indexed numbers sums exactly to the target. -/
def HasSubsetSum (I : SubsetSumInstance) : Prop :=
  ∃ chosen : Finset SubsetSumItem,
    chosen ⊆ I.items ∧
      ∑ item ∈ chosen, I.value item = I.target

instance decidableHasSubsetSum (I : SubsetSumInstance) :
    Decidable I.HasSubsetSum := by
  unfold HasSubsetSum
  infer_instance

end SubsetSumInstance
end CLRS.Chapter34
