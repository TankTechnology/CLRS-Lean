import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ComposedPreservation

/-!
# Root-normalized B-tree deletion

Raw {lit}`composedDelete` may return an empty root with one child, so it
does not preserve the root-specialized {lit}`WellFormed` predicate directly.
The public root operation {lit}`composedDeleteRoot` contracts that one
transient level.  This module exposes its key-subset, height, and structural
postconditions.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/--
Root-normalized deletion represents only keys from the input tree.
-/
theorem composedDeleteRoot_keys_subset
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    KeysSubset (composedDeleteRoot t x tr) tr := by
  have hraw :=
    (composedDelete_rootResult t x ht hwf).1
  intro k hk
  apply hraw k
  simpa [composedDeleteRoot, keysOf_normalizeRoot] using hk

/--
Root normalization either preserves the raw height or contracts exactly one
root level.
-/
theorem composedDeleteRoot_height
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    heightOf (composedDeleteRoot t x tr) = heightOf tr ∨
      heightOf (composedDeleteRoot t x tr) + 1 = heightOf tr := by
  have hraw :=
    (composedDelete_rootResult t x ht hwf).2.2
  have hnormalize :=
    heightOf_normalizeRoot (composedDelete t x tr)
  change
    heightOf (normalizeRoot (composedDelete t x tr)) = heightOf tr ∨
      heightOf (normalizeRoot (composedDelete t x tr)) + 1 =
        heightOf tr
  rcases hnormalize with hsame | hcontract
  · exact Or.inl (hsame.trans hraw)
  · exact Or.inr (hcontract.trans hraw)

/--
The root-normalized CLRS deletion operation preserves the complete
well-formedness invariant.
-/
theorem composedDeleteRoot_wellFormed
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    WellFormed t (composedDeleteRoot t x tr) := by
  have hraw :=
    (composedDelete_rootResult t x ht hwf).2.1
  simpa [composedDeleteRoot] using
    (normalizeRoot_wellFormed ht hraw)

end BTree
end Chapter18
end CLRS
