import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Exact

/-!
# Root-normalized B-tree deletion

Raw {lit}`composedDelete` may return an empty root with one child, so it
does not preserve the root-specialized {lit}`WellFormed` predicate directly.
The public root operation {lit}`composedDeleteRoot` contracts that one
transient level.  This module combines its key-subset, height, and structural
postconditions with exact erase-one key-bag semantics.  Under global key
uniqueness, it also proves deleted-key absence and compatibility with the
specification-level deletion and membership search.
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

/--
Root normalization preserves the erase-one key-bag semantics of raw deletion.
-/
theorem composedDeleteRoot_keyBag
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    keyBag (composedDeleteRoot t x tr) =
      (keyBag tr).erase x := by
  have hraw :=
    composedDelete_keyBag t x ht hwf.nodeWF
  simpa only [composedDeleteRoot, keyBag, keysOf_normalizeRoot] using hraw

/--
Root-normalized deletion preserves membership of every key distinct from the
requested key, without requiring key uniqueness.
-/
theorem composedDeleteRoot_mem_iff_of_ne
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) (hyx : y ≠ x) :
    mem y (composedDeleteRoot t x tr) ↔ mem y tr := by
  have hraw :=
    composedDelete_mem_iff_of_ne t x y ht hwf.nodeWF hyx
  simpa only [composedDeleteRoot, mem, keysOf_normalizeRoot] using hraw

/--
When represented keys are unique, root-normalized deletion leaves no
occurrence of the requested key.
-/
theorem composedDeleteRoot_not_mem
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    ¬ mem x (composedDeleteRoot t x tr) := by
  have hbag :=
    composedDeleteRoot_keyBag t x ht hwf.1
  have hnodup : (keyBag tr).Nodup := by
    simpa only [keyBag] using
      (Multiset.coe_nodup.mpr hwf.2)
  intro hx
  have hxBag :
      x ∈ keyBag (composedDeleteRoot t x tr) := by
    simpa only [mem, keyBag, Multiset.mem_coe] using hx
  rw [hbag] at hxBag
  exact hnodup.notMem_erase hxBag

/--
Under key uniqueness, membership after root-normalized deletion is exactly
old membership restricted to keys different from the requested key.
-/
theorem composedDeleteRoot_mem_iff
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    mem y (composedDeleteRoot t x tr) ↔
      y ≠ x ∧ mem y tr := by
  have hbag :=
    composedDeleteRoot_keyBag t x ht hwf.1
  have hnodup : (keyBag tr).Nodup := by
    simpa only [keyBag] using
      (Multiset.coe_nodup.mpr hwf.2)
  have hmem :=
    Multiset.Nodup.mem_erase_iff
      (a := y) (b := x) hnodup
  rw [← hbag] at hmem
  simpa only [mem, keyBag, Multiset.mem_coe] using hmem

/--
Root-normalized deletion preserves both structural well-formedness and global
key uniqueness.
-/
theorem composedDeleteRoot_wellFormedUnique
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    WellFormedUnique t (composedDeleteRoot t x tr) := by
  refine
    ⟨composedDeleteRoot_wellFormed t x ht hwf.1, ?_⟩
  have hbag :=
    composedDeleteRoot_keyBag t x ht hwf.1
  have hbefore : (keyBag tr).Nodup := by
    simpa only [keyBag] using
      (Multiset.coe_nodup.mpr hwf.2)
  have hafter :
      (keyBag (composedDeleteRoot t x tr)).Nodup := by
    rw [hbag]
    exact hbefore.erase x
  exact Multiset.coe_nodup.mp (by
    simpa only [keyBag] using hafter)

/--
On well-formed trees with unique keys, executable root deletion and
specification deletion have identical membership.
-/
theorem composedDeleteRoot_mem_iff_delete
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    mem y (composedDeleteRoot t x tr) ↔
      mem y (delete x tr) := by
  exact
    (composedDeleteRoot_mem_iff t x y ht hwf).trans
      (delete_mem_iff_ne x y tr).symm

/--
On well-formed trees with unique keys, the membership-oracle searches after
executable root deletion and specification deletion agree.
-/
theorem composedDeleteRoot_search_eq_delete
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormedUnique t tr) :
    search y (composedDeleteRoot t x tr) =
      search y (delete x tr) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [search_true_iff] using
    composedDeleteRoot_mem_iff_delete t x y ht hwf

/--
Root-normalized deletion simultaneously has exact erase-one semantics,
preserves well-formedness, and preserves or contracts height by one level.
-/
theorem composedDeleteRoot_correct
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    keyBag (composedDeleteRoot t x tr) =
        (keyBag tr).erase x ∧
      WellFormed t (composedDeleteRoot t x tr) ∧
      (heightOf (composedDeleteRoot t x tr) = heightOf tr ∨
        heightOf (composedDeleteRoot t x tr) + 1 = heightOf tr) := by
  exact
    ⟨composedDeleteRoot_keyBag t x ht hwf,
      composedDeleteRoot_wellFormed t x ht hwf,
      composedDeleteRoot_height t x ht hwf⟩

end BTree
end Chapter18
end CLRS
