import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.KeyMultiset
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.MergeReassembly
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.RotationReassembly

/-!
# Exact parent reassembly for B-tree deletion

This module lifts the exact key-multiset equations for primitive deletion
operations through the parent-reassembly steps used by composed deletion.
The proofs need only local index witnesses, recursive exactness, and routing
facts; structural preservation is supplied separately by the reassembly
packet modules.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/--
Replacing a witnessed child balances the new parent and old child against the
old parent and new child.
-/
theorem replaceChild_keyBag_balance
    {i : Nat} {ks : List Nat} {cs : List BTree}
    {old new : BTree}
    (hold : cs[i]? = some old) :
    keyBag (node ks (cs.set i new)) + keyBag old =
      keyBag (node ks cs) + keyBag new := by
  have hchildren :=
    flatMap_set_bag_balance (new := new) keysOf hold
  simp only [keyBag, keysOf, ← Multiset.coe_add] at hchildren ⊢
  simpa only [add_assoc] using
    congrArg (fun bag => (↑ks : Multiset Nat) + bag) hchildren

/--
Replacing the routed recursive child lifts deletion of one key occurrence to
the enclosing parent.
-/
theorem replaceChild_keyBag_erase
    {i x : Nat} {ks : List Nat} {cs : List BTree}
    {old new : BTree}
    (hold : cs[i]? = some old)
    (hroute : x ∈ keysOf (node ks cs) → x ∈ keysOf old)
    (hrec : keyBag new = (keyBag old).erase x) :
    keyBag (node ks (cs.set i new)) =
      (keyBag (node ks cs)).erase x := by
  apply keyBag_erase_of_balance (replaceChild_keyBag_balance hold) hrec
  simpa only [keyBag, Multiset.mem_coe] using hroute

/--
Changing one separator and one witnessed child gives a joint key-bag balance.
-/
theorem replaceSeparatorChild_keyBag_balance
    {separatorIndex childIndex oldSep newSep : Nat}
    {ks : List Nat} {cs : List BTree} {old new : BTree}
    (hsep : ks[separatorIndex]? = some oldSep)
    (hold : cs[childIndex]? = some old) :
    keyBag
          (node (ks.set separatorIndex newSep)
            (cs.set childIndex new)) +
        {oldSep} + keyBag old =
      keyBag (node ks cs) + {newSep} + keyBag new := by
  have hkeys :=
    list_set_bag_balance (new := newSep) hsep
  have hchildren :=
    flatMap_set_bag_balance (new := new) keysOf hold
  simp only [keyBag, keysOf, ← Multiset.coe_add] at hkeys hchildren ⊢
  calc
    (↑(ks.set separatorIndex newSep) : Multiset Nat) +
          ↑((cs.set childIndex new).flatMap keysOf) +
          {oldSep} + ↑(keysOf old) =
        ((↑(ks.set separatorIndex newSep) : Multiset Nat) + {oldSep}) +
          (↑((cs.set childIndex new).flatMap keysOf) + ↑(keysOf old)) := by
            ac_rfl
    _ = ((↑ks : Multiset Nat) + {newSep}) +
          (↑(cs.flatMap keysOf) + ↑(keysOf new)) := by
            rw [hkeys, hchildren]
    _ = (↑ks : Multiset Nat) + ↑(cs.flatMap keysOf) +
          {newSep} + ↑(keysOf new) := by
            ac_rfl

/--
Replacing a separator by its predecessor while recursively deleting that
predecessor removes exactly the old separator from the parent key bag.
-/
theorem replacePredecessor_keyBag_erase
    {t i sep : Nat} {b : Bool}
    {ks : List Nat} {cs : List BTree} {left left' : BTree}
    (ht : 2 ≤ t)
    (hparent : NodeWF t b (node ks cs))
    (hsep : ks[i]? = some sep)
    (hleft : cs[i]? = some left)
    (hrec :
      keyBag left' = (keyBag left).erase (maxKey left)) :
    keyBag
        (node (ks.set i (maxKey left)) (cs.set i left')) =
      (keyBag (node ks cs)).erase sep := by
  have hleftMem : left ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i, hleft⟩
  have hleftWF : NodeWF t false left :=
    hparent.child hleftMem
  have hmaxMemList : maxKey left ∈ keysOf left :=
    maxKey_mem left (hleftWF.nonRoot_allKeysPos ht)
  have hmaxMem : maxKey left ∈ keyBag left := by
    simpa only [keyBag, Multiset.mem_coe] using hmaxMemList
  have hrestore :
      {maxKey left} + keyBag left' = keyBag left := by
    rw [hrec, Multiset.singleton_add]
    exact Multiset.cons_erase hmaxMem
  have hbalance :=
    replaceSeparatorChild_keyBag_balance
      (newSep := maxKey left) (new := left') hsep hleft
  have hframe :
      keyBag
            (node (ks.set i (maxKey left)) (cs.set i left')) +
          {sep} =
        keyBag (node ks cs) := by
    apply add_right_cancel (b := keyBag left)
    calc
      (keyBag
              (node (ks.set i (maxKey left)) (cs.set i left')) +
            {sep}) +
          keyBag left =
        keyBag
              (node (ks.set i (maxKey left)) (cs.set i left')) +
            {sep} + keyBag left := by rfl
      _ = keyBag (node ks cs) + {maxKey left} + keyBag left' :=
        hbalance
      _ = keyBag (node ks cs) +
          ({maxKey left} + keyBag left') := by
            rw [add_assoc]
      _ = keyBag (node ks cs) + keyBag left := by
            rw [hrestore]
  apply keyBag_erase_of_balance
      (old := ({sep} : Multiset Nat)) (new := 0)
  · simpa using hframe
  · simp
  · simp

/--
Splicing a recursive merge result into the parent balances it against the
unmodified merged child.
-/
theorem spliceMerged_keyBag_balance
    {j sep : Nat} {ks : List Nat} {cs : List BTree}
    {left right newMerged : BTree}
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right) :
    let out :=
      node (ks.take j ++ ks.drop (j + 1))
        (cs.take j ++ [newMerged] ++ cs.drop (j + 2))
    keyBag out + keyBag (mergeNodes left sep right) =
      keyBag (node ks cs) + keyBag newMerged := by
  dsimp only
  have hkeys :=
    take_drop_succ_bag_balance hsep
  have hchildren :=
    flatMap_splice_bag_balance
      (new := newMerged) keysOf hleft hright
  have hmerge := mergeNodes_keyBag left sep right
  simp only [keyBag, keysOf, ← Multiset.coe_add] at hkeys hchildren hmerge ⊢
  rw [hmerge]
  calc
    ((↑(ks.take j) : Multiset Nat) + ↑(ks.drop (j + 1))) +
          ↑((cs.take j ++ [newMerged] ++ cs.drop (j + 2)).flatMap keysOf) +
          (keyBag left + {sep} + keyBag right) =
        (((↑(ks.take j) : Multiset Nat) + ↑(ks.drop (j + 1))) + {sep}) +
          (↑((cs.take j ++ [newMerged] ++ cs.drop (j + 2)).flatMap keysOf) +
            ↑(keysOf left) + ↑(keysOf right)) := by
              simp only [keyBag]
              ac_rfl
    _ = (↑ks : Multiset Nat) +
          (↑(cs.flatMap keysOf) + ↑(keysOf newMerged)) := by
            rw [hkeys, hchildren]
    _ = (↑ks : Multiset Nat) + ↑(cs.flatMap keysOf) +
          ↑(keysOf newMerged) := by
            ac_rfl

/--
After a merge, recursively deleting a routed key from the merged child removes
exactly one occurrence from the reassembled parent.
-/
theorem spliceMerged_keyBag_erase
    {j sep x : Nat} {ks : List Nat} {cs : List BTree}
    {left right newMerged : BTree}
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right)
    (hroute :
      x ∈ keysOf (node ks cs) →
        x ∈ keysOf (mergeNodes left sep right))
    (hrec :
      keyBag newMerged =
        (keyBag (mergeNodes left sep right)).erase x) :
    let out :=
      node (ks.take j ++ ks.drop (j + 1))
        (cs.take j ++ [newMerged] ++ cs.drop (j + 2))
    keyBag out = (keyBag (node ks cs)).erase x := by
  dsimp only
  apply keyBag_erase_of_balance
      (spliceMerged_keyBag_balance hsep hleft hright) hrec
  simpa only [keyBag, Multiset.mem_coe] using hroute

/--
Replacing a separator by its successor while recursively deleting that
successor removes exactly the old separator from the parent key bag.
-/
theorem replaceSuccessor_keyBag_erase
    {t i sep : Nat} {b : Bool}
    {ks : List Nat} {cs : List BTree} {right right' : BTree}
    (ht : 2 ≤ t)
    (hparent : NodeWF t b (node ks cs))
    (hsep : ks[i]? = some sep)
    (hright : cs[i + 1]? = some right)
    (hrec :
      keyBag right' = (keyBag right).erase (minKey right)) :
    keyBag
        (node (ks.set i (minKey right))
          (cs.set (i + 1) right')) =
      (keyBag (node ks cs)).erase sep := by
  have hrightMem : right ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i + 1, hright⟩
  have hrightWF : NodeWF t false right :=
    hparent.child hrightMem
  have hminMemList : minKey right ∈ keysOf right :=
    minKey_mem right (hrightWF.nonRoot_allKeysPos ht)
  have hminMem : minKey right ∈ keyBag right := by
    simpa only [keyBag, Multiset.mem_coe] using hminMemList
  have hrestore :
      {minKey right} + keyBag right' = keyBag right := by
    rw [hrec, Multiset.singleton_add]
    exact Multiset.cons_erase hminMem
  have hbalance :=
    replaceSeparatorChild_keyBag_balance
      (separatorIndex := i) (childIndex := i + 1)
      (newSep := minKey right) (new := right') hsep hright
  have hframe :
      keyBag
            (node (ks.set i (minKey right))
              (cs.set (i + 1) right')) +
          {sep} =
        keyBag (node ks cs) := by
    apply add_right_cancel (b := keyBag right)
    calc
      (keyBag
              (node (ks.set i (minKey right))
                (cs.set (i + 1) right')) +
            {sep}) +
          keyBag right =
        keyBag
              (node (ks.set i (minKey right))
                (cs.set (i + 1) right')) +
            {sep} + keyBag right := by rfl
      _ = keyBag (node ks cs) + {minKey right} + keyBag right' :=
        hbalance
      _ = keyBag (node ks cs) +
          ({minKey right} + keyBag right') := by
            rw [add_assoc]
      _ = keyBag (node ks cs) + keyBag right := by
            rw [hrestore]
  apply keyBag_erase_of_balance
      (old := ({sep} : Multiset Nat)) (new := 0)
  · simpa using hframe
  · simp
  · simp

/--
Every key of the original left child remains in the repaired left child after
a right rotation.
-/
theorem mem_rotateRight_left_of_mem_left
    (left : BTree) (sep : Nat) (right : BTree) {x : Nat}
    (hx : x ∈ keysOf left) :
    x ∈ keysOf (rotateRight left sep right).1 := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  cases rKeys <;>
    simp only [rotateRight_nil, rotateRight_cons, keysOf,
      List.mem_append, List.mem_cons,
      List.mem_flatMap] at hx ⊢ <;>
    aesop

/--
Every key of the original right child remains in the repaired right child
after a left rotation.
-/
theorem mem_rotateLeft_right_of_mem_right
    (left : BTree) (sep : Nat) (right : BTree) {x : Nat}
    (hx : x ∈ keysOf right) :
    x ∈ keysOf (rotateLeft left sep right).2.2 := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  cases lKeys <;>
    simp only [rotateLeft_nil, rotateLeft_cons, keysOf,
      List.mem_append, List.mem_cons, List.mem_flatMap] at hx ⊢ <;>
    aesop

private theorem flatMap_set_adjacent_bag_balance
    {α β : Type*} {xs : List α} {j : Nat}
    {left right newLeft newRight : α}
    (f : α → List β)
    (hleft : xs[j]? = some left)
    (hright : xs[j + 1]? = some right) :
    (↑(((xs.set j newLeft).set (j + 1) newRight).flatMap f) :
          Multiset β) +
        ↑(f left) + ↑(f right) =
      (↑(xs.flatMap f) : Multiset β) +
        ↑(f newLeft) + ↑(f newRight) := by
  have hrightAfter :
      (xs.set j newLeft)[j + 1]? = some right := by
    rw [List.getElem?_set_ne (by omega : j ≠ j + 1)]
    exact hright
  have hfirst :=
    flatMap_set_bag_balance (new := newLeft) f hleft
  have hsecond :=
    flatMap_set_bag_balance (new := newRight) f hrightAfter
  calc
    (↑(((xs.set j newLeft).set (j + 1) newRight).flatMap f) :
          Multiset β) +
        ↑(f left) + ↑(f right) =
      ((↑(((xs.set j newLeft).set (j + 1) newRight).flatMap f) :
          Multiset β) + ↑(f right)) + ↑(f left) := by
            ac_rfl
    _ = ((↑((xs.set j newLeft).flatMap f) : Multiset β) +
          ↑(f newRight)) + ↑(f left) := by
            rw [hsecond]
    _ = ((↑((xs.set j newLeft).flatMap f) : Multiset β) +
          ↑(f left)) + ↑(f newRight) := by
            ac_rfl
    _ = ((↑(xs.flatMap f) : Multiset β) + ↑(f newLeft)) +
          ↑(f newRight) := by
            rw [hfirst]

/--
Replacing one separator and both adjacent children gives an atomic key-bag
balance for a rotation.
-/
theorem replaceAdjacent_keyBag_balance
    {j sep newSep : Nat} {ks : List Nat} {cs : List BTree}
    {left right newLeft newRight : BTree}
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right) :
    keyBag
          (node (ks.set j newSep)
            ((cs.set j newLeft).set (j + 1) newRight)) +
        (keyBag left + {sep} + keyBag right) =
      keyBag (node ks cs) +
        (keyBag newLeft + {newSep} + keyBag newRight) := by
  have hkeys :=
    list_set_bag_balance (new := newSep) hsep
  have hchildren :=
    flatMap_set_adjacent_bag_balance
      (newLeft := newLeft) (newRight := newRight)
      keysOf hleft hright
  simp only [keyBag, keysOf, ← Multiset.coe_add] at hkeys hchildren ⊢
  calc
    (↑(ks.set j newSep) : Multiset Nat) +
          ↑(((cs.set j newLeft).set (j + 1) newRight).flatMap keysOf) +
          (↑(keysOf left) + {sep} + ↑(keysOf right)) =
        ((↑(ks.set j newSep) : Multiset Nat) + {sep}) +
          (↑(((cs.set j newLeft).set (j + 1) newRight).flatMap keysOf) +
            ↑(keysOf left) + ↑(keysOf right)) := by
              ac_rfl
    _ = ((↑ks : Multiset Nat) + {newSep}) +
          (↑(cs.flatMap keysOf) +
            ↑(keysOf newLeft) + ↑(keysOf newRight)) := by
              rw [hkeys, hchildren]
    _ = (↑ks : Multiset Nat) + ↑(cs.flatMap keysOf) +
          (↑(keysOf newLeft) + {newSep} + ↑(keysOf newRight)) := by
            ac_rfl

/-- A right rotation preserves the complete parent key bag. -/
theorem rotateRight_parent_keyBag
    {j sep : Nat} {ks : List Nat} {cs : List BTree}
    {left right : BTree}
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right) :
    let repaired := rotateRight left sep right
    keyBag
        (node (ks.set j repaired.2.1)
          ((cs.set j repaired.1).set (j + 1) repaired.2.2)) =
      keyBag (node ks cs) := by
  dsimp only
  have hbalance :=
    replaceAdjacent_keyBag_balance
      (newSep := (rotateRight left sep right).2.1)
      (newLeft := (rotateRight left sep right).1)
      (newRight := (rotateRight left sep right).2.2)
      hsep hleft hright
  have hrotation := rotateRight_keyBag left sep right
  apply add_right_cancel
      (b := keyBag left + {sep} + keyBag right)
  calc
    keyBag
          (node (ks.set j (rotateRight left sep right).2.1)
            ((cs.set j (rotateRight left sep right).1).set
              (j + 1) (rotateRight left sep right).2.2)) +
        (keyBag left + {sep} + keyBag right) =
      keyBag (node ks cs) +
        (keyBag (rotateRight left sep right).1 +
          {(rotateRight left sep right).2.1} +
          keyBag (rotateRight left sep right).2.2) :=
      hbalance
    _ = keyBag (node ks cs) +
        (keyBag left + {sep} + keyBag right) := by
          rw [hrotation]

/-- A left rotation preserves the complete parent key bag. -/
theorem rotateLeft_parent_keyBag
    {j sep : Nat} {ks : List Nat} {cs : List BTree}
    {left right : BTree}
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right) :
    let repaired := rotateLeft left sep right
    keyBag
        (node (ks.set j repaired.2.1)
          ((cs.set j repaired.1).set (j + 1) repaired.2.2)) =
      keyBag (node ks cs) := by
  dsimp only
  have hbalance :=
    replaceAdjacent_keyBag_balance
      (newSep := (rotateLeft left sep right).2.1)
      (newLeft := (rotateLeft left sep right).1)
      (newRight := (rotateLeft left sep right).2.2)
      hsep hleft hright
  have hrotation := rotateLeft_keyBag left sep right
  apply add_right_cancel
      (b := keyBag left + {sep} + keyBag right)
  calc
    keyBag
          (node (ks.set j (rotateLeft left sep right).2.1)
            ((cs.set j (rotateLeft left sep right).1).set
              (j + 1) (rotateLeft left sep right).2.2)) +
        (keyBag left + {sep} + keyBag right) =
      keyBag (node ks cs) +
        (keyBag (rotateLeft left sep right).1 +
          {(rotateLeft left sep right).2.1} +
          keyBag (rotateLeft left sep right).2.2) :=
      hbalance
    _ = keyBag (node ks cs) +
        (keyBag left + {sep} + keyBag right) := by
          rw [hrotation]

/--
After borrowing from the right, deleting a routed key recursively from the
repaired left child removes exactly one occurrence from the parent.
-/
theorem rotateRight_reassembly_keyBag_erase
    {j sep x : Nat} {ks : List Nat} {cs : List BTree}
    {left right left' : BTree}
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right)
    (hroute :
      x ∈ keysOf (node ks cs) → x ∈ keysOf left)
    (hrec :
      keyBag left' =
        (keyBag (rotateRight left sep right).1).erase x) :
    let repaired := rotateRight left sep right
    keyBag
        (node (ks.set j repaired.2.1)
          ((cs.set j left').set (j + 1) repaired.2.2)) =
      (keyBag (node ks cs)).erase x := by
  dsimp only
  have hrotated :=
    rotateRight_parent_keyBag hsep hleft hright
  dsimp only at hrotated
  obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp hleft
  have htargetAt :
      ((cs.set j (rotateRight left sep right).1).set
          (j + 1) (rotateRight left sep right).2.2)[j]? =
        some (rotateRight left sep right).1 := by
    rw [List.getElem?_set_ne (by omega : j + 1 ≠ j),
      List.getElem?_set_eq_of_lt _ hj]
  have htargetRoute :
      x ∈ keysOf
          (node (ks.set j (rotateRight left sep right).2.1)
            ((cs.set j (rotateRight left sep right).1).set
              (j + 1) (rotateRight left sep right).2.2)) →
        x ∈ keysOf (rotateRight left sep right).1 := by
    intro hx
    have hxBag :
        x ∈ keyBag
          (node (ks.set j (rotateRight left sep right).2.1)
            ((cs.set j (rotateRight left sep right).1).set
              (j + 1) (rotateRight left sep right).2.2)) := by
      simpa only [keyBag, Multiset.mem_coe] using hx
    rw [hrotated] at hxBag
    have hxOriginal : x ∈ keysOf (node ks cs) := by
      simpa only [keyBag, Multiset.mem_coe] using hxBag
    exact
      mem_rotateRight_left_of_mem_left left sep right
        (hroute hxOriginal)
  have hfinal :=
    replaceChild_keyBag_erase htargetAt htargetRoute hrec
  have hchildren :
      (((cs.set j (rotateRight left sep right).1).set
          (j + 1) (rotateRight left sep right).2.2).set j left') =
        (cs.set j left').set
          (j + 1) (rotateRight left sep right).2.2 := by
    rw [List.set_comm _ _ (by omega : j + 1 ≠ j), List.set_set]
  rw [hchildren, hrotated] at hfinal
  exact hfinal

/--
After borrowing from the left, deleting a routed key recursively from the
repaired right child removes exactly one occurrence from the parent.
-/
theorem rotateLeft_reassembly_keyBag_erase
    {j sep x : Nat} {ks : List Nat} {cs : List BTree}
    {left right right' : BTree}
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right)
    (hroute :
      x ∈ keysOf (node ks cs) → x ∈ keysOf right)
    (hrec :
      keyBag right' =
        (keyBag (rotateLeft left sep right).2.2).erase x) :
    let repaired := rotateLeft left sep right
    keyBag
        (node (ks.set j repaired.2.1)
          ((cs.set j repaired.1).set (j + 1) right')) =
      (keyBag (node ks cs)).erase x := by
  dsimp only
  have hrotated :=
    rotateLeft_parent_keyBag hsep hleft hright
  dsimp only at hrotated
  obtain ⟨hjRight, _⟩ :=
    List.getElem?_eq_some_iff.mp hright
  have htargetAt :
      ((cs.set j (rotateLeft left sep right).1).set
          (j + 1) (rotateLeft left sep right).2.2)[j + 1]? =
        some (rotateLeft left sep right).2.2 :=
    List.getElem?_set_eq_of_lt _ (by simpa using hjRight)
  have htargetRoute :
      x ∈ keysOf
          (node (ks.set j (rotateLeft left sep right).2.1)
            ((cs.set j (rotateLeft left sep right).1).set
              (j + 1) (rotateLeft left sep right).2.2)) →
        x ∈ keysOf (rotateLeft left sep right).2.2 := by
    intro hx
    have hxBag :
        x ∈ keyBag
          (node (ks.set j (rotateLeft left sep right).2.1)
            ((cs.set j (rotateLeft left sep right).1).set
              (j + 1) (rotateLeft left sep right).2.2)) := by
      simpa only [keyBag, Multiset.mem_coe] using hx
    rw [hrotated] at hxBag
    have hxOriginal : x ∈ keysOf (node ks cs) := by
      simpa only [keyBag, Multiset.mem_coe] using hxBag
    exact
      mem_rotateLeft_right_of_mem_right left sep right
        (hroute hxOriginal)
  have hfinal :=
    replaceChild_keyBag_erase htargetAt htargetRoute hrec
  simpa only [List.set_set, hrotated] using hfinal

end BTree
end Chapter18
end CLRS
