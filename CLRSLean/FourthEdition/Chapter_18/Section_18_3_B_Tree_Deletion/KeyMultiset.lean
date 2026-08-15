import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion

/-!
# Exact key multisets for B-tree deletion

Executable B-tree deletion removes one occurrence of a key, whereas the
specification-level deletion operation filters every occurrence.  This module
records represented keys as a multiset and proves the exact conservation
equations for the primitive deletion operations.

The generic frame-balance lemmas expose the list accounting needed by parent
reassembly without depending on any B-tree structural invariant.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-- The represented keys of a B-tree, retaining multiplicity and ignoring order. -/
def keyBag (tr : BTree) : Multiset Nat :=
  ↑(keysOf tr)

private theorem coe_append_eq_add {α : Type*} (xs ys : List α) :
    (↑(xs ++ ys) : Multiset α) = ↑xs + ↑ys :=
  (Multiset.coe_add xs ys).symm

private theorem coe_cons_eq_singleton_add {α : Type*} (x : α) (xs : List α) :
    (↑(x :: xs) : Multiset α) = {x} + ↑xs := by
  rw [Multiset.singleton_add, Multiset.cons_coe]

/--
Replacing a witnessed list element balances the new and old list bags against
the removed and inserted elements.
-/
theorem list_set_bag_balance
    {α : Type*} {xs : List α} {i : Nat} {old new : α}
    (hold : xs[i]? = some old) :
    (↑(xs.set i new) : Multiset α) + {old} =
      (↑xs : Multiset α) + {new} := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hold
  have hset :
      (↑(xs.set i new) : Multiset α) =
        ↑(new :: xs.eraseIdx i) :=
    Multiset.coe_eq_coe.mpr (List.set_perm_cons_eraseIdx hi new)
  have holdSource :
      (↑(old :: xs.eraseIdx i) : Multiset α) = ↑xs := by
    apply Multiset.coe_eq_coe.mpr
    simpa only [hget] using List.getElem_cons_eraseIdx_perm hi
  rw [hset, ← holdSource]
  simp only [coe_cons_eq_singleton_add]
  abel

/--
Replacing a witnessed element before {name}`List.flatMap` balances the
flattened bags of the old and new elements.
-/
theorem flatMap_set_bag_balance
    {α β : Type*} {xs : List α} {i : Nat} {old new : α}
    (f : α → List β)
    (hold : xs[i]? = some old) :
    (↑((xs.set i new).flatMap f) : Multiset β) + ↑(f old) =
      (↑(xs.flatMap f) : Multiset β) + ↑(f new) := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hold
  have hsetPerm :
      ((xs.set i new).flatMap f).Perm
        ((new :: xs.eraseIdx i).flatMap f) :=
    (List.set_perm_cons_eraseIdx hi new).flatMap
      (fun _ _ => List.Perm.refl _)
  have holdPerm :
      ((old :: xs.eraseIdx i).flatMap f).Perm
        (xs.flatMap f) := by
    have hsource := List.getElem_cons_eraseIdx_perm hi
    have hsource' : (old :: xs.eraseIdx i).Perm xs := by
      simpa only [hget] using hsource
    exact hsource'.flatMap (fun _ _ => List.Perm.refl _)
  have hsetBag :
      (↑((xs.set i new).flatMap f) : Multiset β) =
        ↑((new :: xs.eraseIdx i).flatMap f) :=
    Multiset.coe_eq_coe.mpr hsetPerm
  have holdBag :
      (↑((old :: xs.eraseIdx i).flatMap f) : Multiset β) =
        ↑(xs.flatMap f) :=
    Multiset.coe_eq_coe.mpr holdPerm
  rw [hsetBag, ← holdBag]
  simp only [List.flatMap_cons, coe_append_eq_add]
  abel

/-- Removing one witnessed list position and retaining its value preserves the bag. -/
theorem take_drop_succ_bag_balance
    {α : Type*} {xs : List α} {j : Nat} {old : α}
    (hold : xs[j]? = some old) :
    (↑(xs.take j ++ xs.drop (j + 1)) : Multiset α) + {old} =
      (↑xs : Multiset α) := by
  obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.mp hold
  rw [← List.eraseIdx_eq_take_drop_succ]
  have hsource :
      (↑(old :: xs.eraseIdx j) : Multiset α) = ↑xs := by
    apply Multiset.coe_eq_coe.mpr
    simpa only [hget] using List.getElem_cons_eraseIdx_perm hj
  simpa only [coe_cons_eq_singleton_add, add_comm] using hsource

/--
Replacing two witnessed adjacent elements by one element preserves the
corresponding {name}`List.flatMap` bag balance.
-/
theorem flatMap_splice_bag_balance
    {α β : Type*} {xs : List α} {j : Nat}
    {left right new : α}
    (f : α → List β)
    (hleft : xs[j]? = some left)
    (hright : xs[j + 1]? = some right) :
    (↑((xs.take j ++ [new] ++ xs.drop (j + 2)).flatMap f) :
          Multiset β) +
        ↑(f left) + ↑(f right) =
      (↑(xs.flatMap f) : Multiset β) + ↑(f new) := by
  obtain ⟨hj, hleftGet⟩ := List.getElem?_eq_some_iff.mp hleft
  obtain ⟨hjRight, hrightGet⟩ :=
    List.getElem?_eq_some_iff.mp hright
  have hdecomp :
      xs.take j ++ left :: right :: xs.drop (j + 2) = xs := by
    calc
      xs.take j ++ left :: right :: xs.drop (j + 2) =
          xs.take j ++ xs.drop j := by
        congr 1
        rw [List.drop_eq_getElem_cons hj, hleftGet]
        rw [List.drop_eq_getElem_cons hjRight, hrightGet]
      _ = xs := List.take_append_drop j xs
  have hsource :
      (↑((xs.take j ++ left :: right :: xs.drop (j + 2)).flatMap f) :
          Multiset β) =
        ↑(xs.flatMap f) := by
    exact congrArg (fun ys : List α =>
      (↑(ys.flatMap f) : Multiset β)) hdecomp
  rw [← hsource]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, coe_append_eq_add]
  abel

/--
A recursive erase equation lifts through a balanced frame when membership of
the deleted key in the pre-update frame implies membership in the recursive
subtree.
-/
theorem keyBag_erase_of_balance
    {after before old new : Multiset Nat} {x : Nat}
    (hbalance : after + old = before + new)
    (hnew : new = old.erase x)
    (hroute : x ∈ before → x ∈ old) :
    after = before.erase x := by
  by_cases hxBefore : x ∈ before
  · have hxOld : x ∈ old := hroute hxBefore
    have hwithCons :
        after + (x ::ₘ old.erase x) =
          (x ::ₘ before.erase x) + old.erase x := by
      calc
        after + (x ::ₘ old.erase x) = after + old := by
          rw [Multiset.cons_erase hxOld]
        _ = before + new := hbalance
        _ = before + old.erase x := by rw [hnew]
        _ = (x ::ₘ before.erase x) + old.erase x := by
          rw [Multiset.cons_erase hxBefore]
    have hcancelX :
        ({x} : Multiset Nat) + (after + old.erase x) =
          {x} + (before.erase x + old.erase x) := by
      calc
        ({x} : Multiset Nat) + (after + old.erase x) =
            after + (x ::ₘ old.erase x) := by
              rw [← Multiset.singleton_add]
              ac_rfl
        _ = (x ::ₘ before.erase x) + old.erase x := hwithCons
        _ = {x} + (before.erase x + old.erase x) := by
              rw [← Multiset.singleton_add]
              ac_rfl
    exact add_right_cancel (add_left_cancel hcancelX)
  · have hxOld : x ∉ old := by
      intro hxOld
      have hwithCons :
          ({x} : Multiset Nat) + after + old.erase x =
            before + old.erase x := by
        calc
          ({x} : Multiset Nat) + after + old.erase x =
              after + (x ::ₘ old.erase x) := by
                rw [← Multiset.singleton_add]
                ac_rfl
          _ = after + old := by rw [Multiset.cons_erase hxOld]
          _ = before + new := hbalance
          _ = before + old.erase x := by rw [hnew]
      have hmemBefore : x ∈ before := by
        have hsingle : ({x} : Multiset Nat) + after = before :=
          add_right_cancel hwithCons
        rw [← hsingle]
        simp
      exact hxBefore hmemBefore
    have hnewEq : new = old := by
      rw [hnew, Multiset.erase_of_notMem hxOld]
    have hsame : after = before := by
      apply add_right_cancel (b := old)
      calc
        after + old = before + new := hbalance
        _ = before + old := by rw [hnewEq]
    rw [Multiset.erase_of_notMem hxBefore]
    exact hsame

/-- {name}`sortedRemove` erases exactly the first matching list occurrence. -/
theorem sortedRemove_keyBag (x : Nat) (ks : List Nat) :
    (↑(sortedRemove x ks) : Multiset Nat) =
      (↑ks : Multiset Nat).erase x := by
  induction ks with
  | nil => simp [sortedRemove]
  | cons k ks ih =>
      rw [sortedRemove_cons]
      split
      next _ =>
        subst k
        simp
      next h =>
        rw [← Multiset.cons_coe, ← Multiset.cons_coe,
          Multiset.erase_cons_tail _ h, ih]

/-- Merging two nodes around a separator preserves their combined key bag. -/
theorem mergeNodes_keyBag (left : BTree) (sep : Nat) (right : BTree) :
    keyBag (mergeNodes left sep right) =
      keyBag left + {sep} + keyBag right := by
  cases left with
  | node lKeys lCh =>
      cases right with
      | node rKeys rCh =>
          simp only [keyBag, mergeNodes_node, keysOf, List.flatMap_append]
          simp only [coe_append_eq_add, coe_cons_eq_singleton_add]
          abel

/-- Borrowing from the right sibling preserves the three-part key bag. -/
theorem rotateRight_keyBag (left : BTree) (sep : Nat) (right : BTree) :
    keyBag (rotateRight left sep right).1 +
        {(rotateRight left sep right).2.1} +
        keyBag (rotateRight left sep right).2.2 =
      keyBag left + {sep} + keyBag right := by
  cases left with
  | node lKeys lCh =>
      cases right with
      | node rKeys rCh =>
          cases rKeys with
          | nil => rfl
          | cons rHead rTail =>
              cases rCh with
              | nil =>
                  simp only [rotateRight_cons, keyBag, keysOf, List.append_nil,
                    List.take_nil, List.drop_nil, List.flatMap_nil]
                  simp only [coe_append_eq_add, coe_cons_eq_singleton_add,
                    Multiset.coe_nil, add_zero]
                  abel
              | cons child children =>
                  simp only [rotateRight_cons, keyBag, keysOf,
                    List.take_succ_cons, List.take_zero,
                    List.drop_succ_cons, List.drop_zero,
                    List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                    List.append_nil]
                  simp only [coe_append_eq_add, coe_cons_eq_singleton_add,
                    Multiset.coe_nil, add_zero]
                  abel

/-- Borrowing from the left sibling preserves the three-part key bag. -/
theorem rotateLeft_keyBag (left : BTree) (sep : Nat) (right : BTree) :
    keyBag (rotateLeft left sep right).1 +
        {(rotateLeft left sep right).2.1} +
        keyBag (rotateLeft left sep right).2.2 =
      keyBag left + {sep} + keyBag right := by
  cases left with
  | node lKeys lCh =>
      cases right with
      | node rKeys rCh =>
          cases lKeys with
          | nil => rfl
          | cons lHead lTail =>
              have hKeys :
                  (lHead :: lTail).dropLast ++
                      [(lHead :: lTail).getLast (List.cons_ne_nil _ _)] =
                    lHead :: lTail :=
                List.dropLast_append_getLast (List.cons_ne_nil _ _)
              have hChildren :
                  lCh.take (lCh.length - 1) ++
                      lCh.drop (lCh.length - 1) =
                    lCh :=
                List.take_append_drop (lCh.length - 1) lCh
              have hKeyBag :
                  (↑(lHead :: lTail).dropLast : Multiset Nat) +
                      {(lHead :: lTail).getLast (List.cons_ne_nil _ _)} =
                    (↑(lHead :: lTail) : Multiset Nat) := by
                simpa only [coe_append_eq_add,
                  coe_cons_eq_singleton_add, Multiset.coe_nil, add_zero] using
                    congrArg (fun xs : List Nat =>
                      (↑xs : Multiset Nat)) hKeys
              have hChildBag :
                  (↑((lCh.take (lCh.length - 1)).flatMap keysOf) :
                      Multiset Nat) +
                      ↑((lCh.drop (lCh.length - 1)).flatMap keysOf) =
                    ↑(lCh.flatMap keysOf) := by
                simpa only [List.flatMap_append, coe_append_eq_add] using
                  congrArg (fun xs : List BTree =>
                    (↑(xs.flatMap keysOf) : Multiset Nat)) hChildren
              simp only [rotateLeft_cons, keyBag, keysOf,
                List.flatMap_append]
              simp only [coe_append_eq_add]
              rw [coe_cons_eq_singleton_add sep rKeys]
              rw [← hKeyBag, ← hChildBag]
              abel

end BTree
end Chapter18
end CLRS
