import Mathlib

/-!
# CLRS Section 12.1 - Binary search trees

This section gives a first Lean model of binary search trees as inductive trees
of natural-number keys.  It proves the fundamental search and insertion facts
used by the textbook invariant argument: search is correct on ordered trees,
minimum and maximum return genuine extremal keys, insertion adds exactly the
inserted key to the membership set, and insertion preserves the BST ordering
invariant.  It also proves functional successor and predecessor queries: the
successor is the least key greater than the query, and the predecessor is the
greatest key less than the query.  Finally, it proves a functional deletion
operation that removes exactly the requested key and preserves ordering.

Main results:

- Theorem {lit}`search_eq_true_iff`: Boolean search is equivalent to tree
  membership on ordered trees.
- Theorem {lit}`minimum?_inTree`: a returned minimum key occurs in the tree.
- Theorem {lit}`minimum?_le_of_ordered`: a returned minimum key is a lower bound
  on an ordered tree.
- Theorem {lit}`maximum?_inTree`: a returned maximum key occurs in the tree.
- Theorem {lit}`le_maximum?_of_ordered`: a returned maximum key is an upper
  bound on an ordered tree.
- Theorem {lit}`successor?_least_greater`: a returned successor is the least
  tree key strictly greater than the query.
- Theorem {lit}`successor?_eq_some_iff`: complete iff specification for a
  returned successor.
- Theorem {lit}`successor?_eq_none_iff`: complete none specification for a
  missing successor.
- Theorem {lit}`successor?_isSome_iff_exists_greater`: successor existence is
  equivalent to the existence of a greater tree key.
- Theorem {lit}`predecessor?_greatest_less`: a returned predecessor is the
  greatest tree key strictly less than the query.
- Theorem {lit}`predecessor?_eq_some_iff`: complete iff specification for a
  returned predecessor.
- Theorem {lit}`predecessor?_eq_none_iff`: complete none specification for a
  missing predecessor.
- Theorem {lit}`predecessor?_isSome_iff_exists_less`: predecessor existence is
  equivalent to the existence of a smaller tree key.
- Theorem {lit}`inTree_insert_iff`: membership after insertion is exactly the
  old membership relation plus the inserted key.
- Theorem {lit}`search_insert_eq_true_iff`: searching after insertion succeeds
  exactly for the inserted key or an old key.
- Theorem {lit}`insert_ordered`: insertion preserves the BST ordering invariant.
- Theorem {lit}`inTree_delete_iff`: functional deletion removes exactly the
  requested key.
- Theorem {lit}`delete_ordered`: functional deletion preserves the BST ordering
  invariant.
- Theorem {lit}`not_inTree_delete_self`: the deleted key is absent afterward.
- Theorem {lit}`delete_eq_self_of_not_inTree`: deleting a missing key leaves an
  ordered tree unchanged.
- Theorem {lit}`search_delete_self_eq_false`: searching for the deleted key
  after deletion returns false.
- Theorem {lit}`search_delete_eq_true_iff`: searching after deletion succeeds
  exactly for old keys different from the deleted key.
- Theorem {lit}`successor?_delete_eq_some_iff`: after deletion, the returned
  successor is the least old key above the query and different from the deleted
  key.
- Theorem {lit}`successor?_delete_eq_none_iff`: after deletion, no successor is
  returned exactly when every old key except the deleted key is at most the
  query.
- Theorem {lit}`predecessor?_delete_eq_some_iff`: after deletion, the returned
  predecessor is the greatest old key below the query and different from the
  deleted key.
- Theorem {lit}`predecessor?_delete_eq_none_iff`: after deletion, no
  predecessor is returned exactly when every old key except the deleted key is
  at least the query.
- Theorem {lit}`searchIter_eq_search`: iterative parent-pointer search matches
  the functional recursive search.
- Theorem {lit}`transplant_preserves_ordered`: TRANSPLANT preserves the BST
  ordering invariant.
- Theorem {lit}`deleteViaTransplant_eq_delete`: TREE-DELETE via transplant
  equals the functional deletion.
- Theorem {lit}`successorZipper_eq_successor?`: parent-pointer successor matches
  the functional successor.
- Theorem {lit}`predecessorZipper_eq_predecessor?`: parent-pointer predecessor
  matches the functional predecessor.
- Theorem {lit}`RepresentsW.tree_unique`: a pointer heap and root pointer
  determine a unique functional tree (the abstraction is a function).
- Theorem {lit}`transplantChild_left_representsW` /
  {lit}`transplantChild_right_representsW`: in-place pointer TRANSPLANT refines the
  functional subtree replacement.
- Theorem {lit}`transplantChild_left_refines_transplant` /
  {lit}`transplantChild_right_refines_transplant`: in-place pointer TRANSPLANT
  refines the functional zipper {lit}`transplant`.
- Theorem {lit}`insertPointer_right_representsW`: pointer TREE-INSERT leaf
  attachment refines the functional subtree replacement.

## Running-time / cost layer (O(h))

- Theorem {lit}`searchCost_le_height`, {lit}`minimumCost_le_height`,
  {lit}`maximumCost_le_height`, {lit}`successorCost_le_height`,
  {lit}`predecessorCost_le_height`, {lit}`insertCost_le_height`,
  {lit}`minKeyCost_le_height`, {lit}`deleteMinCost_le_height`: each descent
  operation costs at most {lit}`height + 1` steps.
- Theorem {lit}`deleteRootCost_le` / {lit}`deleteCost_le`: deletion costs at most
  {lit}`2·height + 3` steps (a root deletion plus a min-extraction and a
  delete-min on the successor subtree).  Together these are the CLRS "each BST
  operation runs in {lit}`O(h)` time" bounds made concrete.

## Randomly built BST (Section 12.4)

- Theorem {lit}`isAncestorOf_iff_firstInInterval`: key {lit}`x` is an ancestor of
  key {lit}`y` in the BST built from a list of distinct keys exactly when
  {lit}`x` is the first key of the list lying in the closed interval between
  them (CLRS Lemma 12.3).  This is the combinatorial workhorse for the
  expected-depth analysis.

Current gaps:

- The zipper-based parent-pointer layer (iterative search, TRANSPLANT,
  TREE-DELETE, parent-pointer successor/predecessor) is proved, and an imperative
  pointer-heap layer now proves in-place TRANSPLANT and leaf TREE-INSERT refine
  the functional specification.
- An explicit RAM cost model over the pointer operations remains future work.
- The probability {lit}`P(i is an ancestor of j) = 1/(|i-j|+1)` and the resulting
  expected-depth bound {lit}`O(log n)` for a randomly built BST are not yet
  formalized; the ancestor characterization above is the needed foundation.
-/

namespace CLRS
namespace Chapter12

/-! ## Tree model and invariant -/

/-- A binary tree of natural-number keys. -/
inductive BSTree where
  | empty : BSTree
  | node : BSTree → Nat → BSTree → BSTree
  deriving Repr, DecidableEq

namespace BSTree

/-- Membership of a key in a binary tree. -/
def InTree (x : Nat) : BSTree → Prop
  | empty => False
  | node left key right => x = key ∨ InTree x left ∨ InTree x right

/-- Every key in the tree is strictly less than {lit}`bound`. -/
def AllLt (bound : Nat) (t : BSTree) : Prop :=
  ∀ x, InTree x t → x < bound

/-- Every key in the tree is strictly greater than {lit}`bound`. -/
def AllGt (bound : Nat) (t : BSTree) : Prop :=
  ∀ x, InTree x t → bound < x

/-- The binary-search-tree ordering invariant. -/
def Ordered : BSTree → Prop
  | empty => True
  | node left key right =>
      Ordered left ∧ Ordered right ∧ AllLt key left ∧ AllGt key right

/-- Functional insertion into a binary search tree. -/
def insert (x : Nat) : BSTree → BSTree
  | empty => node empty x empty
  | node left key right =>
      if x < key then
        node (insert x left) key right
      else if key < x then
        node left key (insert x right)
      else
        node left key right

/-! ## Search, minimum, and maximum operations -/

/-- Search for a key using the binary-search-tree ordering decisions. -/
def search (x : Nat) : BSTree → Bool
  | empty => false
  | node left key right =>
      if x = key then
        true
      else if x < key then
        search x left
      else
        search x right

/-- The minimum key of a nonempty tree, found by following left children. -/
def minimum? : BSTree → Option Nat
  | empty => none
  | node empty key _right => some key
  | node left@(node _ _ _) _key _right => minimum? left

/-- The maximum key of a nonempty tree, found by following right children. -/
def maximum? : BSTree → Option Nat
  | empty => none
  | node _left key empty => some key
  | node _left _key right@(node _ _ _) => maximum? right

/--
The least key in the tree that is strictly greater than {lit}`x`, if such a
key exists.  This is a functional counterpart of CLRS successor search without
parent pointers.
-/
def successor? (x : Nat) : BSTree → Option Nat
  | empty => none
  | node left key right =>
      if x < key then
        match successor? x left with
        | some y => some y
        | none => some key
      else
        successor? x right

/--
The greatest key in the tree that is strictly less than {lit}`x`, if such a
key exists.  This is a functional counterpart of CLRS predecessor search without
parent pointers.
-/
def predecessor? (x : Nat) : BSTree → Option Nat
  | empty => none
  | node left key right =>
      if key < x then
        match predecessor? x right with
        | some y => some y
        | none => some key
      else
        predecessor? x left

/--
A total version of the minimum-key operation.  The value on an empty tree is a
dummy; all public theorems use it only through membership hypotheses or
nonempty subtrees.
-/
def minKey : BSTree → Nat
  | empty => 0
  | node empty key _right => key
  | node left@(node _ _ _) _key _right => minKey left

/-- Delete the minimum key from a tree, leaving empty trees unchanged. -/
def deleteMin : BSTree → BSTree
  | empty => empty
  | node empty _key right => right
  | node left@(node _ _ _) key right => node (deleteMin left) key right

/--
Delete the root of a tree.  When both children are present, the root is replaced
by the minimum key of the right subtree, matching the successor-replacement
idea from the CLRS deletion proof.
-/
def deleteRoot : BSTree → BSTree
  | empty => empty
  | node left _key empty => left
  | node left _key right@(node _ _ _) => node left (minKey right) (deleteMin right)

/-- Functional deletion from a binary search tree. -/
def delete (x : Nat) : BSTree → BSTree
  | empty => empty
  | node left key right =>
      if x < key then
        node (delete x left) key right
      else if key < x then
        node left key (delete x right)
      else
        deleteRoot (node left key right)

/-! ## Search correctness -/

/-- On an ordered tree, Boolean search is equivalent to tree membership. -/
theorem search_eq_true_iff {x : Nat} {t : BSTree}
    (ht : Ordered t) : search x t = true ↔ InTree x t := by
  induction t with
  | empty =>
      simp [search, InTree]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hxkey : x = key
      · simp [search, InTree, hxkey]
      · by_cases hxlt : x < key
        · have hnotRight : ¬ InTree x right := by
            intro hxRight
            exact (Nat.lt_asymm hxlt (hGt x hxRight)).elim
          simp [search, InTree, hxkey, hxlt, ihLeft hLeft, hnotRight]
        · have hnotLeft : ¬ InTree x left := by
            intro hxLeft
            exact hxlt (hLt x hxLeft)
          simp [search, InTree, hxkey, hxlt, ihRight hRight, hnotLeft]

/-! ## Minimum and maximum correctness -/

/-- If {lit}`minimum?` returns a key, that key occurs in the tree. -/
theorem minimum?_inTree {t : BSTree} {m : Nat}
    (hmin : minimum? t = some m) : InTree m t := by
  induction t with
  | empty =>
      simp [minimum?] at hmin
  | node left key right ihLeft _ihRight =>
      cases left with
      | empty =>
          simp [minimum?, InTree] at hmin ⊢
          exact Or.inl hmin.symm
      | node ll lk lr =>
          have hminLeft : (node ll lk lr).minimum? = some m := by
            simpa [minimum?] using hmin
          have hLeft : InTree m (node ll lk lr) := ihLeft hminLeft
          exact Or.inr (Or.inl hLeft)

/-- On an ordered tree, the result returned by {lit}`minimum?` is a lower bound. -/
theorem minimum?_le_of_ordered {t : BSTree} {m : Nat}
    (ht : Ordered t) (hmin : minimum? t = some m) :
    ∀ x, InTree x t → m ≤ x := by
  induction t generalizing m with
  | empty =>
      simp [minimum?] at hmin
  | node left key right ihLeft _ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      cases left with
      | empty =>
          simp [minimum?] at hmin
          subst m
          intro x hx
          simp [InTree] at hx
          rcases hx with rfl | hxRight
          · exact le_rfl
          · exact Nat.le_of_lt (hGt x hxRight)
      | node ll lk lr =>
          have hminLeft : (node ll lk lr).minimum? = some m := by
            simpa [minimum?] using hmin
          have hMinLeft : InTree m (node ll lk lr) := minimum?_inTree hminLeft
          have hm_lt_key : m < key := hLt m hMinLeft
          intro x hx
          simp [InTree] at hx
          rcases hx with rfl | hxLeft | hxRight
          · exact Nat.le_of_lt hm_lt_key
          · exact ihLeft hLeft hminLeft x hxLeft
          · exact Nat.le_trans (Nat.le_of_lt hm_lt_key) (Nat.le_of_lt (hGt x hxRight))

/-- If {lit}`maximum?` returns a key, that key occurs in the tree. -/
theorem maximum?_inTree {t : BSTree} {m : Nat}
    (hmax : maximum? t = some m) : InTree m t := by
  induction t with
  | empty =>
      simp [maximum?] at hmax
  | node left key right _ihLeft ihRight =>
      cases right with
      | empty =>
          simp [maximum?, InTree] at hmax ⊢
          exact Or.inl hmax.symm
      | node rl rk rr =>
          have hmaxRight : (node rl rk rr).maximum? = some m := by
            simpa [maximum?] using hmax
          have hRight : InTree m (node rl rk rr) := ihRight hmaxRight
          exact Or.inr (Or.inr hRight)

/-- On an ordered tree, the result returned by {lit}`maximum?` is an upper bound. -/
theorem le_maximum?_of_ordered {t : BSTree} {m : Nat}
    (ht : Ordered t) (hmax : maximum? t = some m) :
    ∀ x, InTree x t → x ≤ m := by
  induction t generalizing m with
  | empty =>
      simp [maximum?] at hmax
  | node left key right _ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      cases right with
      | empty =>
          simp [maximum?] at hmax
          subst m
          intro x hx
          simp [InTree] at hx
          rcases hx with rfl | hxLeft
          · exact le_rfl
          · exact Nat.le_of_lt (hLt x hxLeft)
      | node rl rk rr =>
          have hmaxRight : (node rl rk rr).maximum? = some m := by
            simpa [maximum?] using hmax
          have hMaxRight : InTree m (node rl rk rr) := maximum?_inTree hmaxRight
          have hkey_lt_m : key < m := hGt m hMaxRight
          intro x hx
          simp [InTree] at hx
          rcases hx with rfl | hxLeft | hxRight
          · exact Nat.le_of_lt hkey_lt_m
          · exact Nat.le_trans (Nat.le_of_lt (hLt x hxLeft)) (Nat.le_of_lt hkey_lt_m)
          · exact ihRight hRight hmaxRight x hxRight

/-! ## Successor and predecessor correctness -/

/--
If the functional successor query returns {lit}`none`, no tree key is strictly
greater than the query key.
-/
theorem successor?_none_le {x : Nat} {t : BSTree}
    (ht : Ordered t) (hs : successor? x t = none) :
    ∀ y, InTree y t → y ≤ x := by
  induction t with
  | empty =>
      intro y hy
      simp [InTree] at hy
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, _hGt⟩
      by_cases hxkey : x < key
      · cases hsuccLeft : successor? x left <;>
          simp [successor?, hxkey, hsuccLeft] at hs
      · have hRightNone : successor? x right = none := by
          simpa [successor?, hxkey] using hs
        have hKeyLe : key ≤ x := Nat.le_of_not_gt hxkey
        intro y hy
        simp [InTree] at hy
        rcases hy with rfl | hyLeft | hyRight
        · exact hKeyLe
        · exact Nat.le_trans (Nat.le_of_lt (hLt y hyLeft)) hKeyLe
        · exact ihRight hRight hRightNone y hyRight

/--
Functional successor correctness: if {lit}`successor? x t = some s` on an
ordered tree, then {lit}`s` occurs in the tree, {lit}`x < s`, and every tree key
greater than {lit}`x` is at least {lit}`s`.
-/
theorem successor?_least_greater {x s : Nat} {t : BSTree}
    (ht : Ordered t) (hs : successor? x t = some s) :
    InTree s t ∧ x < s ∧ ∀ y, InTree y t → x < y → s ≤ y := by
  induction t generalizing s with
  | empty =>
      simp [successor?] at hs
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hxkey : x < key
      · cases hsuccLeft : successor? x left with
        | some sl =>
            have hsome : some sl = some s := by
              simpa [successor?, hxkey, hsuccLeft] using hs
            injection hsome with hsl
            subst s
            rcases ihLeft hLeft hsuccLeft with ⟨hInLeft, hxsl, hLeastLeft⟩
            exact ⟨
              Or.inr (Or.inl hInLeft),
              hxsl,
              by
                intro y hy hxy
                simp [InTree] at hy
                rcases hy with rfl | hyLeft | hyRight
                · exact Nat.le_of_lt (hLt sl hInLeft)
                · exact hLeastLeft y hyLeft hxy
                · exact Nat.le_trans
                    (Nat.le_of_lt (hLt sl hInLeft))
                    (Nat.le_of_lt (hGt y hyRight))
            ⟩
        | none =>
            have hsome : some key = some s := by
              simpa [successor?, hxkey, hsuccLeft] using hs
            injection hsome with hkey
            subst s
            have hNoLeft := successor?_none_le hLeft hsuccLeft
            exact ⟨
              Or.inl rfl,
              hxkey,
              by
                intro y hy hxy
                simp [InTree] at hy
                rcases hy with rfl | hyLeft | hyRight
                · exact le_rfl
                · exact False.elim ((Nat.not_lt_of_ge (hNoLeft y hyLeft)) hxy)
                · exact Nat.le_of_lt (hGt y hyRight)
            ⟩
      · have hRightSome : successor? x right = some s := by
          simpa [successor?, hxkey] using hs
        have hKeyLe : key ≤ x := Nat.le_of_not_gt hxkey
        rcases ihRight hRight hRightSome with ⟨hInRight, hxs, hLeastRight⟩
        exact ⟨
          Or.inr (Or.inr hInRight),
          hxs,
          by
            intro y hy hxy
            simp [InTree] at hy
            rcases hy with rfl | hyLeft | hyRight
            · exact False.elim (hxkey hxy)
            · have hyLeX : y ≤ x :=
                Nat.le_trans (Nat.le_of_lt (hLt y hyLeft)) hKeyLe
              exact False.elim ((Nat.not_lt_of_ge hyLeX) hxy)
            · exact hLeastRight y hyRight hxy
        ⟩

/--
If the functional predecessor query returns {lit}`none`, no tree key is strictly
less than the query key.
-/
theorem predecessor?_none_ge {x : Nat} {t : BSTree}
    (ht : Ordered t) (hp : predecessor? x t = none) :
    ∀ y, InTree y t → x ≤ y := by
  induction t with
  | empty =>
      intro y hy
      simp [InTree] at hy
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, _hLt, hGt⟩
      by_cases hkeyx : key < x
      · cases hpredRight : predecessor? x right <;>
          simp [predecessor?, hkeyx, hpredRight] at hp
      · have hLeftNone : predecessor? x left = none := by
          simpa [predecessor?, hkeyx] using hp
        have hxLeKey : x ≤ key := Nat.le_of_not_gt hkeyx
        intro y hy
        simp [InTree] at hy
        rcases hy with rfl | hyLeft | hyRight
        · exact hxLeKey
        · exact ihLeft hLeft hLeftNone y hyLeft
        · exact Nat.le_trans hxLeKey (Nat.le_of_lt (hGt y hyRight))

/--
Functional predecessor correctness: if {lit}`predecessor? x t = some p` on an
ordered tree, then {lit}`p` occurs in the tree, {lit}`p < x`, and every tree key
less than {lit}`x` is at most {lit}`p`.
-/
theorem predecessor?_greatest_less {x p : Nat} {t : BSTree}
    (ht : Ordered t) (hp : predecessor? x t = some p) :
    InTree p t ∧ p < x ∧ ∀ y, InTree y t → y < x → y ≤ p := by
  induction t generalizing p with
  | empty =>
      simp [predecessor?] at hp
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hkeyx : key < x
      · cases hpredRight : predecessor? x right with
        | some pr =>
            have hsome : some pr = some p := by
              simpa [predecessor?, hkeyx, hpredRight] using hp
            injection hsome with hpr
            subst p
            rcases ihRight hRight hpredRight with ⟨hInRight, hprx, hGreatestRight⟩
            exact ⟨
              Or.inr (Or.inr hInRight),
              hprx,
              by
                intro y hy hyx
                simp [InTree] at hy
                rcases hy with rfl | hyLeft | hyRight
                · exact Nat.le_of_lt (hGt pr hInRight)
                · exact Nat.le_trans
                    (Nat.le_of_lt (hLt y hyLeft))
                    (Nat.le_of_lt (hGt pr hInRight))
                · exact hGreatestRight y hyRight hyx
            ⟩
        | none =>
            have hsome : some key = some p := by
              simpa [predecessor?, hkeyx, hpredRight] using hp
            injection hsome with hkey
            subst p
            have hNoRight := predecessor?_none_ge hRight hpredRight
            exact ⟨
              Or.inl rfl,
              hkeyx,
              by
                intro y hy hyx
                simp [InTree] at hy
                rcases hy with rfl | hyLeft | hyRight
                · exact le_rfl
                · exact Nat.le_of_lt (hLt y hyLeft)
                · exact False.elim ((Nat.not_lt_of_ge (hNoRight y hyRight)) hyx)
            ⟩
      · have hLeftSome : predecessor? x left = some p := by
          simpa [predecessor?, hkeyx] using hp
        have hxLeKey : x ≤ key := Nat.le_of_not_gt hkeyx
        rcases ihLeft hLeft hLeftSome with ⟨hInLeft, hpx, hGreatestLeft⟩
        exact ⟨
          Or.inr (Or.inl hInLeft),
          hpx,
          by
            intro y hy hyx
            simp [InTree] at hy
            rcases hy with rfl | hyLeft | hyRight
            · exact False.elim (hkeyx hyx)
            · exact hGreatestLeft y hyLeft hyx
            · have hx_lt_y : x < y := Nat.lt_of_le_of_lt hxLeKey (hGt y hyRight)
              exact False.elim (Nat.lt_asymm hyx hx_lt_y)
        ⟩

/-- Complete iff specification for a returned functional successor. -/
theorem successor?_eq_some_iff {x s : Nat} {t : BSTree}
    (ht : Ordered t) :
    successor? x t = some s ↔
      InTree s t ∧ x < s ∧ ∀ y, InTree y t → x < y → s ≤ y := by
  constructor
  · exact successor?_least_greater ht
  · intro hsSpec
    cases hs : successor? x t with
    | none =>
        have hNoGreater := successor?_none_le ht hs
        exact False.elim ((Nat.not_lt_of_ge (hNoGreater s hsSpec.1)) hsSpec.2.1)
    | some z =>
        rcases successor?_least_greater ht hs with ⟨hzIn, hxz, hzLeast⟩
        have hzs : z ≤ s := hzLeast s hsSpec.1 hsSpec.2.1
        have hsz : s ≤ z := hsSpec.2.2 z hzIn hxz
        have hEq : z = s := Nat.le_antisymm hzs hsz
        simp [hEq] at hs ⊢

/-- Complete none specification for a missing functional successor. -/
theorem successor?_eq_none_iff {x : Nat} {t : BSTree}
    (ht : Ordered t) :
    successor? x t = none ↔ ∀ y, InTree y t → y ≤ x := by
  constructor
  · exact successor?_none_le ht
  · intro hNoGreater
    cases hs : successor? x t with
    | none => rfl
    | some s =>
        rcases successor?_least_greater ht hs with ⟨hsIn, hxs, _hLeast⟩
        exact False.elim ((Nat.not_lt_of_ge (hNoGreater s hsIn)) hxs)

/-- Complete iff specification for a returned functional predecessor. -/
theorem predecessor?_eq_some_iff {x p : Nat} {t : BSTree}
    (ht : Ordered t) :
    predecessor? x t = some p ↔
      InTree p t ∧ p < x ∧ ∀ y, InTree y t → y < x → y ≤ p := by
  constructor
  · exact predecessor?_greatest_less ht
  · intro hpSpec
    cases hp : predecessor? x t with
    | none =>
        have hNoLesser := predecessor?_none_ge ht hp
        exact False.elim ((Nat.not_lt_of_ge (hNoLesser p hpSpec.1)) hpSpec.2.1)
    | some z =>
        rcases predecessor?_greatest_less ht hp with ⟨hzIn, hzx, hzGreatest⟩
        have hzp : z ≤ p := hpSpec.2.2 z hzIn hzx
        have hpz : p ≤ z := hzGreatest p hpSpec.1 hpSpec.2.1
        have hEq : z = p := Nat.le_antisymm hzp hpz
        simp [hEq] at hp ⊢

/-- Complete none specification for a missing functional predecessor. -/
theorem predecessor?_eq_none_iff {x : Nat} {t : BSTree}
    (ht : Ordered t) :
    predecessor? x t = none ↔ ∀ y, InTree y t → x ≤ y := by
  constructor
  · exact predecessor?_none_ge ht
  · intro hNoLesser
    cases hp : predecessor? x t with
    | none => rfl
    | some p =>
        rcases predecessor?_greatest_less ht hp with ⟨hpIn, hpx, _hGreatest⟩
        exact False.elim ((Nat.not_lt_of_ge (hNoLesser p hpIn)) hpx)

/-- A functional successor exists exactly when some tree key is greater. -/
theorem successor?_isSome_iff_exists_greater {x : Nat} {t : BSTree}
    (ht : Ordered t) :
    (successor? x t).isSome ↔ ∃ y, InTree y t ∧ x < y := by
  constructor
  · intro hSome
    cases hs : successor? x t with
    | none =>
        simp [hs] at hSome
    | some s =>
        rcases successor?_least_greater ht hs with ⟨hsIn, hxs, _hLeast⟩
        exact ⟨s, hsIn, hxs⟩
  · intro hExists
    rcases hExists with ⟨y, hyIn, hxy⟩
    cases hs : successor? x t with
    | none =>
        have hNoGreater := (successor?_eq_none_iff ht).mp hs
        exact False.elim ((Nat.not_lt_of_ge (hNoGreater y hyIn)) hxy)
    | some _s =>
        simp

/-- A functional predecessor exists exactly when some tree key is smaller. -/
theorem predecessor?_isSome_iff_exists_less {x : Nat} {t : BSTree}
    (ht : Ordered t) :
    (predecessor? x t).isSome ↔ ∃ y, InTree y t ∧ y < x := by
  constructor
  · intro hSome
    cases hp : predecessor? x t with
    | none =>
        simp [hp] at hSome
    | some p =>
        rcases predecessor?_greatest_less ht hp with ⟨hpIn, hpx, _hGreatest⟩
        exact ⟨p, hpIn, hpx⟩
  · intro hExists
    rcases hExists with ⟨y, hyIn, hyx⟩
    cases hp : predecessor? x t with
    | none =>
        have hNoLesser := (predecessor?_eq_none_iff ht).mp hp
        exact False.elim ((Nat.not_lt_of_ge (hNoLesser y hyIn)) hyx)
    | some _p =>
        simp

/-! ## Functional deletion correctness -/

/-- A node is never the empty tree. -/
theorem node_ne_empty (left : BSTree) (key : Nat) (right : BSTree) :
    node left key right ≠ empty := by
  intro h
  cases h

/-- On nonempty trees, the total {lit}`minKey` agrees with {lit}`minimum?`. -/
theorem minimum?_eq_some_minKey {t : BSTree} (h : t ≠ empty) :
    minimum? t = some (minKey t) := by
  induction t with
  | empty =>
      exact (h rfl).elim
  | node left key right ihLeft _ihRight =>
      cases left with
      | empty =>
          simp [minimum?, minKey]
      | node ll lk lr =>
          have hLeftNonempty : BSTree.node ll lk lr ≠ empty :=
            node_ne_empty ll lk lr
          simpa [minimum?, minKey] using ihLeft hLeftNonempty

/-- The total minimum key of a nonempty tree occurs in that tree. -/
theorem minKey_inTree {t : BSTree} (h : t ≠ empty) :
    InTree (minKey t) t := by
  exact minimum?_inTree (minimum?_eq_some_minKey h)

/-- On an ordered tree, {lit}`minKey` is a lower bound for all members. -/
theorem minKey_le_of_ordered {t : BSTree} (ht : Ordered t) :
    ∀ y, InTree y t → minKey t ≤ y := by
  by_cases h : t = empty
  · subst t
    intro y hy
    simp [InTree] at hy
  · exact minimum?_le_of_ordered ht (minimum?_eq_some_minKey h)

/--
Deleting the minimum key removes exactly that key from an ordered tree.
The empty-tree case is harmless because membership is false.
-/
theorem inTree_deleteMin_iff {y : Nat} {t : BSTree}
    (ht : Ordered t) :
    InTree y (deleteMin t) ↔ InTree y t ∧ y ≠ minKey t := by
  induction t generalizing y with
  | empty =>
      simp [deleteMin, InTree, minKey]
  | node left key right ihLeft _ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, _hRight, hLt, hGt⟩
      cases left with
      | empty =>
          simp [deleteMin, minKey, InTree]
          constructor
          · intro hyRight
            refine ⟨Or.inr hyRight, ?_⟩
            intro hyEq
            subst y
            exact (Nat.lt_irrefl key) (hGt key hyRight)
          · intro h
            rcases h with ⟨hyNode, hyNe⟩
            rcases hyNode with hyKey | hyRight
            · exact False.elim (hyNe hyKey)
            · exact hyRight
      | node ll lk lr =>
          have hLeftNonempty : BSTree.node ll lk lr ≠ empty :=
            node_ne_empty ll lk lr
          have hMinInLeft :
              InTree (minKey (BSTree.node ll lk lr)) (BSTree.node ll lk lr) :=
            minKey_inTree hLeftNonempty
          have hMinLtKey : minKey (BSTree.node ll lk lr) < key :=
            hLt (minKey (BSTree.node ll lk lr)) hMinInLeft
          have ih := ihLeft (y := y) hLeft
          simp [deleteMin, minKey, InTree]
          constructor
          · intro hy
            rcases hy with hyKey | hyLeft | hyRight
            · refine ⟨Or.inl hyKey, ?_⟩
              intro hyMin
              omega
            · rcases (ih.mp hyLeft) with ⟨hyOldLeft, hyNe⟩
              exact ⟨Or.inr (Or.inl hyOldLeft), hyNe⟩
            · refine ⟨Or.inr (Or.inr hyRight), ?_⟩
              intro hyMin
              have hKeyLtY : key < y := hGt y hyRight
              omega
          · intro h
            rcases h with ⟨hyNode, hyNe⟩
            rcases hyNode with hyKey | hyLeft | hyRight
            · exact Or.inl hyKey
            · exact Or.inr (Or.inl (ih.mpr ⟨hyLeft, hyNe⟩))
            · exact Or.inr (Or.inr hyRight)

/-- Deleting the minimum key preserves the BST ordering invariant. -/
theorem deleteMin_ordered {t : BSTree} (ht : Ordered t) :
    Ordered (deleteMin t) := by
  induction t with
  | empty =>
      simp [deleteMin, Ordered]
  | node left key right ihLeft _ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      cases left with
      | empty =>
          simpa [deleteMin] using hRight
      | node ll lk lr =>
          have hDeletedLeftOrdered :
              Ordered (deleteMin (BSTree.node ll lk lr)) :=
            ihLeft hLeft
          have hDeletedLeftLt :
              AllLt key (deleteMin (BSTree.node ll lk lr)) := by
            intro y hy
            exact hLt y ((inTree_deleteMin_iff (y := y) hLeft).mp hy).1
          simp [deleteMin, Ordered]
          exact ⟨hDeletedLeftOrdered, hRight, hDeletedLeftLt, hGt⟩

/-- Deleting a root removes exactly the old root key from an ordered node. -/
theorem inTree_deleteRoot_iff {y : Nat} {left right : BSTree} {key : Nat}
    (ht : Ordered (node left key right)) :
    InTree y (deleteRoot (node left key right)) ↔
      InTree y (node left key right) ∧ y ≠ key := by
  simp [Ordered] at ht
  rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
  cases right with
  | empty =>
      simp [deleteRoot, InTree]
      constructor
      · intro hyLeft
        refine ⟨Or.inr hyLeft, ?_⟩
        intro hyEq
        subst y
        exact (Nat.lt_irrefl key) (hLt key hyLeft)
      · intro h
        rcases h with ⟨hyNode, hyNe⟩
        rcases hyNode with hyKey | hyLeft
        · exact False.elim (hyNe hyKey)
        · exact hyLeft
  | node rl rk rr =>
      have hRightNonempty : BSTree.node rl rk rr ≠ empty :=
        node_ne_empty rl rk rr
      have hMinInRight :
          InTree (minKey (BSTree.node rl rk rr)) (BSTree.node rl rk rr) :=
        minKey_inTree hRightNonempty
      have hKeyLtMin : key < minKey (BSTree.node rl rk rr) :=
        hGt (minKey (BSTree.node rl rk rr)) hMinInRight
      have hDelMin := inTree_deleteMin_iff (y := y) hRight
      simp [deleteRoot, InTree]
      constructor
      · intro hy
        rcases hy with hyMin | hyLeft | hyRightDeleted
        · subst y
          refine ⟨Or.inr (Or.inr hMinInRight), ?_⟩
          intro hEq
          omega
        · refine ⟨Or.inr (Or.inl hyLeft), ?_⟩
          intro hyEq
          subst y
          exact (Nat.lt_irrefl key) (hLt key hyLeft)
        · rcases hDelMin.mp hyRightDeleted with ⟨hyRight, _hyNeMin⟩
          refine ⟨Or.inr (Or.inr hyRight), ?_⟩
          intro hyEq
          subst y
          exact (Nat.lt_irrefl key) (hGt key hyRight)
      · intro h
        rcases h with ⟨hyNode, hyNeKey⟩
        rcases hyNode with hyKey | hyLeft | hyRight
        · exact False.elim (hyNeKey hyKey)
        · exact Or.inr (Or.inl hyLeft)
        · by_cases hyMin : y = minKey (BSTree.node rl rk rr)
          · exact Or.inl hyMin
          · exact Or.inr (Or.inr (hDelMin.mpr ⟨hyRight, hyMin⟩))

/-- Deleting a root preserves the BST ordering invariant. -/
theorem deleteRoot_ordered {left right : BSTree} {key : Nat}
    (ht : Ordered (node left key right)) :
    Ordered (deleteRoot (node left key right)) := by
  simp [Ordered] at ht
  rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
  cases right with
  | empty =>
      simpa [deleteRoot] using hLeft
  | node rl rk rr =>
      have hRightNonempty : BSTree.node rl rk rr ≠ empty :=
        node_ne_empty rl rk rr
      have hMinInRight :
          InTree (minKey (BSTree.node rl rk rr)) (BSTree.node rl rk rr) :=
        minKey_inTree hRightNonempty
      have hKeyLtMin : key < minKey (BSTree.node rl rk rr) :=
        hGt (minKey (BSTree.node rl rk rr)) hMinInRight
      have hLeftLtMin : AllLt (minKey (BSTree.node rl rk rr)) left := by
        intro y hyLeft
        exact Nat.lt_trans (hLt y hyLeft) hKeyLtMin
      have hDeletedRightGt :
          AllGt (minKey (BSTree.node rl rk rr))
            (deleteMin (BSTree.node rl rk rr)) := by
        intro y hyDeleted
        rcases (inTree_deleteMin_iff (y := y) hRight).mp hyDeleted with
          ⟨hyRight, hyNeMin⟩
        have hMinLeY :
            minKey (BSTree.node rl rk rr) ≤ y :=
          minKey_le_of_ordered hRight y hyRight
        omega
      simp [deleteRoot, Ordered]
      exact ⟨hLeft, deleteMin_ordered hRight, hLeftLtMin, hDeletedRightGt⟩

/-- Functional deletion removes exactly the requested key from an ordered tree. -/
theorem inTree_delete_iff {x y : Nat} {t : BSTree}
    (ht : Ordered t) :
    InTree y (delete x t) ↔ InTree y t ∧ y ≠ x := by
  induction t generalizing x y with
  | empty =>
      simp [delete, InTree]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hxkey : x < key
      · have ih := ihLeft (x := x) (y := y) hLeft
        simp [delete, InTree, hxkey]
        constructor
        · intro hy
          rcases hy with hyKey | hyLeftDeleted | hyRight
          · refine ⟨Or.inl hyKey, ?_⟩
            intro hyx
            omega
          · rcases ih.mp hyLeftDeleted with ⟨hyLeft, hyNe⟩
            exact ⟨Or.inr (Or.inl hyLeft), hyNe⟩
          · refine ⟨Or.inr (Or.inr hyRight), ?_⟩
            intro hyx
            have hKeyLtY : key < y := hGt y hyRight
            omega
        · intro h
          rcases h with ⟨hyNode, hyNe⟩
          rcases hyNode with hyKey | hyLeft | hyRight
          · exact Or.inl hyKey
          · exact Or.inr (Or.inl (ih.mpr ⟨hyLeft, hyNe⟩))
          · exact Or.inr (Or.inr hyRight)
      · by_cases hkeyx : key < x
        · have ih := ihRight (x := x) (y := y) hRight
          simp [delete, InTree, hxkey, hkeyx]
          constructor
          · intro hy
            rcases hy with hyKey | hyLeft | hyRightDeleted
            · refine ⟨Or.inl hyKey, ?_⟩
              intro hyx
              omega
            · refine ⟨Or.inr (Or.inl hyLeft), ?_⟩
              intro hyx
              have hYLtKey : y < key := hLt y hyLeft
              omega
            · rcases ih.mp hyRightDeleted with ⟨hyRight, hyNe⟩
              exact ⟨Or.inr (Or.inr hyRight), hyNe⟩
          · intro h
            rcases h with ⟨hyNode, hyNe⟩
            rcases hyNode with hyKey | hyLeft | hyRight
            · exact Or.inl hyKey
            · exact Or.inr (Or.inl hyLeft)
            · exact Or.inr (Or.inr (ih.mpr ⟨hyRight, hyNe⟩))
        · have hxEq : x = key :=
            Nat.le_antisymm (Nat.le_of_not_gt hkeyx) (Nat.le_of_not_gt hxkey)
          subst x
          have hNode : Ordered (node left key right) := by
            simp [Ordered, hLeft, hRight, hLt, hGt]
          simpa [delete, hxkey, hkeyx] using
            (inTree_deleteRoot_iff (y := y) (left := left) (right := right)
              (key := key) hNode)

/-- Functional deletion preserves the binary-search-tree ordering invariant. -/
theorem delete_ordered {x : Nat} {t : BSTree}
    (ht : Ordered t) : Ordered (delete x t) := by
  induction t generalizing x with
  | empty =>
      simp [delete, Ordered]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hxkey : x < key
      · have hDeletedLeftLt : AllLt key (delete x left) := by
          intro y hy
          exact hLt y ((inTree_delete_iff (x := x) (y := y) hLeft).mp hy).1
        simp [delete, Ordered, hxkey]
        exact ⟨ihLeft (x := x) hLeft, hRight, hDeletedLeftLt, hGt⟩
      · by_cases hkeyx : key < x
        · have hDeletedRightGt : AllGt key (delete x right) := by
            intro y hy
            exact hGt y ((inTree_delete_iff (x := x) (y := y) hRight).mp hy).1
          simp [delete, Ordered, hxkey, hkeyx]
          exact ⟨hLeft, ihRight (x := x) hRight, hLt, hDeletedRightGt⟩
        · have hNode : Ordered (node left key right) := by
            simp [Ordered, hLeft, hRight, hLt, hGt]
          simpa [delete, hxkey, hkeyx] using
            (deleteRoot_ordered (left := left) (right := right) (key := key) hNode)

/-- The key requested for functional deletion is absent afterward. -/
theorem not_inTree_delete_self {x : Nat} {t : BSTree}
    (ht : Ordered t) : ¬ InTree x (delete x t) := by
  intro hxDeleted
  exact ((inTree_delete_iff (x := x) (y := x) ht).mp hxDeleted).2 rfl

/-- Keys different from the deleted key are preserved by functional deletion. -/
theorem inTree_delete_of_ne {x y : Nat} {t : BSTree}
    (ht : Ordered t) (hy : InTree y t) (hyne : y ≠ x) :
    InTree y (delete x t) := by
  exact (inTree_delete_iff (x := x) (y := y) ht).mpr ⟨hy, hyne⟩

/-- Every key present after functional deletion was already present before it. -/
theorem inTree_of_inTree_delete {x y : Nat} {t : BSTree}
    (ht : Ordered t) (hy : InTree y (delete x t)) :
    InTree y t := by
  exact ((inTree_delete_iff (x := x) (y := y) ht).mp hy).1

/-- Deleting a missing key leaves an ordered functional BST unchanged. -/
theorem delete_eq_self_of_not_inTree {x : Nat} {t : BSTree}
    (ht : Ordered t) (hx : ¬ InTree x t) :
    delete x t = t := by
  induction t generalizing x with
  | empty =>
      simp [delete]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, _hLt, _hGt⟩
      have hxNeKey : x ≠ key := by
        intro hxEq
        exact hx (by simp [InTree, hxEq])
      by_cases hxkey : x < key
      · have hxNotLeft : ¬ InTree x left := by
          intro hxLeft
          exact hx (by simp [InTree, hxLeft])
        simp [delete, hxkey, ihLeft hLeft hxNotLeft]
      · by_cases hkeyx : key < x
        · have hxNotRight : ¬ InTree x right := by
            intro hxRight
            exact hx (by simp [InTree, hxRight])
          simp [delete, hxkey, hkeyx, ihRight hRight hxNotRight]
        · have hxEqKey : x = key :=
            Nat.le_antisymm (Nat.le_of_not_gt hkeyx) (Nat.le_of_not_gt hxkey)
          exact False.elim (hxNeKey hxEqKey)

/-- Searching for a deleted key in the resulting ordered tree returns false. -/
theorem search_delete_self_eq_false {x : Nat} {t : BSTree}
    (ht : Ordered t) : search x (delete x t) = false := by
  have hOrderedDeleted : Ordered (delete x t) := delete_ordered (x := x) ht
  have hNotInDeleted : ¬ InTree x (delete x t) := not_inTree_delete_self ht
  cases hsearch : search x (delete x t) with
  | false => rfl
  | true =>
      have hxIn : InTree x (delete x t) :=
        (search_eq_true_iff hOrderedDeleted).mp hsearch
      exact False.elim (hNotInDeleted hxIn)

/-- Searching after deletion succeeds exactly for old keys different from the deleted key. -/
theorem search_delete_eq_true_iff {x y : Nat} {t : BSTree}
    (ht : Ordered t) :
    search y (delete x t) = true ↔ search y t = true ∧ y ≠ x := by
  have hDeletedOrdered : Ordered (delete x t) := delete_ordered (x := x) ht
  constructor
  · intro hSearch
    have hyDeleted : InTree y (delete x t) :=
      (search_eq_true_iff hDeletedOrdered).mp hSearch
    rcases (inTree_delete_iff (x := x) (y := y) ht).mp hyDeleted with
      ⟨hyOld, hyNe⟩
    exact ⟨(search_eq_true_iff ht).mpr hyOld, hyNe⟩
  · intro h
    rcases h with ⟨hySearch, hyNe⟩
    have hyOld : InTree y t := (search_eq_true_iff ht).mp hySearch
    have hyDeleted : InTree y (delete x t) :=
      (inTree_delete_iff (x := x) (y := y) ht).mpr ⟨hyOld, hyNe⟩
    exact (search_eq_true_iff hDeletedOrdered).mpr hyDeleted

/-- Successor after deletion is the least old key above the query except the deleted key. -/
theorem successor?_delete_eq_some_iff {x q s : Nat} {t : BSTree}
    (ht : Ordered t) :
    successor? q (delete x t) = some s ↔
      InTree s t ∧ s ≠ x ∧ q < s ∧
        ∀ y, InTree y t → y ≠ x → q < y → s ≤ y := by
  have hDeletedOrdered : Ordered (delete x t) := delete_ordered (x := x) ht
  constructor
  · intro hs
    rcases (successor?_eq_some_iff hDeletedOrdered).mp hs with
      ⟨hsDeleted, hqs, hLeastDeleted⟩
    rcases (inTree_delete_iff (x := x) (y := s) ht).mp hsDeleted with
      ⟨hsOld, hsNe⟩
    exact ⟨
      hsOld,
      hsNe,
      hqs,
      by
        intro y hyOld hyNe hqy
        have hyDeleted : InTree y (delete x t) :=
          (inTree_delete_iff (x := x) (y := y) ht).mpr ⟨hyOld, hyNe⟩
        exact hLeastDeleted y hyDeleted hqy
    ⟩
  · intro hsSpec
    rcases hsSpec with ⟨hsOld, hsNe, hqs, hLeastOld⟩
    apply (successor?_eq_some_iff hDeletedOrdered).mpr
    refine ⟨?_, hqs, ?_⟩
    · exact (inTree_delete_iff (x := x) (y := s) ht).mpr ⟨hsOld, hsNe⟩
    · intro y hyDeleted hqy
      rcases (inTree_delete_iff (x := x) (y := y) ht).mp hyDeleted with
        ⟨hyOld, hyNe⟩
      exact hLeastOld y hyOld hyNe hqy

/-- No successor remains after deletion exactly when every remaining old key is below the query. -/
theorem successor?_delete_eq_none_iff {x q : Nat} {t : BSTree}
    (ht : Ordered t) :
    successor? q (delete x t) = none ↔
      ∀ y, InTree y t → y ≠ x → y ≤ q := by
  have hDeletedOrdered : Ordered (delete x t) := delete_ordered (x := x) ht
  constructor
  · intro hs y hyOld hyNe
    have hyDeleted : InTree y (delete x t) :=
      (inTree_delete_iff (x := x) (y := y) ht).mpr ⟨hyOld, hyNe⟩
    exact (successor?_eq_none_iff hDeletedOrdered).mp hs y hyDeleted
  · intro hNoGreater
    apply (successor?_eq_none_iff hDeletedOrdered).mpr
    intro y hyDeleted
    rcases (inTree_delete_iff (x := x) (y := y) ht).mp hyDeleted with
      ⟨hyOld, hyNe⟩
    exact hNoGreater y hyOld hyNe

/-- Predecessor after deletion is the greatest old key below the query except the deleted key. -/
theorem predecessor?_delete_eq_some_iff {x q p : Nat} {t : BSTree}
    (ht : Ordered t) :
    predecessor? q (delete x t) = some p ↔
      InTree p t ∧ p ≠ x ∧ p < q ∧
        ∀ y, InTree y t → y ≠ x → y < q → y ≤ p := by
  have hDeletedOrdered : Ordered (delete x t) := delete_ordered (x := x) ht
  constructor
  · intro hp
    rcases (predecessor?_eq_some_iff hDeletedOrdered).mp hp with
      ⟨hpDeleted, hpq, hGreatestDeleted⟩
    rcases (inTree_delete_iff (x := x) (y := p) ht).mp hpDeleted with
      ⟨hpOld, hpNe⟩
    exact ⟨
      hpOld,
      hpNe,
      hpq,
      by
        intro y hyOld hyNe hyq
        have hyDeleted : InTree y (delete x t) :=
          (inTree_delete_iff (x := x) (y := y) ht).mpr ⟨hyOld, hyNe⟩
        exact hGreatestDeleted y hyDeleted hyq
    ⟩
  · intro hpSpec
    rcases hpSpec with ⟨hpOld, hpNe, hpq, hGreatestOld⟩
    apply (predecessor?_eq_some_iff hDeletedOrdered).mpr
    refine ⟨?_, hpq, ?_⟩
    · exact (inTree_delete_iff (x := x) (y := p) ht).mpr ⟨hpOld, hpNe⟩
    · intro y hyDeleted hyq
      rcases (inTree_delete_iff (x := x) (y := y) ht).mp hyDeleted with
        ⟨hyOld, hyNe⟩
      exact hGreatestOld y hyOld hyNe hyq

/-- No predecessor remains after deletion exactly when every remaining old key is above the query. -/
theorem predecessor?_delete_eq_none_iff {x q : Nat} {t : BSTree}
    (ht : Ordered t) :
    predecessor? q (delete x t) = none ↔
      ∀ y, InTree y t → y ≠ x → q ≤ y := by
  have hDeletedOrdered : Ordered (delete x t) := delete_ordered (x := x) ht
  constructor
  · intro hp y hyOld hyNe
    have hyDeleted : InTree y (delete x t) :=
      (inTree_delete_iff (x := x) (y := y) ht).mpr ⟨hyOld, hyNe⟩
    exact (predecessor?_eq_none_iff hDeletedOrdered).mp hp y hyDeleted
  · intro hNoLesser
    apply (predecessor?_eq_none_iff hDeletedOrdered).mpr
    intro y hyDeleted
    rcases (inTree_delete_iff (x := x) (y := y) ht).mp hyDeleted with
      ⟨hyOld, hyNe⟩
    exact hNoLesser y hyOld hyNe

/-! ## Membership after insertion -/

/-- Insertion adds exactly the inserted key to the tree membership relation. -/
theorem inTree_insert_iff (x y : Nat) (t : BSTree) :
    InTree y (insert x t) ↔ y = x ∨ InTree y t := by
  induction t with
  | empty =>
      simp [insert, InTree]
  | node left key right ihLeft ihRight =>
      by_cases hxkey : x < key
      · simp [insert, InTree, hxkey, ihLeft, or_assoc, or_left_comm]
      · by_cases hkeyx : key < x
        · simp [insert, InTree, hxkey, hkeyx, ihRight, or_left_comm]
        · have hxeq : x = key := by
            exact Nat.le_antisymm (Nat.le_of_not_gt hkeyx) (Nat.le_of_not_gt hxkey)
          subst x
          simp [insert, InTree]

/-- The inserted key is a member of the resulting tree. -/
theorem inTree_insert_self (x : Nat) (t : BSTree) :
    InTree x (insert x t) := by
  exact (inTree_insert_iff x x t).mpr (Or.inl rfl)

/-- Existing members remain members after insertion. -/
theorem inTree_insert_of_inTree {x y : Nat} {t : BSTree}
    (h : InTree y t) : InTree y (insert x t) := by
  exact (inTree_insert_iff x y t).mpr (Or.inr h)

/-! ## Ordering after insertion -/

/-- Insertion preserves an upper-bound invariant when the inserted key satisfies it. -/
theorem allLt_insert {x bound : Nat} {t : BSTree}
    (hx : x < bound) (ht : AllLt bound t) :
    AllLt bound (insert x t) := by
  intro y hy
  rcases (inTree_insert_iff x y t).mp hy with rfl | hyold
  · exact hx
  · exact ht y hyold

/-- Insertion preserves a lower-bound invariant when the inserted key satisfies it. -/
theorem allGt_insert {x bound : Nat} {t : BSTree}
    (hx : bound < x) (ht : AllGt bound t) :
    AllGt bound (insert x t) := by
  intro y hy
  rcases (inTree_insert_iff x y t).mp hy with rfl | hyold
  · exact hx
  · exact ht y hyold

/-- Functional BST insertion preserves the binary-search-tree ordering invariant. -/
theorem insert_ordered {x : Nat} {t : BSTree}
    (ht : Ordered t) : Ordered (insert x t) := by
  induction t with
  | empty =>
      simp [insert, Ordered, AllLt, AllGt, InTree]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      by_cases hxkey : x < key
      · simp [insert, Ordered, hxkey]
        exact ⟨ihLeft hLeft, hRight, allLt_insert hxkey hLt, hGt⟩
      · by_cases hkeyx : key < x
        · simp [insert, Ordered, hxkey, hkeyx]
          exact ⟨hLeft, ihRight hRight, hLt, allGt_insert hkeyx hGt⟩
        · simp [insert, Ordered, hxkey, hkeyx, hLeft, hRight, hLt, hGt]

/-- Searching after insertion succeeds exactly for the inserted key or an old key. -/
theorem search_insert_eq_true_iff {x y : Nat} {t : BSTree}
    (ht : Ordered t) :
    search y (insert x t) = true ↔ y = x ∨ search y t = true := by
  have hInsertedOrdered : Ordered (insert x t) := insert_ordered (x := x) ht
  constructor
  · intro hSearch
    have hyInserted : InTree y (insert x t) :=
      (search_eq_true_iff hInsertedOrdered).mp hSearch
    rcases (inTree_insert_iff x y t).mp hyInserted with hyEq | hyOld
    · exact Or.inl hyEq
    · exact Or.inr ((search_eq_true_iff ht).mpr hyOld)
  · intro h
    have hyInserted : InTree y (insert x t) := by
      rcases h with hyEq | hySearch
      · subst y
        exact inTree_insert_self x t
      · exact inTree_insert_of_inTree ((search_eq_true_iff ht).mp hySearch)
    exact (search_eq_true_iff hInsertedOrdered).mpr hyInserted

/-! ## Parent-pointer refinement via Zipper

This section adds a zipper (cursor) layer that encodes parent-pointers in
pure functional style.  The zipper does not touch the existing {lit}`BSTree` type
or its 30+ proved theorems.  Every new operation is proved equivalent to its
functional counterpart via the {lit}`toTree` bridge.

**CLRS correspondence:**

- {lit}`Zipper` : cursor with a path from the root to the current node (implicit
  parent pointers)
- {lit}`searchZipper` : iterative {lit}`TREE-SEARCH` (CLRS Figure 12.2)
- {lit}`transplant` : {lit}`TRANSPLANT(T, u, v)` (CLRS Section 12.3)
- {lit}`deleteViaTransplant` : {lit}`TREE-DELETE` using transplant
- {lit}`successorZipper` / {lit}`predecessorZipper` : successor/predecessor with parent
  pointer ascent

Main results:

- Theorem {lit}`searchZipper_toTree` : the zipper is a view, not a mutation
- Theorem {lit}`searchIter_eq_search` : iterative search matches functional search
- Theorem {lit}`transplant_preserves_ordered` : TRANSPLANT preserves BST ordering
- Theorem {lit}`deleteViaTransplant_eq_delete` : TREE-DELETE using transplant
  matches functional {lit}`delete`
- Theorem {lit}`successorZipper_eq_successor?` : parent-pointer successor matches
  functional successor
-/

/-- A stack frame recording one descent step: direction, the parent key, and
the sibling subtree that was not taken. -/
inductive Frame where
  | fromLeft  (parentKey : Nat) (rightSibling : BSTree)
  | fromRight (parentKey : Nat) (leftSibling  : BSTree)

/-- Reconstruct the parent node from a frame and a replacement child. -/
def Frame.plug (fr : Frame) (t : BSTree) : BSTree :=
  match fr with
  | .fromLeft  pk rs => .node t pk rs
  | .fromRight pk ls => .node ls pk t

/-- A zipper: cursor with a path from the root to the current focus.
The {lit}`ctx` list is a stack — the head is the immediate parent frame.
{lit}`toTree` reconstructs the full tree by folding {lit}`plug` bottom-up. -/
structure Zipper where
  focus : BSTree
  ctx   : List Frame

/-- Reconstruct the full tree from a zipper by folding frames bottom-up. -/
def Zipper.toTree (z : Zipper) : BSTree :=
  z.ctx.foldl (fun t fr => fr.plug t) z.focus

/-- The key bound immediately above the focus (or {lit}`none` if at root or
descended right). -/
def Zipper.upperBound? (z : Zipper) : Option Nat :=
  match z.ctx.head? with
  | none => none
  | some (.fromLeft pk _) => some pk
  | some (.fromRight _ _) => none

/-- The key bound immediately below the focus (or {lit}`none` if at root or
descended left). -/
def Zipper.lowerBound? (z : Zipper) : Option Nat :=
  match z.ctx.head? with
  | none => none
  | some (.fromRight pk _) => some pk
  | some (.fromLeft _ _) => none

/-- A local validity helper: the reconstructed tree is ordered and the focus
respects the optional bounds contributed by its immediate parent frame.  The
full-context replacement theorem below states the stronger hypotheses it uses
explicitly. -/
def Zipper.Valid (z : Zipper) : Prop :=
  Ordered z.toTree ∧
  (match z.upperBound? with
  | none => True
  | some pk => AllLt pk z.focus) ∧
  (match z.lowerBound? with
  | none => True
  | some pk => AllGt pk z.focus)

/-! ### Iterative search (CLRS Figure 12.2) -/

/-- Whether a tree is a nonempty node. -/
def nonempty : BSTree → Bool
  | .empty => false
  | .node _ _ _ => true

/-- Auxiliary iterative search: descend the tree, pushing a frame for each
direction taken.  Structural recursion on the tree; {lit}`ctx` accumulates the path. -/
def searchZipperAux (x : Nat) : BSTree → List Frame → Zipper
  | .empty, ctx => ⟨.empty, ctx⟩
  | .node l k r, ctx =>
    if x = k then ⟨.node l k r, ctx⟩
    else if x < k then searchZipperAux x l (.fromLeft k r :: ctx)
    else searchZipperAux x r (.fromRight k l :: ctx)

/-- Iterative zipper search from a tree root.  Returns a zipper whose focus is
the node found (or {lit}`empty` if absent). -/
def searchZipper (x : Nat) (t : BSTree) : Zipper :=
  searchZipperAux x t []

/-- Iterative Boolean search via the zipper. -/
def searchIter (x : Nat) (t : BSTree) : Bool :=
  (searchZipper x t).focus.nonempty

/-! ### Correctness of iterative search (AC-1, AC-2) -/

/-- Descending and pushing frames does not change the reconstructed tree. -/
theorem searchZipperAux_toTree (x : Nat) (t : BSTree) (ctx : List Frame) :
    (searchZipperAux x t ctx).toTree = (Zipper.mk t ctx).toTree := by
  induction t generalizing ctx with
  | empty => rfl
  | node l k r ih_l ih_r =>
    dsimp [searchZipperAux]
    by_cases h_eq : x = k
    · simp [h_eq]
    · by_cases h_lt : x < k
      · simp only [if_neg h_eq, if_pos h_lt]
        rw [ih_l (.fromLeft k r :: ctx)]
        simp [Zipper.toTree, Frame.plug]
      · simp only [if_neg h_eq, if_neg h_lt]
        rw [ih_r (.fromRight k l :: ctx)]
        simp [Zipper.toTree, Frame.plug]

/-- The zipper is a view: reconstructing from a search zipper recovers the
original tree (AC-1). -/
theorem searchZipper_toTree (x : Nat) (t : BSTree) :
    (searchZipper x t).toTree = t := by
  rw [searchZipper, searchZipperAux_toTree]
  simp [Zipper.toTree]

/-- Iterative search matches the existing functional {lit}`search` (AC-2). -/
theorem searchIter_eq_search (x : Nat) (t : BSTree) :
    searchIter x t = search x t := by
  dsimp [searchIter, searchZipper]
  suffices h : ∀ ctx, (searchZipperAux x t ctx).focus.nonempty = search x t by
    exact h []
  intro ctx
  induction t generalizing ctx with
  | empty => rfl
  | node l k r ih_l ih_r =>
    dsimp [searchZipperAux, search]
    by_cases h_eq : x = k
    · simp [h_eq, nonempty]
    · by_cases h_lt : x < k
      · simp only [if_neg h_eq, if_pos h_lt]
        exact ih_l (.fromLeft k r :: ctx)
      · simp only [if_neg h_eq, if_neg h_lt]
        exact ih_r (.fromRight k l :: ctx)

/-! ### TRANSPLANT and ordering preservation (AC-3) -/

/-- {lit}`AllLt` distributes over a node. -/
theorem allLt_node {b k : Nat} {l r : BSTree} :
    AllLt b (node l k r) ↔ k < b ∧ AllLt b l ∧ AllLt b r := by
  constructor
  · intro h
    exact ⟨h k (Or.inl rfl),
      fun y hy => h y (Or.inr (Or.inl hy)),
      fun y hy => h y (Or.inr (Or.inr hy))⟩
  · rintro ⟨hk, hl, hr⟩ y hy
    have hy' : y = k ∨ InTree y l ∨ InTree y r := hy
    rcases hy' with rfl | hyl | hyr
    · exact hk
    · exact hl y hyl
    · exact hr y hyr

/-- {lit}`AllGt` distributes over a node. -/
theorem allGt_node {b k : Nat} {l r : BSTree} :
    AllGt b (node l k r) ↔ b < k ∧ AllGt b l ∧ AllGt b r := by
  constructor
  · intro h
    exact ⟨h k (Or.inl rfl),
      fun y hy => h y (Or.inr (Or.inl hy)),
      fun y hy => h y (Or.inr (Or.inr hy))⟩
  · rintro ⟨hk, hl, hr⟩ y hy
    have hy' : y = k ∨ InTree y l ∨ InTree y r := hy
    rcases hy' with rfl | hyl | hyr
    · exact hk
    · exact hl y hyl
    · exact hr y hyr

/-- Reconstruction peels one frame off the top of the context. -/
theorem toTree_cons (t : BSTree) (fr : Frame) (rest : List Frame) :
    (Zipper.mk t (fr :: rest)).toTree = (Zipper.mk (fr.plug t) rest).toTree := by
  simp [Zipper.toTree]

/-- Reconstruction from an empty context is the focus itself. -/
theorem toTree_nil (t : BSTree) : (Zipper.mk t []).toTree = t := by
  simp [Zipper.toTree]

/-- If a reconstructed tree is ordered, so is the focus (ordering is
hereditary downward through the context). -/
theorem ordered_focus_of_ordered_toTree (t : BSTree) (ctx : List Frame)
    (h : Ordered (Zipper.mk t ctx).toTree) : Ordered t := by
  induction ctx generalizing t with
  | nil => simpa [toTree_nil] using h
  | cons fr rest ih =>
    rw [toTree_cons] at h
    have hplug : Ordered (fr.plug t) := ih (fr.plug t) h
    cases fr with
    | fromLeft pk rs =>
      simp only [Frame.plug, Ordered] at hplug
      exact hplug.1
    | fromRight pk ls =>
      simp only [Frame.plug, Ordered] at hplug
      exact hplug.2.1

/-- **Core ordering-preservation lemma.**  Replacing the focus subtree with a
new subtree whose keys respect the same bounds as the old focus preserves the
ordering of the whole reconstructed tree. -/
theorem toTree_ordered_of_subrange :
    ∀ (ctx : List Frame) (focus newFocus : BSTree),
    Ordered (Zipper.mk focus ctx).toTree →
    Ordered newFocus →
    (∀ b, AllLt b focus → AllLt b newFocus) →
    (∀ b, AllGt b focus → AllGt b newFocus) →
    Ordered (Zipper.mk newFocus ctx).toTree := by
  intro ctx
  induction ctx with
  | nil =>
    intro focus newFocus _ hNew _ _
    simpa [toTree_nil] using hNew
  | cons fr rest ih =>
    intro focus newFocus hOrd hNew hLt hGt
    rw [toTree_cons] at hOrd ⊢
    cases fr with
    | fromLeft pk rs =>
      simp only [Frame.plug] at hOrd ⊢
      have hNodeOrd : Ordered (node focus pk rs) :=
        ordered_focus_of_ordered_toTree _ _ hOrd
      simp only [Ordered] at hNodeOrd
      obtain ⟨hFocusOrd, hRsOrd, hLtFocus, hGtRs⟩ := hNodeOrd
      have hNewNodeOrd : Ordered (node newFocus pk rs) := by
        simp only [Ordered]
        exact ⟨hNew, hRsOrd, hLt pk hLtFocus, hGtRs⟩
      refine ih (node focus pk rs) (node newFocus pk rs) hOrd hNewNodeOrd ?_ ?_
      · intro b hb
        rw [allLt_node] at hb ⊢
        exact ⟨hb.1, hLt b hb.2.1, hb.2.2⟩
      · intro b hb
        rw [allGt_node] at hb ⊢
        exact ⟨hb.1, hGt b hb.2.1, hb.2.2⟩
    | fromRight pk ls =>
      simp only [Frame.plug] at hOrd ⊢
      have hNodeOrd : Ordered (node ls pk focus) :=
        ordered_focus_of_ordered_toTree _ _ hOrd
      simp only [Ordered] at hNodeOrd
      obtain ⟨hLsOrd, hFocusOrd, hLtLs, hGtFocus⟩ := hNodeOrd
      have hNewNodeOrd : Ordered (node ls pk newFocus) := by
        simp only [Ordered]
        exact ⟨hLsOrd, hNew, hLtLs, hGt pk hGtFocus⟩
      refine ih (node ls pk focus) (node ls pk newFocus) hOrd hNewNodeOrd ?_ ?_
      · intro b hb
        rw [allLt_node] at hb ⊢
        exact ⟨hb.1, hb.2.1, hLt b hb.2.2⟩
      · intro b hb
        rw [allGt_node] at hb ⊢
        exact ⟨hb.1, hb.2.1, hGt b hb.2.2⟩

/-- {lit}`TRANSPLANT(T, u, v)`: replace the subtree under the cursor {lit}`z` with
{lit}`newFocus`, reconstructing the full tree.  Matches CLRS Section 12.3. -/
def transplant (z : Zipper) (newFocus : BSTree) : BSTree :=
  (Zipper.mk newFocus z.ctx).toTree

/-- **AC-3.** TRANSPLANT preserves the BST ordering invariant when the new
subtree respects the same key bounds as the replaced focus. -/
theorem transplant_preserves_ordered (z : Zipper) (newFocus : BSTree)
    (hOrd : Ordered z.toTree) (hNewOrd : Ordered newFocus)
    (hLt : ∀ b, AllLt b z.focus → AllLt b newFocus)
    (hGt : ∀ b, AllGt b z.focus → AllGt b newFocus) :
    Ordered (transplant z newFocus) := by
  have hz : z.toTree = (Zipper.mk z.focus z.ctx).toTree := rfl
  rw [hz] at hOrd
  exact toTree_ordered_of_subrange z.ctx z.focus newFocus hOrd hNewOrd hLt hGt

/-! ### TREE-DELETE via TRANSPLANT (AC-4) -/

/-- CLRS {lit}`TREE-DELETE` using TRANSPLANT (Figure 12.4).

{lit}`ctx` accumulates the path from the root (the parent-pointer chain); the
top-level call starts with {lit}`ctx = []`.  On reaching the target node the local
replacement subtree is spliced back into the full tree by {lit}`transplant`
(the CLRS TRANSPLANT operation), which is precisely the parent-pointer
rewiring step.  The local replacement follows the same successor-replacement
discipline as the functional {lit}`deleteRoot`: if the right child is empty, splice
the left child; otherwise replace the key with its successor ({lit}`minKey` of the
right subtree) and delete that successor from the right subtree. -/
def deleteViaTransplant (x : Nat) : BSTree → List Frame → BSTree
  | .empty, ctx => (Zipper.mk .empty ctx).toTree
  | .node l k r, ctx =>
    if x < k then deleteViaTransplant x l (.fromLeft k r :: ctx)
    else if k < x then deleteViaTransplant x r (.fromRight k l :: ctx)
    else
      match r with
      | .empty => transplant ⟨node l k r, ctx⟩ l
      | .node _ _ _ => transplant ⟨node l k r, ctx⟩ (node l (minKey r) (deleteMin r))

/-- Reconstructing the delete-via-transplant result equals plugging the
functional {lit}`delete` result into the same context. -/
theorem deleteViaTransplant_eq_toTree_delete (x : Nat) :
    ∀ (t : BSTree) (ctx : List Frame),
    deleteViaTransplant x t ctx = (Zipper.mk (delete x t) ctx).toTree := by
  intro t
  induction t with
  | empty => intro ctx; simp [deleteViaTransplant, delete]
  | node l k r ih_l ih_r =>
    intro ctx
    simp only [deleteViaTransplant, delete]
    by_cases h_lt : x < k
    · simp only [if_pos h_lt]
      rw [ih_l (.fromLeft k r :: ctx), toTree_cons]
      simp [Frame.plug]
    · by_cases h_gt : k < x
      · simp only [if_neg h_lt, if_pos h_gt]
        rw [ih_r (.fromRight k l :: ctx), toTree_cons]
        simp [Frame.plug]
      · simp only [if_neg h_lt, if_neg h_gt]
        cases r with
        | empty =>
          simp [transplant, deleteRoot]
        | node rl rk rr =>
          simp [transplant, deleteRoot]

/-- **AC-4.** TREE-DELETE using transplant equals the functional {lit}`delete`. -/
theorem deleteViaTransplant_eq_delete (x : Nat) (t : BSTree) :
    deleteViaTransplant x t [] = delete x t := by
  rw [deleteViaTransplant_eq_toTree_delete, toTree_nil]

/-! ### Successor and predecessor via parent-pointer ascent (AC-5) -/

/-- Combine a primary option with a fallback (the successor found by ascending
the parent chain). -/
def orFb : Option Nat → Option Nat → Option Nat
  | some y, _ => some y
  | none, fb => fb

/-- Ascend the parent chain looking for the nearest ancestor reached from a
left child; its key is the successor when the focus has no right subtree.
Mirrors CLRS TREE-SUCCESSOR's upward walk. -/
def ascendSuccessor : List Frame → Option Nat
  | [] => none
  | .fromLeft pk _ :: _ => some pk
  | .fromRight _ _ :: rest => ascendSuccessor rest

/-- Ascend the parent chain looking for the nearest ancestor reached from a
right child; its key is the predecessor when the focus has no left subtree. -/
def ascendPredecessor : List Frame → Option Nat
  | [] => none
  | .fromRight pk _ :: _ => some pk
  | .fromLeft _ _ :: rest => ascendPredecessor rest

/-- When every key of {lit}`t` is greater than {lit}`x`, the functional successor of {lit}`x`
is the minimum of {lit}`t`. -/
theorem successor?_eq_minimum?_of_allGt {x : Nat} {t : BSTree}
    (ht : Ordered t) (hgt : AllGt x t) : successor? x t = minimum? t := by
  induction t with
  | empty => simp [successor?, minimum?]
  | node l k r ih_l _ih_r =>
    simp only [Ordered] at ht
    obtain ⟨hlO, _hrO, _hlLt, _hrGt⟩ := ht
    have hxk : x < k := hgt k (Or.inl rfl)
    have hxl : AllGt x l := fun y hy => hgt y (Or.inr (Or.inl hy))
    simp only [successor?, if_pos hxk]
    cases l with
    | empty => simp [successor?, minimum?]
    | node ll lk lr =>
      rw [ih_l hlO hxl]
      have hmin : minimum? (node ll lk lr) = some (minKey (node ll lk lr)) :=
        minimum?_eq_some_minKey (node_ne_empty ll lk lr)
      rw [hmin]
      simp [minimum?, hmin]

/-- A total maximum-key operation (dummy on the empty tree), mirroring
{lit}`minKey`. -/
def maxKey : BSTree → Nat
  | empty => 0
  | node _left key empty => key
  | node _left _key right@(node _ _ _) => maxKey right

/-- On nonempty trees, {lit}`maxKey` agrees with {lit}`maximum?`. -/
theorem maximum?_eq_some_maxKey {t : BSTree} (h : t ≠ empty) :
    maximum? t = some (maxKey t) := by
  induction t with
  | empty => exact (h rfl).elim
  | node left key right _ihLeft ihRight =>
    cases right with
    | empty => simp [maximum?, maxKey]
    | node rl rk rr =>
      have hne : node rl rk rr ≠ empty := node_ne_empty rl rk rr
      simpa [maximum?, maxKey] using ihRight hne

/-- When every key of {lit}`t` is less than {lit}`x`, the functional predecessor of {lit}`x`
is the maximum of {lit}`t`. -/
theorem predecessor?_eq_maximum?_of_allLt {x : Nat} {t : BSTree}
    (ht : Ordered t) (hlt : AllLt x t) : predecessor? x t = maximum? t := by
  induction t with
  | empty => simp [predecessor?, maximum?]
  | node l k r _ih_l ih_r =>
    simp only [Ordered] at ht
    obtain ⟨_hlO, hrO, _hlLt, _hrGt⟩ := ht
    have hkx : k < x := hlt k (Or.inl rfl)
    have hxr : AllLt x r := fun y hy => hlt y (Or.inr (Or.inr hy))
    simp only [predecessor?, if_pos hkx]
    cases r with
    | empty => simp [predecessor?, maximum?]
    | node rl rk rr =>
      rw [ih_r hrO hxr]
      have hmax : maximum? (node rl rk rr) = some (maxKey (node rl rk rr)) :=
        maximum?_eq_some_maxKey (node_ne_empty rl rk rr)
      rw [hmax]
      simp [maximum?, hmax]

/-- Successor of the focus node: minimum of the right subtree if present,
otherwise the successor found by ascending the parent chain. -/
def zsucc (z : Zipper) : Option Nat :=
  match z.focus with
  | .empty => none
  | .node _ _ r =>
    match r with
    | .empty => ascendSuccessor z.ctx
    | .node _ _ _ => minimum? r

/-- Predecessor of the focus node: maximum of the left subtree if present,
otherwise the predecessor found by ascending the parent chain. -/
def zpred (z : Zipper) : Option Nat :=
  match z.focus with
  | .empty => none
  | .node l _ _ =>
    match l with
    | .empty => ascendPredecessor z.ctx
    | .node _ _ _ => maximum? l

/-- Parent-pointer successor query: descend to {lit}`x`, then use the right subtree
or ascend. -/
def successorZipper (x : Nat) (t : BSTree) : Option Nat := zsucc (searchZipper x t)

/-- Parent-pointer predecessor query: descend to {lit}`x`, then use the left subtree
or ascend. -/
def predecessorZipper (x : Nat) (t : BSTree) : Option Nat := zpred (searchZipper x t)

/-- Bridge: the parent-pointer successor computed while descending with an
accumulated context equals the functional successor, falling back to the
ascent value stored in the context. -/
theorem successorZipper_bridge (x : Nat) :
    ∀ (t : BSTree) (ctx : List Frame), Ordered t → InTree x t →
    zsucc (searchZipperAux x t ctx) = orFb (successor? x t) (ascendSuccessor ctx) := by
  intro t
  induction t with
  | empty => intro ctx _ hx; exact absurd hx (by simp [InTree])
  | node l k r ih_l ih_r =>
    intro ctx ht hx
    simp only [Ordered] at ht
    obtain ⟨hlO, hrO, hlLt, hrGt⟩ := ht
    by_cases hxk : x = k
    · subst hxk
      have hfocus : searchZipperAux x (node l x r) ctx = ⟨node l x r, ctx⟩ := by
        simp [searchZipperAux]
      rw [hfocus]
      simp only [zsucc]
      cases r with
      | empty =>
        simp [successor?, orFb]
      | node rl rk rr =>
        have hsucc : successor? x (node rl rk rr) = minimum? (node rl rk rr) :=
          successor?_eq_minimum?_of_allGt hrO hrGt
        have hmin : minimum? (node rl rk rr) = some (minKey (node rl rk rr)) :=
          minimum?_eq_some_minKey (node_ne_empty rl rk rr)
        have houter : successor? x (node l x (node rl rk rr))
            = successor? x (node rl rk rr) := by
          simp [successor?]
        rw [houter, hsucc, hmin]
        simp [orFb]
    · by_cases hxlt : x < k
      · have hxInl : InTree x l := by
          have hx' : x = k ∨ InTree x l ∨ InTree x r := hx
          rcases hx' with h | h | h
          · exact absurd h hxk
          · exact h
          · exact absurd (hrGt x h) (Nat.not_lt.mpr (Nat.le_of_lt hxlt))
        have hstep : searchZipperAux x (node l k r) ctx
            = searchZipperAux x l (.fromLeft k r :: ctx) := by
          simp [searchZipperAux, hxk, hxlt]
        rw [hstep, ih_l (.fromLeft k r :: ctx) hlO hxInl]
        simp only [successor?, if_pos hxlt, ascendSuccessor]
        cases hsl : successor? x l with
        | none => simp [orFb]
        | some y => simp [orFb]
      · have hkx : k < x := by omega
        have hxInr : InTree x r := by
          have hx' : x = k ∨ InTree x l ∨ InTree x r := hx
          rcases hx' with h | h | h
          · exact absurd h hxk
          · exact absurd (hlLt x h) (Nat.not_lt.mpr (Nat.le_of_lt hkx))
          · exact h
        have hstep : searchZipperAux x (node l k r) ctx
            = searchZipperAux x r (.fromRight k l :: ctx) := by
          simp [searchZipperAux, hxk, hxlt]
        rw [hstep, ih_r (.fromRight k l :: ctx) hrO hxInr]
        simp only [successor?, if_neg hxlt, ascendSuccessor]

/-- **AC-5 (successor).** Parent-pointer successor matches the functional
successor on ordered trees, for keys present in the tree. -/
theorem successorZipper_eq_successor? (x : Nat) (t : BSTree)
    (ht : Ordered t) (hx : InTree x t) :
    successorZipper x t = successor? x t := by
  simp only [successorZipper, searchZipper]
  rw [successorZipper_bridge x t [] ht hx]
  cases successor? x t <;> simp [ascendSuccessor, orFb]

/-- Bridge for predecessor: parent-pointer predecessor while descending equals
the functional predecessor, falling back to the ascent value. -/
theorem predecessorZipper_bridge (x : Nat) :
    ∀ (t : BSTree) (ctx : List Frame), Ordered t → InTree x t →
    zpred (searchZipperAux x t ctx) = orFb (predecessor? x t) (ascendPredecessor ctx) := by
  intro t
  induction t with
  | empty => intro ctx _ hx; exact absurd hx (by simp [InTree])
  | node l k r ih_l ih_r =>
    intro ctx ht hx
    simp only [Ordered] at ht
    obtain ⟨hlO, hrO, hlLt, hrGt⟩ := ht
    by_cases hxk : x = k
    · subst hxk
      have hfocus : searchZipperAux x (node l x r) ctx = ⟨node l x r, ctx⟩ := by
        simp [searchZipperAux]
      rw [hfocus]
      simp only [zpred]
      cases l with
      | empty =>
        simp [predecessor?, orFb]
      | node ll lk lr =>
        have hpred : predecessor? x (node ll lk lr) = maximum? (node ll lk lr) :=
          predecessor?_eq_maximum?_of_allLt hlO hlLt
        have hmax : maximum? (node ll lk lr) = some (maxKey (node ll lk lr)) :=
          maximum?_eq_some_maxKey (node_ne_empty ll lk lr)
        have houter : predecessor? x (node (node ll lk lr) x r)
            = predecessor? x (node ll lk lr) := by
          simp [predecessor?]
        rw [houter, hpred, hmax]
        simp [orFb]
    · by_cases hxlt : x < k
      · have hxInl : InTree x l := by
          have hx' : x = k ∨ InTree x l ∨ InTree x r := hx
          rcases hx' with h | h | h
          · exact absurd h hxk
          · exact h
          · exact absurd (hrGt x h) (Nat.not_lt.mpr (Nat.le_of_lt hxlt))
        have hstep : searchZipperAux x (node l k r) ctx
            = searchZipperAux x l (.fromLeft k r :: ctx) := by
          simp [searchZipperAux, hxk, hxlt]
        rw [hstep, ih_l (.fromLeft k r :: ctx) hlO hxInl]
        have hkx : ¬ k < x := by omega
        simp only [predecessor?, if_neg hkx, ascendPredecessor]
      · have hkx : k < x := by omega
        have hxInr : InTree x r := by
          have hx' : x = k ∨ InTree x l ∨ InTree x r := hx
          rcases hx' with h | h | h
          · exact absurd h hxk
          · exact absurd (hlLt x h) (Nat.not_lt.mpr (Nat.le_of_lt hkx))
          · exact h
        have hstep : searchZipperAux x (node l k r) ctx
            = searchZipperAux x r (.fromRight k l :: ctx) := by
          simp [searchZipperAux, hxk, hxlt]
        rw [hstep, ih_r (.fromRight k l :: ctx) hrO hxInr]
        simp only [predecessor?, if_pos hkx, ascendPredecessor]
        cases hpr : predecessor? x r with
        | none => simp [orFb]
        | some y => simp [orFb]

/-- **AC-5 (predecessor).** Parent-pointer predecessor matches the functional
predecessor on ordered trees, for keys present in the tree. -/
theorem predecessorZipper_eq_predecessor? (x : Nat) (t : BSTree)
    (ht : Ordered t) (hx : InTree x t) :
    predecessorZipper x t = predecessor? x t := by
  simp only [predecessorZipper, searchZipper]
  rw [predecessorZipper_bridge x t [] ht hx]
  cases predecessor? x t <;> simp [ascendPredecessor, orFb]

/-! ## Imperative pointer-heap refinement (Issue #25)

The zipper layer above encodes parent pointers in pure functional style but never
mutates a cell.  This section adds the next refinement layer: an explicit
**pointer heap** of node records with mutable {lit}`left`, {lit}`right`, and
{lit}`parent` fields, in the style of the CLRS pointer machine, and proves that
the imperative {lit}`TRANSPLANT` operation — which rewires child and parent
pointers in place — refines the functional subtree-replacement specification.

**Model.**  A {lit}`Node` is a record with a key and three optional pointers
({lit}`none` is the CLRS {lit}`NIL`).  A {lit}`Store` is a finite map (a
{lit}`Std.HashMap`) from node identifiers to records; this is the addressable
heap where {lit}`x.left`, {lit}`x.right`, {lit}`x.p` are physical cells.  The
abstraction relation {lit}`RepresentsW s p t S` says that reading the heap {lit}`s`
downward from pointer {lit}`p` (following child links, ignoring parent links)
yields the functional tree {lit}`t`, with {lit}`S` the finite set of node ids used;
the relation bakes in the acyclicity/no-sharing invariant ({lit}`i ∉ Sl`, {lit}`i ∉ Sr`,
{lit}`Disjoint Sl Sr`), which is exactly the disjointness needed to reason about
in-place mutation.

**CLRS correspondence.**

- {lit}`Node` / {lit}`Store` : the pointer-machine node records and heap (AC-1)
- {lit}`RepresentsW` : the heap-to-tree abstraction function, with sharing ruled out
- {lit}`transplantChild` : the pointer-rewiring core of {lit}`TRANSPLANT(T, u, v)`
  (CLRS Section 12.3), swinging a parent's child pointer and reparenting the new
  subtree
- {lit}`insertPointer_right_representsW` : the pointer-level {lit}`TREE-INSERT` leaf
  attachment (CLRS Section 12.3)

Main results:

- Theorem {lit}`RepresentsW.tree_unique` : the heap and root pointer determine a
  unique functional tree (the abstraction is a function, i.e. the imperative
  state is observationally a BST)
- Theorem {lit}`RepresentsW.set_of_not_mem` : writing a cell outside a subtree's id
  set does not change what that subtree represents (the pointer frame rule)
- Theorem {lit}`RepresentsW.of_agreeChild` : representation depends only on
  key/left/right cells, so parent-pointer writes are invisible to downward reading
- Theorem {lit}`transplantChild_left_representsW` /
  {lit}`transplantChild_right_representsW` : in-place {lit}`TRANSPLANT` refines
  functional subtree replacement (AC-2)
- Theorem {lit}`insertPointer_right_representsW` : attaching a freshly allocated leaf
  cell refines functional subtree replacement (AC-3, leaf case)
-/

/-- A heap node record: a key together with explicit {lit}`left`, {lit}`right`, and
{lit}`parent` pointers.  Pointers are {lit}`Option Nat` node identifiers, with
{lit}`none` playing the role of the CLRS {lit}`NIL` sentinel. -/
structure Node where
  key    : Nat
  left   : Option Nat
  right  : Option Nat
  parent : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-- A pointer heap: a finite map from node identifiers to records.  This is the
CLRS pointer machine's addressable memory, where a node's {lit}`left`, {lit}`right`,
and {lit}`parent` are mutable cells reachable by identifier.  It is backed by a
{lit}`Std.HashMap`; all reasoning goes through {lit}`get` and {lit}`set` and the two
rewrite lemmas {lit}`get_set_self` and {lit}`get_set_ne`. -/
structure Store where
  map : Std.HashMap Nat Node

/-- Read the record stored at an address, or {lit}`none` if unallocated. -/
def Store.get (s : Store) (i : Nat) : Option Node := s.map[i]?

/-- Write (allocate or overwrite) the record at an address. -/
def Store.set (s : Store) (i : Nat) (nd : Node) : Store := ⟨s.map.insert i nd⟩

/-- Reading the address just written returns the written record. -/
@[simp] theorem Store.get_set_self (s : Store) (i : Nat) (nd : Node) :
    (s.set i nd).get i = some nd := by
  simp [Store.get, Store.set]

/-- Writing one address does not affect reads at any other address. -/
theorem Store.get_set_ne {s : Store} {i j : Nat} {nd : Node} (h : i ≠ j) :
    (s.set i nd).get j = s.get j := by
  simp only [Store.get, Store.set, Std.HashMap.getElem?_insert]
  split
  · next hbeq => exact absurd (by simpa using hbeq) h
  · rfl

/-- The heap-to-tree abstraction relation.  {lit}`RepresentsW s p t S` holds when
following child pointers in the heap {lit}`s` from the pointer {lit}`p` yields the
functional tree {lit}`t`, using exactly the node ids in the finite set {lit}`S`.
The side conditions {lit}`i ∉ Sl`, {lit}`i ∉ Sr`, and {lit}`Disjoint Sl Sr` bake in the
BST-layout invariant that no cell is shared between a node and its subtrees or
across the two subtrees — the pointer-model analogue of acyclicity. -/
inductive RepresentsW (s : Store) : Option Nat → BSTree → Finset Nat → Prop where
  | nil : RepresentsW s none BSTree.empty ∅
  | node {i k : Nat} {lp rp pp : Option Nat} {l r : BSTree} {Sl Sr : Finset Nat}
      (hget : s.get i = some ⟨k, lp, rp, pp⟩)
      (hl : RepresentsW s lp l Sl)
      (hr : RepresentsW s rp r Sr)
      (hil : i ∉ Sl) (hir : i ∉ Sr) (hd : Disjoint Sl Sr) :
      RepresentsW s (some i) (BSTree.node l k r) (Insert.insert i (Sl ∪ Sr))

/-- **Faithfulness.**  The heap together with a root pointer determines a unique
functional tree: the abstraction {lit}`RepresentsW` is a partial function of the
heap state.  Consequently the imperative pointer state is observationally exactly
one binary search tree. -/
theorem RepresentsW.tree_unique {s : Store} :
    ∀ {p : Option Nat} {t1 S1 t2 S2}, RepresentsW s p t1 S1 →
      RepresentsW s p t2 S2 → t1 = t2 := by
  intro p t1 S1 t2 S2 h1
  induction h1 generalizing t2 S2 with
  | nil =>
    intro h2
    cases h2 with
    | nil => rfl
  | @node i k lp rp pp l r Sl Sr hget hl hr hil hir hd ihl ihr =>
    intro h2
    cases h2 with
    | @node _ k2 lp2 rp2 pp2 l2 r2 Sl2 Sr2 hget2 hl2 hr2 _ _ _ =>
      rw [hget] at hget2
      injection hget2 with hrec
      injection hrec with hk hlp hrp _
      subst hk; subst hlp; subst hrp
      rw [ihl hl2, ihr hr2]

/-- **Pointer frame rule.**  Overwriting a cell whose id is outside a subtree's id
set leaves the subtree's abstraction unchanged.  This is the workhorse for
reasoning that a local pointer write does not disturb untouched subtrees. -/
theorem RepresentsW.set_of_not_mem {s : Store} {p : Option Nat} {t : BSTree}
    {S : Finset Nat} (h : RepresentsW s p t S) {w : Nat} {nd : Node} :
    w ∉ S → RepresentsW (s.set w nd) p t S := by
  induction h with
  | nil => intro _; exact RepresentsW.nil
  | @node i k lp rp pp l r Sl Sr hget hl hr hil hir hd ihl ihr =>
    intro hw
    simp only [Finset.mem_insert, Finset.mem_union, not_or] at hw
    obtain ⟨hwi, hwl, hwr⟩ := hw
    have hget' : (s.set w nd).get i = some ⟨k, lp, rp, pp⟩ := by
      rw [Store.get_set_ne hwi]; exact hget
    exact RepresentsW.node hget' (ihl hwl) (ihr hwr) hil hir hd

/-- Two heaps agree on child structure when, at every address, they store records
with the same key, left, and right pointers (the parent field may differ). -/
def Store.AgreeChild (s s' : Store) : Prop :=
  ∀ i k lp rp pp, s.get i = some ⟨k, lp, rp, pp⟩ → ∃ pp', s'.get i = some ⟨k, lp, rp, pp'⟩

/-- Every heap agrees with itself on child structure. -/
theorem Store.AgreeChild.refl (s : Store) : Store.AgreeChild s s :=
  fun _ _ _ _ pp hi => ⟨pp, hi⟩

/-- **Parent-write invisibility.**  Downward reading ignores parent pointers, so a
heap agreeing on child structure represents the same tree.  This is what lets the
{lit}`TRANSPLANT` reparenting step (which only touches a {lit}`parent` cell) preserve
the tree abstraction. -/
theorem RepresentsW.of_agreeChild {s s' : Store} {p : Option Nat} {t : BSTree}
    {S : Finset Nat} (h : RepresentsW s p t S) (hag : Store.AgreeChild s s') :
    RepresentsW s' p t S := by
  induction h with
  | nil => exact RepresentsW.nil
  | @node i k lp rp pp l r Sl Sr hget hl hr hil hir hd ihl ihr =>
    obtain ⟨pp', hget'⟩ := hag i k lp rp pp hget
    exact RepresentsW.node hget' ihl ihr hil hir hd

/-- Set the {lit}`parent` field of the node at address {lit}`w` to {lit}`par`,
leaving key and child pointers intact (a no-op if {lit}`w` is unallocated). -/
def Store.reparentOne (s : Store) (w : Nat) (par : Option Nat) : Store :=
  match s.get w with
  | none => s
  | some nd => s.set w { nd with parent := par }

/-- Reparenting a single node preserves child structure. -/
theorem Store.agreeChild_reparentOne (s : Store) (w : Nat) (par : Option Nat) :
    Store.AgreeChild s (s.reparentOne w par) := by
  intro i k lp rp pp hi
  simp only [Store.reparentOne]
  split
  · next hw => exact ⟨pp, hi⟩
  · next nd hw =>
    by_cases hiw : i = w
    · subst hiw
      rw [hw] at hi
      obtain rfl := Option.some.inj hi
      exact ⟨par, by simp⟩
    · exact ⟨pp, by rw [Store.get_set_ne (Ne.symm hiw)]; exact hi⟩

/-- Reparent an optional pointer: reparent the target node if the pointer is
non-null, otherwise do nothing. -/
def Store.reparentOpt (s : Store) (vp : Option Nat) (par : Option Nat) : Store :=
  match vp with
  | none => s
  | some vid => s.reparentOne vid par

/-- Reparenting through an optional pointer preserves child structure. -/
theorem Store.agreeChild_reparentOpt (s : Store) (vp par : Option Nat) :
    Store.AgreeChild s (s.reparentOpt vp par) := by
  cases vp with
  | none => exact Store.AgreeChild.refl s
  | some vid => exact Store.agreeChild_reparentOne s vid par

/-- Overwrite the left (if {lit}`isLeft`) or right child pointer of the node at
{lit}`pid` with {lit}`cp` (a no-op if {lit}`pid` is unallocated). -/
def Store.setChild (s : Store) (pid : Nat) (isLeft : Bool) (cp : Option Nat) : Store :=
  match s.get pid with
  | none => s
  | some nd => if isLeft then s.set pid { nd with left := cp } else s.set pid { nd with right := cp }

/-- **In-place TRANSPLANT.**  Swing one child pointer of the parent node at
{lit}`pid` to point at {lit}`vp`, then set {lit}`vp`'s parent pointer to
{lit}`pid` — the pointer-rewiring core of CLRS {lit}`TRANSPLANT(T, u, v)`. -/
def Store.transplantChild (s : Store) (pid : Nat) (isLeft : Bool) (vp : Option Nat) : Store :=
  (s.setChild pid isLeft vp).reparentOpt vp (some pid)

/-- **AC-2 (left).**  In-place {lit}`TRANSPLANT` on a left child refines functional
subtree replacement: after rewiring the parent's left pointer to the new subtree
{lit}`V` and reparenting it, reading the heap downward from the parent yields the
functional node {lit}`node V k R`, where {lit}`R` is the untouched right sibling. -/
theorem transplantChild_left_representsW
    {s : Store} {pid k : Nat} {oldl rp pp vp : Option Nat}
    {R V : BSTree} {SR SV : Finset Nat}
    (hpid : s.get pid = some ⟨k, oldl, rp, pp⟩)
    (hR : RepresentsW s rp R SR)
    (hV : RepresentsW s vp V SV)
    (hpidR : pid ∉ SR) (hpidV : pid ∉ SV) (hVR : Disjoint SV SR) :
    RepresentsW (s.transplantChild pid true vp) (some pid)
      (BSTree.node V k R) (Insert.insert pid (SV ∪ SR)) := by
  have hop : s.transplantChild pid true vp
      = (s.set pid ⟨k, vp, rp, pp⟩).reparentOpt vp (some pid) := by
    simp [Store.transplantChild, Store.setChild, hpid]
  rw [hop]
  have hag : Store.AgreeChild (s.set pid ⟨k, vp, rp, pp⟩)
      ((s.set pid ⟨k, vp, rp, pp⟩).reparentOpt vp (some pid)) :=
    Store.agreeChild_reparentOpt _ vp (some pid)
  have hV2 : RepresentsW ((s.set pid ⟨k, vp, rp, pp⟩).reparentOpt vp (some pid)) vp V SV :=
    (hV.set_of_not_mem hpidV).of_agreeChild hag
  have hR2 : RepresentsW ((s.set pid ⟨k, vp, rp, pp⟩).reparentOpt vp (some pid)) rp R SR :=
    (hR.set_of_not_mem hpidR).of_agreeChild hag
  have hpid1 : (s.set pid ⟨k, vp, rp, pp⟩).get pid = some ⟨k, vp, rp, pp⟩ :=
    Store.get_set_self _ _ _
  obtain ⟨pp', hpid2⟩ := hag pid k vp rp pp hpid1
  exact RepresentsW.node hpid2 hV2 hR2 hpidV hpidR hVR

/-- **AC-2 (right).**  In-place {lit}`TRANSPLANT` on a right child refines functional
subtree replacement, symmetric to {lit}`transplantChild_left_representsW`. -/
theorem transplantChild_right_representsW
    {s : Store} {pid k : Nat} {lp oldr pp vp : Option Nat}
    {L V : BSTree} {SL SV : Finset Nat}
    (hpid : s.get pid = some ⟨k, lp, oldr, pp⟩)
    (hL : RepresentsW s lp L SL)
    (hV : RepresentsW s vp V SV)
    (hpidL : pid ∉ SL) (hpidV : pid ∉ SV) (hLV : Disjoint SL SV) :
    RepresentsW (s.transplantChild pid false vp) (some pid)
      (BSTree.node L k V) (Insert.insert pid (SL ∪ SV)) := by
  have hop : s.transplantChild pid false vp
      = (s.set pid ⟨k, lp, vp, pp⟩).reparentOpt vp (some pid) := by
    simp [Store.transplantChild, Store.setChild, hpid]
  rw [hop]
  have hag : Store.AgreeChild (s.set pid ⟨k, lp, vp, pp⟩)
      ((s.set pid ⟨k, lp, vp, pp⟩).reparentOpt vp (some pid)) :=
    Store.agreeChild_reparentOpt _ vp (some pid)
  have hL2 : RepresentsW ((s.set pid ⟨k, lp, vp, pp⟩).reparentOpt vp (some pid)) lp L SL :=
    (hL.set_of_not_mem hpidL).of_agreeChild hag
  have hV2 : RepresentsW ((s.set pid ⟨k, lp, vp, pp⟩).reparentOpt vp (some pid)) vp V SV :=
    (hV.set_of_not_mem hpidV).of_agreeChild hag
  have hpid1 : (s.set pid ⟨k, lp, vp, pp⟩).get pid = some ⟨k, lp, vp, pp⟩ :=
    Store.get_set_self _ _ _
  obtain ⟨pp', hpid2⟩ := hag pid k lp vp pp hpid1
  exact RepresentsW.node hpid2 hL2 hV2 hpidL hpidV hLV

/-- **AC-2 refinement of the functional zipper {lit}`transplant`.**  Reading the
heap after in-place TRANSPLANT on a left child yields exactly the functional
{lit}`transplant` of the zipper whose cursor is that left child (focus {lit}`U`,
context a single left-descent frame), with the new subtree {lit}`V` spliced in.
This is the pointer-level implementation of {lit}`transplant` from the zipper
layer. -/
theorem transplantChild_left_refines_transplant
    {s : Store} {pid k : Nat} {oldl rp pp vp : Option Nat}
    {U R V : BSTree} {SU SR SV : Finset Nat}
    (hpid : s.get pid = some ⟨k, oldl, rp, pp⟩)
    (_hU : RepresentsW s oldl U SU)
    (hR : RepresentsW s rp R SR) (hV : RepresentsW s vp V SV)
    (hpidR : pid ∉ SR) (hpidV : pid ∉ SV) (hVR : Disjoint SV SR) :
    RepresentsW (s.transplantChild pid true vp) (some pid)
      (transplant ⟨U, [Frame.fromLeft k R]⟩ V) (Insert.insert pid (SV ∪ SR)) := by
  have heq : transplant ⟨U, [Frame.fromLeft k R]⟩ V = BSTree.node V k R := by
    simp [transplant, Zipper.toTree, Frame.plug]
  rw [heq]
  exact transplantChild_left_representsW hpid hR hV hpidR hpidV hVR

/-- **AC-2 refinement of the functional zipper {lit}`transplant` (right child).**
Symmetric to {lit}`transplantChild_left_refines_transplant`. -/
theorem transplantChild_right_refines_transplant
    {s : Store} {pid k : Nat} {lp oldr pp vp : Option Nat}
    {L U V : BSTree} {SL SU SV : Finset Nat}
    (hpid : s.get pid = some ⟨k, lp, oldr, pp⟩)
    (hL : RepresentsW s lp L SL) (_hU : RepresentsW s oldr U SU)
    (hV : RepresentsW s vp V SV)
    (hpidL : pid ∉ SL) (hpidV : pid ∉ SV) (hLV : Disjoint SL SV) :
    RepresentsW (s.transplantChild pid false vp) (some pid)
      (transplant ⟨U, [Frame.fromRight k L]⟩ V) (Insert.insert pid (SL ∪ SV)) := by
  have heq : transplant ⟨U, [Frame.fromRight k L]⟩ V = BSTree.node L k V := by
    simp [transplant, Zipper.toTree, Frame.plug]
  rw [heq]
  exact transplantChild_right_representsW hpid hL hV hpidL hpidV hLV

/-- A freshly allocated leaf cell (key {lit}`nk`, null children) with parent
{lit}`par`, written at a fresh address {lit}`z`. -/
def Store.allocLeaf (s : Store) (z nk : Nat) (par : Option Nat) : Store :=
  s.set z ⟨nk, none, none, par⟩

/-- A store whose cell at {lit}`z` holds a null-child record represents the
single-node tree {lit}`node empty nk empty`, using only the id {lit}`z`. -/
theorem representsW_leaf {s : Store} {z nk : Nat} {pp : Option Nat}
    (hz : s.get z = some ⟨nk, none, none, pp⟩) :
    RepresentsW s (some z) (BSTree.node BSTree.empty nk BSTree.empty) {z} := by
  have h : RepresentsW s (some z) (BSTree.node BSTree.empty nk BSTree.empty)
      (Insert.insert z ((∅ : Finset Nat) ∪ ∅)) :=
    RepresentsW.node hz RepresentsW.nil RepresentsW.nil
      (by simp) (by simp) (by simp)
  simpa using h

/-- Functional insertion of a strictly larger key at a node whose right child is
empty attaches it as a right leaf. -/
theorem insert_right_leaf {L : BSTree} {k nk : Nat} (h : k < nk) :
    BSTree.insert nk (BSTree.node L k BSTree.empty)
      = BSTree.node L k (BSTree.node BSTree.empty nk BSTree.empty) := by
  have hlt : ¬ nk < k := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [BSTree.insert, hlt, h]

/-- **AC-3 (pointer TREE-INSERT).**  Allocating a fresh leaf cell and swinging the
parent's (empty) right child pointer to it — the pointer-machine {lit}`TREE-INSERT`
attachment step — refines functional subtree replacement: reading the heap from
the parent yields {lit}`node L k (node empty nk empty)`.  With {lit}`k < nk` this is
exactly {lit}`BSTree.insert nk (node L k empty)` (see {lit}`insert_right_leaf`). -/
theorem insertPointer_right_representsW
    {s : Store} {pid k nk z : Nat} {lp pp : Option Nat}
    {L : BSTree} {SL : Finset Nat}
    (hpid : s.get pid = some ⟨k, lp, none, pp⟩)
    (hL : RepresentsW s lp L SL)
    (hpidL : pid ∉ SL) (hzL : z ∉ SL) (hzpid : z ≠ pid) :
    RepresentsW ((s.allocLeaf z nk (some pid)).transplantChild pid false (some z))
      (some pid) (BSTree.node L k (BSTree.node BSTree.empty nk BSTree.empty))
      (Insert.insert pid (SL ∪ {z})) := by
  have hz : (s.allocLeaf z nk (some pid)).get z = some ⟨nk, none, none, some pid⟩ :=
    Store.get_set_self _ _ _
  have hpid' : (s.allocLeaf z nk (some pid)).get pid = some ⟨k, lp, none, pp⟩ := by
    rw [Store.allocLeaf, Store.get_set_ne hzpid]; exact hpid
  have hL' : RepresentsW (s.allocLeaf z nk (some pid)) lp L SL :=
    hL.set_of_not_mem hzL
  have hV : RepresentsW (s.allocLeaf z nk (some pid)) (some z)
      (BSTree.node BSTree.empty nk BSTree.empty) {z} := representsW_leaf hz
  have hpidz : pid ∉ ({z} : Finset Nat) := by
    simp [Ne.symm hzpid]
  have hdisj : Disjoint SL ({z} : Finset Nat) := by
    simp [Finset.disjoint_singleton_right, hzL]
  exact transplantChild_right_representsW hpid' hL' hV hpidL hpidz hdisj

/-! ## Height and O(h) cost model

Every BST operation descends at most one root-to-leaf path.  This section gives
the tree {lit}`height` and branch-faithful cost functions that count the descent
steps each operation actually performs, then proves the CLRS "each BST operation
runs in {lit}`O(h)` time" bound concretely: each descent operation costs at most
{lit}`height + 1`, and deletion — which additionally extracts and deletes the
successor subtree's minimum — costs at most {lit}`2·height + 3`. -/

/-- Height of a binary tree: 0 for the empty tree, and 1 plus the taller
child's height for a node. -/
def height : BSTree → Nat
  | empty => 0
  | node left _key right => 1 + max (height left) (height right)

/-- Number of descent steps taken by {lit}`search` for key {lit}`x`. -/
def searchCost (x : Nat) : BSTree → Nat
  | empty => 1
  | node left key right =>
      if x = key then 1
      else if x < key then 1 + searchCost x left
      else 1 + searchCost x right

/-- Number of descent steps taken by {lit}`minimum?`. -/
def minimumCost : BSTree → Nat
  | empty => 1
  | node empty _key _right => 1
  | node left@(node _ _ _) _key _right => 1 + minimumCost left

/-- Number of descent steps taken by {lit}`maximum?`. -/
def maximumCost : BSTree → Nat
  | empty => 1
  | node _left _key empty => 1
  | node _left _key right@(node _ _ _) => 1 + maximumCost right

/-- Number of descent steps taken by {lit}`successor?` for key {lit}`x`. -/
def successorCost (x : Nat) : BSTree → Nat
  | empty => 1
  | node left key right =>
      if x < key then 1 + successorCost x left
      else 1 + successorCost x right

/-- Number of descent steps taken by {lit}`predecessor?` for key {lit}`x`. -/
def predecessorCost (x : Nat) : BSTree → Nat
  | empty => 1
  | node left key right =>
      if key < x then 1 + predecessorCost x right
      else 1 + predecessorCost x left

/-- Number of descent steps taken by {lit}`insert` for key {lit}`x`. -/
def insertCost (x : Nat) : BSTree → Nat
  | empty => 1
  | node left key right =>
      if x < key then 1 + insertCost x left
      else if key < x then 1 + insertCost x right
      else 1

/-- Number of descent steps taken by {lit}`minKey`. -/
def minKeyCost : BSTree → Nat
  | empty => 1
  | node empty _key _right => 1
  | node left@(node _ _ _) _key _right => 1 + minKeyCost left

/-- Number of descent steps taken by {lit}`deleteMin`. -/
def deleteMinCost : BSTree → Nat
  | empty => 1
  | node empty _key _right => 1
  | node left@(node _ _ _) _key _right => 1 + deleteMinCost left

/-- Number of descent steps taken by {lit}`deleteRoot`, counting the minimum
extraction and the delete-min on the successor subtree when the right child is
nonempty. -/
def deleteRootCost : BSTree → Nat
  | empty => 1
  | node _left _key empty => 1
  | node _left _key right@(node _ _ _) => 1 + minKeyCost right + deleteMinCost right

/-- Number of descent steps taken by {lit}`delete` for key {lit}`x`. -/
def deleteCost (x : Nat) : BSTree → Nat
  | empty => 1
  | node left key right =>
      if x < key then 1 + deleteCost x left
      else if key < x then 1 + deleteCost x right
      else deleteRootCost (node left key right)

/-- **O(h) search.**  {lit}`search` descends at most one path, so its cost is
bounded by the tree height plus one. -/
theorem searchCost_le_height (x : Nat) (t : BSTree) :
    searchCost x t ≤ height t + 1 := by
  induction t with
  | empty => simp [searchCost, height]
  | node left key right ihL ihR =>
      by_cases hxkey : x = key
      · simp [searchCost, height, hxkey]
      · by_cases hxlt : x < key
        · simp [searchCost, height, hxkey, hxlt]
          omega
        · simp [searchCost, height, hxkey, hxlt]
          omega

/-- **O(h) minimum.**  {lit}`minimum?` follows left children, so its cost is
bounded by the tree height plus one. -/
theorem minimumCost_le_height (t : BSTree) :
    minimumCost t ≤ height t + 1 := by
  induction t with
  | empty => simp [minimumCost, height]
  | node left key right ihL ihR =>
      cases left with
      | empty => simp [minimumCost, height]
      | node _ _ _ =>
          simp [minimumCost, height] at *
          omega

/-- **O(h) maximum.**  {lit}`maximum?` follows right children, so its cost is
bounded by the tree height plus one. -/
theorem maximumCost_le_height (t : BSTree) :
    maximumCost t ≤ height t + 1 := by
  induction t with
  | empty => simp [maximumCost, height]
  | node left key right ihL ihR =>
      cases right with
      | empty => simp [maximumCost, height]
      | node _ _ _ =>
          simp [maximumCost, height] at *
          omega

/-- **O(h) successor.**  {lit}`successor?` descends at most one path, so its
cost is bounded by the tree height plus one. -/
theorem successorCost_le_height (x : Nat) (t : BSTree) :
    successorCost x t ≤ height t + 1 := by
  induction t with
  | empty => simp [successorCost, height]
  | node left key right ihL ihR =>
      by_cases hxlt : x < key
      · simp [successorCost, height, hxlt]
        omega
      · simp [successorCost, height, hxlt]
        omega

/-- **O(h) predecessor.**  {lit}`predecessor?` descends at most one path, so its
cost is bounded by the tree height plus one. -/
theorem predecessorCost_le_height (x : Nat) (t : BSTree) :
    predecessorCost x t ≤ height t + 1 := by
  induction t with
  | empty => simp [predecessorCost, height]
  | node left key right ihL ihR =>
      by_cases hxgt : key < x
      · simp [predecessorCost, height, hxgt]
        omega
      · simp [predecessorCost, height, hxgt]
        omega

/-- **O(h) insertion.**  {lit}`insert` descends at most one path, so its cost is
bounded by the tree height plus one. -/
theorem insertCost_le_height (x : Nat) (t : BSTree) :
    insertCost x t ≤ height t + 1 := by
  induction t with
  | empty => simp [insertCost, height]
  | node left key right ihL ihR =>
      by_cases hxlt : x < key
      · simp [insertCost, height, hxlt]
        omega
      · by_cases hxgt : key < x
        · simp [insertCost, height, hxlt, hxgt]
          omega
        · simp [insertCost, height, hxlt, hxgt]

/-- **O(h) minimum extraction.**  {lit}`minKey` follows left children, so its
cost is bounded by the tree height plus one. -/
theorem minKeyCost_le_height (t : BSTree) :
    minKeyCost t ≤ height t + 1 := by
  induction t with
  | empty => simp [minKeyCost, height]
  | node left key right ihL ihR =>
      cases left with
      | empty => simp [minKeyCost, height]
      | node _ _ _ =>
          simp [minKeyCost, height] at *
          omega

/-- **O(h) delete-min.**  {lit}`deleteMin` follows left children, so its cost is
bounded by the tree height plus one. -/
theorem deleteMinCost_le_height (t : BSTree) :
    deleteMinCost t ≤ height t + 1 := by
  induction t with
  | empty => simp [deleteMinCost, height]
  | node left key right ihL ihR =>
      cases left with
      | empty => simp [deleteMinCost, height]
      | node _ _ _ =>
          simp [deleteMinCost, height] at *
          omega

/-- **O(h) root deletion.**  {lit}`deleteRoot` either detaches the left child
(constant work) or runs a minimum extraction plus a delete-min on the right
subtree, so its cost is linear in the tree height. -/
theorem deleteRootCost_le : ∀ t : BSTree, deleteRootCost t ≤ 2 * height t + 3
  | empty => by simp [deleteRootCost, height]
  | node left key empty => by simp [deleteRootCost, height]
  | node left key (node rl rk rr) => by
      have h1 := minKeyCost_le_height (node rl rk rr)
      have h2 := deleteMinCost_le_height (node rl rk rr)
      simp [deleteRootCost, height] at *
      omega

/-- **O(h) deletion.**  {lit}`delete` descends at most one path and then
performs a root deletion, so its cost is linear in the tree height. -/
theorem deleteCost_le (x : Nat) (t : BSTree) :
    deleteCost x t ≤ 2 * height t + 3 := by
  induction t with
  | empty => simp [deleteCost, height]
  | node left key right ihL ihR =>
      by_cases hxlt : x < key
      · simp [deleteCost, hxlt]
        change 1 + deleteCost x left ≤ 2 * (1 + max (height left) (height right)) + 3
        omega
      · by_cases hxgt : key < x
        · simp [deleteCost, hxlt, hxgt]
          change 1 + deleteCost x right ≤ 2 * (1 + max (height left) (height right)) + 3
          omega
        · simp [deleteCost, hxlt, hxgt]
          exact deleteRootCost_le (node left key right)

/-! ## Randomly built binary search trees (Section 12.4)

A randomly built BST inserts a uniform random permutation of `Fin n` into the
empty tree.  This section proves the classic combinatorial characterization
(Lemma 12.3): key `x` is an ancestor of key `y` in the tree built from a list of
distinct keys exactly when `x` is the first key of the list that lies in the
closed interval between them.  This is the workhorse behind the `O(log n)`
expected-depth analysis of a randomly built BST.

**Remaining gap.**  The probability `P(i is an ancestor of j) = 1/(|i-j|+1)` and
the resulting expected-depth bound `O(log n)` are not yet formalized; the
combinatorial characterization below is the needed foundation.
-/

/-- Depth of key `y` (0 at root, 0 when absent). -/
def depth (y : Nat) : BSTree → Nat
  | empty => 0
  | node left key right =>
      if y = key then 0
      else if y < key then 1 + depth y left
      else 1 + depth y right

/-- `x` lies on the root-to-`y` search path (including `x = y`). -/
def isAncestorOf (x y : Nat) : BSTree → Prop
  | empty => False
  | node left key right =>
      if y = key then x = key
      else if y < key then x = key ∨ isAncestorOf x y left
      else x = key ∨ isAncestorOf x y right

/-- Insert a list of keys in order (head first = root). -/
def insertAll : List Nat → BSTree → BSTree
  | [], t => t
  | x :: xs, t => insertAll xs (insert x t)

/-- BST built by inserting `xs` in order. -/
def buildFromList (xs : List Nat) : BSTree := insertAll xs empty

/-- `x` is the first element of the list lying in `[a, b]`. -/
def IsFirstInInterval (x a b : Nat) : List Nat → Prop
  | [] => False
  | z :: zs => if a ≤ z ∧ z ≤ b then z = x else IsFirstInInterval x a b zs

/-- If `x` is on the path to `y`, then `x` occurs in the tree. -/
theorem isAncestorOf_implies_inTree {x y : Nat} {t : BSTree} :
    isAncestorOf x y t → InTree x t := by
  induction t with
  | empty => simp [isAncestorOf]
  | node left key right ihL ihR =>
      intro h
      by_cases hykey : y = key
      · simp [isAncestorOf, hykey] at h
        subst x; simp [InTree]
      · by_cases hylt : y < key
        · simp [isAncestorOf, hykey, hylt] at h
          rcases h with h | h
          · subst x; simp [InTree]
          · exact Or.inr (Or.inl (ihL h))
        · simp [isAncestorOf, hykey, hylt] at h
          rcases h with h | h
          · subst x; simp [InTree]
          · exact Or.inr (Or.inr (ihR h))

/-- Membership after inserting a whole list. -/
theorem InTree_insertAll_iff (k : Nat) (zs : List Nat) (t : BSTree) :
    InTree k (insertAll zs t) ↔ InTree k t ∨ k ∈ zs := by
  induction zs generalizing t with
  | nil => simp [insertAll]
  | cons z zs ih =>
      rw [insertAll, ih, inTree_insert_iff]
      simp [List.mem_cons]
      tauto

/-- A key occurs in `buildFromList xs` iff it belongs to `xs`. -/
theorem InTree_buildFromList_iff (k : Nat) (xs : List Nat) :
    InTree k (buildFromList xs) ↔ k ∈ xs := by
  unfold buildFromList
  rw [InTree_insertAll_iff]
  simp [InTree]

/-- Inserting a list of keys into a node splits them by comparison with the
node key. -/
theorem insertAll_split (z : Nat) (L R : BSTree) (zs : List Nat) :
    insertAll zs (node L z R) =
      node (insertAll (zs.filter (fun k => k < z)) L) z
        (insertAll (zs.filter (fun k => z < k)) R) := by
  induction zs generalizing L R with
  | nil => simp [insertAll]
  | cons k ks ih =>
      by_cases hkz : k < z
      · have hzk : ¬ z < k := by omega
        simp only [insertAll, insert, hkz]
        rw [show (k :: ks).filter (fun k => k < z) = k :: ks.filter (fun k => k < z) from
              List.filter_cons_of_pos (by simp [hkz])]
        rw [show (k :: ks).filter (fun k => z < k) = ks.filter (fun k => z < k) from
              List.filter_cons_of_neg (by simp [hzk])]
        exact ih (insert k L) R
      · by_cases hzk : z < k
        · simp only [insertAll, insert, hkz, hzk]
          rw [show (k :: ks).filter (fun k => k < z) = ks.filter (fun k => k < z) from
                List.filter_cons_of_neg (by simp [hkz])]
          rw [show (k :: ks).filter (fun k => z < k) = k :: ks.filter (fun k => z < k) from
                List.filter_cons_of_pos (by simp [hzk])]
          exact ih L (insert k R)
        · simp only [insertAll, insert, hkz, hzk]
          rw [show (k :: ks).filter (fun k => k < z) = ks.filter (fun k => k < z) from
                List.filter_cons_of_neg (by simp [hkz])]
          rw [show (k :: ks).filter (fun k => z < k) = ks.filter (fun k => z < k) from
                List.filter_cons_of_neg (by simp [hzk])]
          exact ih L R

/-- The head of the list becomes the root, splitting the rest by comparison. -/
theorem buildFromList_cons (z : Nat) (zs : List Nat) :
    buildFromList (z :: zs) =
      node (buildFromList (zs.filter (fun k => k < z))) z
        (buildFromList (zs.filter (fun k => z < k))) := by
  simp [buildFromList, insertAll, insert]
  exact insertAll_split z empty empty zs

/-- Filtering out keys `≥ r` (all above `b`) does not change the first element
of the list in `[a, b]`. -/
theorem IsFirstInInterval_filter_lt {zs : List Nat} {x a b r : Nat}
    (hbr : b < r) :
    IsFirstInInterval x a b (zs.filter (fun k => k < r)) = IsFirstInInterval x a b zs := by
  induction zs with
  | nil => simp [IsFirstInInterval]
  | cons z zs ih =>
      by_cases hzr : z < r
      · simp [List.filter, hzr, IsFirstInInterval, ih]
      · have hrz : r ≤ z := Nat.le_of_not_gt hzr
        have hz_out : ¬ (a ≤ z ∧ z ≤ b) := by intro hz; omega
        simp [List.filter, hzr, IsFirstInInterval, hz_out, ih]

/-- Filtering out keys `≤ r` (all below `a`) does not change the first element
of the list in `[a, b]`. -/
theorem IsFirstInInterval_filter_gt {zs : List Nat} {x a b r : Nat}
    (hra : r < a) :
    IsFirstInInterval x a b (zs.filter (fun k => r < k)) = IsFirstInInterval x a b zs := by
  induction zs with
  | nil => simp [IsFirstInInterval]
  | cons z zs ih =>
      by_cases hzr : r < z
      · simp [List.filter, hzr, IsFirstInInterval, ih]
      · have hzr' : z ≤ r := Nat.le_of_not_gt hzr
        have hz_out : ¬ (a ≤ z ∧ z ≤ b) := by intro hz; omega
        simp [List.filter, hzr, IsFirstInInterval, hz_out, ih]

/-- **Randomly-built-BST characterization.**  In a BST built by inserting keys
in list order, `x` is an ancestor of `y` exactly when `x` is the first key of
the list that lies in the closed interval between them. -/
theorem isAncestorOf_iff_firstInInterval (xs : List Nat) (x y : Nat) :
    isAncestorOf x y (buildFromList xs) ↔ IsFirstInInterval x (min x y) (max x y) xs := by
  have hmain : ∀ n : Nat, ∀ xs : List Nat, xs.length = n → ∀ x y : Nat,
      isAncestorOf x y (buildFromList xs) ↔ IsFirstInInterval x (min x y) (max x y) xs := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro xs hlen x y
        cases xs with
        | nil => simp [buildFromList, insertAll, isAncestorOf, IsFirstInInterval]
        | cons z zs =>
            rw [buildFromList_cons]
            by_cases hyz : y = z
            · simp [isAncestorOf, IsFirstInInterval, hyz]
              exact ⟨Eq.symm, Eq.symm⟩
            · by_cases hylt : y < z
              · simp only [isAncestorOf, IsFirstInInterval, hyz, hylt]
                by_cases hzIn : min x y ≤ z ∧ z ≤ max x y
                · have hz_le_x : z ≤ x := by
                    have hz_le_max : z ≤ max x y := hzIn.2
                    by_cases hxy : x ≤ y
                    · have : max x y = y := max_eq_right hxy
                      rw [this] at hz_le_max
                      omega
                    · have : max x y = x := max_eq_left (le_of_lt (Nat.lt_of_not_ge hxy))
                      rw [this] at hz_le_max
                      exact hz_le_max
                  simp only [hzIn]
                  constructor
                  · intro h
                    rcases h with h | h
                    · exact h.symm
                    · have hin := isAncestorOf_implies_inTree h
                      rw [InTree_buildFromList_iff] at hin
                      have hxz_lt : x < z := of_decide_eq_true (List.mem_filter.mp hin).2
                      omega
                  · intro hzx
                    exact Or.inl hzx.symm
                · have hmax_lt_z : max x y < z := by
                    by_cases hxy : x ≤ y
                    · have hmax : max x y = y := max_eq_right hxy
                      rw [hmax]; exact hylt
                    · have hxy' : y < x := Nat.lt_of_not_ge hxy
                      have hmax : max x y = x := max_eq_left (le_of_lt hxy')
                      have hmin : min x y = y := min_eq_right (le_of_lt hxy')
                      rw [hmax]
                      apply Nat.lt_of_not_ge
                      intro hzle
                      have hzIn' : min x y ≤ z ∧ z ≤ max x y := by
                        rw [hmin, hmax]; exact ⟨le_of_lt hylt, hzle⟩
                      exact hzIn hzIn'
                  have hx_ne_z : x ≠ z := by
                    have : x ≤ max x y := le_max_left x y
                    omega
                  simp only [hzIn, hx_ne_z]
                  have hih' := ih (zs.filter (fun k => k < z)).length
                    (by
                      have hlen' : zs.length + 1 = n := by simpa using hlen
                      have : (zs.filter (fun k => k < z)).length ≤ zs.length := List.length_filter_le _ _
                      omega)
                    (zs.filter (fun k => k < z)) rfl x y
                  rw [hih', IsFirstInInterval_filter_lt hmax_lt_z]
                  simp
              · have hzlt : z < y := by omega
                simp only [isAncestorOf, IsFirstInInterval, hyz, hylt]
                by_cases hzIn : min x y ≤ z ∧ z ≤ max x y
                · have hx_le_z : x ≤ z := by
                    have hmin_le_z : min x y ≤ z := hzIn.1
                    by_cases hxy : x ≤ y
                    · have : min x y = x := min_eq_left hxy
                      rw [this] at hmin_le_z; exact hmin_le_z
                    · have : min x y = y := min_eq_right (le_of_lt (Nat.lt_of_not_ge hxy))
                      rw [this] at hmin_le_z
                      omega
                  simp only [hzIn]
                  constructor
                  · intro h
                    rcases h with h | h
                    · exact h.symm
                    · have hin := isAncestorOf_implies_inTree h
                      rw [InTree_buildFromList_iff] at hin
                      have hzx_lt : z < x := of_decide_eq_true (List.mem_filter.mp hin).2
                      omega
                  · intro hzx
                    exact Or.inl hzx.symm
                · have hmin_gt_z : z < min x y := by
                    by_cases hxy : x ≤ y
                    · have hmin : min x y = x := min_eq_left hxy
                      have hmax : max x y = y := max_eq_right hxy
                      rw [hmin]
                      apply Nat.lt_of_not_ge
                      intro hx_le_z
                      apply hzIn
                      rw [hmin, hmax]
                      exact ⟨hx_le_z, le_of_lt hzlt⟩
                    · have hmin : min x y = y := min_eq_right (le_of_lt (Nat.lt_of_not_ge hxy))
                      rw [hmin]
                      exact hzlt
                  have hx_ne_z : x ≠ z := by
                    have : min x y ≤ x := min_le_left x y
                    omega
                  simp only [hzIn, hx_ne_z]
                  have hih' := ih (zs.filter (fun k => z < k)).length
                    (by
                      have hlen' : zs.length + 1 = n := by simpa using hlen
                      have : (zs.filter (fun k => z < k)).length ≤ zs.length := List.length_filter_le _ _
                      omega)
                    (zs.filter (fun k => z < k)) rfl x y
                  rw [hih', IsFirstInInterval_filter_gt hmin_gt_z]
                  simp
  exact hmain xs.length xs rfl x y

/-! ## §12.4 Randomly-built BST: probability and expected depth -/

/-- The keys `π 0, …, π (n-1)` in insertion order, as naturals. -/
def permKeys {n : Nat} (π : Equiv.Perm (Fin n)) : List Nat :=
  (List.finRange n).map (fun i => (π i : Nat))

/-- Build the BST by inserting a uniform random permutation of `Fin n`. -/
def buildFromPerm {n : Nat} (π : Equiv.Perm (Fin n)) : BSTree :=
  buildFromList (permKeys π)

/-- `i` has minimum insertion position among the keys of the closed interval
between `i` and `j`. -/
def firstInInterval {n : Nat} (π : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  ∀ k : Fin n, (min (i : Nat) (j : Nat) ≤ (k : Nat)) → ((k : Nat) ≤ max (i : Nat) (j : Nat)) →
    (π.symm i : Nat) ≤ (π.symm k : Nat)

/-- `i` has minimum position among the keys of the set `S`. -/
def isFirstOf {n : Nat} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ S ∧ ∀ k ∈ S, (π.symm i : Nat) ≤ (π.symm k : Nat)

theorem firstInInterval_iff_isFirstOf {n : Nat} (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    firstInInterval π i j ↔
      isFirstOf π (Finset.Icc (min i j) (max i j)) i := by
  unfold firstInInterval isFirstOf
  constructor
  · intro h
    constructor
    · exact Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
    · intro k hk
      exact h k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
  · intro h
    intro k hklo hkhi
    exact h.2 k (Finset.mem_Icc.mpr ⟨hklo, hkhi⟩)

end BSTree

end Chapter12
end CLRS
