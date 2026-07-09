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

The section also formalises structural properties of functional BSTs:

- Theorem {lit}`height_insert_le_height_add_one`: insertion increases height by
  at most one.
- Theorem {lit}`height_delete_le_height`: deletion does not increase height.
- Theorem {lit}`height_deleteMin_le_height`: deleting the minimum does not
  increase height.
- Theorem {lit}`height_deleteRoot_le_height`: deleting the root does not
  increase height.
- Theorem {lit}`inorder_sorted`: the inorder traversal of an ordered tree yields
  a strictly increasing list of keys (as a {lit}`List.Pairwise (<)`).
- Theorem {lit}`mem_inorder_iff_inTree`: inorder-list membership is equivalent
  to tree membership.
- Theorem {lit}`length_inorder_eq_size`: the inorder list length equals the tree
  size.
- Theorem {lit}`inorder_nodup`: an ordered tree's inorder traversal is
  duplicate-free.
- Theorem {lit}`size_insert`: insertion changes the size by 0 or +1.
- Theorem {lit}`size_insert_le_size_add_one`: insertion increases size by at
  most one.

Current gaps:

- Parent-pointer successor/predecessor procedures, transplant, and pointer-level
  tree mutation are future section targets.
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

/-! ## Height, inorder traversal, and size -/

/-- The height of a binary tree: 0 for empty, 1 + max(left, right) for nodes. -/
def height : BSTree → Nat
  | empty => 0
  | node left _key right => 1 + max (height left) (height right)

/-- The number of nodes in the tree. -/
def size : BSTree → Nat
  | empty => 0
  | node left _key right => 1 + size left + size right

/-- Inorder traversal of the tree, producing a list of keys in left-root-right order. -/
def inorder : BSTree → List Nat
  | empty => []
  | node left key right => inorder left ++ [key] ++ inorder right

/-- Membership in {lit}`inorder` is equivalent to {lit}`InTree`. -/
theorem mem_inorder_iff_inTree {x : Nat} {t : BSTree} :
    x ∈ inorder t ↔ InTree x t := by
  induction t with
  | empty => simp [inorder, InTree]
  | node left key right ihLeft ihRight =>
      simp [inorder, InTree, ihLeft, ihRight]
      tauto

/-- The length of the inorder list equals the size of the tree. -/
theorem length_inorder_eq_size (t : BSTree) : (inorder t).length = size t := by
  induction t with
  | empty => simp [inorder, size]
  | node left key right ihLeft ihRight =>
      simp [inorder, size, ihLeft, ihRight]
      omega

/-- Deleting the minimum key does not increase the height. -/
theorem height_deleteMin_le_height (t : BSTree) : height (deleteMin t) ≤ height t := by
  induction t with
  | empty => simp [height, deleteMin]
  | node left key right ihLeft _ihRight =>
      cases left with
      | empty => simp [height, deleteMin]
      | node ll lk lr =>
          have hMax : max (height (deleteMin (node ll lk lr))) (height right) ≤
                     max (height (node ll lk lr)) (height right) :=
            max_le_max ihLeft (le_refl _)
          simpa [height, deleteMin] using Nat.add_le_add_left hMax 1

/-- Deleting the root does not increase the height. -/
theorem height_deleteRoot_le_height (t : BSTree) : height (deleteRoot t) ≤ height t := by
  induction t with
  | empty => simp [height, deleteRoot]
  | node left key right _ihLeft _ihRight =>
      cases right with
      | empty => simp [height, deleteRoot]
      | node rl rk rr =>
          have hMax : max (height left) (height (deleteMin (node rl rk rr))) ≤
                     max (height left) (height (node rl rk rr)) :=
            max_le_max (le_refl _) (height_deleteMin_le_height (node rl rk rr))
          simpa [height, deleteRoot] using Nat.add_le_add_left hMax 1

/-- Insertion increases the height by at most one. -/
theorem height_insert_le_height_add_one (x : Nat) (t : BSTree) :
    height (insert x t) ≤ height t + 1 := by
  induction t with
  | empty => simp [height, insert]
  | node left key right ihLeft ihRight =>
      by_cases hxkey : x < key
      · have hMaxLe : max (height (insert x left)) (height right) ≤
                     max (height left) (height right) + 1 := by
          have h1 : height (insert x left) ≤ max (height left) (height right) + 1 :=
            calc
              height (insert x left) ≤ height left + 1 := ihLeft
              _ ≤ max (height left) (height right) + 1 :=
                Nat.add_le_add_right (le_max_left _ _) 1
          have h2 : height right ≤ max (height left) (height right) + 1 :=
            Nat.le_trans (le_max_right _ _) (Nat.le_succ _)
          exact max_le h1 h2
        simpa [height, insert, hxkey, add_assoc] using Nat.add_le_add_left hMaxLe 1
      · by_cases hkeyx : key < x
        · have hMaxLe : max (height left) (height (insert x right)) ≤
                       max (height left) (height right) + 1 := by
            have h1 : height left ≤ max (height left) (height right) + 1 :=
              Nat.le_trans (le_max_left _ _) (Nat.le_succ _)
            have h2 : height (insert x right) ≤ max (height left) (height right) + 1 :=
              calc
                height (insert x right) ≤ height right + 1 := ihRight
                _ ≤ max (height left) (height right) + 1 :=
                  Nat.add_le_add_right (le_max_right _ _) 1
            exact max_le h1 h2
          simpa [height, insert, hxkey, hkeyx, add_assoc] using Nat.add_le_add_left hMaxLe 1
        · simp [height, insert, hxkey, hkeyx]

/-- Functional deletion does not increase the height. -/
theorem height_delete_le_height (x : Nat) (t : BSTree) : height (delete x t) ≤ height t := by
  induction t generalizing x with
  | empty => simp [height, delete]
  | node left key right ihLeft ihRight =>
      by_cases hxkey : x < key
      · have hMax : max (height (delete x left)) (height right) ≤
                   max (height left) (height right) :=
          max_le_max (ihLeft x) (le_refl _)
        simpa [height, delete, hxkey] using Nat.add_le_add_left hMax 1
      · by_cases hkeyx : key < x
        · have hMax : max (height left) (height (delete x right)) ≤
                     max (height left) (height right) :=
            max_le_max (le_refl _) (ihRight x)
          simpa [height, delete, hxkey, hkeyx] using Nat.add_le_add_left hMax 1
        · have hxEq : x = key := Nat.le_antisymm (Nat.le_of_not_gt hkeyx) (Nat.le_of_not_gt hxkey)
          subst x
          simpa [height, delete] using height_deleteRoot_le_height (node left key right)

/-- On an ordered tree, the inorder traversal produces a strictly increasing list. -/
theorem inorder_sorted {t : BSTree} (ht : Ordered t) :
    List.Pairwise (· < ·) (inorder t) := by
  induction t with
  | empty =>
      simp [inorder]
  | node left key right ihLeft ihRight =>
      simp [Ordered] at ht
      rcases ht with ⟨hLeft, hRight, hLt, hGt⟩
      have hSortedLeft : List.Pairwise (· < ·) (inorder left) := ihLeft hLeft
      have hSortedRight : List.Pairwise (· < ·) (inorder right) := ihRight hRight
      have hAllLeftLtKey : ∀ a, a ∈ inorder left → a < key := by
        intro a ha
        have haTree := (mem_inorder_iff_inTree (x := a) (t := left)).mp ha
        exact hLt a haTree
      have hKeyLtAllRight : ∀ b, b ∈ inorder right → key < b := by
        intro b hb
        have hbTree := (mem_inorder_iff_inTree (x := b) (t := right)).mp hb
        exact hGt b hbTree
      have hKeySorted : List.Pairwise (· < ·) [key] := by
        simp
      have hLeftKeyCross : ∀ a ∈ inorder left, ∀ b ∈ [key], a < b := by
        intro a ha b hb
        simp at hb
        subst b
        exact hAllLeftLtKey a ha
      have hLeftKeySorted : List.Pairwise (· < ·) (inorder left ++ [key]) := by
        rw [List.pairwise_append]
        exact ⟨hSortedLeft, hKeySorted, hLeftKeyCross⟩
      have hLeftKeyRightCross : ∀ a ∈ inorder left ++ [key], ∀ b ∈ inorder right, a < b := by
        intro a ha b hb
        rcases List.mem_append.mp ha with (haLeft | haKey)
        · have haLtKey := hAllLeftLtKey a haLeft
          have hKeyLtB := hKeyLtAllRight b hb
          exact lt_trans haLtKey hKeyLtB
        · simp at haKey
          subst a
          exact hKeyLtAllRight b hb
      rw [inorder, List.pairwise_append]
      exact ⟨hLeftKeySorted, hSortedRight, hLeftKeyRightCross⟩

/-- On an ordered tree, the inorder traversal contains no duplicate keys. -/
theorem inorder_nodup {t : BSTree} (ht : Ordered t) : (inorder t).Nodup := by
  have hSorted := inorder_sorted ht
  exact hSorted.nodup

/-- Insertion changes the tree size by 0 (key already present) or +1 (new key). -/
theorem size_insert (x : Nat) (t : BSTree) : size (insert x t) = size t ∨ size (insert x t) = size t + 1 := by
  induction t with
  | empty => simp [size, insert]
  | node left key right ihLeft ihRight =>
      by_cases hxkey : x < key
      · simp [size, insert, hxkey]
        rcases ihLeft with (hL | hL)
        · left; omega
        · right; omega
      · by_cases hkeyx : key < x
        · simp [size, insert, hxkey, hkeyx]
          rcases ihRight with (hR | hR)
          · left; omega
          · right; omega
        · simp [size, insert, hxkey, hkeyx]

/-- Insertion does not decrease the size. -/
theorem size_le_size_insert (x : Nat) (t : BSTree) : size t ≤ size (insert x t) := by
  rcases size_insert x t with (h | h)
  · rw [h]
  · omega

/-- Insertion increases size by at most one. -/
theorem size_insert_le_size_add_one (x : Nat) (t : BSTree) : size (insert x t) ≤ size t + 1 := by
  rcases size_insert x t with (h | h)
  · omega
  · omega

end BSTree

end Chapter12
end CLRS
