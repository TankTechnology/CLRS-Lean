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
greatest key less than the query.

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
- Theorem {lit}`predecessor?_greatest_less`: a returned predecessor is the
  greatest tree key strictly less than the query.
- Theorem {lit}`inTree_insert_iff`: membership after insertion is exactly the
  old membership relation plus the inserted key.
- Theorem {lit}`insert_ordered`: insertion preserves the BST ordering invariant.

Current gaps:

- Parent-pointer successor/predecessor procedures, transplant, deletion, and
  pointer-level tree mutation are future section targets.
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

end BSTree

end Chapter12
end CLRS
