import Mathlib.Tactic

-- Prototype in development: silence the unused-simp-argument linter noise.
set_option linter.unusedSimpArgs false

/-!
# Randomized treap (prototype)

A **treap** is a binary search tree whose nodes also carry a priority, kept as
a heap: every node's priority is at least the priorities of its children (a
*max-heap* order).  If the priorities are distinct and chosen uniformly at
random, the treap on a fixed set of {lit}`(key, priority)` pairs is unique and
has expected height {lit}`O(log n)`, which makes a treap a randomized balanced
BST.

This module is a **prototype**: the executable definitions and the two
membership theorems are kernel-checked, but the headline *expected-height*
result is not yet stated (it needs the finite-expectation layer).  The module
is **not** registered in {lit}`literate.toml` and does not appear on the site
until it is promoted.

The membership theorems carry an {lit}`IsBST` (binary-search-tree) hypothesis:
the executable {lit}`member` really is a guided search, and for a non-BST tree
a rotation can change what the search finds, so the statement is only
meaningful for well-formed trees.

Main results:

- Theorem {lit}`keys_insert`: inserting {lit}`(x, p)` adds exactly {lit}`x` to
  the key set.
- Theorem {lit}`member_insert`: for well-formed trees, membership of
  {lit}`insert x p t` equals the old membership together with the new key.
- Theorem {lit}`insert_member`: after inserting {lit}`x`, searching for
  {lit}`x` succeeds.

Planned (not yet stated — needs the finite-expectation layer):

- Expected height {lit}`O(log n)` under uniformly random distinct priorities,
  using {lit}`CLRSLean.Probability.FiniteExpectation`.

Notation conventions:

- {lit}`α` : key type with decidable linear order
- priority : {lit}`Nat`, treated as an opaque tie-breaker
- {lit}`IsBST t` : {lit}`t` is a binary search tree on its keys
-/

namespace CLRS.Extensions

/-- A treap over keys {lit}`α`: either empty, or a node carrying a key, a priority,
and left/right subtrees. -/
inductive Treap (α : Type u) where
  | nil : Treap α
  | node (key : α) (prio : Nat) (left right : Treap α) : Treap α
  deriving Repr

namespace Treap

/-- The height of a treap: the number of nodes on a longest root-to-leaf path. -/
def height : Treap α → Nat
  | nil => 0
  | node _ _ l r => 1 + max (height l) (height r)

/-- The finite set of keys occurring in a treap. -/
def keys [DecidableEq α] : Treap α → Finset α
  | nil => ∅
  | node k _ l r => Insert.insert k (keys l ∪ keys r)

/-- Membership test: whether {lit}`x` occurs as a key (guided search over the
BST). -/
def member [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) : Treap α → Bool
  | nil => false
  | node k _ l r =>
      if x = k then true
      else if x < k then member x l
      else member x r

/-- Right rotation: promote the left child to the root. -/
def rotR : Treap α → Treap α
  | node a pa (node b pb lb rb) r => node b pb lb (node a pa rb r)
  | t => t

/-- Left rotation: promote the right child to the root. -/
def rotL : Treap α → Treap α
  | node a pa l (node b pb lb rb) => node b pb (node a pa l lb) rb
  | t => t

/-- Insert {lit}`(x, p)` into a treap, preserving the BST order on keys and the
max-heap order on priorities.  Existing keys are kept unchanged. -/
def insert [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p : Nat) : Treap α → Treap α
  | nil => node x p nil nil
  | node k pk l r =>
      if x < k then
        let l' := insert x p l
        match l' with
        | node _ p' _ _ => if p' > pk then rotR (node k pk l' r) else node k pk l' r
        | nil => node k pk l' r
      else if k < x then
        let r' := insert x p r
        match r' with
        | node _ p' _ _ => if p' > pk then rotL (node k pk l r') else node k pk l r'
        | nil => node k pk l r'
      else node k pk l r

/-- {lit}`insert` never returns the empty tree. -/
theorem insert_ne_nil [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p : Nat)
    (t : Treap α) : insert x p t ≠ nil := by
  induction t with
  | nil => simp [insert]
  | node k pk l r ih_l ih_r =>
      by_cases h1 : x < k
      · -- x < k: insert follows the left branch and always returns a node
        simp [insert, h1]
        cases insert x p l with
        | nil => simp
        | node b pb lb rb =>
            by_cases hrot : pb > pk
            · simp [rotR, hrot]
            · simp [hrot]
      · by_cases h2 : k < x
        · -- k < x: insert follows the right branch
          simp [insert, h1, h2]
          cases insert x p r with
          | nil => simp
          | node b pb lb rb =>
              by_cases hrot : pb > pk
              · simp [rotL, hrot]
              · simp [hrot]
        · -- x = k: tree unchanged
          simp [insert, h1, h2]

/-- Right rotation preserves the key set. -/
theorem keys_rotR [DecidableEq α] (t : Treap α) : keys (rotR t) = keys t := by
  cases t with
  | nil => rfl
  | node a pa l r =>
      cases l with
      | nil => rfl
      | node b pb lb rb =>
          ext y
          simp [keys, rotR, Finset.mem_insert, Finset.mem_union, or_assoc, or_left_comm, or_comm]

/-- Left rotation preserves the key set. -/
theorem keys_rotL [DecidableEq α] (t : Treap α) : keys (rotL t) = keys t := by
  cases t with
  | nil => rfl
  | node a pa l r =>
      cases r with
      | nil => rfl
      | node b pb lb rb =>
          ext y
          simp [keys, rotL, Finset.mem_insert, Finset.mem_union, or_assoc, or_left_comm, or_comm]

/-- Inserting {lit}`(x, p)` adds exactly the key {lit}`x` to the key set. -/
theorem keys_insert [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p : Nat)
    (t : Treap α) : keys (insert x p t) = Insert.insert x (keys t) := by
  induction t with
  | nil => simp [insert, keys]
  | node k pk l r ih_l ih_r =>
      by_cases h1 : x < k
      · by_cases h2 : k < x
        · exfalso
          exact (lt_asymm h1 h2)
        · -- x < k (and not k < x)
          cases hl' : insert x p l with
          | nil =>
              exfalso
              exact insert_ne_nil x p l hl'
          | node b pb lb rb =>
              have hlkey : keys (node b pb lb rb) = Insert.insert x (keys l) := by
                rw [← hl']
                exact ih_l
              by_cases hrot : pb > pk
              · simp [insert, h1, hl', hrot]
                rw [keys_rotR]
                ext y
                change y ∈ Insert.insert k (keys (node b pb lb rb) ∪ keys r) ↔
                       y ∈ Insert.insert x (Insert.insert k (keys l ∪ keys r))
                rw [hlkey]
                simp [Finset.mem_insert, Finset.mem_union, or_assoc, or_left_comm, or_comm]
              · simp [insert, h1, hl', hrot]
                ext y
                change y ∈ Insert.insert k (keys (node b pb lb rb) ∪ keys r) ↔
                       y ∈ Insert.insert x (Insert.insert k (keys l ∪ keys r))
                rw [hlkey]
                simp [Finset.mem_insert, Finset.mem_union, or_assoc, or_left_comm, or_comm]
      · by_cases h2 : k < x
        · -- k < x
          cases hr' : insert x p r with
          | nil =>
              exfalso
              exact insert_ne_nil x p r hr'
          | node b pb lb rb =>
              have hrkey : keys (node b pb lb rb) = Insert.insert x (keys r) := by
                rw [← hr']
                exact ih_r
              by_cases hrot : pb > pk
              · simp [insert, h1, h2, hr', hrot]
                rw [keys_rotL]
                ext y
                change y ∈ Insert.insert k (keys l ∪ keys (node b pb lb rb)) ↔
                       y ∈ Insert.insert x (Insert.insert k (keys l ∪ keys r))
                rw [hrkey]
                simp [Finset.mem_insert, Finset.mem_union, or_assoc, or_left_comm, or_comm]
              · simp [insert, h1, h2, hr', hrot]
                ext y
                change y ∈ Insert.insert k (keys l ∪ keys (node b pb lb rb)) ↔
                       y ∈ Insert.insert x (Insert.insert k (keys l ∪ keys r))
                rw [hrkey]
                simp [Finset.mem_insert, Finset.mem_union, or_assoc, or_left_comm, or_comm]
        · -- x = k: insert keeps the node unchanged
          have hxk : x = k := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
          simp [insert, h1, h2, hxk, keys, Finset.insert_idem]

/-- A treap is a *binary search tree* when every key in the left subtree is
smaller than the root and every key in the right subtree is larger, and this
holds recursively. -/
def IsBST [LinearOrder α] [DecidableEq α] : Treap α → Prop
  | nil => True
  | node k _ l r =>
      IsBST l ∧ IsBST r ∧ (∀ y ∈ keys l, y < k) ∧ (∀ y ∈ keys r, k < y)

/-- Right rotation preserves well-formedness (BST). -/
theorem IsBST_rotR [LinearOrder α] [DecidableEq α] [DecidableLT α] {t : Treap α}
    (h : IsBST t) : IsBST (rotR t) := by
  cases t with
  | nil => simpa [rotR] using h
  | node a pa l r =>
      cases l with
      | nil => simpa [rotR] using h
      | node b pb lb rb =>
          rcases h with ⟨hl, hr, hlt, hgt⟩
          rcases hl with ⟨hlb, hrb, hltb, hgtrb⟩
          have hba : b < a := hlt b (by simp [keys])
          simp [rotR]
          refine ⟨hlb, ?_, hltb, ?_⟩
          · -- IsBST (node a pa rb r)
            refine ⟨hrb, hr, ?_, hgt⟩
            intro y hy
            exact hlt y (by simp [keys, hy])
          · -- ∀ y ∈ keys (node a pa rb r), b < y
            intro y hy
            have hy' : y ∈ Insert.insert a (keys rb ∪ keys r) := by simpa [keys] using hy
            by_cases hya : y = a
            · rw [hya]; exact hba
            · by_cases hyrb : y ∈ keys rb
              · exact hgtrb y hyrb
              · have hyr : y ∈ keys r := by simpa [hya, hyrb] using hy'
                exact lt_trans hba (hgt y hyr)

/-- Left rotation preserves well-formedness (BST). -/
theorem IsBST_rotL [LinearOrder α] [DecidableEq α] [DecidableLT α] {t : Treap α}
    (h : IsBST t) : IsBST (rotL t) := by
  cases t with
  | nil => simpa [rotL] using h
  | node a pa l r =>
      cases r with
      | nil => simpa [rotL] using h
      | node b pb lb rb =>
          rcases h with ⟨hl, hr, hlt, hgt⟩
          rcases hr with ⟨hlb, hrb, hltb, hgtrb⟩
          have hab : a < b := hgt b (by simp [keys])
          simp [rotL]
          refine ⟨?_, hrb, ?_, hgtrb⟩
          · -- IsBST (node a pa l lb)
            refine ⟨hl, hlb, hlt, ?_⟩
            intro y hy
            exact hgt y (by simp [keys, hy])
          · -- ∀ y ∈ keys (node a pa l lb), y < b
            intro y hy
            have hy' : y ∈ Insert.insert a (keys l ∪ keys lb) := by simpa [keys] using hy
            by_cases hyb : y ∈ keys lb
            · exact hltb y hyb
            · by_cases hya : y = a
              · rw [hya]; exact hab
              · have hyl : y ∈ keys l := by simpa [hya, hyb] using hy'
                exact lt_trans (hlt y hyl) hab

/-- Inserting into a well-formed treap keeps it well-formed. -/
theorem IsBST_insert [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p : Nat)
    (t : Treap α) : IsBST t → IsBST (insert x p t) := by
  induction t with
  | nil => intro _; simp [insert, IsBST, keys]
  | node k pk l r ih_l ih_r =>
      intro h
      rcases h with ⟨hl, hr, hlt, hgt⟩
      by_cases h1 : x < k
      · by_cases h2 : k < x
        · exfalso
          exact (lt_asymm h1 h2)
        · cases hl' : insert x p l with
          | nil => exfalso; exact insert_ne_nil x p l hl'
          | node b pb lb rb =>
              have hlbst : IsBST (node b pb lb rb) := by
                rw [← hl']
                exact ih_l hl
              have hnew : IsBST (node k pk (node b pb lb rb) r) := by
                refine ⟨hlbst, hr, ?_, hgt⟩
                intro y hy
                have hyins : y ∈ keys (insert x p l) := by rw [hl']; exact hy
                have hykeys : y ∈ Insert.insert x (keys l) := by
                  rw [keys_insert x p l] at hyins
                  exact hyins
                by_cases hyx : y = x
                · rw [hyx]; exact h1
                · exact hlt y (by simpa [hyx] using hykeys)
              by_cases hrot : pb > pk
              · have hrot' : IsBST (rotR (node k pk (node b pb lb rb) r)) := IsBST_rotR hnew
                simpa [insert, h1, hl', hrot]
              · simpa [insert, h1, hl', hrot]
      · by_cases h2 : k < x
        · cases hr' : insert x p r with
          | nil => exfalso; exact insert_ne_nil x p r hr'
          | node b pb lb rb =>
              have hrbst : IsBST (node b pb lb rb) := by
                rw [← hr']
                exact ih_r hr
              have hnew : IsBST (node k pk l (node b pb lb rb)) := by
                refine ⟨hl, hrbst, hlt, ?_⟩
                intro y hy
                have hyins : y ∈ keys (insert x p r) := by rw [hr']; exact hy
                have hykeys : y ∈ Insert.insert x (keys r) := by
                  rw [keys_insert x p r] at hyins
                  exact hyins
                by_cases hyx : y = x
                · rw [hyx]; exact h2
                · exact hgt y (by simpa [hyx] using hykeys)
              by_cases hrot : pb > pk
              · have hrot' : IsBST (rotL (node k pk l (node b pb lb rb))) := IsBST_rotL hnew
                simpa [insert, h1, h2, hr', hrot]
              · simpa [insert, h1, h2, hr', hrot]
        · -- x = k: insert keeps the node unchanged
          simp [insert, h1, h2]
          exact ⟨hl, hr, hlt, hgt⟩

/-- In a well-formed treap, the guided search agrees with set membership. -/
theorem member_iff_keys [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) :
    ∀ t : Treap α, IsBST t → (member x t = true ↔ x ∈ keys t) := by
  intro t
  induction t with
  | nil => simp [member, keys]
  | node k pk l r ih_l ih_r =>
      intro h
      rcases h with ⟨hl, hr, hlt, hgt⟩
      by_cases hx : x = k
      · simp [member, keys, hx]
      · have hxne : x ≠ k := hx
        by_cases hxlt : x < k
        · have hxnr : x ∉ keys r := by
            intro hxr
            exact (lt_asymm hxlt (hgt x hxr))
          simp [member, hxne, hxlt]
          rw [ih_l hl]
          simp [keys, hxne, hxnr]
        · have hxnl : x ∉ keys l := by
            intro hxl
            exact hxlt (hlt x hxl)
          simp [member, hxne, hxlt]
          rw [ih_r hr]
          simp [keys, hxne, hxnl]

/-- **Target (proved).**  Membership of {lit}`insert x p t` is the old
membership together with the new key, for well-formed treaps. -/
theorem member_insert [LinearOrder α] [DecidableEq α] [DecidableLT α] (y x : α) (p : Nat)
    (t : Treap α) (h : IsBST t) :
    member y (insert x p t) = true ↔ member y t = true ∨ y = x := by
  rw [member_iff_keys y (insert x p t) (IsBST_insert x p t h), keys_insert,
    member_iff_keys y t h]
  simp [Finset.mem_insert, or_assoc, or_left_comm, or_comm]

/-- **Target (proved).**  Inserting {lit}`x` and then searching for it always
finds it, for well-formed treaps. -/
theorem insert_member [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p : Nat)
    (t : Treap α) (h : IsBST t) : member x (insert x p t) = true := by
  rw [member_iff_keys x (insert x p t) (IsBST_insert x p t h), keys_insert]
  exact Finset.mem_insert_self x (keys t)

end Treap

end CLRS.Extensions
