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

This module is a **prototype**: the executable `insert`/`member` and the
*correctness* half — membership, BST preservation, and max-heap preservation —
are all kernel-checked.  The probabilistic analysis is developed separately:
{lit}`TreapRandom` proves the harmonic expected-depth bound, and
{lit}`TreapHeight` proves the headline {lit}`E[height] ≤ 30 · H_n` result.
These extension pages remain outside the textbook coverage ledger.

The membership theorems carry an {lit}`IsBST` (binary-search-tree) hypothesis:
the executable {lit}`member` really is a guided search, and for a non-BST tree
a rotation can change what the search finds, so the statement is only
meaningful for well-formed trees.

Main results (all kernel-checked):

- Membership: {lit}`keys_insert`, {lit}`member_iff_keys`, {lit}`member_insert`,
  {lit}`insert_member`.
- BST preservation: {lit}`IsBST_insert` (with {lit}`IsBST_rotL`/`IsBST_rotR`).
- Heap preservation: {lit}`prioOf_insert` (the structural core),
  {lit}`IsHeap_insert` (the capstone), with {lit}`prioLE_insert`,
  {lit}`insert_of_mem_keys`, {lit}`IsHeap_rotL`/`IsHeap_rotR`.

Analysis layers:

- {lit}`TreapRandom`: expected depth {lit}`O(log n)` under uniformly random
  distinct priorities.
- {lit}`TreapHeight`: the explicit expected-height bound
  {lit}`E[height] ≤ 30 · H_n`.

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

/-! ## Heap correctness

A treap must also satisfy the *max-heap* property on priorities: every node's
priority is at least its children's.  This section proves that {lit}`insert`
preserves it.  The subtle part is that a single rotation repairs exactly one
heap violation along the insertion path; the structural fact that makes it
tick is {lit}`prioOf_insert` — insertion attaches the new priority {lit}`p`
only to the new key {lit}`x` and leaves every existing key's priority
untouched. -/

/-- The priority attached to a key {lit}`y` in a treap ({lit}`0` if {lit}`y`
is absent). -/
def prioOf [LinearOrder α] [DecidableEq α] [DecidableLT α] (t : Treap α) (y : α) : Nat :=
  match t with
  | nil => 0
  | node k p l r =>
      if y = k then p
      else if y < k then prioOf l y
      else prioOf r y

/-- {lit}`prioLE p t`: the priority of every key present in {lit}`t` is at
most {lit}`p`. -/
def prioLE [LinearOrder α] [DecidableEq α] [DecidableLT α] (p : Nat) (t : Treap α) : Prop :=
  ∀ y ∈ keys t, prioOf t y ≤ p

/-- A treap is a *max-heap on priorities* when every node's priority is at
least the priorities of its children, recursively. -/
def IsHeap [LinearOrder α] [DecidableEq α] [DecidableLT α] : Treap α → Prop
  | nil => True
  | node _ p l r => IsHeap l ∧ IsHeap r ∧ prioLE p l ∧ prioLE p r

/-- Right rotation preserves the priority attached to every key, on a
well-formed (BST) treap. -/
theorem prioOf_rotR [LinearOrder α] [DecidableEq α] [DecidableLT α] {t : Treap α}
    (h : IsBST t) (y : α) : prioOf (rotR t) y = prioOf t y := by
  cases t with
  | nil => rfl
  | node a pa l r =>
      cases l with
      | nil => rfl
      | node b pb lb rb =>
          rcases h with ⟨hl, hr, hlt, hgt⟩
          rcases hl with ⟨hlb, hrb, hltb, hgtrb⟩
          have hba : b < a := hlt b (by simp [keys])
          by_cases h1 : y = b
          · simp [prioOf, rotR, h1, hba, ne_of_lt hba]
          · have h1ne : y ≠ b := h1
            by_cases h2 : y < b
            · have hya : y < a := lt_trans h2 hba
              have hyane : y ≠ a := ne_of_lt hya
              simp [prioOf, rotR, h1ne, h2, hya, hyane]
            · by_cases h3 : y = a
              · have hanb : ¬ a < b := fun hab => lt_asymm hab hba
                simp [prioOf, rotR, h1ne, h2, h3, Ne.symm (ne_of_lt hba), hanb]
              · have h3ne : y ≠ a := h3
                by_cases h4 : y < a
                · simp [prioOf, rotR, h1ne, h2, h3ne, h4]
                · simp [prioOf, rotR, h1ne, h2, h3ne, h4]

/-- Left rotation preserves the priority attached to every key, on a
well-formed (BST) treap. -/
theorem prioOf_rotL [LinearOrder α] [DecidableEq α] [DecidableLT α] {t : Treap α}
    (h : IsBST t) (y : α) : prioOf (rotL t) y = prioOf t y := by
  cases t with
  | nil => rfl
  | node a pa l r =>
      cases r with
      | nil => rfl
      | node b pb lb rb =>
          rcases h with ⟨hl, hr, hlt, hgt⟩
          rcases hr with ⟨hlb, hrb, hltb, hgtrb⟩
          have hab : a < b := hgt b (by simp [keys])
          by_cases h1 : y = a
          · simp [prioOf, rotL, h1, hab, ne_of_lt hab]
          · have h1ne : y ≠ a := h1
            by_cases h2 : y < a
            · have hyb : y < b := lt_trans h2 hab
              have hybne : y ≠ b := ne_of_lt hyb
              simp [prioOf, rotL, h1ne, h2, hyb, hybne]
            · by_cases h3 : y = b
              · have hbna : ¬ b < a := fun hba => lt_asymm hba hab
                simp [prioOf, rotL, h1ne, h2, h3, Ne.symm (ne_of_lt hab), hbna]
              · have h3ne : y ≠ b := h3
                by_cases h4 : y < b
                · simp [prioOf, rotL, h1ne, h2, h3ne, h4]
                · simp [prioOf, rotL, h1ne, h2, h3ne, h4]

/-- Inserting a fresh key attaches the new priority {lit}`p` exactly to the
new key {lit}`x` and leaves every existing key's priority untouched. -/
theorem prioOf_insert [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p : Nat)
    (t : Treap α) (h : IsBST t) (hx : x ∉ keys t) :
    ∀ y : α, prioOf (insert x p t) y = if y = x then p else prioOf t y := by
  intro y
  induction t with
  | nil => simp [insert, prioOf]
  | node k pk l r ih_l ih_r =>
      rcases h with ⟨hl, hr, hlt, hgt⟩
      have hxl : x ∉ keys l := by
        intro hxl'
        exact hx (by simp [keys, hxl'])
      have hxr : x ∉ keys r := by
        intro hxr'
        exact hx (by simp [keys, hxr'])
      by_cases h1 : x < k
      · by_cases h2 : k < x
        · exfalso
          exact (lt_asymm h1 h2)
        · -- x < k
          cases hl' : insert x p l with
          | nil => exfalso; exact insert_ne_nil x p l hl'
          | node b pb lb rb =>
              have hlbst : IsBST (node b pb lb rb) := by rw [← hl']; exact IsBST_insert x p l hl
              have hnew : IsBST (node k pk (node b pb lb rb) r) := by
                refine ⟨hlbst, hr, ?_, hgt⟩
                intro z hz
                have hzins : z ∈ keys (insert x p l) := by rw [hl']; exact hz
                have hzkeys : z ∈ Insert.insert x (keys l) := by rw [keys_insert x p l] at hzins; exact hzins
                by_cases hzx : z = x
                · rw [hzx]; exact h1
                · exact hlt z (by simpa [hzx] using hzkeys)
              by_cases hrot : pb > pk
              · -- rotR branch
                simp [insert, h1, hl', hrot]
                have hprio : prioOf (rotR (node k pk (node b pb lb rb) r)) y =
                    prioOf (node k pk (node b pb lb rb) r) y := prioOf_rotR hnew y
                rw [hprio]
                by_cases hyk : y = k
                · simp [prioOf, hyk, Ne.symm (ne_of_lt h1)]
                · have hykne : y ≠ k := hyk
                  by_cases hylt : y < k
                  · rw [← hl']
                    simp [prioOf, hykne, hylt]
                    exact ih_l hl hxl
                  · have hyxne : y ≠ x := fun hyx => hylt (by simpa [hyx] using h1)
                    simp [prioOf, hykne, hylt, hyxne]
              · simp [insert, h1, hl', hrot]
                by_cases hyk : y = k
                · simp [prioOf, hyk, Ne.symm (ne_of_lt h1)]
                · have hykne : y ≠ k := hyk
                  by_cases hylt : y < k
                  · rw [← hl']
                    simp [prioOf, hykne, hylt]
                    exact ih_l hl hxl
                  · have hyxne : y ≠ x := fun hyx => hylt (by simpa [hyx] using h1)
                    simp [prioOf, hykne, hylt, hyxne]
      · by_cases h2 : k < x
        · -- k < x
          cases hr' : insert x p r with
          | nil => exfalso; exact insert_ne_nil x p r hr'
          | node b pb lb rb =>
              have hrbst : IsBST (node b pb lb rb) := by rw [← hr']; exact IsBST_insert x p r hr
              have hnew : IsBST (node k pk l (node b pb lb rb)) := by
                refine ⟨hl, hrbst, hlt, ?_⟩
                intro z hz
                have hzins : z ∈ keys (insert x p r) := by rw [hr']; exact hz
                have hzkeys : z ∈ Insert.insert x (keys r) := by rw [keys_insert x p r] at hzins; exact hzins
                by_cases hzx : z = x
                · rw [hzx]; exact h2
                · exact hgt z (by simpa [hzx] using hzkeys)
              by_cases hrot : pb > pk
              · -- rotL branch
                simp [insert, h1, h2, hr', hrot]
                have hprio : prioOf (rotL (node k pk l (node b pb lb rb))) y =
                    prioOf (node k pk l (node b pb lb rb)) y := prioOf_rotL hnew y
                rw [hprio]
                by_cases hyk : y = k
                · simp [prioOf, hyk, ne_of_lt h2]
                · have hykne : y ≠ k := hyk
                  by_cases hylt : y < k
                  · have hyxne : y ≠ x := fun hyx => h1 (by simpa [hyx] using hylt)
                    simp [prioOf, hykne, hylt, hyxne]
                  · rw [← hr']
                    simp [prioOf, hykne, hylt]
                    exact ih_r hr hxr
              · simp [insert, h1, h2, hr', hrot]
                by_cases hyk : y = k
                · simp [prioOf, hyk, ne_of_lt h2]
                · have hykne : y ≠ k := hyk
                  by_cases hylt : y < k
                  · have hyxne : y ≠ x := fun hyx => h1 (by simpa [hyx] using hylt)
                    simp [prioOf, hykne, hylt, hyxne]
                  · rw [← hr']
                    simp [prioOf, hykne, hylt]
                    exact ih_r hr hxr
        · -- x = k (impossible: x is fresh)
          have hxk : x = k := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
          exfalso
          exact hx (by simp [keys, hxk])

/-- Inserting an already-present key leaves the treap unchanged (duplicate
keys are ignored), on a well-formed treap. -/
theorem insert_of_mem_keys [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p : Nat)
    (t : Treap α) (h : IsBST t) (hh : IsHeap t) : x ∈ keys t → insert x p t = t := by
  intro hx
  induction t with
  | nil => simp [keys] at hx
  | node k pk l r ih_l ih_r =>
      rcases h with ⟨hl, hr, hlt, hgt⟩
      rcases hh with ⟨hhl, hhr, hpl, hpr⟩
      by_cases h1 : x < k
      · by_cases h2 : k < x
        · exfalso
          exact (lt_asymm h1 h2)
        · -- x < k: the BST routes x into the left subtree
          have hxl : x ∈ keys l := by
            have hx' : x ∈ Insert.insert k (keys l ∪ keys r) := by simpa [keys] using hx
            have hxk : x ≠ k := ne_of_lt h1
            have hxnr : x ∉ keys r := by
              intro hxr
              exact (lt_asymm h1 (hgt x hxr))
            simpa [hxk, hxnr] using hx'
          have hrec : insert x p l = l := ih_l hl hhl hxl
          simp [insert, h1, hrec]
          cases l with
          | nil => simp
          | node b pb lb rb =>
              have hpb_pk : pb ≤ pk := by
                simpa [prioOf] using hpl b (by simp [keys])
              by_cases hrot : pb > pk
              · exfalso
                exact (not_lt_of_ge hpb_pk) hrot
              · simp [hrot]
      · by_cases h2 : k < x
        · -- k < x: the BST routes x into the right subtree
          have hxr : x ∈ keys r := by
            have hx' : x ∈ Insert.insert k (keys l ∪ keys r) := by simpa [keys] using hx
            have hxk : x ≠ k := ne_of_gt h2
            have hxnl : x ∉ keys l := by
              intro hxl
              exact (lt_asymm (hlt x hxl) h2)
            simpa [hxk, hxnl] using hx'
          have hrec : insert x p r = r := ih_r hr hhr hxr
          simp [insert, h1, h2, hrec]
          cases r with
          | nil => simp
          | node b pb lb rb =>
              have hpb_pk : pb ≤ pk := by
                simpa [prioOf] using hpr b (by simp [keys])
              by_cases hrot : pb > pk
              · exfalso
                exact (not_lt_of_ge hpb_pk) hrot
              · simp [hrot]
        · -- x = k: the node is returned unchanged
          simp [insert, h1, h2]

/-- Inserting a key of priority {lit}`p ≤ c` into a treap whose priorities are
all at most {lit}`c` keeps every priority at most {lit}`c`. -/
theorem prioLE_insert [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p c : Nat)
    (t : Treap α) (h : IsBST t) (hh : IsHeap t) (hc : prioLE c t) (hp : p ≤ c) :
    prioLE c (insert x p t) := by
  unfold prioLE
  intro y hy
  have hy' : y ∈ Insert.insert x (keys t) := by
    rw [keys_insert x p t] at hy
    exact hy
  by_cases hxm : x ∈ keys t
  · -- duplicate: insert keeps the tree, so the bound is unchanged
    have hdup : insert x p t = t := insert_of_mem_keys x p t h hh hxm
    rw [hdup] at hy ⊢
    exact hc y hy
  · -- fresh key: the only new priority is `p`, which is already ≤ c
    by_cases hyx : y = x
    · rw [prioOf_insert x p t h hxm y]
      simp [hyx]
      exact hp
    · have hyt : y ∈ keys t := by
        simpa [hyx] using hy'
      rw [prioOf_insert x p t h hxm y]
      simp [hyx]
      exact hc y hyt

/-- The priority of an absent key is {lit}`0`. -/
theorem prioOf_eq_zero_of_not_mem [LinearOrder α] [DecidableEq α] [DecidableLT α] {t : Treap α}
    {y : α} (h : y ∉ keys t) : prioOf t y = 0 := by
  induction t with
  | nil => rfl
  | node k pk l r ih_l ih_r =>
      have hyk : y ≠ k := by
        intro hyk
        exact h (by simp [keys, hyk])
      by_cases hylt : y < k
      · have hyl : y ∉ keys l := by
          intro hyl'
          exact h (by simp [keys, hyl'])
        simp [prioOf, hyk, hylt]
        exact ih_l hyl
      · have hyr : y ∉ keys r := by
          intro hyr'
          exact h (by simp [keys, hyr'])
        simp [prioOf, hyk, hylt]
        exact ih_r hyr

/-- A {lit}`prioLE` bound applies to the priority of every key, present or
absent. -/
theorem prioOf_le_of_prioLE [LinearOrder α] [DecidableEq α] [DecidableLT α] {t : Treap α}
    {c : Nat} (h : prioLE c t) : ∀ y, prioOf t y ≤ c := by
  intro y
  by_cases hym : y ∈ keys t
  · exact h y hym
  · have hz : prioOf t y = 0 := prioOf_eq_zero_of_not_mem hym
    rw [hz]
    exact Nat.zero_le c

/-- Promoting the left child above the root keeps the max-heap property, given
that the promoted child's priority is at least the root's and the moved subtree
stays bounded by the root's priority. -/
theorem IsHeap_rotR [LinearOrder α] [DecidableEq α] [DecidableLT α] {a b : α} {pa pb : Nat}
    {lb rb r : Treap α} (hl' : IsHeap (node b pb lb rb)) (hr : IsHeap r)
    (hpb : pa ≤ pb) (hpa_rb : prioLE pa rb) (hpa_r : prioLE pa r) :
    IsHeap (rotR (node a pa (node b pb lb rb) r)) := by
  rcases hl' with ⟨hlb, hrb, hpb_lb, hpb_rb⟩
  change IsHeap (node b pb lb (node a pa rb r))
  refine ⟨hlb, ?_, hpb_lb, ?_⟩
  · -- IsHeap (node a pa rb r)
    refine ⟨hrb, hr, hpa_rb, hpa_r⟩
  · -- prioLE pb (node a pa rb r)
    unfold prioLE
    intro y hy
    have hy' : y ∈ Insert.insert a (keys rb ∪ keys r) := by simpa [keys] using hy
    by_cases hya : y = a
    · rw [hya]
      have hpa_prio : prioOf (node a pa rb r) a = pa := by simp [prioOf]
      rw [hpa_prio]
      exact hpb
    · have hya_ne : y ≠ a := hya
      by_cases hylt : y < a
      · have hprio : prioOf (node a pa rb r) y = prioOf rb y := by
          simp [prioOf, hya_ne, hylt]
        rw [hprio]
        exact prioOf_le_of_prioLE hpb_rb y
      · have hprio : prioOf (node a pa rb r) y = prioOf r y := by
          simp [prioOf, hya_ne, hylt]
        rw [hprio]
        exact le_trans (prioOf_le_of_prioLE hpa_r y) hpb

/-- Promoting the right child above the root keeps the max-heap property,
symmetrically. -/
theorem IsHeap_rotL [LinearOrder α] [DecidableEq α] [DecidableLT α] {a b : α} {pa pb : Nat}
    {l lb rb : Treap α} (hl : IsHeap l) (hr' : IsHeap (node b pb lb rb))
    (hpb : pa ≤ pb) (hpa_lb : prioLE pa lb) (hpa_l : prioLE pa l) :
    IsHeap (rotL (node a pa l (node b pb lb rb))) := by
  rcases hr' with ⟨hlb, hrb, hpb_lb, hpb_rb⟩
  change IsHeap (node b pb (node a pa l lb) rb)
  refine ⟨?_, hrb, ?_, hpb_rb⟩
  · -- IsHeap (node a pa l lb)
    refine ⟨hl, hlb, hpa_l, hpa_lb⟩
  · -- prioLE pb (node a pa l lb)
    unfold prioLE
    intro y hy
    have hy' : y ∈ Insert.insert a (keys l ∪ keys lb) := by simpa [keys] using hy
    by_cases hya : y = a
    · rw [hya]
      have hpa_prio : prioOf (node a pa l lb) a = pa := by simp [prioOf]
      rw [hpa_prio]
      exact hpb
    · have hya_ne : y ≠ a := hya
      by_cases hylt : y < a
      · have hprio : prioOf (node a pa l lb) y = prioOf l y := by
          simp [prioOf, hya_ne, hylt]
        rw [hprio]
        exact le_trans (prioOf_le_of_prioLE hpa_l y) hpb
      · have hprio : prioOf (node a pa l lb) y = prioOf lb y := by
          simp [prioOf, hya_ne, hylt]
        rw [hprio]
        exact le_trans (prioOf_le_of_prioLE hpa_lb y) hpb

/-- In a max-heap treap, if the root priority is at most {lit}`c` then every
priority is at most {lit}`c`. -/
theorem prioLE_of_heap_root_le [LinearOrder α] [DecidableEq α] [DecidableLT α]
    {b : α} {pb c : Nat} {lb rb : Treap α}
    (hheap : IsHeap (node b pb lb rb)) (hpb : pb ≤ c) :
    prioLE c (node b pb lb rb) := by
  rcases hheap with ⟨hlb, hrb, hpb_lb, hpb_rb⟩
  unfold prioLE
  intro y hy
  have hy' : y ∈ Insert.insert b (keys lb ∪ keys rb) := by simpa [keys] using hy
  by_cases hyb : y = b
  · rw [hyb]
    have hprio : prioOf (node b pb lb rb) b = pb := by simp [prioOf]
    rw [hprio]
    exact hpb
  · by_cases hylt : y < b
    · have hprio : prioOf (node b pb lb rb) y = prioOf lb y := by simp [prioOf, hyb, hylt]
      rw [hprio]
      exact le_trans (prioOf_le_of_prioLE hpb_lb y) hpb
    · have hprio : prioOf (node b pb lb rb) y = prioOf rb y := by simp [prioOf, hyb, hylt]
      rw [hprio]
      exact le_trans (prioOf_le_of_prioLE hpb_rb y) hpb

/-- **Capstone.**  Inserting into a well-formed (BST + heap) treap keeps it a
valid treap: the single rotation along the insertion path repairs exactly the
one heap violation. -/
theorem IsHeap_insert [LinearOrder α] [DecidableEq α] [DecidableLT α] (x : α) (p : Nat)
    (t : Treap α) : IsBST t → IsHeap t → IsHeap (insert x p t) := by
  intro h hh
  induction t with
  | nil => simp [insert, IsHeap, prioLE, keys]
  | node k pk l r ih_l ih_r =>
      rcases h with ⟨hl, hr, hlt, hgt⟩
      rcases hh with ⟨hhl, hhr, hpl, hpr⟩
      by_cases h1 : x < k
      · by_cases h2 : k < x
        · exfalso
          exact (lt_asymm h1 h2)
        · -- x < k: insert into the left subtree
          have hhl' : IsHeap (insert x p l) := ih_l hl hhl
          cases hl' : insert x p l with
          | nil => exfalso; exact insert_ne_nil x p l hl'
          | node b pb lb rb =>
              have hlbst' : IsBST (node b pb lb rb) := by rw [← hl']; exact IsBST_insert x p l hl
              have hhl'' : IsHeap (node b pb lb rb) := by simpa [hl'] using hhl'
              by_cases hrot : pb > pk
              · -- rotation branch: the moved subtree rb stays bounded by pk
                have hxnl : x ∉ keys l := by
                  intro hxl
                  have hdup : insert x p l = l := insert_of_mem_keys x p l hl hhl hxl
                  rw [hdup] at hl'
                  have hpb_pk : pb ≤ pk := by
                    have hpb' : prioOf l b ≤ pk := hpl b (by simp [keys, hl'])
                    simpa [hl', prioOf] using hpb'
                  exact (not_lt_of_ge hpb_pk) hrot
                have hbx : b = x := by
                  have hb_mem' : b ∈ keys (insert x p l) := by rw [hl']; simp [keys]
                  have hbmem : b ∈ Insert.insert x (keys l) := by
                    rw [keys_insert x p l] at hb_mem'
                    exact hb_mem'
                  by_cases hbxl : b = x
                  · exact hbxl
                  · exfalso
                    have hb_l : b ∈ keys l := by simpa [hbxl] using hbmem
                    have hpb_eq : pb = prioOf l b := by
                      have hpi : prioOf (insert x p l) b = if b = x then p else prioOf l b :=
                        prioOf_insert x p l hl hxnl b
                      have hpi' : prioOf (insert x p l) b = pb := by rw [hl']; simp [prioOf]
                      rw [hpi'] at hpi
                      simp [hbxl] at hpi
                      exact hpi
                    have hpb_pk : pb ≤ pk := by rw [hpb_eq]; exact hpl b hb_l
                    exact (not_lt_of_ge hpb_pk) hrot
                have hpk_rb : prioLE pk rb := by
                  unfold prioLE
                  intro z hz
                  have hb_lt_z : b < z := hlbst'.2.2.2 z hz
                  have hzx : z ≠ x := by
                    intro hzx'
                    have : x < x := by simp [hbx, hzx'] at hb_lt_z ⊢
                    exact (lt_irrefl x this)
                  have hzins : z ∈ keys (insert x p l) := by rw [hl']; simp [keys, hz]
                  have hzkeys : z ∈ Insert.insert x (keys l) := by
                    rw [keys_insert x p l] at hzins
                    exact hzins
                  have hzl : z ∈ keys l := by simpa [hzx] using hzkeys
                  have hprio : prioOf rb z = prioOf l z := by
                    have hpi : prioOf (insert x p l) z = if z = x then p else prioOf l z :=
                      prioOf_insert x p l hl hxnl z
                    have hpi' : prioOf (insert x p l) z = prioOf rb z := by
                      rw [hl']
                      have hzb : z ≠ b := ne_of_gt hb_lt_z
                      have hznlt : ¬ z < b := not_lt_of_gt hb_lt_z
                      simp [prioOf, hzb, hznlt]
                    rw [hpi'] at hpi
                    simp [hzx] at hpi
                    exact hpi
                  rw [hprio]
                  exact hpl z hzl
                simp [insert, h1, hl', hrot]
                exact IsHeap_rotR hhl'' hhr (le_of_lt hrot) hpk_rb hpr
              · -- no rotation: the root priority already bounds everything
                simp [insert, h1, hl', hrot]
                refine ⟨hhl'', hhr, prioLE_of_heap_root_le hhl'' (not_lt.mp hrot), hpr⟩
      · by_cases h2 : k < x
        · -- k < x: insert into the right subtree (symmetric)
          have hhr' : IsHeap (insert x p r) := ih_r hr hhr
          cases hr' : insert x p r with
          | nil => exfalso; exact insert_ne_nil x p r hr'
          | node b pb lb rb =>
              have hrbst' : IsBST (node b pb lb rb) := by rw [← hr']; exact IsBST_insert x p r hr
              have hhr'' : IsHeap (node b pb lb rb) := by simpa [hr'] using hhr'
              by_cases hrot : pb > pk
              · -- rotation branch: the moved subtree lb stays bounded by pk
                have hxnr : x ∉ keys r := by
                  intro hxr
                  have hdup : insert x p r = r := insert_of_mem_keys x p r hr hhr hxr
                  rw [hdup] at hr'
                  have hpb_pk : pb ≤ pk := by
                    have hpb' : prioOf r b ≤ pk := hpr b (by simp [keys, hr'])
                    simpa [hr', prioOf] using hpb'
                  exact (not_lt_of_ge hpb_pk) hrot
                have hbx : b = x := by
                  have hb_mem' : b ∈ keys (insert x p r) := by rw [hr']; simp [keys]
                  have hbmem : b ∈ Insert.insert x (keys r) := by
                    rw [keys_insert x p r] at hb_mem'
                    exact hb_mem'
                  by_cases hbxl : b = x
                  · exact hbxl
                  · exfalso
                    have hb_r : b ∈ keys r := by simpa [hbxl] using hbmem
                    have hpb_eq : pb = prioOf r b := by
                      have hpi : prioOf (insert x p r) b = if b = x then p else prioOf r b :=
                        prioOf_insert x p r hr hxnr b
                      have hpi' : prioOf (insert x p r) b = pb := by rw [hr']; simp [prioOf]
                      rw [hpi'] at hpi
                      simp [hbxl] at hpi
                      exact hpi
                    have hpb_pk : pb ≤ pk := by rw [hpb_eq]; exact hpr b hb_r
                    exact (not_lt_of_ge hpb_pk) hrot
                have hpk_lb : prioLE pk lb := by
                  unfold prioLE
                  intro z hz
                  have hz_lt_b : z < b := hrbst'.2.2.1 z hz
                  have hzx : z ≠ x := by
                    intro hzx'
                    have : x < x := by simp [hbx, hzx'] at hz_lt_b ⊢
                    exact (lt_irrefl x this)
                  have hzins : z ∈ keys (insert x p r) := by rw [hr']; simp [keys, hz]
                  have hzkeys : z ∈ Insert.insert x (keys r) := by
                    rw [keys_insert x p r] at hzins
                    exact hzins
                  have hzr : z ∈ keys r := by simpa [hzx] using hzkeys
                  have hprio : prioOf lb z = prioOf r z := by
                    have hpi : prioOf (insert x p r) z = if z = x then p else prioOf r z :=
                      prioOf_insert x p r hr hxnr z
                    have hpi' : prioOf (insert x p r) z = prioOf lb z := by
                      rw [hr']
                      have hzb : z ≠ b := ne_of_lt hz_lt_b
                      simp [prioOf, hzb, hz_lt_b]
                    rw [hpi'] at hpi
                    simp [hzx] at hpi
                    exact hpi
                  rw [hprio]
                  exact hpr z hzr
                simp [insert, h1, h2, hr', hrot]
                exact IsHeap_rotL hhl hhr'' (le_of_lt hrot) hpk_lb hpl
              · -- no rotation
                simp [insert, h1, h2, hr', hrot]
                refine ⟨hhl, hhr'', hpl, prioLE_of_heap_root_le hhr'' (not_lt.mp hrot)⟩
        · -- x = k: duplicate, tree unchanged
          simp [insert, h1, h2]
          exact ⟨hhl, hhr, hpl, hpr⟩

end Treap

end CLRS.Extensions
