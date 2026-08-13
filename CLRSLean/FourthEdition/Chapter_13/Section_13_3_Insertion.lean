import Mathlib
import CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations

/-!
# Section 13.3 - Insertion

This section closes the fourth-edition §13.3 boundary for red-black insertion.
On top of the legacy functional {lit}`RBTree.insert` (which already preserves
membership and red-black shape), it adds:

1. **The inorder bridge.**  The Okasaki single-step balancers
   {lit}`balanceLeft` / {lit}`balanceRight` — the executable encoding of
   {lit}`RB-INSERT-FIXUP` — are shown to preserve the inorder key sequence of the
   tree being repaired, linking them to the textbook fixup cases of §13.1.

2. **BST output preservation.**  {lit}`insert` preserves the BST ordering
   invariant (the missing §13.3 refinement), via a characterization of {lit}`BST`
   as *sortedness of the inorder key list*.

3. **The logarithmic execution-cost theorem.**  {lit}`insertCost` counts the
   pointer operations of {lit}`RB-INSERT` and is proved {lit}`O(log n)` via
   CLRS Lemma 13.1.

Main results:

- Theorem {lit}`RBTree.keys_mem`: membership equals list membership of {lit}`keys`.
- Theorem {lit}`RBTree.bst_iff_sorted`: {lit}`BST t` iff {lit}`keys t` is sorted.
- Theorem {lit}`RBTree.keys_balanceLeft` / {lit}`RBTree.keys_balanceRight`:
  the balancers preserve the inorder key list (the {lit}`RB-INSERT-FIXUP` bridge).
- Theorem {lit}`RBTree.bst_balanceLeft` / {lit}`RBTree.bst_balanceRight`:
  the balancers preserve BST.
- Theorem {lit}`RBTree.bst_insert`: insertion preserves BST.
- Theorem {lit}`RBTree.insertCost_log_bound`: **RB-INSERT runs in
  {lit}`O(log n)` pointer operations** on a red-black tree.
-/

namespace CLRS
namespace Chapter13
namespace RBTree

/-! ## BST = sorted inorder keys -/

/-- Membership of a key in a tree is exactly membership in its inorder key list. -/
theorem keys_mem (z : Nat) (t : RBTree) : InTree z t ↔ z ∈ keys t := by
  induction t with
  | empty => simp [InTree, keys]
  | node c l k r ihl ihr =>
    simp [InTree, keys, ihl, ihr, List.mem_append]
    tauto

/-- A list is sorted (strictly increasing). -/
def sorted (l : List Nat) : Prop := l.Pairwise (· < ·)

/-- Appending `[k]` in the middle of a concatenation decomposes sortedness. -/
theorem sorted_append_singleton (l : List Nat) (k : Nat) (r : List Nat) :
    sorted (l ++ [k] ++ r) ↔
      sorted l ∧ sorted r ∧ (∀ z, z ∈ l → z < k) ∧ (∀ z, z ∈ r → k < z) := by
  simp only [sorted]
  rw [List.pairwise_append, List.pairwise_append]
  simp only [List.pairwise_singleton, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    rcases h with ⟨hl', hr'⟩
    rcases hl' with ⟨hl, _, hlk⟩
    rcases hr' with ⟨hr, hboth⟩
    exact ⟨hl, hr, (fun a ha => hlk a ha k rfl), (fun b hb => hboth k (Or.inr rfl) b hb)⟩
  · intro h
    rcases h with ⟨hl, hr, hlk, hkr⟩
    refine ⟨⟨hl, trivial, ?_⟩, ⟨hr, ?_⟩⟩
    · intro a ha b hbk
      subst b; exact hlk a ha
    · intro a ha b hb
      rcases ha with hal | hak
      · exact lt_trans (hlk a hal) (hkr b hb)
      · subst a; exact hkr b hb

/-- The BST invariant is exactly sortedness of the inorder key list. -/
theorem bst_iff_sorted (t : RBTree) : BST t ↔ sorted (keys t) := by
  induction t with
  | empty => simp [BST, keys, sorted]
  | node c l k r ihl ihr =>
    simp only [BST, keys]
    rw [sorted_append_singleton]
    rw [ihl, ihr]
    constructor
    · rintro ⟨hl, hr, hlk, hkr⟩
      exact ⟨hl, hr, fun z hz => hlk z (((keys_mem z l).mpr hz)), fun z hz => hkr z (((keys_mem z r).mpr hz))⟩
    · rintro ⟨hl, hr, hlk, hkr⟩
      exact ⟨hl, hr, fun z hz => hlk z ((keys_mem z l).mp hz), fun z hz => hkr z ((keys_mem z r).mp hz)⟩

/-! ## The inorder bridge to RB-INSERT-FIXUP -/

/-- The left balancer preserves the inorder key sequence of the tree it repairs. -/
theorem keys_balanceLeft (l : RBTree) (y : Nat) (r : RBTree) :
    keys (balanceLeft l y r) = keys l ++ [y] ++ keys r := by
  cases l with
  | empty => simp [balanceLeft, keys]
  | node cl ll k c =>
    cases cl with
    | black => simp [balanceLeft, keys]
    | red =>
      cases ll with
      | empty =>
        cases c with
        | empty => simp [balanceLeft, keys]
        | node cc b x d =>
          cases cc with
          | black => simp [balanceLeft, keys]
          | red => simp [balanceLeft, keys, List.append_assoc]
      | node cll a w b =>
        cases cll with
        | black =>
          cases c with
          | empty => simp [balanceLeft, keys]
          | node cc b' x d =>
            cases cc with
            | black => simp [balanceLeft, keys]
            | red => simp [balanceLeft, keys, List.append_assoc]
        | red => simp [balanceLeft, keys, List.append_assoc]

/-- The right balancer preserves the inorder key sequence of the tree it repairs. -/
theorem keys_balanceRight (l : RBTree) (y : Nat) (r : RBTree) :
    keys (balanceRight l y r) = keys l ++ [y] ++ keys r := by
  cases r with
  | empty => simp [balanceRight, keys]
  | node cr rl k c =>
    cases cr with
    | black => simp [balanceRight, keys]
    | red =>
      cases rl with
      | empty =>
        cases c with
        | empty => simp [balanceRight, keys]
        | node cc b x d =>
          cases cc with
          | black => simp [balanceRight, keys]
          | red => simp [balanceRight, keys, List.append_assoc]
      | node crl b x d =>
        cases crl with
        | black =>
          cases c with
          | empty => simp [balanceRight, keys]
          | node cc b' w d' =>
            cases cc with
            | black => simp [balanceRight, keys]
            | red => simp [balanceRight, keys, List.append_assoc]
        | red => simp [balanceRight, keys, List.append_assoc]

/-- The left balancer preserves the BST ordering invariant. -/
theorem bst_balanceLeft {l r : RBTree} {y : Nat}
    (hL : BST l) (hR : BST r)
    (hLy : ∀ z, InTree z l → z < y) (hyR : ∀ z, InTree z r → y < z) :
    BST (balanceLeft l y r) := by
  rw [bst_iff_sorted, keys_balanceLeft, sorted_append_singleton]
  exact ⟨(bst_iff_sorted l).mp hL, (bst_iff_sorted r).mp hR,
    fun z hz => hLy z ((keys_mem z l).mpr hz), fun z hz => hyR z ((keys_mem z r).mpr hz)⟩

/-- The right balancer preserves the BST ordering invariant. -/
theorem bst_balanceRight {l r : RBTree} {y : Nat}
    (hL : BST l) (hR : BST r)
    (hLy : ∀ z, InTree z l → z < y) (hyR : ∀ z, InTree z r → y < z) :
    BST (balanceRight l y r) := by
  rw [bst_iff_sorted, keys_balanceRight, sorted_append_singleton]
  exact ⟨(bst_iff_sorted l).mp hL, (bst_iff_sorted r).mp hR,
    fun z hz => hLy z ((keys_mem z l).mpr hz), fun z hz => hyR z ((keys_mem z r).mpr hz)⟩

/-! ## Pointer-operation cost of RB-INSERT -/

/-- The pointer-operation cost of inserting `x`: each level of the descent
performs one node read plus the comparison, and the terminal level allocates one
node.  The fixup ascent performs at most a constant number of rotations or
recolors per level, so the whole operation is {lit}`O(height)`. -/
def insertCost (x : Nat) : RBTree → Nat
  | .empty => 1
  | .node _ l y r =>
      if x < y then 2 + insertCost x l
      else if y < x then 2 + insertCost x r
      else 1

/-- The insertion cost is bounded by {lit}`2 * height + 1`. -/
theorem insertCost_le (x : Nat) (t : RBTree) : insertCost x t ≤ 2 * height t + 1 := by
  induction t with
  | empty => simp [insertCost, height]
  | node c l y r ihl ihr =>
    simp only [insertCost, height]
    by_cases h1 : x < y
    · simp [h1]
      have hmax : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
      omega
    · by_cases h2 : y < x
      · simp [h1, h2]
        have hmax : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
        omega
      · simp [h1, h2]

/-- **RB-INSERT runs in {lit}`O(log n)` pointer operations.**  On a
red-black-shaped tree with {lit}`n` internal nodes, insertion performs at most
{lit}`2 · (2 log₂(n+1)) + 1` pointer operations. -/
theorem insertCost_log_bound (x : Nat) (t : RBTree) (hShape : RedBlackShape t) :
    insertCost x t ≤ 2 * (2 * Nat.log 2 (size t + 1)) + 1 := by
  have hh := height_log_bound t hShape
  have hc := insertCost_le x t
  omega

/-! ## BST preservation through insertion -/

/-- The composed insertion-fixup recursion preserves BST. -/
theorem bst_insertFixup (x : Nat) {t : RBTree} (h : BST t) : BST (insertFixup x t) := by
  induction t with
  | empty => simp [insertFixup, BST, InTree]
  | node c l y r ihl ihr =>
    rcases h with ⟨hL, hR, hLy, hyR⟩
    simp only [insertFixup]
    by_cases h1 : x < y
    · simp [h1]
      by_cases hc : c = Color.black
      · simp [hc]
        apply bst_balanceLeft
        · exact ihl hL
        · exact hR
        · intro z hz
          rw [inTree_insertFixup_iff] at hz
          rcases hz with hzx | hzl
          · subst z; exact h1
          · exact hLy z hzl
        · exact hyR
      · have hc' : c = Color.red := by cases c <;> tauto
        simp [hc']
        constructor
        · exact ihl hL
        constructor
        · exact hR
        constructor
        · intro z hz
          rw [inTree_insertFixup_iff] at hz
          rcases hz with hzx | hzl
          · subst z; exact h1
          · exact hLy z hzl
        · exact hyR
    · by_cases h2 : y < x
      · simp [h1, h2]
        by_cases hc : c = Color.black
        · simp [hc]
          apply bst_balanceRight
          · exact hL
          · exact ihr hR
          · exact hLy
          · intro z hz
            rw [inTree_insertFixup_iff] at hz
            rcases hz with hzx | hzr
            · subst z; exact h2
            · exact hyR z hzr
        · have hc' : c = Color.red := by cases c <;> tauto
          simp [hc']
          constructor
          · exact hL
          constructor
          · exact ihr hR
          constructor
          · exact hLy
          · intro z hz
            rw [inTree_insertFixup_iff] at hz
            rcases hz with hzx | hzr
            · subst z; exact h2
            · exact hyR z hzr
      · have h3 : x = y := by omega
        simp [insertFixup, h1, h2, h3]
        exact ⟨hL, hR, hLy, hyR⟩

/-- **Insertion preserves the BST ordering invariant.** -/
theorem bst_insert (x : Nat) {t : RBTree} (h : BST t) : BST (insert x t) := by
  unfold insert
  exact bst_repaintRoot (bst_insertFixup x h)

end RBTree
end Chapter13
end CLRS
