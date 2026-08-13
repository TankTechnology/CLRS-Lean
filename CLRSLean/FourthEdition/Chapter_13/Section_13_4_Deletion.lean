import Mathlib
import CLRSLean.FourthEdition.Chapter_13.Section_13_3_Insertion

/-!
# Section 13.4 - Deletion

This section closes the fourth-edition §13.4 boundary for red-black deletion.
The legacy functional {lit}`RBTree.delete` already preserves membership
({lit}`inTree_delete_iff`) and red-black shape ({lit}`redBlackShape_delete`).
Here we add the remaining **logarithmic execution-cost** layer.

The composed deletion {lit}`RBTree.delete` = {lit}`repaintRoot black (del x t)`:
{lit}`del` searches down the tree, then at the deletion point applies
{lit}`join`, which removes the minimum of the right subtree via {lit}`splitMin`
and rebalances with {lit}`baldL`/`baldR`.  Every one of these stages touches at
most a root-to-leaf path, so the whole operation is {lit}`O(height)` pointer
operations.

Main results:

- Definition {lit}`RBTree.deleteCost`: the auditable pointer-operation cost of
  {lit}`RB-DELETE` (one node read and one comparison per search level, plus the
  {lit}`join`/`splitMin`/rebalance work bounded by the heights of the two
  subtrees).
- Theorem {lit}`RBTree.deleteCost_le`: the deletion cost is bounded by
  {lit}`4 * height + 1`.
- Theorem {lit}`RBTree.deleteCost_log_bound`: **RB-DELETE runs in
  {lit}`O(log n)` pointer operations** on a red-black tree.
- Theorem {lit}`RBTree.bst_delete`: **RB-DELETE preserves the BST ordering
  invariant** — the composed {lit}`delete` keeps the inorder key sequence sorted
  (via {lit}`bst_iff_sorted` and a {lit}`keys` sublist argument through
  {lit}`del`/{lit}`join`/{lit}`splitMin`/{lit}`baldL`/{lit}`baldR`), closing the
  §13.4 ordering refinement alongside the §13.3 {lit}`bst_insert` and the §13.2
  rotation {lit}`bst_rotateLeft`/`bst_rotateRight`.

Current gaps: none for the represented §13.4 boundary; the lower-level
imperative {lit}`RB-DELETE-FIXUP` pointer-rewiring refinement is optional.
-/

namespace CLRS
namespace Chapter13
namespace RBTree

/-! ## Pointer-operation cost of RB-DELETE -/

/-- The pointer-operation cost of deleting `x`: one node read and one comparison
per level of the descent, plus — at the deletion point — the cost of joining the
two subtrees (removing the minimum of the right subtree and rebalancing), which
is bounded by the sum of the two subtree heights. -/
def deleteCost (x : Nat) : RBTree → Nat
  | .empty => 1
  | .node _ l y r =>
      if x < y then 2 + deleteCost x l
      else if y < x then 2 + deleteCost x r
      else 2 + height l + height r

/-- The deletion cost is bounded by {lit}`4 * height + 1`. -/
theorem deleteCost_le (x : Nat) (t : RBTree) : deleteCost x t ≤ 4 * height t + 1 := by
  induction t with
  | empty => simp [deleteCost, height]
  | node c l y r ihl ihr =>
    simp only [deleteCost, height]
    by_cases h1 : x < y
    · simp [h1]
      have hmax : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
      omega
    · by_cases h2 : y < x
      · simp [h1, h2]
        have hmax : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
        omega
      · simp [h1, h2]
        have hmaxl : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
        have hmaxr : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
        omega

/-- **RB-DELETE runs in {lit}`O(log n)` pointer operations.**  On a
red-black-shaped tree with {lit}`n` internal nodes, deletion performs at most
{lit}`4 · (2 log₂(n+1)) + 1` pointer operations. -/
theorem deleteCost_log_bound (x : Nat) (t : RBTree) (hShape : RedBlackShape t) :
    deleteCost x t ≤ 4 * (2 * Nat.log 2 (size t + 1)) + 1 := by
  have hh := height_log_bound t hShape
  have hc := deleteCost_le x t
  omega

/-! ## BST ordering preservation of RB-DELETE -/

/-- The left deletion re-balancer {lit}`baldL` preserves the inorder key
sequence: the repaired node still reads as `keys l ++ [k] ++ keys r`. -/
theorem keys_baldL (l : RBTree) (k : Nat) (r : RBTree) :
    keys (baldL l k r) = keys l ++ [k] ++ keys r := by
  cases l with
  | empty =>
    cases r with
    | empty => rfl
    | node c a y b =>
      cases c with
      | black => simp [baldL, keys, keys_balanceRight]
      | red =>
        cases a with
        | empty => simp [baldL, keys]
        | node ca _ _ _ =>
          cases ca <;> simp [baldL, keys, keys_balanceRight, keys_repaintRoot, List.append_assoc]
  | node c a x b =>
    cases c with
    | red => simp [baldL, keys]
    | black =>
      cases r with
      | empty => simp [baldL, keys]
      | node rc a' y b' =>
        cases rc with
        | black => simp [baldL, keys, keys_balanceRight]
        | red =>
          cases a' with
          | empty => simp [baldL, keys]
          | node rca _ _ _ =>
            cases rca <;> simp [baldL, keys, keys_balanceRight, keys_repaintRoot, List.append_assoc]

/-- The right deletion re-balancer {lit}`baldR` preserves the inorder key
sequence: the repaired node still reads as `keys l ++ [k] ++ keys r`. -/
theorem keys_baldR (l : RBTree) (k : Nat) (r : RBTree) :
    keys (baldR l k r) = keys l ++ [k] ++ keys r := by
  cases r with
  | empty =>
    cases l with
    | empty => rfl
    | node c a y b =>
      cases c with
      | black => simp [baldR, keys, keys_balanceLeft]
      | red =>
        cases b with
        | empty => simp [baldR, keys]
        | node cb _ _ _ =>
          cases cb <;> simp [baldR, keys, keys_balanceLeft, keys_repaintRoot, List.append_assoc]
  | node c a x b =>
    cases c with
    | red => simp [baldR, keys]
    | black =>
      cases l with
      | empty => simp [baldR, keys]
      | node lc a' y b' =>
        cases lc with
        | black => simp [baldR, keys, keys_balanceLeft]
        | red =>
          cases b' with
          | empty => simp [baldR, keys]
          | node lcb _ _ _ =>
            cases lcb <;> simp [baldR, keys, keys_balanceLeft, keys_repaintRoot, List.append_assoc]

/-- {lit}`splitMin` peels the minimum key off the front of the inorder key
sequence: for a non-empty tree, `keys t` is the removed minimum followed by the
keys of the remaining tree. -/
theorem keys_splitMin_cons {t : RBTree} (h : t ≠ empty) :
    (splitMin t).1 :: keys (splitMin t).2 = keys t := by
  induction t with
  | empty => cases h rfl
  | node c l k r ihl =>
    cases l with
    | empty => simp [splitMin, keys]
    | node lc ll lk lr =>
      have hne : node lc ll lk lr ≠ empty := by intro h'; injection h'
      have ih := ihl hne
      by_cases hrb : rootBlack (node lc ll lk lr) = true
      · simp [splitMin, hrb, keys, keys_baldL]
        rw [← List.cons_append, ih]
        simp [keys, List.append_assoc]
      · simp [splitMin, hrb, keys]
        rw [← List.cons_append, ih]
        simp [keys, List.append_assoc]

/-- {lit}`join` concatenates the inorder key sequences of its two trees (the
minimum of the right tree is re-attached to the front of its keys, so no key is
lost). -/
theorem keys_join (l r : RBTree) : keys (join l r) = keys l ++ keys r := by
  unfold join
  split_ifs with hr hl hrb
  · subst hr; simp [keys]
  · subst hl; simp [keys]
  · have hne : r ≠ empty := hr
    simp [keys_baldR, keys_splitMin_cons hne, List.append_assoc]
  · have hne : r ≠ empty := hr
    simp [keys, keys_splitMin_cons hne, List.append_assoc]

/-- Recursive deletion never introduces or reorders keys: the inorder key
sequence of {lit}`del x t` is a sublist of the inorder key sequence of `t`. -/
theorem keys_del_sublist (x : Nat) (t : RBTree) : List.Sublist (keys (del x t)) (keys t) := by
  induction t with
  | empty => simp [del, keys]
  | node c l y r ihl ihr =>
    simp only [del]
    by_cases h1 : x < y
    · by_cases hlb : rootBlack l = true
      · simpa [h1, hlb, keys_baldL, keys] using ihl
      · simpa [h1, hlb, keys] using ihl
    · by_cases h2 : y < x
      · by_cases hrb : rootBlack r = true
        · simpa [h1, h2, hrb, keys_baldR, keys] using ihr
        · simpa [h1, h2, hrb, keys] using ihr
      · simp [h1, h2, keys_join, keys]

/-- Recursive deletion preserves the BST ordering invariant. -/
theorem bst_del {x : Nat} {t : RBTree} (h : BST t) : BST (del x t) := by
  rw [bst_iff_sorted] at h ⊢
  exact List.Pairwise.sublist (keys_del_sublist x t) h

/-- **RB-DELETE preserves the BST ordering invariant.**  Deleting a key from a
binary search tree yields a binary search tree (the composed
{lit}`RBTree.delete` = {lit}`repaintRoot black (del x t)`). -/
theorem bst_delete {x : Nat} {t : RBTree} (h : BST t) : BST (delete x t) := by
  unfold delete
  exact bst_repaintRoot (bst_del h)

end RBTree
end Chapter13
end CLRS
