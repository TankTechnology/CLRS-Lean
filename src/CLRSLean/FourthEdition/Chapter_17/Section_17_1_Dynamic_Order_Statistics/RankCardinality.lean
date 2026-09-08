import CLRSLean.FourthEdition.Chapter_17.Section_17_1_Dynamic_Order_Statistics

/-!
# Order-statistic rank as a set cardinality

BST ordering and cached-size correctness are separate requirements. Ordering
identifies the recursive rank with the number of keys strictly below the query;
well-sizedness then transfers that interpretation to the cached query. The query
need not be present, and the answer is a zero-based insertion rank.
-/

namespace CLRS.Chapter14.OSRBTree
open CLRS.Chapter13 (RBTree)

theorem toRB_keys (t : OSRBTree) : RBTree.keys (toRB t) = keys t := by
  induction t with
  | empty => rfl
  | node c l k s r ihl ihr => simp [toRB, keys, RBTree.keys, ihl, ihr]

theorem keys_length (t : OSRBTree) : (keys t).length = realSize t := by
  induction t with
  | empty => rfl
  | node c l k s r ihl ihr => simp [keys, realSize, ihl, ihr]; omega

theorem keys_nodup_of_bst {t : OSRBTree} (h : RBTree.BST (toRB t)) :
    (keys t).Nodup := by
  have hs := (RBTree.bst_iff_sorted (toRB t)).mp h
  rw [RBTree.sorted, toRB_keys] at hs
  exact hs.imp (fun hlt => Nat.ne_of_lt hlt)

private theorem filter_lt_all (ys : List Nat) (x : Nat)
    (h : ∀ y ∈ ys, y < x) : ys.filter (fun y => decide (y < x)) = ys := by
  apply List.filter_eq_self.mpr
  intro y hy
  simpa using h y hy

private theorem filter_lt_none (ys : List Nat) (x : Nat)
    (h : ∀ y ∈ ys, x ≤ y) : ys.filter (fun y => decide (y < x)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro y hy
  simpa using Nat.not_lt.mpr (h y hy)

/-- Recursive rank counts the strict lower-key prefix, even for absent queries. -/
theorem rankOf_eq_filter_length {t : OSRBTree} (h : RBTree.BST (toRB t)) (x : Nat) :
    rankOf t x = ((keys t).filter (fun y => decide (y < x))).length := by
  induction t with
  | empty => simp [rankOf, keys]
  | node c l k s r ihl ihr =>
      rcases h with ⟨hl, hr, hleft, hright⟩
      have hlkeys : ∀ y ∈ keys l, y < k := by
        intro y hy
        exact hleft y ((inTree_toRB y l).mpr hy)
      have hrkeys : ∀ y ∈ keys r, k < y := by
        intro y hy
        exact hright y ((inTree_toRB y r).mpr hy)
      by_cases hx : x < k
      · have hn := filter_lt_none (keys r) x (by intro y hy; exact Nat.le_of_lt (lt_trans hx (hrkeys y hy)))
        simp [rankOf, keys, hx, show ¬k < x by omega, List.filter_append, hn, ihl hl]
      · by_cases hk : k < x
        · have ha := filter_lt_all (keys l) x (by intro y hy; exact lt_trans (hlkeys y hy) hk)
          simp [rankOf, keys, hx, hk, List.filter_append, ha, keys_length, ihr hr]
          omega
        · have heq : x = k := by omega
          subst x
          have ha := filter_lt_all (keys l) k hlkeys
          have hn := filter_lt_none (keys r) k (by intro y hy; exact Nat.le_of_lt (hrkeys y hy))
          simp [rankOf, keys, List.filter_append, ha, hn, keys_length]

/-- BST trees have distinct keys, so the list-prefix count is a set cardinality. -/
theorem rankOf_eq_card_lt {t : OSRBTree} (h : RBTree.BST (toRB t)) (x : Nat) :
    rankOf t x = ((keys t).toFinset.filter (fun y => y < x)).card := by
  rw [rankOf_eq_filter_length h]
  have hn := (keys_nodup_of_bst h).filter (fun y => decide (y < x))
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext y
  simp

/-- Semantic cardinal-rank contract for the cached query. -/
theorem osRank_eq_card_lt {t : OSRBTree} (hs : WellSized t)
    (hb : RBTree.BST (toRB t)) (x : Nat) :
    osRank t x = ((keys t).toFinset.filter (fun y => y < x)).card := by
  rw [osRank_eq_rankOf_of_wellSized hs, rankOf_eq_card_lt hb]

end CLRS.Chapter14.OSRBTree
