import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model

/-!
# CLRS Section 18.1 - B-tree search helpers

Defines the child-selection function used by B-tree search and insertion,
together with reusable path-localization and height lemmas.
-/

namespace CLRS.Chapter18.BTree

open List

/-! ## Child selection -/

/-- Index of the child that key `x` descends into: the number of leading keys
`≤ x` (correct for a sorted key list). -/
def findChild : List Nat → Nat → Nat
  | [], _ => 0
  | k :: ks, x => if k ≤ x then findChild ks x + 1 else 0

/-! ## Height lemmas -/

/-- `foldl max` never drops below its accumulator. -/
lemma foldl_max_ge (b : Nat) (l : List Nat) : b ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left b y) (ih (max b y))

/-- Every element of `l` is `≤ l.foldl max b`. -/
lemma mem_le_foldl_max : ∀ {l : List Nat} {a b : Nat}, a ∈ l → a ≤ l.foldl max b := by
  intro l
  induction l with
  | nil => intro a b h; simp at h
  | cons y ys ih =>
    intro a b h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right b a) (foldl_max_ge (max b a) ys)
    · exact ih h

/-- If every element of `l` is `≤ M` and `b ≤ M`, then `l.foldl max b ≤ M`. -/
lemma foldl_max_le' : ∀ {l : List Nat} {M b : Nat}, b ≤ M → (∀ a ∈ l, a ≤ M) → l.foldl max b ≤ M := by
  intro l
  induction l with
  | nil => intro M b hb _; simpa using hb
  | cons y ys ih =>
    intro M b hb h
    simp only [List.foldl_cons]
    exact ih (max_le hb (h y (by simp))) (fun a ha => h a (by simp [ha]))

/-- Folding `max` over the heights of a sub-multiset of children is `≤` folding
over the full children list. -/
lemma foldl_max_heightOf_subset {cs' cs : List BTree} (h : cs' ⊆ cs) :
    (cs'.map heightOf).foldl max 0 ≤ (cs.map heightOf).foldl max 0 := by
  apply foldl_max_le' (foldl_max_ge 0 _)
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  exact mem_le_foldl_max (List.mem_map_of_mem (h hc))

/-- A child is strictly shorter than its parent. -/
lemma heightOf_mem_lt {ks : List Nat} {children : List BTree} {c : BTree}
    (hc : c ∈ children) : heightOf c < heightOf (node ks children) := by
  cases children with
  | nil => simp at hc
  | cons d ds =>
    have hle := mem_le_foldl_max (a := heightOf c) (b := 0) (List.mem_map_of_mem hc)
    simp only [heightOf]
    omega

/-- Replacing the children of a node by a sub-multiset cannot increase the height. -/
lemma heightOf_le_of_children_subset {a b : List Nat} {cs' cs : List BTree}
    (h : cs' ⊆ cs) : heightOf (node a cs') ≤ heightOf (node b cs) := by
  cases cs' with
  | nil => simp [heightOf]
  | cons d ds =>
    cases cs with
    | nil => exact absurd (h List.mem_cons_self) (by simp)
    | cons e es =>
      have hsub := foldl_max_heightOf_subset (cs' := d :: ds) (cs := e :: es) h
      simp only [heightOf]
      omega

/-! ## Child-index bounds and range correctness -/

/-- `findChild` never exceeds the number of keys, so on a node with
`children.length = keys.length + 1` it always indexes a real child. -/
lemma findChild_le (ks : List Nat) (x : Nat) : findChild ks x ≤ ks.length := by
  induction ks with
  | nil => simp [findChild]
  | cons k ks ih =>
    unfold findChild
    split
    · simp only [List.length_cons]; omega
    · omega

/-- Every key before the chosen child index is `≤ x`. -/
lemma findChild_take_le (x : Nat) : ∀ (ks : List Nat), ∀ k ∈ ks.take (findChild ks x), k ≤ x := by
  intro ks
  induction ks with
  | nil => intro k hk; simp at hk
  | cons a as ih =>
    intro k hk
    rw [findChild] at hk
    split at hk
    · rename_i hax
      rw [List.take_succ_cons] at hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hax
      · exact ih k hk
    · simp at hk

/-- On a sorted key list, every key from the chosen child index onward is `> x`. -/
lemma findChild_drop_gt (x : Nat) : ∀ {ks : List Nat}, List.Pairwise (· ≤ ·) ks →
    ∀ k ∈ ks.drop (findChild ks x), x < k := by
  intro ks
  induction ks with
  | nil => intro _ k hk; simp at hk
  | cons a as ih =>
    intro hs k hk
    have hsa : ∀ b ∈ as, a ≤ b := (List.pairwise_cons.mp hs).1
    have hs' : List.Pairwise (· ≤ ·) as := (List.pairwise_cons.mp hs).2
    rw [findChild] at hk
    split at hk
    · rename_i hax
      rw [List.drop_succ_cons] at hk
      exact ih hs' k hk
    · rename_i hax
      have hxa : x < a := not_le.mp hax
      simp only [List.drop_zero, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact hxa
      · exact lt_of_lt_of_le hxa (hsa k hk)

/-- The right separator at the chosen child bounds `x` from above (sorted keys). -/
lemma findChild_x_hi {ks : List Nat} (hs : List.Pairwise (· ≤ ·) ks) (x : Nat) :
    ∀ hi, ks[findChild ks x]? = some hi → x ≤ hi := by
  intro hi hhi
  have hmem : hi ∈ ks.drop (findChild ks x) := by
    rw [List.mem_iff_getElem?]
    exact ⟨0, by rw [List.getElem?_drop, Nat.add_zero]; exact hhi⟩
  exact le_of_lt (findChild_drop_gt x hs hi hmem)

/-- The left separator at the chosen child bounds `x` from below. -/
lemma findChild_x_lo (ks : List Nat) (x : Nat) :
    findChild ks x = 0 ∨ ∀ lo, ks[findChild ks x - 1]? = some lo → lo ≤ x := by
  rcases Nat.eq_zero_or_pos (findChild ks x) with h0 | hpos
  · exact Or.inl h0
  · right
    intro lo hlo
    have hmem : lo ∈ ks.take (findChild ks x) := by
      rw [List.mem_iff_getElem?]
      exact ⟨findChild ks x - 1, by rw [List.getElem?_take_of_lt (by omega)]; exact hlo⟩
    exact findChild_take_le x ks lo hmem

end CLRS.Chapter18.BTree
