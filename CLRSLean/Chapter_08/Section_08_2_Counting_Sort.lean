import Mathlib

/-!
# CLRS Section 8.2 - Counting sort

This file starts Chapter 8 with the stable bucket view of counting sort.  CLRS
implements the algorithm with a count array and prefix sums; the mathematical
content is that keys are emitted in increasing order and that each equal-key
subsequence is copied in its original order.

We model that proof spine directly.  Given a key function into natural numbers
and a maximum key, {lit}`countingSortBy` scans the key values in order and emits
the corresponding input bucket.  The main theorem packages the three facts used
by the textbook proof:

* the output is ordered by key;
* every key bucket is exactly the corresponding input bucket, hence stable;
* membership is preserved when all input keys are at most the declared maximum.

The count-array implementation and linear-time cost model are future
refinements of this stable bucket specification.

## Implementation details

The executable refinement pages remain available outside the main sidebar:

* [Count-Table Refinement](CLRSLean/Chapter_08/Section_08_2_Counting_Sort/CountTables/)
* [Mutable Output-Array Refinement](CLRSLean/Chapter_08/Section_08_2_Counting_Sort/MutableOutputArray/)
-/

namespace CLRS
namespace Chapter08

/-! ## Ordered lists by key -/

/-- A compact sortedness predicate for lists ordered by a natural-number key. -/
def OrderedBy (key : α → Nat) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => key x ≤ key y ∧ OrderedBy key (y :: ys)

/-- Every element in a list has key at most {lit}`upper`. -/
def AllKeysLe (key : α → Nat) (xs : List α) (upper : Nat) : Prop :=
  ∀ x ∈ xs, key x ≤ upper

/-- Every element in a list has key at least {lit}`lower`. -/
def AllKeysGe (key : α → Nat) (lower : Nat) (xs : List α) : Prop :=
  ∀ x ∈ xs, lower ≤ key x

theorem orderedBy_tail {key : α → Nat} {x : α} {xs : List α}
    (h : OrderedBy key (x :: xs)) : OrderedBy key xs := by
  cases xs with
  | nil =>
      trivial
  | cons _ _ =>
      exact h.2

theorem orderedBy_allKeysGe_tail {key : α → Nat} {x : α} {xs : List α}
    (h : OrderedBy key (x :: xs)) : AllKeysGe key (key x) xs := by
  induction xs generalizing x with
  | nil =>
      intro y hy
      simp at hy
  | cons y ys ih =>
      intro z hz
      simp at hz
      rcases hz with rfl | hz
      · exact h.1
      · exact Nat.le_trans h.1 (ih h.2 z hz)

theorem orderedBy_cons_of_allKeysGe {key : α → Nat} {x : α} {xs : List α}
    (hxs : OrderedBy key xs) (hall : AllKeysGe key (key x) xs) :
    OrderedBy key (x :: xs) := by
  cases xs with
  | nil =>
      trivial
  | cons y ys =>
      exact ⟨hall y (by simp), hxs⟩

theorem orderedBy_append_of_rel {key : α → Nat} {xs ys : List α}
    (hxs : OrderedBy key xs) (hys : OrderedBy key ys)
    (hrel : ∀ x ∈ xs, ∀ y ∈ ys, key x ≤ key y) :
    OrderedBy key (xs ++ ys) := by
  induction xs with
  | nil =>
      simpa using hys
  | cons x xs ih =>
      have htail : OrderedBy key (xs ++ ys) := by
        refine ih (orderedBy_tail hxs) ?_
        intro a ha b hb
        exact hrel a (by simp [ha]) b hb
      have hall : AllKeysGe key (key x) (xs ++ ys) := by
        intro z hz
        simp at hz
        rcases hz with hzxs | hzys
        · exact orderedBy_allKeysGe_tail hxs z hzxs
        · exact hrel x (by simp) z hzys
      simpa using orderedBy_cons_of_allKeysGe htail hall

theorem orderedBy_of_all_keys_eq {key : α → Nat} {xs : List α} {k : Nat}
    (h : ∀ x ∈ xs, key x = k) : OrderedBy key xs := by
  induction xs with
  | nil =>
      trivial
  | cons x xs ih =>
      cases xs with
      | nil =>
          trivial
      | cons y ys =>
          have hxy : key x ≤ key y := by
            rw [h x (by simp), h y (by simp)]
          have htail : OrderedBy key (y :: ys) := by
            refine ih ?_
            intro z hz
            exact h z (by simp [hz])
          exact ⟨hxy, htail⟩

/-! ## Stable buckets -/

/-- The input bucket whose elements have key {lit}`k`, preserving input order. -/
def bucket (key : α → Nat) (xs : List α) (k : Nat) : List α :=
  xs.filter fun x => key x == k

theorem bucket_append (key : α → Nat) (xs ys : List α) (k : Nat) :
    bucket key (xs ++ ys) k = bucket key xs k ++ bucket key ys k := by
  simp [bucket]

theorem mem_bucket_iff {key : α → Nat} {xs : List α} {k : Nat} {x : α} :
    x ∈ bucket key xs k ↔ x ∈ xs ∧ key x = k := by
  simp [bucket]

theorem bucket_all_keys_eq (key : α → Nat) (xs : List α) (k : Nat) :
    ∀ x ∈ bucket key xs k, key x = k := by
  intro x hx
  exact (mem_bucket_iff.mp hx).2

theorem bucket_orderedBy (key : α → Nat) (xs : List α) (k : Nat) :
    OrderedBy key (bucket key xs k) :=
  orderedBy_of_all_keys_eq (bucket_all_keys_eq key xs k)

theorem count_bucket_self [DecidableEq α]
    (key : α → Nat) (xs : List α) (x : α) :
    List.count x (bucket key xs (key x)) = List.count x xs := by
  simp [bucket]

/-- Filtering a bucket by a second key keeps it only when the keys agree. -/
theorem bucket_bucket_eq (key : α → Nat) (xs : List α) (j k : Nat) :
    bucket key (bucket key xs j) k =
      if j = k then bucket key xs k else [] := by
  by_cases hjk : j = k
  · subst hjk
    simp [bucket, List.filter_filter]
  · simp [hjk]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hxj : key x = j := (mem_bucket_iff.mp (mem_bucket_iff.mp hx).1).2
    have hxk : key x = k := (mem_bucket_iff.mp hx).2
    exact hjk (hxj ▸ hxk)

theorem bucket_eq_nil_of_allKeysLe_lt {key : α → Nat} {xs : List α}
    {upper k : Nat} (hxs : AllKeysLe key xs upper) (hgt : upper < k) :
    bucket key xs k = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have hxmem : x ∈ xs := (mem_bucket_iff.mp hx).1
  have hxkey : key x = k := (mem_bucket_iff.mp hx).2
  exact (Nat.not_lt_of_ge (hxs x hxmem)) (hxkey ▸ hgt)

/-! ## Counting sort by stable buckets -/

/--
Stable counting sort by natural-number keys bounded by {lit}`maxKey`.

The function emits the bucket for key {lit}`0`, then key {lit}`1`, and so on
through {lit}`maxKey`.
-/
def countingSortBy (maxKey : Nat) (key : α → Nat) (xs : List α) : List α :=
  (List.range (maxKey + 1)).flatMap (bucket key xs)

theorem countingSortBy_succ (maxKey : Nat) (key : α → Nat) (xs : List α) :
    countingSortBy (maxKey + 1) key xs =
      countingSortBy maxKey key xs ++ bucket key xs (maxKey + 1) := by
  simp [countingSortBy, List.range_succ, List.flatMap_append]

theorem countingSortBy_allKeysLe (maxKey : Nat) (key : α → Nat) (xs : List α) :
    AllKeysLe key (countingSortBy maxKey key xs) maxKey := by
  intro x hx
  rw [countingSortBy, List.mem_flatMap] at hx
  rcases hx with ⟨k, hk_range, hx_bucket⟩
  have hk_le : k ≤ maxKey := by
    have hk_lt : k < maxKey + 1 := (List.mem_range.mp hk_range)
    exact Nat.le_of_lt_succ hk_lt
  have hxkey : key x = k := (mem_bucket_iff.mp hx_bucket).2
  exact hxkey ▸ hk_le

/--
If {lit}`k ≤ maxKey`, the {lit}`k`-bucket of the output is exactly the
{lit}`k`-bucket of the input.  This is the stable-copy theorem for in-range
keys.
-/
theorem countingSortBy_bucket_eq_of_le
    (maxKey : Nat) (key : α → Nat) (xs : List α) {k : Nat}
    (hk : k ≤ maxKey) :
    bucket key (countingSortBy maxKey key xs) k = bucket key xs k := by
  induction maxKey with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simp [countingSortBy, bucket_bucket_eq]
  | succ maxKey ih =>
      rw [countingSortBy_succ, bucket_append]
      by_cases hlast : k = maxKey + 1
      · subst hlast
        have hprev_empty :
            bucket key (countingSortBy maxKey key xs) (maxKey + 1) = [] := by
          exact bucket_eq_nil_of_allKeysLe_lt
            (countingSortBy_allKeysLe maxKey key xs) (Nat.lt_succ_self maxKey)
        rw [hprev_empty, bucket_bucket_eq]
        simp
      · have hk_prev : k ≤ maxKey := by
          exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hk hlast)
        have hlast_empty : bucket key (bucket key xs (maxKey + 1)) k = [] := by
          have hne : maxKey + 1 ≠ k := by
            intro h
            exact hlast h.symm
          simp [bucket_bucket_eq, hne]
        rw [ih hk_prev, hlast_empty, List.append_nil]

theorem countingSortBy_bucket_eq_of_gt
    (maxKey : Nat) (key : α → Nat) (xs : List α) {k : Nat}
    (hk : maxKey < k) :
    bucket key (countingSortBy maxKey key xs) k = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have hxle := countingSortBy_allKeysLe maxKey key xs x (mem_bucket_iff.mp hx).1
  have hxkey := (mem_bucket_iff.mp hx).2
  exact (Nat.not_lt_of_ge hxle) (hxkey ▸ hk)

/--
Counting sort preserves every equal-key subsequence when the input keys are
bounded by {lit}`maxKey`.  This is the stability statement.
-/
theorem countingSortBy_bucket_eq
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (k : Nat) :
    bucket key (countingSortBy maxKey key xs) k = bucket key xs k := by
  by_cases hk : k ≤ maxKey
  · exact countingSortBy_bucket_eq_of_le maxKey key xs hk
  · have hgt : maxKey < k := Nat.lt_of_not_ge hk
    rw [countingSortBy_bucket_eq_of_gt maxKey key xs hgt,
      bucket_eq_nil_of_allKeysLe_lt hxs hgt]

theorem countingSortBy_ordered (maxKey : Nat) (key : α → Nat) (xs : List α) :
    OrderedBy key (countingSortBy maxKey key xs) := by
  induction maxKey with
  | zero =>
      simpa [countingSortBy] using bucket_orderedBy key xs 0
  | succ maxKey ih =>
      rw [countingSortBy_succ]
      refine orderedBy_append_of_rel ih (bucket_orderedBy key xs (maxKey + 1)) ?_
      intro a ha b hb
      have hale := countingSortBy_allKeysLe maxKey key xs a ha
      have hbkey := (mem_bucket_iff.mp hb).2
      exact Nat.le_trans hale (by simp [hbkey])

theorem countingSortBy_mem_iff
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) (x : α) :
    x ∈ countingSortBy maxKey key xs ↔ x ∈ xs := by
  constructor
  · intro hx
    rw [countingSortBy, List.mem_flatMap] at hx
    rcases hx with ⟨k, _hk, hx_bucket⟩
    exact (mem_bucket_iff.mp hx_bucket).1
  · intro hx
    have hxkey_le : key x ≤ maxKey := hxs x hx
    have hbucket : bucket key (countingSortBy maxKey key xs) (key x) =
        bucket key xs (key x) :=
      countingSortBy_bucket_eq maxKey key xs hxs (key x)
    have hx_bucket_input : x ∈ bucket key xs (key x) := by
      exact mem_bucket_iff.mpr ⟨hx, rfl⟩
    have hx_bucket_output : x ∈ bucket key (countingSortBy maxKey key xs) (key x) := by
      simpa [hbucket] using hx_bucket_input
    exact (mem_bucket_iff.mp hx_bucket_output).1

theorem countingSortBy_perm [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    (countingSortBy maxKey key xs).Perm xs := by
  classical
  apply List.perm_iff_count.mpr
  intro x
  have hbucket := countingSortBy_bucket_eq maxKey key xs hxs (key x)
  calc
    List.count x (countingSortBy maxKey key xs)
        = List.count x (bucket key (countingSortBy maxKey key xs) (key x)) := by
            rw [count_bucket_self]
    _ = List.count x (bucket key xs (key x)) := by
            rw [hbucket]
    _ = List.count x xs := by
            rw [count_bucket_self]

/-- Reader-facing correctness theorem for stable counting sort. -/
theorem countingSortBy_correct [DecidableEq α]
    (maxKey : Nat) (key : α → Nat) (xs : List α)
    (hxs : AllKeysLe key xs maxKey) :
    OrderedBy key (countingSortBy maxKey key xs) ∧
      (∀ k, bucket key (countingSortBy maxKey key xs) k = bucket key xs k) ∧
      (∀ x, x ∈ countingSortBy maxKey key xs ↔ x ∈ xs) ∧
      (countingSortBy maxKey key xs).Perm xs :=
  ⟨countingSortBy_ordered maxKey key xs,
    countingSortBy_bucket_eq maxKey key xs hxs,
    countingSortBy_mem_iff maxKey key xs hxs,
    countingSortBy_perm maxKey key xs hxs⟩

end Chapter08
end CLRS
