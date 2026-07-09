import CLRSLean.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.Probability.FiniteExpectation
import Mathlib
/-!
# CLRS Section 8.4 - Bucket sort

This file adds a deterministic correctness layer for bucket sort and a first
finite-uniform probability interface for the expected-time argument.

The full probabilistic expected-time analysis in CLRS depends on a
distributional assumption about the input.  Here we isolate the pure correctness
spine:

* distribute values into buckets by a bucket-index function;
* sort each bucket by the final key;
* concatenate buckets in increasing bucket-index order;
* prove the result is ordered and is a permutation of the input.

The theorem is intentionally parametric in the bucket-index function.  A
separate cross-bucket assumption states that every value in an earlier bucket is
at most every value in a later bucket according to the final sort key.

The finite-uniform layer proves the collision fact behind the textbook expected
time argument: two independently chosen uniform buckets collide with
probability {lit}`1/m`; therefore the expected quadratic bucket-occupancy cost
for {lit}`n` independent samples into {lit}`n` buckets is at most linear in
{lit}`n`.  The final wrapper adds the linear scan/distribution term used by the
CLRS expected-time proof and obtains a concrete {lit}`≤ 3n` bound for this
abstract cost expression.
-/

namespace CLRS
namespace Chapter08

universe u v
variable {α : Type u}

/-! ## Bucket-sort model -/

/-- Every element in a list has bucket index strictly below {lit}`upper`. -/
def AllKeysLt (key : α → Nat) (xs : List α) (upper : Nat) : Prop :=
  ∀ x ∈ xs, key x < upper

/--
Bucket sort with an abstract per-bucket sorter.

The buckets are scanned in increasing order {lit}`0, 1, ..., bucketCount - 1`.
-/
def bucketSortBy (bucketCount : Nat) (bucketOf : α → Nat)
    (sortBucket : List α → List α) (xs : List α) : List α :=
  (List.range bucketCount).flatMap fun k => sortBucket (bucket bucketOf xs k)

theorem bucketSortBy_succ (bucketCount : Nat) (bucketOf : α → Nat)
    (sortBucket : List α → List α) (xs : List α) :
    bucketSortBy (bucketCount + 1) bucketOf sortBucket xs =
      bucketSortBy bucketCount bucketOf sortBucket xs ++
        sortBucket (bucket bucketOf xs bucketCount) := by
  simp [bucketSortBy, List.range_succ, List.flatMap_append]

theorem orderedBy_of_pairwise {key : α → Nat} :
    ∀ {xs : List α}, xs.Pairwise (fun x y => key x ≤ key y) →
      OrderedBy key xs
  | [], _ => by
      trivial
  | [_], _ => by
      trivial
  | x :: y :: ys, h => by
      cases h with
      | cons hhead htail =>
          exact ⟨hhead y (by simp), orderedBy_of_pairwise htail⟩

theorem flatMap_perm_of_forall {β : Type v} (ks : List β)
    (f g : β → List α)
    (h : ∀ k ∈ ks, (f k).Perm (g k)) :
    (ks.flatMap f).Perm (ks.flatMap g) := by
  induction ks with
  | nil =>
      simp
  | cons k ks ih =>
      simp at h ⊢
      exact List.Perm.append h.1 (ih h.2)

theorem bucketSortBy_perm_bucket_scan (bucketCount : Nat)
    (bucketOf : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys) :
    (bucketSortBy bucketCount bucketOf sortBucket xs).Perm
      ((List.range bucketCount).flatMap fun k => bucket bucketOf xs k) := by
  unfold bucketSortBy
  apply flatMap_perm_of_forall
  intro k _hk
  exact hsort_perm _

theorem bucketSortBy_allKeysLt (bucketCount : Nat) (bucketOf : α → Nat)
    (sortBucket : List α → List α) (xs : List α)
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys) :
    AllKeysLt bucketOf (bucketSortBy bucketCount bucketOf sortBucket xs)
      bucketCount := by
  intro x hx
  rw [bucketSortBy, List.mem_flatMap] at hx
  rcases hx with ⟨k, hk_range, hx_sort⟩
  have hx_bucket : x ∈ bucket bucketOf xs k :=
    (hsort_perm (bucket bucketOf xs k)).mem_iff.mp hx_sort
  have hxkey : bucketOf x = k := (mem_bucket_iff.mp hx_bucket).2
  exact hxkey ▸ List.mem_range.mp hk_range

theorem bucketSortBy_ordered (bucketCount : Nat)
    (bucketOf rank : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hsort_ordered :
      ∀ k, OrderedBy rank (sortBucket (bucket bucketOf xs k)))
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys)
    (hcross : ∀ {x y : α}, bucketOf x < bucketOf y → rank x ≤ rank y) :
    OrderedBy rank (bucketSortBy bucketCount bucketOf sortBucket xs) := by
  induction bucketCount with
  | zero =>
      simp [bucketSortBy, OrderedBy]
  | succ bucketCount ih =>
      rw [bucketSortBy_succ]
      refine orderedBy_append_of_rel ih (hsort_ordered bucketCount) ?_
      intro x hx y hy
      have hxlt :
          bucketOf x < bucketCount :=
        bucketSortBy_allKeysLt bucketCount bucketOf sortBucket xs hsort_perm x hx
      have hy_bucket : y ∈ bucket bucketOf xs bucketCount :=
        (hsort_perm (bucket bucketOf xs bucketCount)).mem_iff.mp hy
      have hykey : bucketOf y = bucketCount :=
        (mem_bucket_iff.mp hy_bucket).2
      exact hcross (by simpa [hykey] using hxlt)

theorem bucketSortBy_perm [DecidableEq α] (bucketCount : Nat)
    (bucketOf : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hxs : AllKeysLt bucketOf xs bucketCount)
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys) :
    (bucketSortBy bucketCount bucketOf sortBucket xs).Perm xs := by
  cases bucketCount with
  | zero =>
      have hnil : xs = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x hx
        exact Nat.not_lt_zero _ (hxs x hx)
      simp [bucketSortBy, hnil]
  | succ maxKey =>
      have hscan :
          (bucketSortBy (maxKey + 1) bucketOf sortBucket xs).Perm
            (countingSortBy maxKey bucketOf xs) := by
        have hperm_scan :=
          bucketSortBy_perm_bucket_scan (maxKey + 1) bucketOf sortBucket xs
            hsort_perm
        simpa [countingSortBy, bucketSortBy] using hperm_scan
      have hle : AllKeysLe bucketOf xs maxKey := by
        intro x hx
        exact Nat.le_of_lt_succ (hxs x hx)
      exact hscan.trans (countingSortBy_perm maxKey bucketOf xs hle)

theorem bucketSortBy_mem_iff [DecidableEq α] (bucketCount : Nat)
    (bucketOf : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hxs : AllKeysLt bucketOf xs bucketCount)
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys) (x : α) :
    x ∈ bucketSortBy bucketCount bucketOf sortBucket xs ↔ x ∈ xs :=
  (bucketSortBy_perm bucketCount bucketOf sortBucket xs hxs hsort_perm).mem_iff

/-- Reader-facing correctness theorem for abstract deterministic bucket sort. -/
theorem bucketSortBy_correct [DecidableEq α] (bucketCount : Nat)
    (bucketOf rank : α → Nat) (sortBucket : List α → List α) (xs : List α)
    (hxs : AllKeysLt bucketOf xs bucketCount)
    (hsort_ordered :
      ∀ k, OrderedBy rank (sortBucket (bucket bucketOf xs k)))
    (hsort_perm : ∀ ys, (sortBucket ys).Perm ys)
    (hcross : ∀ {x y : α}, bucketOf x < bucketOf y → rank x ≤ rank y) :
    OrderedBy rank (bucketSortBy bucketCount bucketOf sortBucket xs) ∧
      (∀ x, x ∈ bucketSortBy bucketCount bucketOf sortBucket xs ↔ x ∈ xs) ∧
      (bucketSortBy bucketCount bucketOf sortBucket xs).Perm xs :=
  ⟨bucketSortBy_ordered bucketCount bucketOf rank sortBucket xs
      hsort_ordered hsort_perm hcross,
    bucketSortBy_mem_iff bucketCount bucketOf sortBucket xs hxs hsort_perm,
    bucketSortBy_perm bucketCount bucketOf sortBucket xs hxs hsort_perm⟩

/-! ## Executable bucket sorter using merge sort inside each bucket -/

/-- Sort one bucket by the final natural-number rank. -/
def sortBucketByRank (rank : α → Nat) (xs : List α) : List α :=
  xs.mergeSort (fun x y => decide (rank x ≤ rank y))

theorem sortBucketByRank_perm (rank : α → Nat) (xs : List α) :
    (sortBucketByRank rank xs).Perm xs := by
  simpa [sortBucketByRank] using
    List.mergeSort_perm xs (fun x y => decide (rank x ≤ rank y))

theorem sortBucketByRank_ordered (rank : α → Nat) (xs : List α) :
    OrderedBy rank (sortBucketByRank rank xs) := by
  apply orderedBy_of_pairwise
  simpa [sortBucketByRank] using
    List.pairwise_mergeSort' (r := fun x y : α => rank x ≤ rank y) xs

/-- Bucket sort whose per-bucket sorter is Lean's verified merge sort. -/
def bucketSortByRank (bucketCount : Nat) (bucketOf rank : α → Nat)
    (xs : List α) : List α :=
  bucketSortBy bucketCount bucketOf (sortBucketByRank rank) xs

/--
Reader-facing correctness theorem for the executable bucket-sort model.

The cross-bucket hypothesis is the deterministic analogue of the CLRS bucket
interval fact: every item in an earlier bucket is no larger than every item in
a later bucket.
-/
theorem bucketSortByRank_correct [DecidableEq α] (bucketCount : Nat)
    (bucketOf rank : α → Nat) (xs : List α)
    (hxs : AllKeysLt bucketOf xs bucketCount)
    (hcross : ∀ {x y : α}, bucketOf x < bucketOf y → rank x ≤ rank y) :
    OrderedBy rank (bucketSortByRank bucketCount bucketOf rank xs) ∧
      (∀ x, x ∈ bucketSortByRank bucketCount bucketOf rank xs ↔ x ∈ xs) ∧
      (bucketSortByRank bucketCount bucketOf rank xs).Perm xs := by
  unfold bucketSortByRank
  exact bucketSortBy_correct bucketCount bucketOf rank (sortBucketByRank rank)
    xs hxs
    (fun k => sortBucketByRank_ordered rank (bucket bucketOf xs k))
    (sortBucketByRank_perm rank)
    hcross

/-! ## Finite-uniform expected-cost interface -/

open CLRS.Probability

/-- A real-valued {lit}`0/1` indicator for finite bucket probabilities.
Alias for {lit}`CLRS.Probability.indicator`. -/
def probabilityIndicator (P : Prop) [Decidable P] : ℝ :=
  CLRS.Probability.indicator P

/-- Uniform average over the finite bucket set {lit}`Fin m`. -/
noncomputable def uniformAverageFin {m : Nat} (X : Fin m → ℝ) : ℝ :=
  (∑ i : Fin m, X i) / (m : ℝ)

/-- Uniform average over two independent finite bucket choices. -/
noncomputable def uniformAverageFin2 {m : Nat} (X : Fin m → Fin m → ℝ) : ℝ :=
  uniformAverageFin fun i => uniformAverageFin fun j => X i j

/-- A fixed bucket has probability {lit}`1/m` under the finite-uniform bucket model. -/
theorem uniformAverageFin_indicator_singleton {m : Nat} (j : Fin m) :
    uniformAverageFin (fun i => probabilityIndicator (i = j)) = 1 / (m : ℝ) := by
  classical
  have hsum :
      (∑ i : Fin m, probabilityIndicator (i = j)) = (1 : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp [probabilityIndicator, CLRS.Probability.indicator]
    · intro b _hb hbj
      simp [probabilityIndicator, CLRS.Probability.indicator, hbj]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  simp [uniformAverageFin, hsum]

/--
Two independently chosen uniform buckets collide with probability {lit}`1/m`.
This is the probability fact used in the CLRS bucket-sort second-moment
calculation.
-/
theorem uniformAverageFin2_collision {m : Nat} (hm : 0 < m) :
    uniformAverageFin2 (fun i j : Fin m => probabilityIndicator (i = j)) =
      1 / (m : ℝ) := by
  classical
  have hden : (m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  have hinner :
      ∀ i : Fin m,
        uniformAverageFin (fun j : Fin m => probabilityIndicator (i = j)) =
          1 / (m : ℝ) := by
    intro i
    simpa [eq_comm] using uniformAverageFin_indicator_singleton (m := m) i
  calc
    uniformAverageFin2 (fun i j : Fin m => probabilityIndicator (i = j))
        = uniformAverageFin (fun _i : Fin m => 1 / (m : ℝ)) := by
          simp [uniformAverageFin2, hinner]
    _ = 1 / (m : ℝ) := by
          simp [uniformAverageFin, Finset.sum_const, Fintype.card_fin]
          field_simp [hden]

/--
The textbook second-moment bucket-occupancy expression for {lit}`n`
independent samples into {lit}`m` uniform buckets:
{lit}`E[Σ_i n_i^2] = n + n(n-1)/m`.
-/
noncomputable def expectedBucketQuadraticCost (m n : Nat) : ℝ :=
  (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) / (m : ℝ)

/--
With as many buckets as input elements, the quadratic bucket-occupancy
expectation is {lit}`2n - 1`.
-/
theorem expectedBucketQuadraticCost_self_eq (n : Nat) (hn : 0 < n) :
    expectedBucketQuadraticCost n n = 2 * (n : ℝ) - 1 := by
  have hden : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  unfold expectedBucketQuadraticCost
  field_simp [hden]
  ring

/--
With {lit}`n` buckets for {lit}`n` elements, the expected quadratic
bucket-occupancy cost is at most {lit}`2n`.
-/
theorem expectedBucketQuadraticCost_self_linear_bound (n : Nat) (hn : 0 < n) :
    expectedBucketQuadraticCost n n ≤ 2 * (n : ℝ) := by
  rw [expectedBucketQuadraticCost_self_eq n hn]
  linarith

/--
Abstract CLRS bucket-sort expected cost: a linear scan/distribution term plus
the expected quadratic bucket-occupancy cost for sorting the buckets.
-/
noncomputable def expectedBucketSortCost (n : Nat) : ℝ :=
  (n : ℝ) + expectedBucketQuadraticCost n n

/--
With {lit}`n` buckets for {lit}`n` elements, the abstract expected bucket-sort
cost is {lit}`3n - 1`.
-/
theorem expectedBucketSortCost_self_eq (n : Nat) (hn : 0 < n) :
    expectedBucketSortCost n = 3 * (n : ℝ) - 1 := by
  unfold expectedBucketSortCost
  rw [expectedBucketQuadraticCost_self_eq n hn]
  ring

/--
CLRS-facing linear expected-cost bound for the finite-uniform bucket-sort cost
interface.
-/
theorem expectedBucketSortCost_linear_bound (n : Nat) (hn : 0 < n) :
    expectedBucketSortCost n ≤ 3 * (n : ℝ) := by
  rw [expectedBucketSortCost_self_eq n hn]
  linarith

end Chapter08
end CLRS
