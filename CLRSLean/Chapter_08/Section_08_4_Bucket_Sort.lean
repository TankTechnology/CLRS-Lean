import CLRSLean.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
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

Beyond the definitional layer, we also prove the CLRS second moment
`E[Σ_j n_j²] = n + n(n-1)/m` as a **true expectation** over the explicit
independent uniform input distribution `Fin n → Fin m` (each key hashed
independently and uniformly to a bucket), reusing
{name}`CLRS.Probability.expect_mul_of_indep` for the independence step
(`expectedBucketQuadraticCost_eq_secondMoment`).  The abstract expected cost is
shown to be {lit}`O(n)` via `expectedBucketSortCost_isBigO`.
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

/-- The finite-uniform bucket average is the shared {name}`CLRS.Probability.fintypeExpect`
toolkit specialised to {lit}`Fin m`.  This bridge lets the algebraic lemmas below
reuse the toolkit instead of re-deriving them. -/
theorem uniformAverageFin_eq_fintypeExpect {m : Nat} (X : Fin m → ℝ) :
    uniformAverageFin X = fintypeExpect X := by
  simp [uniformAverageFin, fintypeExpect, Fintype.card_fin]

/-- A fixed bucket has probability {lit}`1/m` under the finite-uniform bucket model. -/
theorem uniformAverageFin_indicator_singleton {m : Nat} (j : Fin m) :
    uniformAverageFin (fun i => probabilityIndicator (i = j)) = 1 / (m : ℝ) := by
  rw [uniformAverageFin_eq_fintypeExpect,
    show (fun i : Fin m => probabilityIndicator (i = j))
        = (fun i => CLRS.Probability.indicator (i = j)) from rfl,
    fintypeExpect_indicator_singleton, Fintype.card_fin]

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

/-- The abstract finite-uniform bucket-sort cost is {lit}`O(n)`. -/
theorem expectedBucketSortCost_isBigO :
    CLRS.Chapter03.isBigO (fun n => expectedBucketSortCost n) (fun n => (n : ℝ)) := by
  rw [CLRS.Chapter03.isBigO_iff]
  refine ⟨3, by norm_num, 1, fun n hn => ?_⟩
  have hn' : 0 < n := hn
  have hle := expectedBucketSortCost_linear_bound n hn'
  have hnonneg : 0 ≤ expectedBucketSortCost n := by
    rw [expectedBucketSortCost_self_eq n hn']
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
    linarith
  rw [abs_of_nonneg hnonneg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  linarith

/-! ## The second moment as a true expectation over an independent input

The finite-uniform layer above is definitional.  We now make the CLRS
second-moment calculation a genuine expectation.  The **explicit independent
uniform input distribution** is `Fin n → Fin m`: each of the {lit}`n` keys is
assigned a bucket in {lit}`Fin m` independently and uniformly.  We prove
`E[Σ_j n_j²] = n + n(n-1)/m` as {name}`CLRS.Probability.fintypeExpect` over this
distribution, reusing {name}`CLRS.Probability.expect_mul_of_indep` for the
independence step. -/

open scoped Classical in
/-- Split a bucket assignment `a : Fin n → Fin m` into the pair of buckets it
sends two distinct keys `i ≠ k` to, together with the assignment of the
remaining keys.  This is the product decomposition witnessing that the two
coordinates are independent of the rest. -/
noncomputable def bucketPairSplit {m n : Nat} (i k : Fin n) (h : i ≠ k) :
    (Fin n → Fin m) ≃ (Fin m × Fin m) × ({x : Fin n // x ≠ i ∧ x ≠ k} → Fin m) where
  toFun a := ((a i, a k), fun x => a x.val)
  invFun q := fun x =>
    if hx : x = i then q.1.1
    else if hy : x = k then q.1.2
    else q.2 ⟨x, hx, hy⟩
  left_inv a := by
    funext x
    by_cases hx : x = i
    · subst hx; simp
    · by_cases hy : x = k
      · subst hy; simp [hx]
      · simp [hx, hy]
  right_inv q := by
    obtain ⟨⟨b, c⟩, rest⟩ := q
    simp only [Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp
    · simp [h.symm]
    · funext x
      obtain ⟨xv, hxi, hxk⟩ := x
      simp [hxi, hxk]

open CLRS.Probability in
/-- Marginalisation: the expectation of a function of two distinct coordinates of
a uniform assignment equals the expectation over the two-bucket product space
{lit}`Fin m × Fin m` (the joint law of two independent uniform keys). -/
theorem fintypeExpect_bucketPair {m n : Nat} (i k : Fin n) (h : i ≠ k) (hm : 0 < m)
    (F : Fin m → Fin m → ℝ) :
    fintypeExpect (fun a : Fin n → Fin m => F (a i) (a k)) =
      fintypeExpect (fun p : Fin m × Fin m => F p.1 p.2) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hcard : Fintype.card ({x : Fin n // x ≠ i ∧ x ≠ k} → Fin m) ≠ 0 :=
    Fintype.card_ne_zero
  have he := fintypeExpect_equiv (bucketPairSplit (m := m) i k h)
    (fun q : (Fin m × Fin m) × ({x : Fin n // x ≠ i ∧ x ≠ k} → Fin m) => F q.1.1 q.1.2)
  simp only [bucketPairSplit, Equiv.coe_fn_mk] at he
  rw [he]
  exact fintypeExpect_fst hcard (fun p : Fin m × Fin m => F p.1 p.2)

open CLRS.Probability in
/-- Two independent uniform keys collide with probability {lit}`1/m` over the
product sample space {lit}`Fin m × Fin m`. -/
theorem collisionProb_pair {m : Nat} (hm : 0 < m) :
    fintypeExpect (fun p : Fin m × Fin m => indicator (p.1 = p.2)) = 1 / (m : ℝ) := by
  have hden : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold fintypeExpect indicator
  rw [Fintype.card_prod, Fintype.card_fin]
  have hsum : (∑ p : Fin m × Fin m, (if p.1 = p.2 then (1 : ℝ) else 0)) = (m : ℝ) := by
    rw [Fintype.sum_prod_type]; simp
  rw [hsum]; push_cast; field_simp

open CLRS.Probability in
/-- The expected collision indicator for two keys `i`, `k`: {lit}`1` on the
diagonal `i = k`, and {lit}`1/m` off-diagonal (using independence). -/
theorem expected_collision {m n : Nat} (i k : Fin n) (hm : 0 < m) :
    fintypeExpect (fun a : Fin n → Fin m => indicator (a i = a k)) =
      if i = k then 1 else 1 / (m : ℝ) := by
  by_cases h : i = k
  · subst h
    have hfun : (fun a : Fin n → Fin m => indicator (a i = a i)) = (fun _ => (1 : ℝ)) := by
      funext a; simp [indicator]
    rw [if_pos rfl, hfun]
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact fintypeExpect_const Fintype.card_ne_zero 1
  · rw [if_neg h, fintypeExpect_bucketPair i k h hm (fun b c => indicator (b = c))]
    exact collisionProb_pair hm

open CLRS.Probability in
/-- Occupancy of bucket {lit}`j`: the number of keys assigned to it. -/
noncomputable def bucketOccupancy {m n : Nat} (a : Fin n → Fin m) (j : Fin m) : ℝ :=
  ∑ i : Fin n, indicator (a i = j)

open CLRS.Probability in
/-- The bucket-occupancy second moment {lit}`Σ_j n_j²` for an assignment `a`. -/
noncomputable def bucketSecondMoment {m n : Nat} (a : Fin n → Fin m) : ℝ :=
  ∑ j : Fin m, (bucketOccupancy a j) ^ 2

open CLRS.Probability in
/-- Per-bucket collision identity: `∑_j 1[a i = j]·1[a k = j] = 1[a i = a k]`. -/
theorem collisionSum {m n : Nat} (a : Fin n → Fin m) (i k : Fin n) :
    ∑ j : Fin m, indicator (a i = j) * indicator (a k = j) = indicator (a i = a k) := by
  rw [Finset.sum_eq_single (a i)]
  · simp only [indicator]
    by_cases h : a i = a k
    · rw [if_pos h.symm, if_pos h, if_true, one_mul]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  · intro j _ hj
    simp only [indicator]
    rw [if_neg (Ne.symm hj), zero_mul]
  · intro hcontra; exact absurd (Finset.mem_univ (a i)) hcontra

open CLRS.Probability in
/-- The second moment equals the double sum of pairwise collision indicators
(CLRS: {lit}`Σ_j n_j² = Σ_i Σ_k 1[a i = a k]`). -/
theorem bucketSecondMoment_eq_collisions {m n : Nat} (a : Fin n → Fin m) :
    bucketSecondMoment a = ∑ i : Fin n, ∑ k : Fin n, indicator (a i = a k) := by
  unfold bucketSecondMoment bucketOccupancy
  have step : ∀ j : Fin m, (∑ i : Fin n, indicator (a i = j)) ^ 2
      = ∑ i : Fin n, ∑ k : Fin n, indicator (a i = j) * indicator (a k = j) := by
    intro j; rw [sq, Finset.sum_mul_sum]
  simp_rw [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => collisionSum a i k)

open CLRS.Probability in
/--
**Bucket-sort second moment (true expectation).**  Over the explicit independent
uniform input distribution `Fin n → Fin m`, the expected bucket-occupancy second
moment is exactly `n + n(n-1)/m`, i.e.
{name}`CLRS.Chapter08.expectedBucketQuadraticCost`.  This is CLRS's key
second-moment computation (equation for `E[Σ n_i²]`) as a genuine expectation.
-/
theorem expectedBucketQuadraticCost_eq_secondMoment {m n : Nat} (hm : 0 < m) :
    fintypeExpect (fun a : Fin n → Fin m => bucketSecondMoment a) =
      expectedBucketQuadraticCost m n := by
  have hden : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have h1 : (fun a : Fin n → Fin m => bucketSecondMoment a)
      = (fun a => ∑ i : Fin n, ∑ k : Fin n, indicator (a i = a k)) := by
    funext a; exact bucketSecondMoment_eq_collisions a
  rw [h1]
  simp only [fintypeExpect_sum]
  have h2 : ∀ i k : Fin n,
      fintypeExpect (fun a : Fin n → Fin m => indicator (a i = a k))
        = if i = k then (1 : ℝ) else 1 / (m : ℝ) := fun i k => expected_collision i k hm
  simp only [h2]
  have hinner : ∀ i : Fin n,
      (∑ k : Fin n, (if i = k then (1 : ℝ) else 1 / (m : ℝ)))
        = (n : ℝ) * (1 / (m : ℝ)) + (1 - 1 / (m : ℝ)) := by
    intro i
    have hsplit : ∀ k : Fin n, (if i = k then (1 : ℝ) else 1 / (m : ℝ))
        = 1 / (m : ℝ) + (if i = k then (1 - 1 / (m : ℝ)) else 0) := by
      intro k; by_cases h : i = k
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq]
    simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold expectedBucketQuadraticCost
  field_simp
  ring

/-! ## Textbook abstract bucket-sort cost

The CLRS unit-cost random variable charges {lit}`n + Σ_j n_j²` for an
assignment of {lit}`n` keys to {lit}`n` buckets: {lit}`n` for the scan and
distribution term, and the occupancy-square sum for the textbook per-bucket
sorting bound.  This is an abstract model over uniformly random bucket
assignments.  It does not instrument the current executable
{name}`bucketSortByRank`, whose implementation repeatedly filters the input to
construct its buckets.
-/

open Chapter03

/-- The CLRS abstract unit-cost random variable {lit}`n + Σ_j n_j²`. -/
noncomputable def textbookBucketSortCost (n : ℕ) (a : Fin n → Fin n) : ℝ :=
  (n : ℝ) + bucketSecondMoment a

/--
The expectation of the textbook random variable is exactly the existing
abstract expected-cost expression.  The second-moment term is discharged by
{name}`expectedBucketQuadraticCost_eq_secondMoment`.
-/
theorem fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost
    (n : ℕ) (hn : 0 < n) :
    fintypeExpect (textbookBucketSortCost n) = expectedBucketSortCost n := by
  classical
  unfold textbookBucketSortCost
  rw [fintypeExpect_add]
  have h_const : fintypeExpect (fun _ : Fin n → Fin n => (n : ℝ)) = (n : ℝ) := by
    simp [fintypeExpect]
  rw [h_const, expectedBucketQuadraticCost_eq_secondMoment hn]
  rfl

/-- The CLRS abstract unit-cost random variable has linear expectation. -/
theorem expectedTextbookBucketSortCost_isBigO :
    isBigO (fun n : ℕ => fintypeExpect (textbookBucketSortCost n))
      (fun n : ℕ => (n : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨3, by norm_num, 1, fun n hn => ?_⟩
  have hn_pos : 0 < n := by omega
  rw [fintypeExpect_textbookBucketSortCost_eq_expectedBucketSortCost n hn_pos]
  have hle : expectedBucketSortCost n ≤ 3 * (n : ℝ) := expectedBucketSortCost_linear_bound n hn_pos
  have h_nonneg : 0 ≤ expectedBucketSortCost n := by
    rw [expectedBucketSortCost_self_eq n hn_pos]
    have : 1 ≤ (n : ℝ) := by exact_mod_cast hn_pos
    nlinarith
  rw [abs_of_nonneg h_nonneg, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hle

end Chapter08
end CLRS
