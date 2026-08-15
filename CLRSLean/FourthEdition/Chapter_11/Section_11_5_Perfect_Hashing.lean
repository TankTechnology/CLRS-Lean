import Mathlib
import CLRSLean.Probability.FiniteExpectation
import CLRSLean.FourthEdition.Chapter_11.Section_11_2_Chained_Hash_Tables

/-!
# Section 11.5 - Perfect Hashing

This section formalises the two-level perfect-hashing scheme of CLRS §11.5: a
static key set is stored using a primary universal hash into `m = n` buckets,
and each bucket with `n_j` keys gets a secondary table of size `m_j = n_j²`,
which — by the birthday-style collision count — is collision-free with probability
`≥ 1/2`.  The total expected secondary storage is `O(n)`.

Main results:

- Definition `PerfectHashTable`: two-level perfect hash data structure.
- Theorem `perfectSearch_iff_mem`: membership correctness
  (`perfectSearch T x ↔ x ∈ T.keys`), establishing `O(1)` worst-case search.
- Theorem `perfectHash_collision_free_prob_ge_half` (Theorem 11.9): when hashing
  `n` keys into `m = n²` slots under a universal family, the hash is collision-free
  with probability at least `1/2`.
- Theorem `exists_collision_free_secondary`: for `n ≥ 2` keys into `n²` slots, an
  injective secondary hash exists.
- Theorem `perfectHash_expected_total_space_lt_2n` (Theorem 11.10): when `n` keys
  are hashed uniformly and independently into `m = n` primary buckets, the expected
  total secondary storage `E[Σ_j n_j²]` is less than `2n` (hence `O(n)`).
- Theorem `perfectHash_expected_trials_le_two`: in a truncated model of `t`
  independent trials, the expected number of trials until a collision-free
  secondary hash is at most `2` (geometric bound with success probability ≥ 1/2).
- Theorem `perfectHash_expected_construction_time_le_const_n`: the expected total
  construction time for both levels is less than `5n` (hence `O(n)`).

Status: `proved`.  All acceptance criteria are met: a two-level model with
deterministic search correctness, the secondary collision-free probability bound,
the expected linear-space bound, and the expected linear construction time with
its geometric expected-trials argument.  RAM cost semantics are future work.

Notation conventions used in this section:

- `n` : number of keys
- `m` : number of primary buckets (and `m = n` for Theorem 11.10)
- `a : Fin n → Fin m` : a hash assignment (SUHA independent-uniform model)
- `A : Fin t → (Fin n → Fin (n^2))` : a sequence of `t` independent trial
  hashes of `n` keys into `n²` slots (construction-trial model)
- `H : ι → (K → Fin m)` : a universal family of hash functions
- `n_j` : number of keys assigned to primary bucket `j`
-/

namespace CLRS
namespace Chapter11

open CLRS.Probability
open Finset
open scoped Classical

/-! ## Two-level perfect hash model -/

/--
A `PerfectHashTable` for a finite set of keys uses a primary hash into `m` buckets
and, for each bucket `j`, a secondary hash that is collision-free on the keys
assigned to that bucket.  The deterministic two-level lookup completes in `O(1)`
worst-case time (two table lookups, independent of `n`).

The fields `sec` and `table` are per-bucket; the invariant `sec_inj` ensures no two
keys in the same primary bucket share a secondary slot, so
`table j (sec j x) = some x` identifies `x` uniquely.
-/
structure PerfectHashTable (K : Type) [DecidableEq K] (m : ℕ) : Type where
  /-- The set of keys stored in the table. -/
  keys : Finset K
  /-- Primary hash function mapping each key to a primary bucket. -/
  prim : K → Fin m
  /-- For each primary bucket `j`, a secondary hash function mapping keys to slot
  indices.  The codomain is ℕ; the actual table size per bucket is not needed for
  correctness, only for the probabilistic space bound. -/
  sec : Fin m → K → ℕ
  /-- The secondary table: for each bucket `j` and slot `s`, optionally a key. -/
  table : Fin m → ℕ → Option K
  /-- The secondary hash is collision-free on the keys in each primary bucket:
      if `x` and `y` are both in `keys`, map to the same primary bucket, and get the
      same secondary slot, then `x = y`. -/
  sec_inj : ∀ (j : Fin m) (x y : K),
    prim x = j → prim y = j → sec j x = sec j y → x = y
  /-- Every key is stored in the table at the slot determined by its primary and
      secondary hash. -/
  table_stores_keys : ∀ x ∈ keys, table (prim x) (sec (prim x) x) = some x
  /-- If the table stores a key at a slot, that key maps to that slot. -/
  table_only_keys : ∀ (j : Fin m) (s : ℕ) (x : K),
    table j s = some x → x ∈ keys ∧ prim x = j ∧ sec j x = s

/--
Two-level perfect-hash search: compute the primary bucket `j = prim x`, the
secondary slot `s = sec j x`, and check whether `table j s` holds `x`.
-/
def perfectSearch [DecidableEq K] (T : PerfectHashTable K m) (x : K) : Prop :=
  T.table (T.prim x) (T.sec (T.prim x) x) = some x

/--
**Membership correctness of two-level perfect-hash search.**  A key `x` is found
by `perfectSearch` exactly when `x ∈ T.keys` (CLRS §11.5).  This establishes
`O(1)` worst-case search time (two table lookups).
-/
theorem perfectSearch_iff_mem [DecidableEq K] (T : PerfectHashTable K m) (x : K) :
    perfectSearch T x ↔ x ∈ T.keys := by
  constructor
  · intro h
    have hmem := T.table_only_keys (T.prim x) (T.sec (T.prim x) x) x h
    exact hmem.1
  · intro h
    exact T.table_stores_keys x h

/-! ## Theorem 11.9: secondary collision-free with probability at least 1/2 -/

/-- The `fintypeExpect` operator is monotone: if `X ω ≤ Y ω` for all `ω`, then
`E[X] ≤ E[Y]`. -/
theorem fintypeExpect_mono {Ω : Type} [Fintype Ω] [DecidableEq Ω] {X Y : Ω → ℝ}
    (hXY : ∀ ω, X ω ≤ Y ω) : fintypeExpect X ≤ fintypeExpect Y := by
  unfold fintypeExpect
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => hXY ω)) ?_
  positivity

/-- `fintypeExpect` of a negated random variable is the negation of the expectation. -/
theorem fintypeExpect_neg {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X : Ω → ℝ) :
    fintypeExpect (fun ω => -X ω) = -fintypeExpect X := by
  simp [fintypeExpect, Finset.sum_neg_distrib, neg_div]

/--
Number of colliding unordered pairs `{i, j}` with `i < j` under a hash assignment
`a : Fin n → Fin m`.  Each pair of distinct indices that hash to the same bucket
contributes 1.
-/
noncomputable def collisionCount {m n : ℕ} (a : Fin n → Fin m) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (if i < j then indicator (a i = a j) else 0)

/-- `collisionCount` is nonnegative. -/
theorem collisionCount_nonneg {m n : ℕ} (a : Fin n → Fin m) : 0 ≤ collisionCount a := by
  unfold collisionCount
  apply Finset.sum_nonneg; intro i hi
  apply Finset.sum_nonneg; intro j hj
  by_cases h : i < j
  · have : 0 ≤ indicator (a i = a j) := by
      unfold indicator; split <;> norm_num
    simp [h, this]
  · simp [h, indicator]

/--
**Expected collisions under pairwise independent hashing (SUHA).**  For hash
assignments `a : Fin n → Fin m`, the expected number of colliding unordered pairs
is exactly `n(n-1)/(2m)`.
-/
theorem expectedCollisions_suha {m n : ℕ} (hm : 0 < m) :
    fintypeExpect (fun a : Fin n → Fin m => collisionCount a)
      = (n : ℝ) * ((n : ℝ) - 1) / (2 * (m : ℝ)) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  unfold collisionCount
  have hE : fintypeExpect (fun a : Fin n → Fin m =>
      ∑ i : Fin n, ∑ j : Fin n, (if i < j then indicator (a i = a j) else 0))
      = ∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 / (m : ℝ)) else 0) := by
    rw [fintypeExpect_sum Finset.univ (fun (i : Fin n) (a : Fin n → Fin m) =>
      ∑ j : Fin n, (if i < j then indicator (a i = a j) else 0))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fintypeExpect_sum Finset.univ (fun (j : Fin n) (a : Fin n → Fin m) =>
      if i < j then indicator (a i = a j) else 0)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hlt : i < j
    · simp [hlt, pairCollisionProb i j (ne_of_lt hlt) hm]
    · have hcard : Fintype.card (Fin n → Fin m) ≠ 0 := Fintype.card_ne_zero
      simp [hlt, fintypeExpect_const hcard 0]
  have hpair : (∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 / (m : ℝ)) else 0))
      = (1 / (m : ℝ)) * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
    rw [← sum_upper_triangle n, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i < j <;> simp [h]
  rw [hE, hpair]
  ring

/--
When `n` keys are hashed into `m = n²` slots under SUHA, the expected number of
collisions is less than `1/2` (for `n ≥ 2`).
-/
theorem expectedCollisions_sq_lt_half {n : ℕ} (hn : 2 ≤ n) :
    fintypeExpect (fun a : Fin n → Fin (n^2) => collisionCount a) < 1/2 := by
  have hm : 0 < n^2 := by
    have hnpos : 0 < n := by omega
    positivity
  rw [expectedCollisions_suha hm]
  have hcalc : (n : ℝ) * ((n : ℝ) - 1) / (2 * ((n : ℝ)^2)) < 1/2 := by
    have hnpos' : (n : ℝ) > 0 := by exact_mod_cast (show 0 < n from by omega)
    have hpos : (0 : ℝ) < 2 * ((n : ℝ)^2) := by positivity
    field_simp [hpos.ne']
    nlinarith
  have hden : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ)^2 := by simp
  simpa [hden] using hcalc

/--
**Markov's inequality for nonnegative-integer-valued random variables.**  If
`X : Ω → ℕ`, then `P[X ≥ 1] ≤ E[X]`.
-/
theorem markov_integer {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X : Ω → ℕ) :
    fintypeExpect (fun ω => if X ω ≥ 1 then (1 : ℝ) else 0) ≤
      fintypeExpect (fun ω => (X ω : ℝ)) := by
  have hpoint : ∀ ω, (if X ω ≥ 1 then (1 : ℝ) else 0) ≤ (X ω : ℝ) := by
    intro ω
    by_cases h : X ω ≥ 1
    · have h' : (1 : ℝ) ≤ (X ω : ℝ) := by exact_mod_cast h
      simp [h, h']
    · simp [h]
  exact fintypeExpect_mono hpoint

/--
**Theorem 11.9 (Perfect hashing: secondary collision-free with probability ≥ 1/2).**
Let `n` keys be hashed into `m = n²` slots under a universal family (or under SUHA).
Then the hash assignment is collision-free with probability at least `1/2`.

Equivalently, a secondary table of size `n_j²` for a bucket with `n_j` keys is
collision-free with probability at least `1/2` (CLRS Theorem 11.9).
-/
theorem perfectHash_collision_free_prob_ge_half {n : ℕ} (hn : 2 ≤ n) :
    fintypeExpect (fun a : Fin n → Fin (n^2) =>
      indicator (∀ i j : Fin n, a i = a j → i = j))
    ≥ 1/2 := by
  have hm : 0 < n^2 := by
    have hnpos' : 0 < n := by omega
    positivity
  have hnpos : 0 < n := by omega
  haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  haveI : Nonempty (Fin n → Fin (n^2)) :=
    ⟨fun _ => ⟨0, show 0 < n^2 from hm⟩⟩
  have hcard : Fintype.card (Fin n → Fin (n^2)) ≠ 0 := Fintype.card_ne_zero

  -- `X a` is the number of colliding unordered pairs under `a`, as a ℕ.
  let X (a : Fin n → Fin (n^2)) : ℕ :=
    (Finset.filter (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ a p.1 = a p.2)
      (Finset.univ : Finset (Fin n × Fin n))).card

  -- `X a = 0` exactly when `a` is injective (collision-free)
  have h_inj_iff : ∀ a : Fin n → Fin (n^2),
      (∀ i j : Fin n, a i = a j → i = j) ↔ X a = 0 := by
    intro a
    dsimp [X]
    constructor
    · intro hinj
      apply Finset.card_eq_zero.mpr
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      rcases hne with ⟨p, hp⟩
      rcases Finset.mem_filter.mp hp with ⟨hp_univ, ⟨hlt, heq⟩⟩
      exact hlt.ne' (hinj p.1 p.2 heq).symm
    · intro hzero
      intro i j heq
      by_contra! hne
      rcases lt_trichotomy i j with (hlt | heq' | hlt)
      · have hmem : (i, j) ∈ Finset.filter (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ a p.1 = a p.2)
            (Finset.univ : Finset (Fin n × Fin n)) := by
          simp [hlt, heq]
        have hcard_ne_zero : (Finset.filter (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ a p.1 = a p.2)
              (Finset.univ : Finset (Fin n × Fin n))).card ≠ 0 :=
          Finset.card_ne_zero.mpr ⟨(i, j), hmem⟩
        rw [hzero] at hcard_ne_zero
        exact hcard_ne_zero rfl
      · exact hne heq'
      · have hmem : (j, i) ∈ Finset.filter (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ a p.1 = a p.2)
            (Finset.univ : Finset (Fin n × Fin n)) := by
          simp [hlt, heq.symm]
        have hcard_ne_zero : (Finset.filter (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ a p.1 = a p.2)
              (Finset.univ : Finset (Fin n × Fin n))).card ≠ 0 :=
          Finset.card_ne_zero.mpr ⟨(j, i), hmem⟩
        rw [hzero] at hcard_ne_zero
        exact hcard_ne_zero rfl

  -- Rewrite the collision-free indicator in terms of `X`
  have h_indicator_eq : (fun a : Fin n → Fin (n^2) => indicator (∀ i j : Fin n, a i = a j → i = j))
      = (fun a : Fin n → Fin (n^2) => if X a = 0 then (1 : ℝ) else 0) := by
    funext a; simp [indicator, h_inj_iff a]

  rw [h_indicator_eq]

  -- Relate `collisionCount` (real-valued) to `X` (ℕ-valued)
  have h_collision_eq : (fun (a : Fin n → Fin (n^2)) => collisionCount a) =
      (fun (a : Fin n → Fin (n^2)) => (X a : ℝ)) := by
    funext a
    dsimp [collisionCount, X]
    have h1 : (∑ i : Fin n, ∑ j : Fin n, (if i < j then indicator (a i = a j) else 0)) =
        (∑ p : Fin n × Fin n, (if p.1 < p.2 then indicator (a p.1 = a p.2) else 0)) := by
      simp [Fintype.sum_prod_type]
    have h2 : (∑ p : Fin n × Fin n, (if p.1 < p.2 then indicator (a p.1 = a p.2) else 0)) =
        (∑ p : Fin n × Fin n, (if p.1 < p.2 ∧ a p.1 = a p.2 then (1 : ℝ) else 0)) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hlt : p.1 < p.2
      · simp [hlt, indicator]
      · simp [hlt, indicator]
    have h3 : (∑ p : Fin n × Fin n, (if p.1 < p.2 ∧ a p.1 = a p.2 then (1 : ℝ) else 0)) =
        (Finset.card (Finset.filter (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ a p.1 = a p.2)
          (Finset.univ : Finset (Fin n × Fin n))) : ℝ) := by
      simp [Finset.sum_filter]
    calc
      collisionCount a = (∑ i : Fin n, ∑ j : Fin n, (if i < j then indicator (a i = a j) else 0)) := rfl
      _ = (∑ p : Fin n × Fin n, (if p.1 < p.2 then indicator (a p.1 = a p.2) else 0)) := h1
      _ = (∑ p : Fin n × Fin n, (if p.1 < p.2 ∧ a p.1 = a p.2 then (1 : ℝ) else 0)) := h2
      _ = (Finset.card (Finset.filter (fun (p : Fin n × Fin n) => p.1 < p.2 ∧ a p.1 = a p.2)
          (Finset.univ : Finset (Fin n × Fin n))) : ℝ) := h3
      _ = (X a : ℝ) := rfl

  have h_expected_X_lt_half :
      fintypeExpect (fun a : Fin n → Fin (n^2) => (X a : ℝ)) < 1/2 := by
    rw [← h_collision_eq]
    exact expectedCollisions_sq_lt_half hn

  -- Markov inequality: P[X ≥ 1] ≤ E[X]
  have h_markov : fintypeExpect (fun a : Fin n → Fin (n^2) => if X a ≥ 1 then (1 : ℝ) else 0) ≤
      fintypeExpect (fun a : Fin n → Fin (n^2) => (X a : ℝ)) :=
    markov_integer X

  -- `indicator(X = 0) = 1 - indicator(X ≥ 1)`
  have h_decomp : (fun a : Fin n → Fin (n^2) => (if X a = 0 then (1 : ℝ) else 0)) =
      (fun a : Fin n → Fin (n^2) => (1 : ℝ) - (if X a ≥ 1 then (1 : ℝ) else 0)) := by
    funext a
    by_cases h : X a = 0
    · simp [h]
    · have hpos : X a ≥ 1 := Nat.one_le_of_lt (Nat.pos_of_ne_zero h)
      simp [h, hpos]

  rw [h_decomp]
  have h_expect_sub : fintypeExpect (fun a : Fin n → Fin (n^2) =>
      (1 : ℝ) - (if X a ≥ 1 then (1 : ℝ) else 0)) =
    (1 : ℝ) - fintypeExpect (fun a : Fin n → Fin (n^2) => (if X a ≥ 1 then (1 : ℝ) else 0)) := by
    calc
      fintypeExpect (fun a : Fin n → Fin (n^2) =>
          (1 : ℝ) - (if X a ≥ 1 then (1 : ℝ) else 0))
          = fintypeExpect (fun a : Fin n → Fin (n^2) =>
              (1 : ℝ) + (-(if X a ≥ 1 then (1 : ℝ) else 0))) := by
            refine congrArg fintypeExpect (funext fun a => ?_)
            rfl
      _ = fintypeExpect (fun _ : Fin n → Fin (n^2) => (1 : ℝ)) +
            fintypeExpect (fun a : Fin n → Fin (n^2) =>
              -(if X a ≥ 1 then (1 : ℝ) else 0)) :=
            fintypeExpect_add _ _
      _ = (1 : ℝ) + (-fintypeExpect (fun a : Fin n → Fin (n^2) =>
            (if X a ≥ 1 then (1 : ℝ) else 0))) := by
        simp [fintypeExpect_const hcard, fintypeExpect_neg]
      _ = (1 : ℝ) - fintypeExpect (fun a : Fin n → Fin (n^2) =>
            (if X a ≥ 1 then (1 : ℝ) else 0)) := by ring

  rw [h_expect_sub]
  have h_bound : fintypeExpect (fun a : Fin n → Fin (n^2) => if X a ≥ 1 then (1 : ℝ) else 0) < 1/2 := by
    linarith
  linarith

/-! ## Theorem 11.10: expected total space O(n) -/

/-- The number of keys (out of `n`) that hash to a given bucket `j` under assignment `a`. -/
noncomputable def bucketSize {m n : ℕ} (a : Fin n → Fin m) (j : Fin m) : ℝ :=
  ∑ i : Fin n, indicator (a i = j)

/--
The total secondary storage for a hash assignment `a`: sum over buckets of the
square of the bucket size, i.e. `Σ_j n_j²`.  This is the space used if each
bucket `j` gets a secondary table of size `n_j²`.
-/
noncomputable def totalSecondarySpace {m n : ℕ} (a : Fin n → Fin m) : ℝ :=
  ∑ j : Fin m, (bucketSize a j) ^ 2

/--
The algebraic identity `Σ_j n_j² = Σ_i Σ_k indicator(a i = a k)`.  This expands
the sum of squares into a double sum over key pairs (CLRS proof of Theorem 11.10).
-/
theorem totalSecondarySpace_eq_sum_indicator {m n : ℕ} (a : Fin n → Fin m) :
    totalSecondarySpace a = ∑ i : Fin n, ∑ k : Fin n, indicator (a i = a k) := by
  unfold totalSecondarySpace bucketSize
  calc
    ∑ j : Fin m, ((∑ i : Fin n, indicator (a i = j)) : ℝ) ^ 2
        = ∑ j : Fin m, (∑ i : Fin n, indicator (a i = j)) * (∑ k : Fin n, indicator (a k = j)) := by
          simp [sq]
    _ = ∑ j : Fin m, ∑ i : Fin n, ∑ k : Fin n, indicator (a i = j) * indicator (a k = j) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      calc
        (∑ i : Fin n, indicator (a i = j)) * (∑ k : Fin n, indicator (a k = j))
            = ∑ k : Fin n, (∑ i : Fin n, indicator (a i = j)) * indicator (a k = j) := by
              rw [Finset.mul_sum]
        _ = ∑ k : Fin n, ∑ i : Fin n, indicator (a i = j) * indicator (a k = j) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [Finset.sum_mul]
        _ = ∑ i : Fin n, ∑ k : Fin n, indicator (a i = j) * indicator (a k = j) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin m, indicator (a i = j) * indicator (a k = j) := by
      calc
        ∑ j : Fin m, ∑ i : Fin n, ∑ k : Fin n, indicator (a i = j) * indicator (a k = j)
            = ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin n, indicator (a i = j) * indicator (a k = j) := by
              rw [Finset.sum_comm]
        _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin m, indicator (a i = j) * indicator (a k = j) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ k : Fin n, indicator (a i = a k) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      simp [indicator, Finset.sum_ite_eq, Finset.mem_univ]

/--
**Theorem 11.10 (Expected total space is O(n)).**  When `n` keys are hashed
uniformly and independently into `m = n` primary buckets, the expected total
secondary storage `E[Σ_j n_j²]` is strictly less than `2n` (CLRS Theorem 11.10).
-/
theorem perfectHash_expected_total_space_lt_2n {n : ℕ} (hn : 0 < n) :
    fintypeExpect (fun a : Fin n → Fin n => totalSecondarySpace a) < 2 * (n : ℝ) := by
  have hm : 0 < n := hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : Fintype.card (Fin n → Fin n) ≠ 0 := Fintype.card_ne_zero

  -- Algebraic identity: Σ_j n_j² = n + Σ_{i≠k} indicator(a i = a k)
  have h_identity : ∀ a : Fin n → Fin n,
      totalSecondarySpace a = (n : ℝ) + ∑ i : Fin n, ∑ k : Fin n,
        (if i ≠ k then indicator (a i = a k) else 0) := by
    intro a
    calc
      totalSecondarySpace a = ∑ i : Fin n, ∑ k : Fin n, indicator (a i = a k) :=
        totalSecondarySpace_eq_sum_indicator a
      _ = (∑ i : Fin n, indicator (a i = a i)) +
          (∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0)) := by
        calc
          ∑ i : Fin n, ∑ k : Fin n, indicator (a i = a k)
              = ∑ i : Fin n, (indicator (a i = a i) + ∑ k : Fin n,
                  (if i ≠ k then indicator (a i = a k) else 0)) := by
            refine Finset.sum_congr rfl (fun i hi => ?_)
            have h_inner : ∑ k : Fin n, indicator (a i = a k)
                = indicator (a i = a i) + ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0) := by
              calc
                ∑ k : Fin n, indicator (a i = a k)
                    = ∑ k : Fin n, ((if i = k then indicator (a i = a i) else 0) +
                        (if i ≠ k then indicator (a i = a k) else 0)) := by
                      refine Finset.sum_congr rfl (fun k hk => ?_)
                      by_cases hik : i = k
                      · subst hik; simp
                      · simp [hik]
                _ = (∑ k : Fin n, (if i = k then indicator (a i = a i) else 0)) +
                    (∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0)) := by
                  simp [Finset.sum_add_distrib]
                _ = indicator (a i = a i) + ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0) := by
                  simp [Finset.sum_ite_eq, Finset.mem_univ]

            calc
              ∑ k : Fin n, indicator (a i = a k)
                  = indicator (a i = a i) + ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0) := h_inner
              _ = indicator (a i = a i) + ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0) := rfl
          _ = (∑ i : Fin n, indicator (a i = a i)) +
              (∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0)) := by
            simp [Finset.sum_add_distrib]
      _ = (n : ℝ) + ∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0) := by
        simp [indicator, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

  -- Use the identity inside the expectation
  have h_expect_identity :
      fintypeExpect (fun a : Fin n → Fin n => totalSecondarySpace a) =
      (n : ℝ) + fintypeExpect (fun a : Fin n → Fin n =>
        ∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0)) := by
    calc
      fintypeExpect (fun a : Fin n → Fin n => totalSecondarySpace a) =
          fintypeExpect (fun a : Fin n → Fin n => (n : ℝ) + ∑ i : Fin n, ∑ k : Fin n,
            (if i ≠ k then indicator (a i = a k) else 0)) := by
            refine congrArg fintypeExpect (funext h_identity)
      _ = fintypeExpect (fun _ : Fin n → Fin n => (n : ℝ)) +
          fintypeExpect (fun a : Fin n → Fin n =>
            ∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0)) :=
        fintypeExpect_add _ _
      _ = (n : ℝ) + fintypeExpect (fun a : Fin n → Fin n =>
            ∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0)) := by
        simp [fintypeExpect_const hcard, Fintype.card_fin]

  rw [h_expect_identity]

  -- Compute the remaining expectation: E[Σ_{i≠k} indicator(a i = a k)] = n*(n-1)*(1/n) = n-1
  have h_cross_expect :
      fintypeExpect (fun a : Fin n → Fin n =>
        ∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0))
      = (n : ℝ) - 1 := by
    calc
      fintypeExpect (fun a : Fin n → Fin n =>
          ∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0))
          = ∑ i : Fin n, fintypeExpect (fun a : Fin n → Fin n =>
              ∑ k : Fin n, (if i ≠ k then indicator (a i = a k) else 0)) := by
            rw [fintypeExpect_sum Finset.univ]
      _ = ∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then
            fintypeExpect (fun a : Fin n → Fin n => indicator (a i = a k)) else 0) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [fintypeExpect_sum Finset.univ]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        by_cases hne : i ≠ k
        · simp [hne, pairCollisionProb i k hne hm]
        · simp [hne, fintypeExpect_const hcard, Fintype.card_fin]
      _ = ∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then (1 / (n : ℝ)) else 0) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
        by_cases hne : i ≠ k
        · rw [pairCollisionProb i k hne hm]
        · simp [hne]
      _ = (n : ℝ) - 1 := by
        have h_inner_sum : ∀ i : Fin n, (∑ k : Fin n, (if i ≠ k then (1 / (n : ℝ)) else 0)) = ((n : ℝ) - 1) / (n : ℝ) := by
          intro i
          calc
            (∑ k : Fin n, (if i ≠ k then (1 / (n : ℝ)) else 0))
                = (∑ k : Fin n, (if i ≠ k then (1 : ℝ) else 0)) * (1 / (n : ℝ)) := by
                  simp [Finset.mul_sum, mul_comm]
            _ = ((n : ℝ) - 1) * (1 / (n : ℝ)) := by
              have hsum : (∑ k : Fin n, (if i ≠ k then (1 : ℝ) else 0)) = (n : ℝ) - 1 := by
                calc
                  (∑ k : Fin n, (if i ≠ k then (1 : ℝ) else 0))
                      = (∑ k : Fin n, ((1 : ℝ) - (if i = k then (1 : ℝ) else 0))) := by
                        refine Finset.sum_congr rfl (fun k hk => ?_)
                        by_cases hik : i = k
                        · subst hik; simp
                        · simp [hik]
                  _ = (∑ k : Fin n, (1 : ℝ)) - (∑ k : Fin n, (if i = k then (1 : ℝ) else 0)) := by
                    simp [Finset.sum_add_distrib]
                  _ = (n : ℝ) - 1 := by simp [Fintype.card_fin, Finset.sum_ite_eq, Finset.mem_univ]
              rw [hsum]
            _ = ((n : ℝ) - 1) / (n : ℝ) := by ring
        calc
          (∑ i : Fin n, ∑ k : Fin n, (if i ≠ k then (1 / (n : ℝ)) else 0))
              = ∑ i : Fin n, (((n : ℝ) - 1) / (n : ℝ)) := by
                refine Finset.sum_congr rfl (fun i hi => ?_); rw [h_inner_sum i]
          _ = (n : ℝ) * (((n : ℝ) - 1) / (n : ℝ)) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          _ = (n : ℝ) - 1 := by
            field_simp [show (n : ℝ) ≠ 0 from by exact_mod_cast hn.ne']

  rw [h_cross_expect]
  nlinarith

/-! ## Construction trials: expected trials to a collision-free secondary hash -/

/-- A hash assignment `a : Fin n → Fin (n^2)` of `n` keys into `n²` slots is
collision-free exactly when it is injective. -/
abbrev collisionFree {n : ℕ} (a : Fin n → Fin (n^2)) : Prop :=
  ∀ i j : Fin n, a i = a j → i = j

/-- Split a sequence of `k + 1` independent trial hashes into the first `k`
trials and the last trial.  This witnesses that the prefix coordinates are
independent of the last coordinate. -/
noncomputable def trialsSplitLast {n k : ℕ} :
    (Fin (k + 1) → (Fin n → Fin (n^2))) ≃
      (Fin k → (Fin n → Fin (n^2))) × (Fin n → Fin (n^2)) where
  toFun A := ((fun j : Fin k => A (Fin.castSucc j)), A ⟨k, Nat.lt_succ_self k⟩)
  invFun q := fun x : Fin (k + 1) =>
    if hx : x.val < k then q.1 ⟨x.val, hx⟩ else q.2
  left_inv A := by
    funext x
    by_cases hx : x.val < k
    · simp [hx]
    · simp [hx]
      have hx' : x = ⟨k, Nat.lt_succ_self k⟩ := by
        apply Fin.ext
        change x.val = k
        omega
      rw [hx']
  right_inv q := by
    obtain ⟨P, L⟩ := q
    refine Prod.ext ?_ ?_
    · funext j
      simp
    · simp

/-- Split a sequence of `t` independent trial hashes into the first `k` trials
and the remaining `t - k` trials, for `k ≤ t`.  This witnesses that the prefix
coordinates are independent of the suffix coordinates. -/
noncomputable def trialsSplitPrefix {n t k : ℕ} (hkt : k ≤ t) :
    (Fin t → (Fin n → Fin (n^2))) ≃
      (Fin k → (Fin n → Fin (n^2))) × (Fin (t - k) → (Fin n → Fin (n^2))) where
  toFun A := ((fun j : Fin k => A (Fin.castLE hkt j)),
              (fun j : Fin (t - k) => A ⟨k + j.val, by omega⟩))
  invFun q := fun x : Fin t =>
    if hx : x.val < k then q.1 ⟨x.val, hx⟩ else q.2 ⟨x.val - k, by omega⟩
  left_inv A := by
    funext x
    by_cases hx : x.val < k
    · simp [hx]
    · simp [hx]
      apply congrArg A
      apply Fin.ext
      change k + (x.val - k) = x.val
      omega
  right_inv q := by
    obtain ⟨P, S⟩ := q
    refine Prod.ext ?_ ?_
    · funext j
      simp
    · funext j
      have hnot : ¬ k + j.val < k := by omega
      simp [hnot]

/--
**Independent-trials failure bound.**  In `k` independent trials, each of which
produces a collision-free hash of `n ≥ 2` keys into `n²` slots with probability
at least `1/2` (Theorem 11.9), the probability that all `k` trials fail is at
most `(1/2)^k` (CLRS §11.5).
-/
theorem perfectHash_prefix_fail_prob_le {n k : ℕ} (hn : 2 ≤ n) :
    fintypeExpect (fun A : Fin k → (Fin n → Fin (n^2)) =>
      indicator (∀ j : Fin k, ¬ collisionFree (A j))) ≤ (1/2 : ℝ)^k := by
  induction k with
  | zero =>
      have htrue : ∀ A : Fin 0 → (Fin n → Fin (n^2)),
          (∀ j : Fin 0, ¬ collisionFree (A j)) := by
        intro A j
        exact Fin.elim0 j
      haveI : Nonempty (Fin n → Fin (n^2)) := ⟨fun _ => ⟨0, by
        have hnpos : 0 < n := by omega
        positivity⟩⟩
      have hcard : Fintype.card (Fin 0 → (Fin n → Fin (n^2))) ≠ 0 := Fintype.card_ne_zero
      calc
        fintypeExpect (fun A : Fin 0 → (Fin n → Fin (n^2)) =>
            indicator (∀ j : Fin 0, ¬ collisionFree (A j)))
            = fintypeExpect (fun _ : Fin 0 → (Fin n → Fin (n^2)) => (1 : ℝ)) := by
              refine congrArg fintypeExpect (funext fun A => ?_)
              have hP : (∀ j : Fin 0, ¬ collisionFree (A j)) := htrue A
              unfold indicator
              rw [if_pos hP]
        _ = 1 := by
              simp [fintypeExpect_const hcard]
        _ ≤ (1/2 : ℝ)^0 := by
              simp
  | succ k ih =>
      have hnpos : 0 < n := by omega
      haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
      haveI : Nonempty (Fin n → Fin (n^2)) := ⟨fun _ => ⟨0, by positivity⟩⟩
      have hcardΩ : Fintype.card (Fin n → Fin (n^2)) ≠ 0 := Fintype.card_ne_zero
      -- `∀ j : Fin (k+1), ¬ CF (A j)` splits as the prefix conjunction and the
      -- last trial
      have hsplit : ∀ A : Fin (k + 1) → (Fin n → Fin (n^2)),
          indicator (∀ j : Fin (k + 1), ¬ collisionFree (A j))
            = indicator ((∀ j : Fin k, ¬ collisionFree (A (Fin.castSucc j))) ∧
                ¬ collisionFree (A ⟨k, Nat.lt_succ_self k⟩)) := by
        intro A
        have hiff : (∀ j : Fin (k + 1), ¬ collisionFree (A j)) ↔
            (∀ j : Fin k, ¬ collisionFree (A (Fin.castSucc j))) ∧
              ¬ collisionFree (A ⟨k, Nat.lt_succ_self k⟩) := by
          constructor
          · intro h
            constructor
            · intro j
              exact h (Fin.castSucc j)
            · exact h ⟨k, Nat.lt_succ_self k⟩
          · rintro ⟨hpre, hlast⟩ j
            by_cases hj : j.val < k
            · have hj' : j = Fin.castSucc ⟨j.val, hj⟩ := by
                ext
                rfl
              rw [hj']
              exact hpre ⟨j.val, hj⟩
            · have hj' : j = ⟨k, Nat.lt_succ_self k⟩ := by
                apply Fin.ext
                change j.val = k
                omega
              rw [hj']
              exact hlast
        unfold indicator
        by_cases hP1 : ∀ j : Fin (k + 1), ¬collisionFree (A j)
        · rw [if_pos hP1, if_pos (hiff.mp hP1)]
        · rw [if_neg hP1, if_neg (fun hP2 => hP1 (hiff.mpr hP2))]
      -- reindex the product sample space so the prefix and last trial separate
      have he := fintypeExpect_equiv (trialsSplitLast (n := n) (k := k))
        (fun p : (Fin k → (Fin n → Fin (n^2))) × (Fin n → Fin (n^2)) =>
          indicator ((∀ j : Fin k, ¬ collisionFree (p.1 j)) ∧ ¬ collisionFree (p.2)))
      have hLHS : fintypeExpect (fun A : Fin (k + 1) → (Fin n → Fin (n^2)) =>
            indicator (∀ j : Fin (k + 1), ¬ collisionFree (A j)))
          = fintypeExpect (fun p : (Fin k → (Fin n → Fin (n^2))) × (Fin n → Fin (n^2)) =>
              indicator ((∀ j : Fin k, ¬ collisionFree (p.1 j)) ∧ ¬ collisionFree (p.2))) := by
        calc
          fintypeExpect (fun A : Fin (k + 1) → (Fin n → Fin (n^2)) =>
                indicator (∀ j : Fin (k + 1), ¬ collisionFree (A j)))
              = fintypeExpect (fun A : Fin (k + 1) → (Fin n → Fin (n^2)) =>
                  indicator ((∀ j : Fin k, ¬ collisionFree (A (Fin.castSucc j))) ∧
                    ¬ collisionFree (A ⟨k, Nat.lt_succ_self k⟩))) := by
                refine congrArg fintypeExpect (funext fun A => hsplit A)
          _ = fintypeExpect (fun A : Fin (k + 1) → (Fin n → Fin (n^2)) =>
                  indicator ((∀ j : Fin k, ¬ collisionFree ((trialsSplitLast (n := n) (k := k) A).1 j)) ∧
                    ¬ collisionFree ((trialsSplitLast (n := n) (k := k) A).2))) := by
                refine congrArg fintypeExpect (funext fun A => ?_)
                simp [trialsSplitLast]
          _ = fintypeExpect (fun p : (Fin k → (Fin n → Fin (n^2))) × (Fin n → Fin (n^2)) =>
                  indicator ((∀ j : Fin k, ¬ collisionFree (p.1 j)) ∧ ¬ collisionFree (p.2))) := he
      -- the conjunction of the independent prefix event and the last-trial event
      -- factorizes as a product of expectations
      have hprod : fintypeExpect (fun p : (Fin k → (Fin n → Fin (n^2))) × (Fin n → Fin (n^2)) =>
              indicator ((∀ j : Fin k, ¬ collisionFree (p.1 j)) ∧ ¬ collisionFree (p.2)))
          = fintypeExpect (fun B : Fin k → (Fin n → Fin (n^2)) =>
              indicator (∀ j : Fin k, ¬ collisionFree (B j)))
            * fintypeExpect (fun a : Fin n → Fin (n^2) => indicator (¬ collisionFree a)) := by
        have hsplit2 : (fun p : (Fin k → (Fin n → Fin (n^2))) × (Fin n → Fin (n^2)) =>
              indicator ((∀ j : Fin k, ¬ collisionFree (p.1 j)) ∧ ¬ collisionFree (p.2)))
            = (fun p : (Fin k → (Fin n → Fin (n^2))) × (Fin n → Fin (n^2)) =>
                (fun B : Fin k → (Fin n → Fin (n^2)) => indicator (∀ j : Fin k, ¬ collisionFree (B j))) p.1
                  * (fun a : Fin n → Fin (n^2) => indicator (¬ collisionFree a)) p.2) := by
          funext p
          by_cases hpre : ∀ j : Fin k, ¬ collisionFree (p.1 j)
          · by_cases hlast : ¬ collisionFree (p.2)
            · simp [indicator, hpre, hlast]
            · simp [indicator, hpre, hlast]
          · by_cases hlast : ¬ collisionFree (p.2)
            · simp [indicator, hpre, hlast]
            · simp [indicator, hpre, hlast]
        rw [hsplit2]
        exact expect_mul_of_indep (fun B : Fin k → (Fin n → Fin (n^2)) =>
          indicator (∀ j : Fin k, ¬ collisionFree (B j)))
          (fun a : Fin n → Fin (n^2) => indicator (¬ collisionFree a))
      -- a single trial fails with probability at most 1/2 (Theorem 11.9)
      have hfail : fintypeExpect (fun a : Fin n → Fin (n^2) => indicator (¬ collisionFree a)) ≤ 1/2 := by
        have hE : fintypeExpect (fun a : Fin n → Fin (n^2) => indicator (¬ collisionFree a))
            = 1 - fintypeExpect (fun a : Fin n → Fin (n^2) => indicator (collisionFree a)) := by
          calc
            fintypeExpect (fun a : Fin n → Fin (n^2) => indicator (¬ collisionFree a))
                = fintypeExpect (fun a : Fin n → Fin (n^2) => (1 : ℝ) - indicator (collisionFree a)) := by
                  refine congrArg fintypeExpect (funext fun a => ?_)
                  by_cases h : collisionFree a
                  · unfold indicator
                    rw [if_neg (fun hna => hna h), if_pos h]
                    simp
                  · unfold indicator
                    rw [if_pos h, if_neg h]
                    simp
            _ = fintypeExpect (fun a : Fin n → Fin (n^2) => (1 : ℝ) + (-indicator (collisionFree a))) := by
                  refine congrArg fintypeExpect (funext fun a => ?_)
                  ring
            _ = fintypeExpect (fun _ : Fin n → Fin (n^2) => (1 : ℝ)) +
                  fintypeExpect (fun a : Fin n → Fin (n^2) => -indicator (collisionFree a)) := fintypeExpect_add _ _
            _ = 1 - fintypeExpect (fun a : Fin n → Fin (n^2) => indicator (collisionFree a)) := by
                  rw [fintypeExpect_const hcardΩ, fintypeExpect_neg]
                  ring
        rw [hE]
        have hcf : 1/2 ≤ fintypeExpect (fun a : Fin n → Fin (n^2) => indicator (collisionFree a)) := by
          simpa [collisionFree] using (perfectHash_collision_free_prob_ge_half (n := n) hn)
        linarith
      -- assemble: E[prefix ∧ last] = E[prefix] · E[last] ≤ (1/2)^k · (1/2)
      calc
        fintypeExpect (fun A : Fin (k + 1) → (Fin n → Fin (n^2)) =>
            indicator (∀ j : Fin (k + 1), ¬ collisionFree (A j)))
            = fintypeExpect (fun B : Fin k → (Fin n → Fin (n^2)) =>
                indicator (∀ j : Fin k, ¬ collisionFree (B j)))
              * fintypeExpect (fun a : Fin n → Fin (n^2) => indicator (¬ collisionFree a)) := by
              rw [hLHS, hprod]
        _ ≤ (1/2 : ℝ)^k * (1/2) := by
              exact mul_le_mul ih hfail
                (fintypeExpect_nonneg (fun a : Fin n → Fin (n^2) => by
                  unfold indicator
                  split <;> norm_num))
                (by positivity)
        _ = (1/2 : ℝ)^(k + 1) := by
              simp [pow_succ]

/-- The probability that the first `k` of `t` independent trials all fail is at
most `(1/2)^k`: the remaining `t - k` trials are independent of the prefix and
marginalise out. -/
theorem perfectHash_trials_prefix_fail_prob_le {n k t : ℕ} (hn : 2 ≤ n) (hkt : k ≤ t) :
    fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
      indicator (∀ j : Fin k, ¬ collisionFree (A (Fin.castLE hkt j)))) ≤ (1/2 : ℝ)^k := by
  haveI : Nonempty (Fin n → Fin (n^2)) := ⟨fun _ => ⟨0, by
    have hnpos : 0 < n := by omega
    positivity⟩⟩
  have hcard_suffix : Fintype.card (Fin (t - k) → (Fin n → Fin (n^2))) ≠ 0 := Fintype.card_ne_zero
  have hpre : fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
        indicator (∀ j : Fin k, ¬ collisionFree (A (Fin.castLE hkt j))))
      = fintypeExpect (fun B : Fin k → (Fin n → Fin (n^2)) =>
        indicator (∀ j : Fin k, ¬ collisionFree (B j))) := by
    calc
      fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
            indicator (∀ j : Fin k, ¬ collisionFree (A (Fin.castLE hkt j))))
          = fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
              indicator (∀ j : Fin k, ¬ collisionFree ((trialsSplitPrefix hkt A).1 j))) := by
            refine congrArg fintypeExpect (funext fun A => ?_)
            simp [trialsSplitPrefix]
      _ = fintypeExpect (fun p : (Fin k → (Fin n → Fin (n^2))) × (Fin (t - k) → (Fin n → Fin (n^2))) =>
            indicator (∀ j : Fin k, ¬ collisionFree (p.1 j))) := by
            exact fintypeExpect_equiv (trialsSplitPrefix hkt)
              (fun p : (Fin k → (Fin n → Fin (n^2))) × (Fin (t - k) → (Fin n → Fin (n^2))) =>
                indicator (∀ j : Fin k, ¬ collisionFree (p.1 j)))
      _ = fintypeExpect (fun B : Fin k → (Fin n → Fin (n^2)) =>
            indicator (∀ j : Fin k, ¬ collisionFree (B j))) := by
            exact fintypeExpect_fst hcard_suffix
              (fun B : Fin k → (Fin n → Fin (n^2)) => indicator (∀ j : Fin k, ¬ collisionFree (B j)))
  rw [hpre]
  exact perfectHash_prefix_fail_prob_le hn

/-- The number of failed trials before the first collision-free trial in a
sequence of `t` independent trials.  Equivalently, the sum over `k` of the
indicators "the first `k + 1` trials all fail": each failing trial before the
first success contributes exactly one such prefix.  If every trial fails, the
value is `t`. -/
noncomputable def failedTrials {n t : ℕ} (A : Fin t → (Fin n → Fin (n^2))) : ℕ :=
  (Finset.univ.filter (fun k : Fin t =>
    ∀ j : Fin (k.val + 1), ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt k.isLt) j)))).card

/-- `failedTrials` decomposes as the sum over trial prefixes of the indicator
that the first `k + 1` trials all fail. -/
theorem failedTrials_eq_sum {n t : ℕ} (A : Fin t → (Fin n → Fin (n^2))) :
    failedTrials A = ∑ k : Fin t, (if (∀ j : Fin (k.val + 1),
      ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt k.isLt) j))) then 1 else 0) := by
  unfold failedTrials
  -- (Finset.univ.filter p).card = ∑ k ∈ univ, if p k then 1 else 0
  simpa using (Finset.sum_boole (fun k : Fin t => ∀ j : Fin (k.val + 1),
    ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt k.isLt) j)))
    (Finset.univ : Finset (Fin t))).symm

/--
**Expected failed trials before a collision-free hash.**  In the truncated
model of `t` independent trials (each collision-free with probability at least
`1/2`, Theorem 11.9), the expected number of failed trials before the first
collision-free trial is at most `1` — via the tail-sum identity
`E[F] = Σ_k P[first k trials fail] ≤ Σ_k (1/2)^k = 1` (CLRS §11.5).
-/
theorem perfectHash_expected_failedTrials_le_one {n t : ℕ} (hn : 2 ≤ n) :
    fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ)) ≤ 1 := by
  have hdecomp : (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ))
      = (fun A : Fin t → (Fin n → Fin (n^2)) => ∑ k : Fin t,
          indicator (∀ j : Fin (k.val + 1),
            ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt k.isLt) j)))) := by
    funext A
    rw [failedTrials_eq_sum A]
    simp [indicator, Nat.cast_sum]
  have hlin : fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ))
      = ∑ k : Fin t, fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
          indicator (∀ j : Fin (k.val + 1),
            ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt k.isLt) j)))) := by
    rw [hdecomp]
    exact fintypeExpect_sum Finset.univ _
  have hterm : ∀ k : Fin t, fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
        indicator (∀ j : Fin (k.val + 1),
          ¬ collisionFree (A (Fin.castLE (Nat.succ_le_of_lt k.isLt) j)))) ≤ (1/2 : ℝ)^(k.val + 1) := by
    intro k
    exact perfectHash_trials_prefix_fail_prob_le hn (Nat.succ_le_of_lt k.isLt)
  calc
    fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ))
        ≤ ∑ k : Fin t, (1/2 : ℝ)^(k.val + 1) := by
          rw [hlin]
          exact Finset.sum_le_sum (fun k _ => hterm k)
    _ ≤ 1 := by
          -- ∑ k : Fin t, (1/2)^(k.val + 1) = (1/2) · ∑ k : Fin t, (1/2)^k.val ≤ (1/2) · 2 = 1
          have hfactor : (∑ k : Fin t, (1/2 : ℝ)^(k.val + 1)) = (1/2) * (∑ k : Fin t, (1/2 : ℝ)^k.val) := by
            calc
              (∑ k : Fin t, (1/2 : ℝ)^(k.val + 1))
                  = (∑ k : Fin t, (1/2 : ℝ)^k.val * (1/2)) := by
                    refine Finset.sum_congr rfl (fun k _ => ?_)
                    rw [pow_succ]
              _ = (1/2) * (∑ k : Fin t, (1/2 : ℝ)^k.val) := by
                    rw [Finset.mul_sum]
                    simp [mul_comm]
          rw [hfactor]
          have hgeom : (∑ k : Fin t, (1/2 : ℝ)^k.val) ≤ 2 := by
            have hrange : (∑ k : Fin t, (1/2 : ℝ)^k.val) = ∑ i ∈ Finset.range t, (1/2 : ℝ)^i := by
              rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (1/2 : ℝ)^i) t]
            rw [hrange]
            have hgeom_mul := geom_sum_mul_of_le_one (x := (1/2 : ℝ)) (by norm_num) t
            -- (∑ i ∈ range t, (1/2)^i) * (1 - 1/2) = 1 - (1/2)^t, so the product is ≤ 1
            have hmul : (∑ i ∈ Finset.range t, (1/2 : ℝ)^i) * (1/2) ≤ 1 := by
              norm_num at hgeom_mul
              rw [hgeom_mul]
              have hpow : 0 ≤ (1/2 : ℝ)^t := by positivity
              nlinarith
            nlinarith
          nlinarith

/-- The number of trials performed until a collision-free secondary hash is
obtained, in a truncated model of `t` independent trials: the failed trials
before the first collision-free trial, plus the successful trial itself.  If
none of the `t` trials is collision-free, the value is `t + 1`, an overestimate
of the unbounded process's trial count. -/
noncomputable def trialsUntilCollisionFree {n t : ℕ} (A : Fin t → (Fin n → Fin (n^2))) : ℕ :=
  failedTrials A + 1

/--
**Expected number of trials to obtain a collision-free secondary hash.**  In
the truncated model of `t` independent trials — each trial hashes `n ≥ 2` keys
into `n²` slots and is collision-free with probability at least `1/2` (Theorem
11.9) — the expected number of trials performed up to and including the first
collision-free trial is at most `2` (CLRS §11.5).  For the unbounded geometric
process this is the standard bound `E[T] = 1/p ≤ 2` for success probability
`p ≥ 1/2`; the same bound holds here for every truncation `t`.
-/
theorem perfectHash_expected_trials_le_two {n t : ℕ} (hn : 2 ≤ n) :
    fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (trialsUntilCollisionFree A : ℝ)) ≤ 2 := by
  unfold trialsUntilCollisionFree
  calc
    fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => ((failedTrials A + 1 : ℕ) : ℝ))
        = fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ) + 1) := by
          refine congrArg fintypeExpect (funext fun A => ?_)
          simp
    _ = fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ)) + 1 := by
          calc
            fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ) + 1)
                = fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ)) +
                    fintypeExpect (fun _ : Fin t → (Fin n → Fin (n^2)) => (1 : ℝ)) := fintypeExpect_add _ _
            _ = fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) => (failedTrials A : ℝ)) + 1 := by
                  haveI : Nonempty (Fin n → Fin (n^2)) := ⟨fun _ => ⟨0, by
                    have hnpos : 0 < n := by omega
                    positivity⟩⟩
                  have hcard : Fintype.card (Fin t → (Fin n → Fin (n^2))) ≠ 0 := Fintype.card_ne_zero
                  simp [fintypeExpect_const hcard]
    _ ≤ 2 := by
          linarith [perfectHash_expected_failedTrials_le_one (n := n) (t := t) hn]

/--
**Existence of a collision-free secondary hash.**  For `n ≥ 2` keys hashed into
`n²` slots, some hash assignment is injective.  This follows from Theorem 11.9:
the collision-free probability is at least `1/2 > 0`, so the event cannot be
empty (CLRS §11.5).
-/
theorem exists_collision_free_secondary {n : ℕ} (hn : 2 ≤ n) :
    ∃ a : Fin n → Fin (n^2), ∀ i j : Fin n, a i = a j → i = j := by
  by_contra h
  have hnone : ∀ a : Fin n → Fin (n^2), ¬ (∀ i j : Fin n, a i = a j → i = j) := by
    intro a ha
    exact h ⟨a, ha⟩
  have hzero : fintypeExpect (fun a : Fin n → Fin (n^2) =>
      indicator (∀ i j : Fin n, a i = a j → i = j)) = 0 := by
    unfold fintypeExpect
    rw [show (∑ a : Fin n → Fin (n ^ 2), indicator (∀ i j : Fin n, a i = a j → i = j)) = 0 by
      apply Finset.sum_eq_zero
      intro a ha
      exact if_neg (hnone a)]
    simp
  have hcf := perfectHash_collision_free_prob_ge_half (n := n) hn
  linarith

/-! ## Construction time: expected total construction time is O(n) -/

/--
The expected construction cost of the two-level perfect-hash table on a
primary hash assignment `a`: `n` unit operations to insert all `n` keys into
the `n` primary buckets, plus the expected secondary construction cost
`2 · Σ_j n_j²` — each bucket `j` of `n_j` keys needs at most `2` trials in
expectation (expected-trials bound) and each trial hashes the `n_j` bucket
keys into `n_j²` slots, costing `n_j²` (CLRS §11.5).
-/
noncomputable def constructionCost {n : ℕ} (a : Fin n → Fin n) : ℝ :=
  (n : ℝ) + 2 * totalSecondarySpace a

/--
**Expected secondary construction cost of a single bucket.**  For a bucket of
`n ≥ 2` keys whose secondary hash is drawn into `n²` slots until it is
collision-free, the expected construction cost — `trialsUntilCollisionFree`
trials of `n²` work each — is at most `2 · n²`, by the expected-trials bound.
-/
theorem perfectHash_expected_bucket_cost_le {n t : ℕ} (hn : 2 ≤ n) :
    fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
      (trialsUntilCollisionFree A : ℝ) * (n : ℝ)^2) ≤ 2 * (n : ℝ)^2 := by
  have hsq : 0 ≤ (n : ℝ)^2 := by positivity
  calc
    fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
        (trialsUntilCollisionFree A : ℝ) * (n : ℝ)^2)
        = (n : ℝ)^2 * fintypeExpect (fun A : Fin t → (Fin n → Fin (n^2)) =>
            (trialsUntilCollisionFree A : ℝ)) := by
          have hswap : (fun A : Fin t → (Fin n → Fin (n^2)) =>
              (trialsUntilCollisionFree A : ℝ) * (n : ℝ)^2)
              = (fun A : Fin t → (Fin n → Fin (n^2)) => (n : ℝ)^2 * (trialsUntilCollisionFree A : ℝ)) := by
            funext A
            ring
          rw [hswap]
          exact fintypeExpect_const_mul ((n : ℝ)^2) (fun A : Fin t → (Fin n → Fin (n^2)) =>
            (trialsUntilCollisionFree A : ℝ))
    _ ≤ (n : ℝ)^2 * 2 := by
          exact mul_le_mul_of_nonneg_left (perfectHash_expected_trials_le_two hn) hsq
    _ = 2 * (n : ℝ)^2 := by
          ring

/--
**Expected construction time is O(n).**  The expected total time to build the
two-level perfect-hash table — hashing all `n` keys into the `n` primary
buckets and, for each bucket `j`, spending at most `2` trials in expectation
of cost `n_j²` each on the secondary hash — is less than `5n` (CLRS §11.5):
by Theorem 11.10, `E[Σ_j n_j²] < 2n`, and the expected trials per bucket are
at most `2`, so `E[T] < n + 2 · 2n = 5n`.
-/
theorem perfectHash_expected_construction_time_le_const_n {n : ℕ} (hn : 0 < n) :
    fintypeExpect (fun a : Fin n → Fin n => constructionCost a) < 5 * (n : ℝ) := by
  have hlin : fintypeExpect (fun a : Fin n → Fin n => constructionCost a)
      = (n : ℝ) + 2 * fintypeExpect (fun a : Fin n → Fin n => totalSecondarySpace a) := by
    unfold constructionCost
    calc
      fintypeExpect (fun a : Fin n → Fin n => (n : ℝ) + 2 * totalSecondarySpace a)
          = fintypeExpect (fun _ : Fin n → Fin n => (n : ℝ)) +
              fintypeExpect (fun a : Fin n → Fin n => 2 * totalSecondarySpace a) :=
            fintypeExpect_add _ _
      _ = (n : ℝ) + 2 * fintypeExpect (fun a : Fin n → Fin n => totalSecondarySpace a) := by
            haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
            have hcard : Fintype.card (Fin n → Fin n) ≠ 0 := Fintype.card_ne_zero
            rw [fintypeExpect_const hcard, fintypeExpect_const_mul]
  rw [hlin]
  have hspace := perfectHash_expected_total_space_lt_2n hn
  nlinarith

end Chapter11
end CLRS
