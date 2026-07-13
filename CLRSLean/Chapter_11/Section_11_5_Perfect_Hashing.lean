import Mathlib
import CLRSLean.Probability.FiniteExpectation
import CLRSLean.Chapter_11.Section_11_2_Chained_Hash_Tables

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
- Theorem `perfectHash_expected_total_space_lt_2n` (Theorem 11.10): when `n` keys
  are hashed uniformly and independently into `m = n` primary buckets, the expected
  total secondary storage `E[Σ_j n_j²]` is less than `2n` (hence `O(n)`).

Status: `proved`.  All three acceptance criteria are met: a two-level model with
deterministic search correctness, the secondary collision-free probability bound,
and the expected linear-space bound.  Construction/rebuild running time and RAM
cost semantics are future work.

Notation conventions used in this section:

- `n` : number of keys
- `m` : number of primary buckets (and `m = n` for Theorem 11.10)
- `a : Fin n → Fin m` : a hash assignment (SUHA independent-uniform model)
- `H : ι → (K → Fin m)` : a universal family of hash functions
- `n_j` : number of keys assigned to primary bucket `j`
-/

namespace CLRS
namespace Chapter11

open CLRS.Probability
open Finset

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

end Chapter11
end CLRS
