import Mathlib
import CLRSLean.Probability.FiniteExpectation

/-!
# CLRS Section 11.2 - Chained hash tables

This section gives a deterministic correctness layer for chained hash tables.
The table is a function from bucket indices to lists of keys.  The hash function
decides the bucket, insertion conses the key onto that bucket, and deletion
filters the key from that same bucket.

Main results:

- Theorem {lit}`bucket_hashInsert_same`: the inserted key appears in its hash
  bucket.
- Theorem {lit}`bucket_hashInsert_other`: buckets with a different index are
  unchanged.
- Theorem {lit}`hashSearch_hashInsert_self`: after insertion, searching for the
  inserted key succeeds.
- Theorem {lit}`hashSearch_hashInsert_iff`: after insertion, searching for any
  query succeeds exactly when it is the inserted key or was already present.
- Theorem {lit}`hashSearch_hashDelete_self`: after deletion, searching for the
  deleted key fails.
- Theorem {lit}`hashSearch_hashDelete_iff`: after deletion, searching for any
  query succeeds exactly when it is different from the deleted key and was
  already present.
- Theorem {lit}`expectedSearchChainLength_eq_loadFactor`: in the finite-uniform
  bucket model, expected chain length is exactly the load factor.
- Theorem {lit}`expectedUnsuccessfulSearchCost_finiteHashInsert`: inserting one
  key increases expected unsuccessful-search cost by {lit}`1/m`.
- Theorem {lit}`expectedRandomChainLength_eq_loadFactor`: under SUHA (keys hashed
  independently and uniformly), the expected chain length at any fixed bucket is
  the load factor {lit}`α = n/m`, as a genuine expectation over the input
  distribution `Fin n → Fin m`.
- Theorem {lit}`expectedRandomUnsuccessfulSearchCost`: the expected unsuccessful
  search cost is {lit}`1 + α`, as a genuine expectation.
- Theorem {lit}`pairCollisionProb`: under SUHA, two distinct keys collide with
  probability exactly {lit}`1/m`, as a genuine expectation.
- Theorem {lit}`expectedRandomSuccessfulSearchCost`: the expected
  successful-search cost is {lit}`1 + (n-1)/(2m)` (CLRS Theorem 11.2), as a
  double expectation over the uniform query key and the SUHA input distribution.
- Definition {lit}`IsUniversal` and Theorems {lit}`universal_expected_collisions`
  / {lit}`universal_expected_search_cost`: a random hash-*function* model, where
  a universal family gives expected collisions {lit}`≤ α` and search cost
  {lit}`≤ 1 + α` (CLRS Theorem 11.3).

Status: `proved` for deterministic correctness, finite-uniform expected cost, the
SUHA true-expectation chain-length / unsuccessful- / successful-search analysis,
and a universal random-hash-function collision-bound model.

Deferred refinements: RAM / probe-count operational semantics.
-/

namespace CLRS
namespace Chapter11

/-! ## Chained table model -/

/-- A chained hash table maps bucket indices to lists of stored keys. -/
abbrev ChainedHashTable (K : Type u) := Nat → List K

/-- Insert a key into the bucket selected by the hash function. -/
def hashInsert (h : K → Nat) (x : K)
    (T : ChainedHashTable K) : ChainedHashTable K :=
  fun i => if i = h x then x :: T i else T i

/--
Delete every copy of a key from the bucket selected by the hash function.  This
is the deterministic functional analogue of CLRS chained-hash deletion; pointer
updates inside a linked list are intentionally outside this model.
-/
def hashDelete [DecidableEq K] (h : K → Nat) (x : K)
    (T : ChainedHashTable K) : ChainedHashTable K :=
  fun i => if i = h x then (T i).filter fun y => y != x else T i

/-- Search for a key in the bucket selected by its hash value. -/
def hashSearch (h : K → Nat) (T : ChainedHashTable K) (x : K) : Prop :=
  x ∈ T (h x)

/-! ## Deterministic correctness -/

/-- The inserted key appears in its own hash bucket. -/
theorem bucket_hashInsert_same (h : K → Nat) (T : ChainedHashTable K) (x : K) :
    x ∈ hashInsert h x T (h x) := by
  simp [hashInsert]

/-- A bucket with a different index is unchanged by insertion. -/
theorem bucket_hashInsert_other {h : K → Nat} {T : ChainedHashTable K}
    {x : K} {i : Nat} (hi : i ≠ h x) :
    hashInsert h x T i = T i := by
  simp [hashInsert, hi]

/-- The deleted key no longer appears in its hash bucket. -/
theorem bucket_hashDelete_same [DecidableEq K]
    (h : K → Nat) (T : ChainedHashTable K) (x : K) :
    x ∉ hashDelete h x T (h x) := by
  simp [hashDelete]

/-- A bucket with a different index is unchanged by deletion. -/
theorem bucket_hashDelete_other [DecidableEq K]
    {h : K → Nat} {T : ChainedHashTable K} {x : K} {i : Nat}
    (hi : i ≠ h x) :
    hashDelete h x T i = T i := by
  simp [hashDelete, hi]

/-- After inserting a key, searching for that key succeeds. -/
theorem hashSearch_hashInsert_self (h : K → Nat)
    (T : ChainedHashTable K) (x : K) :
    hashSearch h (hashInsert h x T) x := by
  exact bucket_hashInsert_same h T x

/--
Searching after insertion succeeds exactly when the query is the inserted key or
the query already appeared in its own hash bucket.
-/
theorem hashSearch_hashInsert_iff (h : K → Nat)
    (T : ChainedHashTable K) (x y : K) :
    hashSearch h (hashInsert h y T) x ↔ x = y ∨ hashSearch h T x := by
  by_cases hxy : h x = h y
  · simp [hashSearch, hashInsert, hxy]
  · have hxne : x ≠ y := by
      intro hkey
      exact hxy (by rw [hkey])
    simp [hashSearch, hashInsert, hxy, hxne]

/-- After deleting a key, searching for that key fails. -/
theorem hashSearch_hashDelete_self [DecidableEq K] (h : K → Nat)
    (T : ChainedHashTable K) (x : K) :
    ¬ hashSearch h (hashDelete h x T) x := by
  exact bucket_hashDelete_same h T x

/--
Searching after deletion succeeds exactly when the query is not the deleted key
and the query was already present in its own hash bucket.
-/
theorem hashSearch_hashDelete_iff [DecidableEq K] (h : K → Nat)
    (T : ChainedHashTable K) (x y : K) :
    hashSearch h (hashDelete h y T) x ↔ x ≠ y ∧ hashSearch h T x := by
  by_cases hxy : h x = h y
  · simp [hashSearch, hashDelete, hxy, and_comm]
  · have hxne : x ≠ y := by
      intro hkey
      exact hxy (by rw [hkey])
    simp [hashSearch, hashDelete, hxy, hxne]

/-! ## Finite-uniform hashing interface -/

/-- A finite chained hash table with exactly {lit}`m` buckets. -/
abbrev FiniteChainedHashTable (m : Nat) (K : Type u) := Fin m → List K

/-- A real-valued {lit}`0/1` indicator for finite probability calculations. -/
def probabilityIndicator (P : Prop) [Decidable P] : ℝ :=
  if P then 1 else 0

/-- Uniform average over the bucket set {lit}`Fin m`. -/
noncomputable def uniformAverageFin {m : Nat} (X : Fin m → ℝ) : ℝ :=
  (∑ i : Fin m, X i) / (m : ℝ)

/-- The finite-uniform bucket average is the shared
{name}`CLRS.Probability.fintypeExpect` toolkit specialised to {lit}`Fin m`.  This
bridge lets the algebraic lemmas below reuse the toolkit instead of re-deriving
them. -/
theorem uniformAverageFin_eq_fintypeExpect {m : Nat} (X : Fin m → ℝ) :
    uniformAverageFin X = CLRS.Probability.fintypeExpect X := by
  simp [uniformAverageFin, CLRS.Probability.fintypeExpect, Fintype.card_fin]

/-- Uniform averages are additive. -/
theorem uniformAverageFin_add {m : Nat} (X Y : Fin m → ℝ) :
    uniformAverageFin (fun i => X i + Y i) =
      uniformAverageFin X + uniformAverageFin Y := by
  simp only [uniformAverageFin_eq_fintypeExpect]
  exact CLRS.Probability.fintypeExpect_add X Y

/-- A uniform average of nonnegative quantities is nonnegative. -/
theorem uniformAverageFin_nonneg {m : Nat} {X : Fin m → ℝ}
    (hX : ∀ i, 0 ≤ X i) :
    0 ≤ uniformAverageFin X := by
  rw [uniformAverageFin_eq_fintypeExpect]
  exact CLRS.Probability.fintypeExpect_nonneg hX

/-- A singleton bucket has probability {lit}`1/m` under the uniform bucket model. -/
theorem uniformAverageFin_indicator_singleton {m : Nat} (j : Fin m) :
    uniformAverageFin (fun i => probabilityIndicator (i = j)) = 1 / (m : ℝ) := by
  rw [uniformAverageFin_eq_fintypeExpect,
    show (fun i : Fin m => probabilityIndicator (i = j))
        = (fun i => CLRS.Probability.indicator (i = j)) from rfl,
    CLRS.Probability.fintypeExpect_indicator_singleton, Fintype.card_fin]

/-- Insert into a finite-bucket chained hash table. -/
def finiteHashInsert {m : Nat} (h : K → Fin m) (x : K)
    (T : FiniteChainedHashTable m K) : FiniteChainedHashTable m K :=
  fun i => if i = h x then x :: T i else T i

/-- Search in a finite-bucket chained hash table. -/
def finiteHashSearch {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) : Prop :=
  x ∈ T (h x)

/-- The finite-bucket load factor: stored keys divided by bucket count. -/
noncomputable def finiteHashLoadFactor {m : Nat}
    (T : FiniteChainedHashTable m K) : ℝ :=
  (∑ i : Fin m, ((T i).length : ℝ)) / (m : ℝ)

/-- Load factor is nonnegative. -/
theorem finiteHashLoadFactor_nonneg {m : Nat}
    (T : FiniteChainedHashTable m K) :
    0 ≤ finiteHashLoadFactor T := by
  unfold finiteHashLoadFactor
  refine div_nonneg ?_ ?_
  · exact Finset.sum_nonneg (fun i _hi => by exact_mod_cast Nat.zero_le (T i).length)
  · exact_mod_cast Nat.zero_le m

/--
Expected chain length for an unsuccessful search when the searched bucket is
uniform over all buckets.
-/
noncomputable def expectedSearchChainLength {m : Nat}
    (T : FiniteChainedHashTable m K) : ℝ :=
  uniformAverageFin (fun i => ((T i).length : ℝ))

/--
Expected unsuccessful-search cost in the current abstraction: one bucket access
plus the expected chain length.
-/
noncomputable def expectedUnsuccessfulSearchCost {m : Nat}
    (T : FiniteChainedHashTable m K) : ℝ :=
  1 + expectedSearchChainLength T

/--
Under uniform hashing over buckets, expected chain length is exactly the load
factor.
-/
theorem expectedSearchChainLength_eq_loadFactor {m : Nat}
    (T : FiniteChainedHashTable m K) :
    expectedSearchChainLength T = finiteHashLoadFactor T := by
  rfl

/-- Expected chain length is nonnegative in the finite-uniform bucket model. -/
theorem expectedSearchChainLength_nonneg {m : Nat}
    (T : FiniteChainedHashTable m K) :
    0 ≤ expectedSearchChainLength T := by
  rw [expectedSearchChainLength_eq_loadFactor]
  exact finiteHashLoadFactor_nonneg T

/--
Under uniform hashing over buckets, unsuccessful search has cost
{lit}`1 + load factor` in the current finite-bucket abstraction.
-/
theorem expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor {m : Nat}
    (T : FiniteChainedHashTable m K) :
    expectedUnsuccessfulSearchCost T = 1 + finiteHashLoadFactor T := by
  rfl

/-- Expected unsuccessful-search cost is at least the initial bucket access. -/
theorem expectedUnsuccessfulSearchCost_ge_one {m : Nat}
    (T : FiniteChainedHashTable m K) :
    1 ≤ expectedUnsuccessfulSearchCost T := by
  unfold expectedUnsuccessfulSearchCost
  have hnonneg := expectedSearchChainLength_nonneg T
  linarith

/-- Inserting one key into a finite chained table increases total chain length by one. -/
theorem totalBucketLength_finiteHashInsert {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) :
    (∑ i : Fin m, ((finiteHashInsert h x T i).length : ℝ)) =
      (∑ i : Fin m, ((T i).length : ℝ)) + 1 := by
  classical
  have hpoint : ∀ i : Fin m,
      ((finiteHashInsert h x T i).length : ℝ) =
        ((T i).length : ℝ) + probabilityIndicator (i = h x) := by
    intro i
    by_cases hi : i = h x
    · simp [finiteHashInsert, probabilityIndicator, hi]
    · simp [finiteHashInsert, probabilityIndicator, hi]
  have hindicator :
      (∑ i : Fin m, probabilityIndicator (i = h x)) = (1 : ℝ) := by
    rw [Finset.sum_eq_single (h x)]
    · simp [probabilityIndicator]
    · intro b _hb hbne
      simp [probabilityIndicator, hbne]
    · intro hmissing
      exact (hmissing (Finset.mem_univ (h x))).elim
  calc
    (∑ i : Fin m, ((finiteHashInsert h x T i).length : ℝ))
        = ∑ i : Fin m, (((T i).length : ℝ) + probabilityIndicator (i = h x)) := by
          exact Finset.sum_congr rfl (fun i _hi => hpoint i)
    _ = (∑ i : Fin m, ((T i).length : ℝ)) +
          ∑ i : Fin m, probabilityIndicator (i = h x) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin m, ((T i).length : ℝ)) + 1 := by
          rw [hindicator]

/--
Inserting one key increases the expected chain length by {lit}`1/m` in the
finite-uniform bucket model.
-/
theorem expectedSearchChainLength_finiteHashInsert {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) :
    expectedSearchChainLength (finiteHashInsert h x T) =
      expectedSearchChainLength T + 1 / (m : ℝ) := by
  simp [expectedSearchChainLength, uniformAverageFin,
    totalBucketLength_finiteHashInsert, add_div]

/--
Inserting one key increases the finite-bucket load factor by {lit}`1/m`.
-/
theorem finiteHashLoadFactor_finiteHashInsert {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) :
    finiteHashLoadFactor (finiteHashInsert h x T) =
      finiteHashLoadFactor T + 1 / (m : ℝ) := by
  simp [finiteHashLoadFactor, totalBucketLength_finiteHashInsert, add_div]

/--
Inserting one key increases expected unsuccessful-search cost by {lit}`1/m` in
the finite-uniform bucket model.
-/
theorem expectedUnsuccessfulSearchCost_finiteHashInsert {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) :
    expectedUnsuccessfulSearchCost (finiteHashInsert h x T) =
      expectedUnsuccessfulSearchCost T + 1 / (m : ℝ) := by
  rw [expectedUnsuccessfulSearchCost, expectedSearchChainLength_finiteHashInsert,
    expectedUnsuccessfulSearchCost]
  ring

/-! ## Expected search cost as a true expectation (SUHA)

The finite-uniform layer above is definitional.  We now derive the CLRS
chained-hash costs as **genuine expectations** under the *simple uniform hashing
assumption*: {lit}`n` keys are hashed independently and uniformly into
{lit}`m` buckets.  The sample space is the explicit independent uniform
distribution `Fin n → Fin m` (the bucket each key hashes to), and the load
factor is `α = n/m`. -/

open CLRS.Probability

/-- The load factor `α = n/m` of `n` keys in `m` buckets. -/
noncomputable def loadFactor (m n : Nat) : ℝ := (n : ℝ) / (m : ℝ)

/-- Split a hash assignment `a : Fin n → Fin m` into the bucket of one key `i`
and the assignment of the remaining keys.  This is the product decomposition
witnessing that coordinate `i` is independent of the rest. -/
noncomputable def hashSplit {m n : Nat} (i : Fin n) :
    (Fin n → Fin m) ≃ Fin m × ({x : Fin n // x ≠ i} → Fin m) where
  toFun a := (a i, fun x => a x.val)
  invFun q := fun x => if hx : x = i then q.1 else q.2 ⟨x, hx⟩
  left_inv a := by
    funext x; by_cases hx : x = i
    · subst hx; simp
    · simp [hx]
  right_inv q := by
    obtain ⟨b, rest⟩ := q
    simp only [Prod.mk.injEq]
    refine ⟨by simp, ?_⟩
    funext x; obtain ⟨xv, hxi⟩ := x; simp [hxi]

/-- Marginalisation: the expectation of a function of a single hash coordinate
equals the expectation over the single-bucket space {lit}`Fin m`. -/
theorem fintypeExpect_hashCoord {m n : Nat} (i : Fin n) (hm : 0 < m) (f : Fin m → ℝ) :
    fintypeExpect (fun a : Fin n → Fin m => f (a i)) = fintypeExpect f := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hcard : Fintype.card ({x : Fin n // x ≠ i} → Fin m) ≠ 0 := Fintype.card_ne_zero
  have he := fintypeExpect_equiv (hashSplit (m := m) i)
    (fun q : Fin m × ({x : Fin n // x ≠ i} → Fin m) => f q.1)
  simp only [hashSplit, Equiv.coe_fn_mk] at he
  rw [he]
  exact fintypeExpect_fst hcard f

/-- A single key hashes to a fixed bucket `q` with probability {lit}`1/m`. -/
theorem singleBucketProb {m n : Nat} (i : Fin n) (q : Fin m) (hm : 0 < m) :
    fintypeExpect (fun a : Fin n → Fin m => indicator (a i = q)) = 1 / (m : ℝ) := by
  rw [fintypeExpect_hashCoord i hm (fun c => indicator (c = q)),
    fintypeExpect_indicator_singleton, Fintype.card_fin]

/-- The length of the chain at bucket `q` under a hash assignment `a`: the number
of keys that hash to `q`. -/
noncomputable def randomChainLength {m n : Nat} (a : Fin n → Fin m) (q : Fin m) : ℝ :=
  ∑ i : Fin n, indicator (a i = q)

/--
**Expected chain length = load factor (true expectation).**  Under SUHA, the
expected number of keys hashing to any fixed bucket `q` is exactly the load
factor `α = n/m` (CLRS Theorem 11.1, unsuccessful-search chain length).
-/
theorem expectedRandomChainLength_eq_loadFactor {m n : Nat} (q : Fin m) (hm : 0 < m) :
    fintypeExpect (fun a : Fin n → Fin m => randomChainLength a q) = loadFactor m n := by
  unfold randomChainLength loadFactor
  rw [fintypeExpect_sum]
  simp only [singleBucketProb _ q hm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/--
**Expected unsuccessful-search cost = `1 + α` (true expectation).**  One bucket
access plus the expected chain length, as a genuine expectation over the SUHA
input distribution (CLRS Theorem 11.1).
-/
theorem expectedRandomUnsuccessfulSearchCost {m n : Nat} (q : Fin m) (hm : 0 < m) :
    fintypeExpect (fun a : Fin n → Fin m => 1 + randomChainLength a q) =
      1 + loadFactor m n := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hcard : Fintype.card (Fin n → Fin m) ≠ 0 := Fintype.card_ne_zero
  have key : (fun a : Fin n → Fin m => 1 + randomChainLength a q)
      = (fun a => (fun _ : Fin n → Fin m => (1 : ℝ)) a
          + (fun a => randomChainLength a q) a) := rfl
  rw [key, fintypeExpect_add, fintypeExpect_const hcard,
    expectedRandomChainLength_eq_loadFactor q hm]

/-! ## Successful search as a true expectation (SUHA)

CLRS Theorem 11.2 analyses a *successful* search: the query key is one of the
`n` stored keys, chosen uniformly, and the number of probes is one (for the key
itself) plus the number of keys that precede it in its chain.  Because new keys
are prepended, the keys ahead of `k_i` are exactly those inserted *after* it,
i.e. the later-indexed keys `k_j` with `j > i` that hash to the same bucket.
Averaging over both the uniformly random query key and the SUHA input
distribution `Fin n → Fin m` gives the expected cost `1 + α/2 - α/(2n)`, which we
prove here in the exact form `1 + (n-1)/(2m)`. -/

/-- Scalar factors pull out of `fintypeExpect`: the finite-uniform expectation is
linear in a constant multiplier. -/
theorem fintypeExpect_const_mul {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (c : ℝ) (X : Ω → ℝ) :
    fintypeExpect (fun ω => c * X ω) = c * fintypeExpect X := by
  unfold fintypeExpect
  rw [← Finset.mul_sum, mul_div_assoc]

/-- Split a hash assignment `a : Fin n → Fin m` into the buckets of two distinct
keys `i ≠ j` together with the assignment of the remaining keys.  This witnesses
that the pair of coordinates `(i, j)` is independent of the rest. -/
noncomputable def hashSplitPair {m n : Nat} (i j : Fin n) (hij : i ≠ j) :
    (Fin n → Fin m) ≃
      (Fin m × Fin m) × ({x : Fin n // x ≠ i ∧ x ≠ j} → Fin m) where
  toFun a := ((a i, a j), fun x => a x.val)
  invFun q := fun x =>
    if hx : x = i then q.1.1
    else if hy : x = j then q.1.2
    else q.2 ⟨x, ⟨hx, hy⟩⟩
  left_inv a := by
    funext x
    by_cases hx : x = i
    · subst hx; simp
    · by_cases hy : x = j
      · subst hy; simp [hx]
      · simp [hx, hy]
  right_inv q := by
    obtain ⟨⟨b1, b2⟩, rest⟩ := q
    simp only [Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp
    · have hji : ¬ (j = i) := fun h => hij h.symm
      simp [hji]
    · funext x; obtain ⟨xv, hxi, hxj⟩ := x
      simp [hxi, hxj]

/-- The uniform probability that the two coordinates of a pair over `Fin m` agree
is `1/m`: the diagonal of `Fin m × Fin m` has `m` of the `m²` points. -/
theorem fintypeExpect_prod_diag {m : Nat} (hm : 0 < m) :
    fintypeExpect (fun q : Fin m × Fin m => indicator (q.1 = q.2)) = 1 / (m : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnum : (∑ q : Fin m × Fin m, indicator (q.1 = q.2)) = (m : ℝ) := by
    unfold indicator
    rw [Fintype.sum_prod_type]
    have hinner : ∀ a : Fin m, (∑ b : Fin m, (if a = b then (1 : ℝ) else 0)) = 1 := by
      intro a; simp
    rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold fintypeExpect
  rw [hnum, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [div_mul_eq_div_div, div_self hm']

/--
**Pairwise collision probability = `1/m` (true expectation).**  Under SUHA, two
distinct keys `i ≠ j` hash to the same bucket with probability exactly `1/m`,
as a genuine expectation over the input distribution `Fin n → Fin m` (CLRS
Corollary/analysis underlying Theorems 11.1-11.2, `E[X_ij] = 1/m`). -/
theorem pairCollisionProb {m n : Nat} (i j : Fin n) (hij : i ≠ j) (hm : 0 < m) :
    fintypeExpect (fun a : Fin n → Fin m => indicator (a i = a j)) = 1 / (m : ℝ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hcard :
      Fintype.card ({x : Fin n // x ≠ i ∧ x ≠ j} → Fin m) ≠ 0 := Fintype.card_ne_zero
  have he := fintypeExpect_equiv (hashSplitPair (m := m) i j hij)
    (fun p : (Fin m × Fin m) × ({x : Fin n // x ≠ i ∧ x ≠ j} → Fin m) =>
      indicator (p.1.1 = p.1.2))
  simp only [hashSplitPair, Equiv.coe_fn_mk] at he
  have h2 : fintypeExpect
        (fun p : (Fin m × Fin m) × ({x : Fin n // x ≠ i ∧ x ≠ j} → Fin m) =>
          indicator (p.1.1 = p.1.2)) = 1 / (m : ℝ) := by
    rw [← fintypeExpect_prod_diag hm]
    exact fintypeExpect_fst hcard (fun q : Fin m × Fin m => indicator (q.1 = q.2))
  exact he.trans h2

/-- The number of ordered pairs `i < j` in `Fin n`, counted in `ℝ`, is
`n(n-1)/2`.  This is the Gauss triangle count obtained from trichotomy and the
symmetry of the strict order. -/
theorem sum_upper_triangle (n : Nat) :
    (∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℝ) else 0))
      = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have hpt : ∀ i j : Fin n,
      (if i < j then (1 : ℝ) else 0) + (if j < i then (1 : ℝ) else 0)
        + (if i = j then (1 : ℝ) else 0) = 1 := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · have h1 : ¬ j < i := lt_asymm h
      have h2 : ¬ i = j := ne_of_lt h
      simp [h, h1, h2]
    · subst h; simp
    · have h1 : ¬ i < j := lt_asymm h
      have h2 : ¬ i = j := fun he => (ne_of_lt h) he.symm
      simp [h, h1, h2]
  have hUL : (∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℝ) else 0))
      = ∑ i : Fin n, ∑ j : Fin n, (if j < i then (1 : ℝ) else 0) := Finset.sum_comm
  have hD : (∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0)) = (n : ℝ) := by
    have hone : ∀ i : Fin n, (∑ j : Fin n, (if i = j then (1 : ℝ) else 0)) = 1 := by
      intro i; simp
    rw [Finset.sum_congr rfl (fun i _ => hone i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hAll : (∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℝ) else 0))
      + (∑ i : Fin n, ∑ j : Fin n, (if j < i then (1 : ℝ) else 0))
      + (∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0))
      = (n : ℝ) * (n : ℝ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hstep : (∑ i : Fin n, ((∑ j : Fin n, (if i < j then (1 : ℝ) else 0))
        + (∑ j : Fin n, (if j < i then (1 : ℝ) else 0))
        + ∑ j : Fin n, (if i = j then (1 : ℝ) else 0)))
        = ∑ _i : Fin n, (n : ℝ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun j _ => hpt i j), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hstep, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hUL, hD] at hAll
  have h2 : (∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 : ℝ) else 0))
      = ((n : ℝ) * (n : ℝ) - (n : ℝ)) / 2 := by linarith
  rw [h2]; ring

/-- Cost of a successful search for the `i`-th inserted key under a hash
assignment `a`: one probe for `k_i` itself, plus one probe for every
later-inserted key `k_j` (index `j > i`) that hashes to the same bucket (CLRS
proof of Theorem 11.2, keys prepended so those ahead of `k_i` are exactly the
later ones). -/
noncomputable def successfulSearchKeyCost {m n : Nat}
    (a : Fin n → Fin m) (i : Fin n) : ℝ :=
  1 + ∑ j : Fin n, (if i < j then indicator (a i = a j) else 0)

/-- Average successful-search cost over the `n` stored keys, for a fixed hash
assignment `a` (the query key is uniform over the stored keys). -/
noncomputable def averageSuccessfulSearchCost {m n : Nat}
    (a : Fin n → Fin m) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, successfulSearchKeyCost a i

/--
**Expected successful-search cost = `1 + (n-1)/(2m)` (true expectation).**  This
is CLRS Theorem 11.2 (`Θ(1 + α)`, exact form `1 + α/2 - α/(2n)`), proved as a
genuine double expectation: over the uniformly random query key and over the
SUHA input distribution `Fin n → Fin m`. -/
theorem expectedRandomSuccessfulSearchCost {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    fintypeExpect (fun a : Fin n → Fin m => averageSuccessfulSearchCost a)
      = 1 + ((n : ℝ) - 1) / (2 * (m : ℝ)) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hmcard : Fintype.card (Fin n → Fin m) ≠ 0 := Fintype.card_ne_zero
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
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
    · simp only [if_pos hlt]
      exact pairCollisionProb i j (ne_of_lt hlt) hm
    · simp only [if_neg hlt]
      exact fintypeExpect_const hmcard 0
  have hpair : (∑ i : Fin n, ∑ j : Fin n, (if i < j then (1 / (m : ℝ)) else 0))
      = (1 / (m : ℝ)) * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
    rw [← sum_upper_triangle n, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i < j <;> simp [h]
  have hG : fintypeExpect (fun a : Fin n → Fin m =>
        ∑ i : Fin n, successfulSearchKeyCost a i)
      = (n : ℝ) + (1 / (m : ℝ)) * ((n : ℝ) * ((n : ℝ) - 1) / 2) := by
    have hGkey : (fun a : Fin n → Fin m => ∑ i : Fin n, successfulSearchKeyCost a i)
        = (fun a => (fun _ : Fin n → Fin m => (n : ℝ)) a
            + (fun a => ∑ i : Fin n, ∑ j : Fin n,
                (if i < j then indicator (a i = a j) else 0)) a) := by
      funext a
      show (∑ i : Fin n, successfulSearchKeyCost a i)
          = (n : ℝ) + ∑ i : Fin n, ∑ j : Fin n,
              (if i < j then indicator (a i = a j) else 0)
      unfold successfulSearchKeyCost
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
    rw [hGkey, fintypeExpect_add, fintypeExpect_const hmcard, hE, hpair]
  have key : (fun a : Fin n → Fin m => averageSuccessfulSearchCost a)
      = (fun a => (1 / (n : ℝ))
          * (fun a => ∑ i : Fin n, successfulSearchKeyCost a i) a) := rfl
  rw [key, fintypeExpect_const_mul, hG]
  field_simp

/-! ## Random hash-function model (universal hashing)

The analysis above randomises *key placement*: keys hash independently and
uniformly.  Universal hashing instead fixes the keys and randomises the *hash
function*, drawn uniformly from a family `H : ι → (K → Fin m)`.  The family is
**universal** when any two distinct keys collide with probability at most `1/m`
(CLRS Definition of a universal family, equation (11.4)).  From this hypothesis
alone we recover the expected collision bound `α = n/m` and the expected search
cost `1 + α` (CLRS Theorem 11.3). -/

/-- A finite family of hash functions `H : ι → (K → Fin m)` is **universal** if
any two distinct keys collide under a uniformly random member of the family with
probability at most `1/m` (CLRS equation (11.4)). -/
def IsUniversal {ι K : Type} [Fintype ι] [DecidableEq ι] {m : Nat}
    (H : ι → (K → Fin m)) : Prop :=
  ∀ x y : K, x ≠ y →
    fintypeExpect (fun t : ι => indicator (H t x = H t y)) ≤ 1 / (m : ℝ)

/--
**Expected collisions under universal hashing ≤ `α = n/m`.**  Fix a query key
`x` and `n` stored keys `k i`, all distinct from `x`.  Under a uniformly random
member of a universal family, the expected number of stored keys colliding with
`x` is at most the load factor `n/m` (CLRS Theorem 11.3). -/
theorem universal_expected_collisions {ι K : Type} [Fintype ι] [DecidableEq ι]
    {m n : Nat} (H : ι → (K → Fin m)) (hU : IsUniversal H)
    (x : K) (k : Fin n → K) (hk : ∀ i, k i ≠ x) :
    fintypeExpect (fun t : ι => ∑ i : Fin n, indicator (H t x = H t (k i)))
      ≤ (n : ℝ) / (m : ℝ) := by
  rw [fintypeExpect_sum Finset.univ
    (fun (i : Fin n) (t : ι) => indicator (H t x = H t (k i)))]
  calc ∑ i : Fin n, fintypeExpect (fun t : ι => indicator (H t x = H t (k i)))
      ≤ ∑ _i : Fin n, (1 / (m : ℝ)) :=
        Finset.sum_le_sum (fun i _ => hU x (k i) (Ne.symm (hk i)))
    _ = (n : ℝ) / (m : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/--
**Expected successful/unsuccessful search cost under universal hashing
≤ `1 + α`.**  One probe plus the expected number of colliding stored keys
(CLRS Theorem 11.3, the universal-hashing analogue of Theorems 11.1-11.2). -/
theorem universal_expected_search_cost {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {m n : Nat} (H : ι → (K → Fin m)) (hU : IsUniversal H)
    (x : K) (k : Fin n → K) (hk : ∀ i, k i ≠ x) :
    fintypeExpect (fun t : ι => 1 + ∑ i : Fin n, indicator (H t x = H t (k i)))
      ≤ 1 + (n : ℝ) / (m : ℝ) := by
  have hcard : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have key : (fun t : ι => 1 + ∑ i : Fin n, indicator (H t x = H t (k i)))
      = (fun t => (fun _ : ι => (1 : ℝ)) t
          + (fun t => ∑ i : Fin n, indicator (H t x = H t (k i))) t) := rfl
  rw [key, fintypeExpect_add, fintypeExpect_const hcard]
  have hbound := universal_expected_collisions H hU x k hk
  linarith

end Chapter11
end CLRS
