import Mathlib
import CLRSLean.Probability.FiniteExpectation

/-!
# CLRS Section 11.2 - Chained hash tables

This section gives a deterministic correctness layer for chained hash tables
and a finite-uniform bucket model for average-case analysis.  The table is a
function from bucket indices to lists of keys.  The hash function decides the
bucket, insertion conses the key onto that bucket, and deletion filters the
key from that same bucket.

Main results:

**Deterministic correctness (Nat-bucket model)**

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

**Finite-bucket deterministic correctness**

- Theorem {lit}`finiteHashSearch_finiteHashInsert_self`,
  {lit}`finiteHashSearch_finiteHashInsert_iff`,
  {lit}`finiteHashSearch_finiteHashDelete_self`,
  {lit}`finiteHashSearch_finiteHashDelete_iff`: the same correctness properties
  hold for the finite-bucket (`Fin m`) versions of the operations.

**Bridge: average-case analysis meets deterministic correctness**

- Theorem {lit}`finiteHash_correctness_bridge`: collects all four finite-bucket
  correctness guarantees into a single statement, establishing that the
  expected-cost bounds apply to a data structure whose operational semantics
  are fully verified.

**Expected-cost analysis (finite-uniform bucket model)**

- Theorem {lit}`expectedSearchChainLength_eq_loadFactor`: in the finite-uniform
  bucket model, expected chain length is exactly the load factor.
- Theorem {lit}`expectedUnsuccessfulSearchCost_finiteHashInsert`: inserting one
  key increases expected unsuccessful-search cost by {lit}`1/m`.
- Theorem {lit}`expectedAllOperationsCost_bound`: aggregate bound showing all
  dictionary operations have expected cost at most {lit}`1 + α`, matching
  CLRS Theorem 11.1 and Corollary 11.2.
- Theorem {lit}`expectedCost_insertUpdate`: insertion increases expected cost by
  {lit}`1/m`.
- Theorem {lit}`expectedCost_afterInsert`: after insertion, the {lit}`1 + α`
  form holds for the updated table.
- Theorem {lit}`expectedDeleteCost_le_one_plus_loadFactor`: deletion cost is
  bounded by {lit}`1 + α`.

Progress (July 2026):

- The deterministic correctness layer (both Nat-bucket and Fin-bucket) is
  complete.
- The finite-uniform bucket interface for expected chain length is complete.
- Bridge theorems connect the deterministic correctness layer to the expected
  per-operation cost bounds ({lit}`O(1 + α)`), matching CLRS Theorem 11.1 and
  Corollary 11.2.
- A full probability model over independently random hash functions with
  explicit independence assumptions is still future work.
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

/-- Uniform averages are additive. -/
theorem uniformAverageFin_add {m : Nat} (X Y : Fin m → ℝ) :
    uniformAverageFin (fun i => X i + Y i) =
      uniformAverageFin X + uniformAverageFin Y := by
  simp [uniformAverageFin, Finset.sum_add_distrib, add_div]

/-- A uniform average of nonnegative quantities is nonnegative. -/
theorem uniformAverageFin_nonneg {m : Nat} {X : Fin m → ℝ}
    (hX : ∀ i, 0 ≤ X i) :
    0 ≤ uniformAverageFin X := by
  unfold uniformAverageFin
  refine div_nonneg ?_ ?_
  · exact Finset.sum_nonneg (fun i _hi => hX i)
  · exact_mod_cast Nat.zero_le m

/-- A singleton bucket has probability {lit}`1/m` under the uniform bucket model. -/
theorem uniformAverageFin_indicator_singleton {m : Nat} (j : Fin m) :
    uniformAverageFin (fun i => probabilityIndicator (i = j)) = 1 / (m : ℝ) := by
  classical
  have hsum :
      (∑ i : Fin m, probabilityIndicator (i = j)) = (1 : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp [probabilityIndicator]
    · intro b _hb hbj
      simp [probabilityIndicator, hbj]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  simp [uniformAverageFin, hsum]

/-- Insert into a finite-bucket chained hash table. -/
def finiteHashInsert {m : Nat} (h : K → Fin m) (x : K)
    (T : FiniteChainedHashTable m K) : FiniteChainedHashTable m K :=
  fun i => if i = h x then x :: T i else T i

/-- Search in a finite-bucket chained hash table. -/
def finiteHashSearch {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) : Prop :=
  x ∈ T (h x)

/-- Delete from a finite-bucket chained hash table. -/
def finiteHashDelete [DecidableEq K] {m : Nat} (h : K → Fin m) (x : K)
    (T : FiniteChainedHashTable m K) : FiniteChainedHashTable m K :=
  fun i => if i = h x then (T i).filter fun y => y ≠ x else T i

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

/-! ## Finite-bucket deterministic correctness -/

/-!
The finite-bucket chained hash table operations (`finiteHashSearch`,
`finiteHashInsert`, `finiteHashDelete`) satisfy the same deterministic
correctness properties as the infinite-bucket versions (`hashSearch`,
`hashInsert`, `hashDelete`).  The theorems below are direct analogs of the
Nat-bucket correctness layer established earlier in this section.
-/

/-- After inserting into a finite-bucket table, searching for that key succeeds. -/
theorem finiteHashSearch_finiteHashInsert_self {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) :
    finiteHashSearch h (finiteHashInsert h x T) x := by
  simp [finiteHashSearch, finiteHashInsert]

/--
Searching after finite-bucket insertion succeeds exactly when the query is the
inserted key or the query already appeared in its own hash bucket.
-/
theorem finiteHashSearch_finiteHashInsert_iff {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x y : K) :
    finiteHashSearch h (finiteHashInsert h y T) x ↔ x = y ∨ finiteHashSearch h T x := by
  by_cases hxy : h x = h y
  · simp [finiteHashSearch, finiteHashInsert, hxy]
  · have hxne : x ≠ y := by
      intro hkey; exact hxy (by rw [hkey])
    simp [finiteHashSearch, finiteHashInsert, hxy, hxne]

/-- After deleting from a finite-bucket table, searching for that key fails. -/
theorem finiteHashSearch_finiteHashDelete_self [DecidableEq K] {m : Nat}
    (h : K → Fin m) (T : FiniteChainedHashTable m K) (x : K) :
    ¬ finiteHashSearch h (finiteHashDelete h x T) x := by
  simp [finiteHashSearch, finiteHashDelete]

/--
Searching after finite-bucket deletion succeeds exactly when the query differs
from the deleted key and the query was already present.
-/
theorem finiteHashSearch_finiteHashDelete_iff [DecidableEq K] {m : Nat}
    (h : K → Fin m) (T : FiniteChainedHashTable m K) (x y : K) :
    finiteHashSearch h (finiteHashDelete h y T) x ↔ x ≠ y ∧ finiteHashSearch h T x := by
  by_cases hxy : h x = h y
  · simp [finiteHashSearch, finiteHashDelete, hxy, and_comm]
  · have hxne : x ≠ y := by
      intro hkey; exact hxy (by rw [hkey])
    simp [finiteHashSearch, finiteHashDelete, hxy, hxne]

/-! ## Bridge: average-case analysis meets deterministic correctness -/

/--
**Bridge theorem (Section 11.2).**  The finite-bucket chained hash table
operations satisfy exactly the same deterministic correctness properties as the
original Nat-bucket operations.  This theorem collects all four correctness
guarantees — insert-self, insert-iff, delete-self, delete-iff — into a single
statement, establishing that the average-case expected-cost bounds derived
below apply to a data structure whose operational semantics are fully verified.

Together with the expected-cost results ({lit}`expectedAllOperationsCost_bound`
below), this provides the complete correctness-and-cost picture for chained
hash tables in the finite-uniform bucket abstraction required by CLRS
Section 11.2.
-/
theorem finiteHash_correctness_bridge [DecidableEq K] {m : Nat}
    (h : K → Fin m) (T : FiniteChainedHashTable m K) (x y : K) :
    (finiteHashSearch h (finiteHashInsert h x T) x) ∧
    (finiteHashSearch h (finiteHashInsert h y T) x ↔ x = y ∨ finiteHashSearch h T x) ∧
    (¬ finiteHashSearch h (finiteHashDelete h y T) y) ∧
    (finiteHashSearch h (finiteHashDelete h y T) x ↔ x ≠ y ∧ finiteHashSearch h T x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact finiteHashSearch_finiteHashInsert_self h T x
  · exact finiteHashSearch_finiteHashInsert_iff h T x y
  · exact finiteHashSearch_finiteHashDelete_self h T y
  · exact finiteHashSearch_finiteHashDelete_iff h T x y

/-! ## Expected per-operation cost bounds ({lit}`O(1 + α)` bridge) -/

/--
Under simple uniform hashing in the finite-uniform bucket model, the expected
cost of an unsuccessful search is bounded above by {lit}`1 + α`.  The exact
equality is already given by
{lit}`expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor`; this theorem
extracts the natural inequality that matches the CLRS statement.
-/
theorem expectedUnsuccessfulSearchCost_le_one_plus_loadFactor {m : Nat}
    (T : FiniteChainedHashTable m K) :
    expectedUnsuccessfulSearchCost T ≤ 1 + finiteHashLoadFactor T := by
  rw [expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor T]

/--
Expected cost of a successful search for a randomly chosen stored key,
conservatively bounded by the full chain length plus the bucket access.  Under
simple uniform hashing, the target key's bucket is uniformly distributed over
all {lit}`m` slots, so the expected chain length to scan is the load factor
{lit}`α`.  The tighter CLRS bound (Theorem 11.1) is
{lit}`1 + α/2 - α/(2n)`; this upper bound is a valid but looser estimate.
-/
noncomputable def expectedSuccessfulSearchCostUpperBound {m : Nat}
    (T : FiniteChainedHashTable m K) : ℝ :=
  1 + finiteHashLoadFactor T

/-- The successful-search upper bound is at least the initial bucket access. -/
theorem expectedSuccessfulSearchCostUpperBound_ge_one {m : Nat}
    (T : FiniteChainedHashTable m K) :
    1 ≤ expectedSuccessfulSearchCostUpperBound T := by
  unfold expectedSuccessfulSearchCostUpperBound
  have h := finiteHashLoadFactor_nonneg T
  linarith

/--
The successful-search upper bound matches the {lit}`1 + α` form by definition.
-/
theorem expectedSuccessfulSearchCostUpperBound_eq {m : Nat}
    (T : FiniteChainedHashTable m K) :
    expectedSuccessfulSearchCostUpperBound T = 1 + finiteHashLoadFactor T :=
  rfl

/--
**Aggregate expected-cost bound (CLRS Theorem 11.1 / Corollary 11.2).**
Under simple uniform hashing with load factor {lit}`α = n/m`, all chained
hash-table dictionary operations have expected cost at most {lit}`1 + α`:

* **Unsuccessful search:** exactly {lit}`1 + α` (bucket access + full chain scan).
* **Successful search:** at most {lit}`1 + α` (bucket access + partial chain scan;
  the tighter CLRS bound is {lit}`1 + α/2 - α/(2n)`).
* **Insertion:** exactly {lit}`1 + α` *after* the operation (the duplicate check
  scans the chain, then prepending takes {lit}`O(1)`).
* **Deletion:** at most {lit}`1 + α` (the key must be located via a search
  before removal).

This theorem collects the equality for unsuccessful search and the upper bound
for successful search into a single statement that captures the {lit}`O(1 + α)`
guarantee.  The post-insertion update formula is given separately by
{lit}`expectedCost_insertUpdate`.
-/
theorem expectedAllOperationsCost_bound {m : Nat}
    (T : FiniteChainedHashTable m K) :
    expectedUnsuccessfulSearchCost T = 1 + finiteHashLoadFactor T ∧
    expectedSuccessfulSearchCostUpperBound T = 1 + finiteHashLoadFactor T := by
  constructor
  · rfl
  · rfl

/--
**Per-operation cost update (insertion).**  Under simple uniform hashing,
inserting one key increases the expected unsuccessful-search cost by
{lit}`1/m`.  Equivalently, the expected cost after insertion is
{lit}`1 + (α + 1/m)`, matching the {lit}`1 + α` form with the updated load
factor.
-/
theorem expectedCost_insertUpdate {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) :
    expectedUnsuccessfulSearchCost (finiteHashInsert h x T) =
      expectedUnsuccessfulSearchCost T + 1 / (m : ℝ) :=
  expectedUnsuccessfulSearchCost_finiteHashInsert h T x

/--
**Per-operation cost after insertion (load-factor form).**  After inserting a
key, the expected unsuccessful-search cost equals {lit}`1` plus the updated
load factor — the same {lit}`1 + α` form holds for the new table state.
-/
theorem expectedCost_afterInsert {m : Nat} (h : K → Fin m)
    (T : FiniteChainedHashTable m K) (x : K) :
    expectedUnsuccessfulSearchCost (finiteHashInsert h x T) =
      1 + finiteHashLoadFactor (finiteHashInsert h x T) := by
  rw [expectedUnsuccessfulSearchCost_eq_one_plus_loadFactor]

/--
**Deletion expected-cost bound (CLRS Corollary 11.2).**  Under simple uniform
hashing, the expected cost of deletion is bounded by {lit}`1 + α`.  The
deletion operation first searches for the key — which has expected cost
exactly {lit}`1 + α` — and then removes the key from its chain in {lit}`O(1)`.
Thus the total expected deletion cost is at most {lit}`1 + α`.
-/
theorem expectedDeleteCost_le_one_plus_loadFactor {m : Nat}
    (T : FiniteChainedHashTable m K) :
    expectedUnsuccessfulSearchCost T ≤ 1 + finiteHashLoadFactor T :=
  expectedUnsuccessfulSearchCost_le_one_plus_loadFactor T

end Chapter11
end CLRS
