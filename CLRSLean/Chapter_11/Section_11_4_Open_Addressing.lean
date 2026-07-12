import Mathlib

/-!
# CLRS Section 11.4 - Open addressing

Open addressing stores every key directly in the table `Fin m → Option K` (no
chains).  Each key `k` has a **probe sequence** `⟨h(k,0), h(k,1), …, h(k,m-1)⟩`, a
permutation of the slots; a search or insertion walks the probe order until it
finds the key (success), an empty slot (stop), or exhausts the table.

This section formalises three layers.

Main results:

- **Functional model (CLRS §11.4 operational layer).**
  - {lit}`openInsert` / {lit}`openSearch`: insert into the first empty slot along
    the probe order; search until the key or the first empty slot.
  - Theorem {lit}`openSearch_eq_false_of_absent`: a key that is nowhere in the
    table is not found (absent key not found).
  - Theorem {lit}`openSearch_openInsert`: after inserting a key along a
    duplicate-free probe order that has an empty slot, a search finds it
    (inserted key is found).
- **Probe schemes (CLRS §11.4, equations (11.5)-(11.7)).**
  - {lit}`linearProbe`, {lit}`quadraticProbe`, {lit}`doubleHashProbe` over
    {lit}`ZMod m`.
  - Theorem {lit}`linearProbe_bijective`: linear probing enumerates every slot.
  - Theorem {lit}`doubleHashProbe_bijective`: double hashing enumerates every slot
    when the second hash is a unit (coprime to `m`, CLRS requirement).
  - Theorem {lit}`quadraticProbe_zero`: quadratic probing starts at the base slot.
- **Expected-probe bounds under uniform hashing (CLRS Theorems 11.6-11.8).**
  - {lit}`probeTail`: the uniform-hashing probability that the first `i` probes of
    an unsuccessful search all hit occupied slots, the without-replacement product
    `∏_{j<i} (n-j)/(m-j)` (CLRS §11.4).
  - Theorem {lit}`probeTail_le_pow`: each such probability is at most `α^i`, the
    per-factor bound `(n-j)/(m-j) ≤ n/m` that CLRS uses.
  - Theorem {lit}`expectedUnsuccessfulProbes_le`: expected unsuccessful-search
    probes `≤ 1/(1-α)` (CLRS Theorem 11.6), as the tail-sum `∑_i probeTail`.
  - Theorem {lit}`expectedInsertionProbes_le`: the same `1/(1-α)` bound for an
    insertion (CLRS Corollary 11.7).
  - Theorem {lit}`expectedSuccessfulProbes_le`: expected successful-search probes
    `≤ (1/α) * ∑_{j<n} 1/(m-j) = (1/α)(H_m - H_{m-n})`, the harmonic form of
    CLRS Theorem 11.8.

Status: `proved` for the functional model, the probe schemes, and the
uniform-hashing expected-probe bounds.

Notation conventions used in this section:

- `m` : the number of table slots
- `n` : the number of stored keys; `α = n/m` is the load factor
    ({lit}`openLoadFactor`)
- `K` : the key type; a slot is `Option K` (`none` = empty)
- `probeTail m n i` : `P[first i probes all occupied]`, the uniform-hashing tail
- `H_k` : the `k`-th harmonic number `∑_{r=1}^{k} 1/r`

Current gaps: the expected-probe values are the tail-sum
`E[X] = ∑_{i≥0} P[X > i]`, with the tail probabilities `probeTail` the standard
uniform-hashing without-replacement products.  Deriving those tails from an
explicit permutation sample space (via `Fintype` counting), and the closed-form
`ln(1/(1-α))` integral bound refining the harmonic sum, are deferred refinements;
RAM / cache-cost semantics remain out of scope (epic #28).
-/

namespace CLRS
namespace Chapter11

/-! ## Functional open-addressing model

The table maps each of the `m` slots to `Option K` (`none` = empty).  A probe
order is a `List` of slots (the slot type is left abstract; the probe schemes
below instantiate it at {lit}`ZMod m`).  `scanFind` and `scanInsertPos` walk a
probe order once. -/

/-- Walk a probe order looking for `k`, stopping at the first empty slot: return
`true` if a slot holding `k` is reached before any empty slot (open-addressing
search semantics). -/
def scanFind {S K : Type*} [DecidableEq K] (T : S → Option K) (k : K) :
    List S → Bool
  | [] => false
  | s :: rest =>
      if T s = some k then true
      else if T s = none then false
      else scanFind T k rest

/-- Walk a probe order returning the first empty slot, or `none` if the order has
no empty slot (table full along this probe order). -/
def scanInsertPos {S K : Type*} [DecidableEq K] (T : S → Option K) :
    List S → Option S
  | [] => none
  | s :: rest => if T s = none then some s else scanInsertPos T rest

/-- Open-addressing search along a probe order. -/
def openSearch {S K : Type*} [DecidableEq K] (T : S → Option K)
    (order : List S) (k : K) : Bool :=
  scanFind T k order

/-- Open-addressing insert along a probe order: place the key in the first empty
slot.  If the probe order has no empty slot the table is returned unchanged (the
table-full junk value; totality over `Option`-slot tables). -/
def openInsert {S K : Type*} [DecidableEq S] [DecidableEq K] (T : S → Option K)
    (order : List S) (k : K) : S → Option K :=
  match scanInsertPos T order with
  | some s => Function.update T s (some k)
  | none => T

/-! ### Model correctness (CLRS §11.4 insert/search behaviour) -/

/-- If a key occupies no slot, an open-addressing search along any probe order
fails. -/
theorem scanFind_absent {S K : Type*} [DecidableEq K] (T : S → Option K) (k : K)
    (h : ∀ s, T s ≠ some k) (order : List S) : scanFind T k order = false := by
  induction order with
  | nil => rfl
  | cons s rest ih =>
      simp only [scanFind, if_neg (h s)]
      by_cases he : T s = none
      · simp [he]
      · simp only [if_neg he]; exact ih

/-- The first empty slot reported by `scanInsertPos` is a member of the probe
order. -/
theorem scanInsertPos_mem {S K : Type*} [DecidableEq K] (T : S → Option K)
    (order : List S) (s : S) (h : scanInsertPos T order = some s) : s ∈ order := by
  induction order with
  | nil => simp [scanInsertPos] at h
  | cons a rest ih =>
      simp only [scanInsertPos] at h
      by_cases ha : T a = none
      · rw [if_pos ha, Option.some_inj] at h
        subst h; simp
      · rw [if_neg ha] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- If the probe order has an empty slot, `scanInsertPos` reports one. -/
theorem scanInsertPos_isSome_of_empty {S K : Type*} [DecidableEq K]
    (T : S → Option K) (order : List S) (h : ∃ s ∈ order, T s = none) :
    ∃ s, scanInsertPos T order = some s := by
  induction order with
  | nil => obtain ⟨s, hs, _⟩ := h; simp at hs
  | cons a rest ih =>
      by_cases ha : T a = none
      · exact ⟨a, by simp [scanInsertPos, ha]⟩
      · obtain ⟨s, hs, hTs⟩ := h
        rw [List.mem_cons] at hs
        rcases hs with rfl | hmem
        · exact absurd hTs ha
        · obtain ⟨s', hs'⟩ := ih ⟨s, hmem, hTs⟩
          exact ⟨s', by simp only [scanInsertPos, if_neg ha]; exact hs'⟩

/-- After inserting a key into the first empty slot of a duplicate-free probe
order, a search along that order finds it. -/
theorem scanFind_update_of_scanInsertPos {S K : Type*} [DecidableEq S]
    [DecidableEq K] (T : S → Option K) (k : K) (order : List S) (s : S)
    (hnd : order.Nodup) (hins : scanInsertPos T order = some s) :
    scanFind (Function.update T s (some k)) k order = true := by
  induction order with
  | nil => simp [scanInsertPos] at hins
  | cons a rest ih =>
      simp only [scanInsertPos] at hins
      by_cases ha : T a = none
      · rw [if_pos ha, Option.some_inj] at hins
        subst hins
        simp [scanFind, Function.update_self]
      · rw [if_neg ha] at hins
        have hmem : s ∈ rest := scanInsertPos_mem T rest s hins
        have hnd' := List.nodup_cons.mp hnd
        have has : a ≠ s := fun hEq => hnd'.1 (hEq ▸ hmem)
        simp only [scanFind, Function.update_of_ne has]
        by_cases hak : T a = some k
        · rw [if_pos hak]
        · rw [if_neg hak, if_neg ha]
          exact ih hnd'.2 hins

/-- **AC-1 (absent key not found).**  A key stored in no slot is not found by an
open-addressing search along any probe order. -/
theorem openSearch_eq_false_of_absent {S K : Type*} [DecidableEq K]
    (T : S → Option K) (order : List S) (k : K) (h : ∀ s, T s ≠ some k) :
    openSearch T order k = false :=
  scanFind_absent T k h order

/-- **AC-1 (inserted key found).**  If a duplicate-free probe order has an empty
slot, then after inserting a key it is found by a search along the same order. -/
theorem openSearch_openInsert {S K : Type*} [DecidableEq S] [DecidableEq K]
    (T : S → Option K) (order : List S) (k : K) (hnd : order.Nodup)
    (hempty : ∃ s ∈ order, T s = none) :
    openSearch (openInsert T order k) order k = true := by
  obtain ⟨s, hs⟩ := scanInsertPos_isSome_of_empty T order hempty
  have hupd : openInsert T order k = Function.update T s (some k) := by
    simp only [openInsert, hs]
  rw [openSearch, hupd]
  exact scanFind_update_of_scanInsertPos T k order s hnd hs

/-! ## Probe schemes (CLRS §11.4, equations (11.5)-(11.7))

Each scheme is a function `ZMod m → ZMod m` mapping a probe number `i` to a slot,
for a fixed key.  CLRS requires each probe sequence to enumerate all `m` slots
(be a permutation); linear probing always does, and double hashing does when the
step size is a unit modulo `m`. -/

/-- **Linear probing** (CLRS equation (11.5)): `h(k,i) = (h'(k) + i) mod m`. -/
def linearProbe {m : ℕ} (h0 : ZMod m) (i : ZMod m) : ZMod m := h0 + i

/-- **Quadratic probing** (CLRS equation (11.6)):
`h(k,i) = (h'(k) + c₁ i + c₂ i²) mod m`. -/
def quadraticProbe {m : ℕ} (h0 c1 c2 : ZMod m) (i : ZMod m) : ZMod m :=
  h0 + c1 * i + c2 * i * i

/-- **Double hashing** (CLRS equation (11.7)):
`h(k,i) = (h₁(k) + i · h₂(k)) mod m`. -/
def doubleHashProbe {m : ℕ} (h1 h2 : ZMod m) (i : ZMod m) : ZMod m := h1 + i * h2

/-- Linear probing enumerates every slot: as a function of the probe number it is
a bijection of `ZMod m` (CLRS: a linear probe sequence is a permutation). -/
theorem linearProbe_bijective {m : ℕ} (h0 : ZMod m) :
    Function.Bijective (linearProbe h0) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun t => t - h0, ?_, ?_⟩
  · intro i; show (h0 + i) - h0 = i; ring
  · intro t; show h0 + (t - h0) = t; ring

/-- Linear probing covers every slot (surjectivity form of the permutation
property). -/
theorem linearProbe_surjective {m : ℕ} (h0 : ZMod m) :
    Function.Surjective (linearProbe h0) :=
  (linearProbe_bijective h0).surjective

/-- Double hashing enumerates every slot when the step `h₂` is a unit modulo `m`
(CLRS: `h₂(k)` must be relatively prime to `m` for the probe sequence to be a
permutation). -/
theorem doubleHashProbe_bijective {m : ℕ} (h1 h2 : ZMod m) (hu : IsUnit h2) :
    Function.Bijective (doubleHashProbe h1 h2) := by
  obtain ⟨u, rfl⟩ := hu
  refine Function.bijective_iff_has_inverse.mpr ⟨fun t => (t - h1) * ↑u⁻¹, ?_, ?_⟩
  · intro i
    show ((doubleHashProbe h1 (↑u) i) - h1) * ↑u⁻¹ = i
    have hu1 : (↑u : ZMod m) * ↑u⁻¹ = 1 := u.mul_inv
    unfold doubleHashProbe
    calc (h1 + i * ↑u - h1) * ↑u⁻¹ = i * (↑u * ↑u⁻¹) := by ring
      _ = i := by rw [hu1, mul_one]
  · intro t
    show doubleHashProbe h1 (↑u) ((t - h1) * ↑u⁻¹) = t
    have hu2 : (↑u⁻¹ : ZMod m) * ↑u = 1 := u.inv_mul
    unfold doubleHashProbe
    calc h1 + (t - h1) * ↑u⁻¹ * ↑u = h1 + (t - h1) * (↑u⁻¹ * ↑u) := by ring
      _ = t := by rw [hu2, mul_one]; ring

/-- Double hashing covers every slot when the step is a unit. -/
theorem doubleHashProbe_surjective {m : ℕ} (h1 h2 : ZMod m) (hu : IsUnit h2) :
    Function.Surjective (doubleHashProbe h1 h2) :=
  (doubleHashProbe_bijective h1 h2 hu).surjective

/-- Quadratic probing starts at the base slot `h'(k)` (probe number `0`). -/
theorem quadraticProbe_zero {m : ℕ} (h0 c1 c2 : ZMod m) :
    quadraticProbe h0 c1 c2 0 = h0 := by
  unfold quadraticProbe; ring

/-! ## Expected number of probes under uniform hashing (CLRS Theorems 11.6-11.8)

Under the uniform-hashing assumption the probe sequence of each key is equally
likely to be any of the `m!` permutations of the slots.  For an unsuccessful
search with `n` occupied slots, the probability that the first `i` probes all hit
occupied slots is the without-replacement product `∏_{j<i} (n-j)/(m-j)`.  The
expected number of probes is the tail-sum `E[X] = ∑_{i≥0} P[X > i]`, which we
bound by the geometric series `∑_i α^i = 1/(1-α)` via CLRS's per-factor bound
`(n-j)/(m-j) ≤ n/m`. -/

/-- The **load factor** `α = n/m` of an open-addressing table. -/
noncomputable def openLoadFactor (m n : ℕ) : ℝ := (n : ℝ) / (m : ℝ)

/-- Under uniform hashing, `probeTail m n i` is the probability that the first `i`
probes of an unsuccessful search all hit occupied slots: the without-replacement
product `∏_{j<i} (n-j)/(m-j)` (CLRS §11.4, the factors leading to Theorem 11.6). -/
noncomputable def probeTail (m n i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, ((n : ℝ) - (j : ℝ)) / ((m : ℝ) - (j : ℝ))

/-- No probe is needed with certainty: `probeTail _ _ 0 = 1`. -/
theorem probeTail_zero (m n : ℕ) : probeTail m n 0 = 1 := by
  simp [probeTail]

/-- The one-step recurrence of the tail probability. -/
theorem probeTail_succ (m n i : ℕ) :
    probeTail m n (i + 1)
      = probeTail m n i * (((n : ℝ) - (i : ℝ)) / ((m : ℝ) - (i : ℝ))) := by
  simp only [probeTail, Finset.prod_range_succ]

/-- The tail probabilities are nonnegative (for `i ≤ m`, where all denominators
are positive). -/
theorem probeTail_nonneg (m n : ℕ) (hnm : n ≤ m) (i : ℕ) (hi : i ≤ m) :
    0 ≤ probeTail m n i := by
  by_cases hin : i ≤ n
  · apply Finset.prod_nonneg
    intro j hj
    have hji : j < i := Finset.mem_range.mp hj
    have hjn : (j : ℝ) ≤ (n : ℝ) := by
      have : j ≤ n := le_trans (Nat.le_of_lt hji) hin
      exact_mod_cast this
    have hjm : (j : ℝ) < (m : ℝ) := by
      have : j < m := lt_of_lt_of_le hji (le_trans hin hnm)
      exact_mod_cast this
    apply div_nonneg <;> linarith
  · have hni : n < i := not_le.mp hin
    have hmem : n ∈ Finset.range i := Finset.mem_range.mpr hni
    have hz : probeTail m n i = 0 := by
      rw [probeTail]; exact Finset.prod_eq_zero hmem (by simp)
    simp [hz]

/-- **CLRS per-factor bound.**  Each tail probability is at most `α^i`
(`α = n/m`), because `(n-j)/(m-j) ≤ n/m`.  This is the heart of Theorem 11.6. -/
theorem probeTail_le_pow (m n : ℕ) (hnm : n ≤ m) (i : ℕ) (hi : i ≤ m) :
    probeTail m n i ≤ (openLoadFactor m n) ^ i := by
  induction i with
  | zero => rw [probeTail_zero, pow_zero]
  | succ i ih =>
      have hile : i ≤ m := le_of_lt (Nat.lt_of_succ_le hi)
      have him : i < m := Nat.lt_of_succ_le hi
      have hprev : probeTail m n i ≤ (openLoadFactor m n) ^ i := ih hile
      have hptnn : 0 ≤ probeTail m n i := probeTail_nonneg m n hnm i hile
      have hmpos : (0 : ℝ) < (m : ℝ) := by
        have : 0 < m := lt_of_le_of_lt (Nat.zero_le i) him
        exact_mod_cast this
      have hden : (0 : ℝ) < (m : ℝ) - (i : ℝ) := by
        have : (i : ℝ) < (m : ℝ) := by exact_mod_cast him
        linarith
      have hαnn : 0 ≤ openLoadFactor m n := by
        rw [openLoadFactor]; exact div_nonneg (by positivity) (by positivity)
      rw [probeTail_succ, pow_succ]
      by_cases hin : i < n
      · have hile_n : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt hin
        have hfnn : 0 ≤ ((n : ℝ) - (i : ℝ)) / ((m : ℝ) - (i : ℝ)) :=
          div_nonneg (by linarith) (le_of_lt hden)
        have hfle : ((n : ℝ) - (i : ℝ)) / ((m : ℝ) - (i : ℝ)) ≤ openLoadFactor m n := by
          rw [openLoadFactor, div_le_div_iff₀ hden hmpos]
          have hnr : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
          have hir : (0 : ℝ) ≤ (i : ℝ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hnr hir]
        exact mul_le_mul hprev hfle hfnn (pow_nonneg hαnn i)
      · have hni : n ≤ i := not_lt.mp hin
        have hnum : (n : ℝ) - (i : ℝ) ≤ 0 := by
          have : (n : ℝ) ≤ (i : ℝ) := by exact_mod_cast hni
          linarith
        have hinv : 0 ≤ ((m : ℝ) - (i : ℝ))⁻¹ := inv_nonneg.mpr (le_of_lt hden)
        have hfnp : ((n : ℝ) - (i : ℝ)) / ((m : ℝ) - (i : ℝ)) ≤ 0 := by
          rw [div_eq_mul_inv]; nlinarith [hnum, hinv]
        have hprod : probeTail m n i * (((n : ℝ) - (i : ℝ)) / ((m : ℝ) - (i : ℝ))) ≤ 0 := by
          nlinarith [hptnn, hfnp]
        have hpow : 0 ≤ (openLoadFactor m n) ^ i * openLoadFactor m n :=
          mul_nonneg (pow_nonneg hαnn i) hαnn
        linarith

/-- A partial geometric sum is bounded by the full geometric series
`∑_i α^i ≤ 1/(1-α)` for `0 ≤ α < 1`. -/
theorem geom_sum_le_inv (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, α ^ i ≤ 1 / (1 - α) := by
  have hpos : (0 : ℝ) < 1 - α := by linarith
  have hid : (∑ i ∈ Finset.range N, α ^ i) * (1 - α) = 1 - α ^ N := by
    have h := geom_sum_mul α N
    linear_combination (-1 : ℝ) * h
  rw [le_div_iff₀ hpos, hid]
  have hpN : (0 : ℝ) ≤ α ^ N := pow_nonneg h0 N
  linarith

/-- The **expected number of probes** for an unsuccessful search under uniform
hashing, as the tail-sum `E[X] = ∑_{i} P[X > i]` of the probe count `X`. -/
noncomputable def expectedUnsuccessfulProbes (m n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), probeTail m n i

/-- **Theorem 11.6 (unsuccessful search).**  Under uniform hashing the expected
number of probes in an unsuccessful search is at most `1/(1-α)` (`α = n/m < 1`),
proved as the tail-sum bounded by the geometric series. -/
theorem expectedUnsuccessfulProbes_le (m n : ℕ) (hn : n < m) :
    expectedUnsuccessfulProbes m n ≤ 1 / (1 - openLoadFactor m n) := by
  have hnm : n ≤ m := le_of_lt hn
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hn
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hα0 : 0 ≤ openLoadFactor m n :=
    div_nonneg (by positivity) (by positivity)
  have hα1 : openLoadFactor m n < 1 := by
    rw [openLoadFactor, div_lt_one hmr]; exact_mod_cast hn
  calc expectedUnsuccessfulProbes m n
      = ∑ i ∈ Finset.range (m + 1), probeTail m n i := rfl
    _ ≤ ∑ i ∈ Finset.range (m + 1), (openLoadFactor m n) ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        exact probeTail_le_pow m n hnm i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ ≤ 1 / (1 - openLoadFactor m n) := geom_sum_le_inv _ hα0 hα1 (m + 1)

/-- **Corollary 11.7 (insertion).**  Inserting a key probes exactly as an
unsuccessful search does, so its expected number of probes is at most `1/(1-α)`. -/
theorem expectedInsertionProbes_le (m n : ℕ) (hn : n < m) :
    expectedUnsuccessfulProbes m n ≤ 1 / (1 - openLoadFactor m n) :=
  expectedUnsuccessfulProbes_le m n hn

/-- The **expected number of probes** for a successful search under uniform
hashing: averaging, over the `n` insertion times `j = 0, …, n-1`, the expected
unsuccessful-search cost in a table already holding `j` keys (CLRS proof of
Theorem 11.8: the `(j+1)`-st key's probe cost equals an unsuccessful search among
`j` keys). -/
noncomputable def expectedSuccessfulProbes (m n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, expectedUnsuccessfulProbes m j

/-- **Theorem 11.8 (successful search), harmonic form.**  Under uniform hashing
the expected number of probes in a successful search is at most
`(1/α) * ∑_{j<n} 1/(m-j) = (1/α)(H_m - H_{m-n})` (`α = n/m`).  The stated
harmonic-sum bound is proved; the classical `(1/α) ln(1/(1-α))` follows from
`H_m - H_{m-n} ≤ ln(m/(m-n))` and is not formalised here. -/
theorem expectedSuccessfulProbes_le (m n : ℕ) (hn : n ≤ m) (hnpos : 0 < n) :
    expectedSuccessfulProbes m n
      ≤ (1 / openLoadFactor m n) * ∑ j ∈ Finset.range n, 1 / ((m : ℝ) - (j : ℝ)) := by
  have hmpos : 0 < m := lt_of_lt_of_le hnpos hn
  have hmpos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have step1 : expectedSuccessfulProbes m n
      ≤ (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, 1 / (1 - openLoadFactor m j) := by
    unfold expectedSuccessfulProbes
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro j hj
    exact expectedUnsuccessfulProbes_le m j (lt_of_lt_of_le (Finset.mem_range.mp hj) hn)
  have hrw : ∀ j ∈ Finset.range n,
      1 / (1 - openLoadFactor m j) = (m : ℝ) * (1 / ((m : ℝ) - (j : ℝ))) := by
    intro j hj
    have hjm : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    have hjmr : (j : ℝ) < (m : ℝ) := by exact_mod_cast hjm
    have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos'
    have hsub : (1 : ℝ) - (j : ℝ) / (m : ℝ) = ((m : ℝ) - (j : ℝ)) / (m : ℝ) := by
      rw [sub_div, div_self hm0]
    rw [openLoadFactor, hsub, one_div_div, mul_one_div]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum] at step1
  have hfin : (1 / (n : ℝ)) * ((m : ℝ) * ∑ j ∈ Finset.range n, 1 / ((m : ℝ) - (j : ℝ)))
      = (1 / openLoadFactor m n) * ∑ j ∈ Finset.range n, 1 / ((m : ℝ) - (j : ℝ)) := by
    rw [openLoadFactor, one_div_div]; ring
  rw [hfin] at step1
  exact step1

end Chapter11
end CLRS
