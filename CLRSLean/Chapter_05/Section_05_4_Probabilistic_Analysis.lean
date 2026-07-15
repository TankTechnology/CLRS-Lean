import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Probability.FiniteExpectation
import Mathlib

/-!
# 5.4. Probabilistic analysis

This section applies the CLRS §5.2 indicator-random-variable technique (see
{lit}`CLRSLean/Chapter_05/Section_05_2_Indicator_Random_Variables.lean`) to two
classic probabilistic analyses from CLRS §5.4, both over a **product uniform**
sample space evaluated with the shared toolkit
{lit}`CLRS.Probability.fintypeExpect`.

- **Birthday paradox** (CLRS eq. (5.6)-(5.8)): with {lit}`k` people and
  {lit}`n` equally likely birthdays, the expected number of unordered pairs
  sharing a birthday is {lit}`C(k,2)/n = k(k-1)/(2n)`.
- **Balls and bins** (CLRS eq. (5.9)-(5.10)): throwing {lit}`k` balls
  independently and uniformly into {lit}`n` bins, the expected number of balls
  landing in a fixed bin is {lit}`k/n`.

Both are pure indicator-plus-linearity arguments.  The sample space is
{lit}`Fin k → Fin n` (each person's birthday / each ball's bin an independent
uniform coordinate).  The section re-derives the two coordinate-marginal
primitives it needs — a single coordinate is uniform ({lit}`singleBinProb`) and a
pair of distinct coordinates collides with probability {lit}`1/n`
({lit}`pairSameProb`) — directly from the toolkit's {lit}`fintypeExpect_equiv`,
{lit}`fintypeExpect_fst` (product independence) and
{lit}`fintypeExpect_indicator_singleton`, keeping the file self-contained and
citing only the shared toolkit.  This mirrors, without modifying, the
balls-and-bins analyses of §8.4 (bucket sort) and §11.2 (chained hashing).

Main results:

- Theorem {lit}`CLRS.Chapter05.singleBinProb`: a fixed ball lands in a fixed bin
  with probability {lit}`1/n`.
- Theorem {lit}`CLRS.Chapter05.pairSameProb`: two distinct people share a
  birthday with probability {lit}`1/n`.
- Theorem {lit}`CLRS.Chapter05.expectedBallsInBin_eq`: the expected number of
  balls in a fixed bin is {lit}`k/n`.
- Theorem {lit}`CLRS.Chapter05.expectedCollisions_eq`: the expected number of
  same-birthday pairs is {lit}`k(k-1)/(2n)`.

Status: `proved` for the product-uniform model over {lit}`Fin k → Fin n`.

Notation conventions used in this section:

- {lit}`k` : number of people / balls; {lit}`n` : number of birthdays / bins
- {lit}`a : Fin k → Fin n` : an assignment (each person's birthday / each ball's
  bin)
- {lit}`i`, {lit}`j` : people / balls in {lit}`Fin k`; {lit}`q` : a fixed bin in
  {lit}`Fin n`
- {lit}`indicator P` : the {lit}`0/1` indicator random variable of the event
  {lit}`P`
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/-! ## Coordinate marginals of the product-uniform space

The sample space is `Fin k → Fin n`: each of `k` coordinates is an independent
uniform draw from `Fin n`.  We first isolate the two marginal facts the two
expectations need. -/

/-- Split an assignment `a : Fin k → Fin n` into the value of one coordinate `i`
and the assignment of the remaining coordinates.  This is the product
decomposition witnessing that coordinate `i` is independent of the rest. -/
noncomputable def binSplit {k n : Nat} (i : Fin k) :
    (Fin k → Fin n) ≃ Fin n × ({x : Fin k // x ≠ i} → Fin n) where
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

/-- Marginalisation: the expectation of a function of a single coordinate equals
the expectation over the single-coordinate space `Fin n`. -/
theorem fintypeExpect_binCoord {k n : Nat} (i : Fin k) (hn : 0 < n) (f : Fin n → ℝ) :
    fintypeExpect (fun a : Fin k → Fin n => f (a i)) = fintypeExpect f := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : Fintype.card ({x : Fin k // x ≠ i} → Fin n) ≠ 0 := Fintype.card_ne_zero
  have he := fintypeExpect_equiv (binSplit (n := n) i)
    (fun q : Fin n × ({x : Fin k // x ≠ i} → Fin n) => f q.1)
  simp only [binSplit, Equiv.coe_fn_mk] at he
  rw [he]
  exact fintypeExpect_fst hcard f

/-- **Single-coordinate probability = `1/n`.**  A fixed ball `i` lands in a fixed
bin `q` — equivalently, a fixed person `i` has a fixed birthday `q` — with
probability exactly `1/n`. -/
theorem singleBinProb {k n : Nat} (i : Fin k) (q : Fin n) (hn : 0 < n) :
    fintypeExpect (fun a : Fin k → Fin n => indicator (a i = q)) = 1 / (n : ℝ) := by
  rw [fintypeExpect_binCoord i hn (fun c => indicator (c = q)),
    fintypeExpect_indicator_singleton, Fintype.card_fin]

/-- Split an assignment `a : Fin k → Fin n` into the values of two distinct
coordinates `i ≠ j` together with the assignment of the remaining coordinates.
This witnesses that the pair `(i, j)` is independent of the rest. -/
noncomputable def binSplitPair {k n : Nat} (i j : Fin k) (hij : i ≠ j) :
    (Fin k → Fin n) ≃
      (Fin n × Fin n) × ({x : Fin k // x ≠ i ∧ x ≠ j} → Fin n) where
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

/-- The uniform probability that the two coordinates of a pair over `Fin n` agree
is `1/n`: the diagonal of `Fin n × Fin n` has `n` of the `n²` points. -/
theorem fintypeExpect_prod_diag {n : Nat} (hn : 0 < n) :
    fintypeExpect (fun q : Fin n × Fin n => indicator (q.1 = q.2)) = 1 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnum : (∑ q : Fin n × Fin n, indicator (q.1 = q.2)) = (n : ℝ) := by
    unfold indicator
    rw [Fintype.sum_prod_type]
    have hinner : ∀ a : Fin n, (∑ b : Fin n, (if a = b then (1 : ℝ) else 0)) = 1 := by
      intro a; simp
    rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold fintypeExpect
  rw [hnum, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [div_mul_eq_div_div, div_self hn']

/-- **Pairwise collision probability = `1/n` (CLRS eq. (5.7)).**  Two distinct
people `i ≠ j` share a birthday — equivalently, two distinct balls land in the
same bin — with probability exactly `1/n`, as a genuine expectation over the
product-uniform input distribution `Fin k → Fin n`, using pairwise
independence. -/
theorem pairSameProb {k n : Nat} (i j : Fin k) (hij : i ≠ j) (hn : 0 < n) :
    fintypeExpect (fun a : Fin k → Fin n => indicator (a i = a j)) = 1 / (n : ℝ) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard :
      Fintype.card ({x : Fin k // x ≠ i ∧ x ≠ j} → Fin n) ≠ 0 := Fintype.card_ne_zero
  have he := fintypeExpect_equiv (binSplitPair (n := n) i j hij)
    (fun p : (Fin n × Fin n) × ({x : Fin k // x ≠ i ∧ x ≠ j} → Fin n) =>
      indicator (p.1.1 = p.1.2))
  simp only [binSplitPair, Equiv.coe_fn_mk] at he
  have h2 : fintypeExpect
        (fun p : (Fin n × Fin n) × ({x : Fin k // x ≠ i ∧ x ≠ j} → Fin n) =>
          indicator (p.1.1 = p.1.2)) = 1 / (n : ℝ) := by
    rw [← fintypeExpect_prod_diag hn]
    exact fintypeExpect_fst hcard (fun q : Fin n × Fin n => indicator (q.1 = q.2))
  exact he.trans h2

/-- The number of ordered pairs `i < j` in `Fin k`, counted in `ℝ`, is
`k(k-1)/2`.  This is the Gauss triangle count obtained from trichotomy and the
symmetry of the strict order. -/
theorem sum_upper_triangle (k : Nat) :
    (∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0))
      = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  have hpt : ∀ i j : Fin k,
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
  have hUL : (∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0))
      = ∑ i : Fin k, ∑ j : Fin k, (if j < i then (1 : ℝ) else 0) := Finset.sum_comm
  have hD : (∑ i : Fin k, ∑ j : Fin k, (if i = j then (1 : ℝ) else 0)) = (k : ℝ) := by
    have hone : ∀ i : Fin k, (∑ j : Fin k, (if i = j then (1 : ℝ) else 0)) = 1 := by
      intro i; simp
    rw [Finset.sum_congr rfl (fun i _ => hone i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hAll : (∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0))
      + (∑ i : Fin k, ∑ j : Fin k, (if j < i then (1 : ℝ) else 0))
      + (∑ i : Fin k, ∑ j : Fin k, (if i = j then (1 : ℝ) else 0))
      = (k : ℝ) * (k : ℝ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hstep : (∑ i : Fin k, ((∑ j : Fin k, (if i < j then (1 : ℝ) else 0))
        + (∑ j : Fin k, (if j < i then (1 : ℝ) else 0))
        + ∑ j : Fin k, (if i = j then (1 : ℝ) else 0)))
        = ∑ _i : Fin k, (k : ℝ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun j _ => hpt i j), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hstep, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hUL, hD] at hAll
  have h2 : (∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 : ℝ) else 0))
      = ((k : ℝ) * (k : ℝ) - (k : ℝ)) / 2 := by linarith
  rw [h2]; ring

/-! ## Birthday paradox -/

/-- The number of same-birthday pairs under a birthday assignment `a`: one for
each unordered pair `{i, j}` with `i < j` and `a i = a j`. -/
noncomputable def sameBirthdayPairs {k n : Nat} (a : Fin k → Fin n) : ℝ :=
  ∑ i : Fin k, ∑ j : Fin k, (if i < j then indicator (a i = a j) else 0)

/-- Expected number of same-birthday pairs among `k` people with `n` uniform
birthdays. -/
noncomputable def expectedCollisions (k n : Nat) : ℝ :=
  fintypeExpect (fun a : Fin k → Fin n => sameBirthdayPairs a)

/-- **Birthday paradox (CLRS §5.4, eq. (5.8)).**  The expected number of
unordered same-birthday pairs among `k` people with `n` equally likely birthdays
is exactly `C(k,2)/n = k(k-1)/(2n)`, by linearity of expectation over the
`C(k,2)` pair indicators, each with collision probability `1/n`. -/
theorem expectedCollisions_eq {k n : Nat} (hn : 0 < n) :
    expectedCollisions k n = (k : ℝ) * ((k : ℝ) - 1) / (2 * (n : ℝ)) := by
  unfold expectedCollisions sameBirthdayPairs
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : Fintype.card (Fin k → Fin n) ≠ 0 := Fintype.card_ne_zero
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hE : fintypeExpect (fun a : Fin k → Fin n =>
      ∑ i : Fin k, ∑ j : Fin k, (if i < j then indicator (a i = a j) else 0))
      = ∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 / (n : ℝ)) else 0) := by
    rw [fintypeExpect_sum Finset.univ (fun (i : Fin k) (a : Fin k → Fin n) =>
      ∑ j : Fin k, (if i < j then indicator (a i = a j) else 0))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fintypeExpect_sum Finset.univ (fun (j : Fin k) (a : Fin k → Fin n) =>
      if i < j then indicator (a i = a j) else 0)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hlt : i < j
    · simp only [if_pos hlt]
      exact pairSameProb i j (ne_of_lt hlt) hn
    · simp only [if_neg hlt]
      exact fintypeExpect_const hcard 0
  rw [hE]
  have hpair : (∑ i : Fin k, ∑ j : Fin k, (if i < j then (1 / (n : ℝ)) else 0))
      = (1 / (n : ℝ)) * ((k : ℝ) * ((k : ℝ) - 1) / 2) := by
    rw [← sum_upper_triangle k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i < j <;> simp [h]
  rw [hpair]
  field_simp

/-! ## Balls and bins -/

/-- The number of balls that land in bin `q` under an assignment `a`. -/
noncomputable def ballsInBin {k n : Nat} (a : Fin k → Fin n) (q : Fin n) : ℝ :=
  ∑ i : Fin k, indicator (a i = q)

/-- Expected number of balls landing in a fixed bin `q` when `k` balls are thrown
independently and uniformly into `n` bins. -/
noncomputable def expectedBallsInBin (k n : Nat) (q : Fin n) : ℝ :=
  fintypeExpect (fun a : Fin k → Fin n => ballsInBin a q)

/-- **Balls and bins (CLRS §5.4, eq. (5.10)).**  The expected number of balls
landing in a fixed bin `q`, when `k` balls are thrown independently and uniformly
into `n` bins, is exactly `k/n`, by linearity of expectation over the `k`
per-ball indicators, each with probability `1/n`. -/
theorem expectedBallsInBin_eq {k n : Nat} (q : Fin n) (hn : 0 < n) :
    expectedBallsInBin k n q = (k : ℝ) / (n : ℝ) := by
  unfold expectedBallsInBin ballsInBin
  rw [fintypeExpect_sum Finset.univ
    (fun (i : Fin k) (a : Fin k → Fin n) => indicator (a i = q))]
  simp only [singleBinProb _ q hn]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

/-! ## Streaks (longest run of heads) -/

/-- Sample space of `n` independent fair coin flips (0 = tails, 1 = heads). -/
def CoinFlip (n : ℕ) : Type := Fin n → Fin 2

instance (n : ℕ) : Fintype (CoinFlip n) := inferInstanceAs (Fintype (Fin n → Fin 2))
instance (n : ℕ) : DecidableEq (CoinFlip n) := inferInstanceAs (DecidableEq (Fin n → Fin 2))

/-- Read position `k` of coin-flip sequence `a`, returning 0 if out of bounds. -/
def headAt (n : ℕ) (a : CoinFlip n) (k : ℕ) : Fin 2 :=
  if h : k < n then a ⟨k, h⟩ else (0 : Fin 2)

/-- `hasRunOfLength n t a` iff sequence `a` contains at least `t` consecutive heads. -/
def hasRunOfLength (n t : ℕ) (a : CoinFlip n) : Prop :=
  t ≤ n ∧ ∃ (i : ℕ), i ∈ Finset.range (n+1) ∧ i + t ≤ n ∧ (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2))

instance (n t : ℕ) (a : CoinFlip n) : Decidable (hasRunOfLength n t a) := by
  unfold hasRunOfLength; infer_instance

/-- Length of the longest run of heads in `a`. -/
noncomputable def longestStreak (n : ℕ) (a : CoinFlip n) : ℕ :=
  (Nat.find (⟨n+1, by
    intro h; rcases h with ⟨hle, hi⟩; omega
  ⟩ : ∃ t, ¬ hasRunOfLength n t a)).pred

open CLRS.Probability

/-- The probability that all `t` coin flips in a sequence of exactly `t` flips are
heads is `1 / 2^t`. -/
lemma prob_first_t_heads (t : ℕ) :
    fintypeExpect (fun (a : CoinFlip t) => indicator (∀ j : Fin t, a j = (1 : Fin 2))) = 1 / ((2 : ℝ) ^ t) := by
  let constOne : CoinFlip t := fun _ => (1 : Fin 2)
  have h_indicator : (fun (a : CoinFlip t) => indicator (∀ j : Fin t, a j = (1 : Fin 2))) =
      (fun a => indicator (a = constOne)) := by
    ext a
    have h_eq : (∀ j : Fin t, a j = (1 : Fin 2)) ↔ (a = constOne) := by
      constructor
      · intro h; apply funext; exact h
      · intro h j; simp [h, constOne]
    simp [h_eq]
  rw [h_indicator]
  have h_card : (Fintype.card (CoinFlip t) : ℝ) = (2 : ℝ) ^ t := by
    have h_nat : Fintype.card (CoinFlip t) = 2 ^ t := by
      calc
        Fintype.card (CoinFlip t) = Fintype.card (Fin t → Fin 2) := rfl
        _ = (Fintype.card (Fin 2)) ^ (Fintype.card (Fin t)) := by rw [Fintype.card_fun]
        _ = 2 ^ t := by simp
    rw [h_nat]
    simp
  calc
    fintypeExpect (fun (a : CoinFlip t) => indicator (a = constOne))
        = 1 / (Fintype.card (CoinFlip t) : ℝ) := fintypeExpect_indicator_singleton constOne
    _ = 1 / ((2 : ℝ) ^ t) := by rw [h_card]

/-- For `k < n`, `headAt` is the same as direct indexing. -/
lemma headAt_eq_of_lt (n : ℕ) (a : CoinFlip n) (k : ℕ) (hk : k < n) : headAt n a k = a ⟨k, hk⟩ := by
  simp [headAt, hk]

/-- If `k ≥ n`, `headAt` returns 0. -/
lemma headAt_eq_zero_of_ge (n : ℕ) (a : CoinFlip n) (k : ℕ) (hk : n ≤ k) : headAt n a k = (0 : Fin 2) := by
  simp [headAt, hk]

/-- The Finset of positions `{i, i+1, ..., i+t-1}` in `Fin n`, given `i + t ≤ n`. -/
def streakS (n t i : ℕ) (h : i + t ≤ n) : Finset (Fin n) :=
  Finset.image (λ (j : Fin t) => ⟨i + j.val, by
    have := j.isLt; omega⟩) (Finset.univ : Finset (Fin t))

lemma card_streakS (n t i : ℕ) (h : i + t ≤ n) : (streakS n t i h).card = t := by
  unfold streakS
  have hinj : Function.Injective (λ (j : Fin t) => ⟨i + j.val, by
    have := j.isLt; omega⟩ : Fin t → Fin n) := by
    intro x y h
    apply Fin.ext
    have hval : (i + x.val : ℕ) = i + y.val := congr_arg (λ (z : Fin n) => z.val) h
    omega
  simp [Finset.card_image_of_injective, hinj, Fintype.card_fin]

/-- A run of `t` consecutive heads starting at position `i` expressed via the
`streakS` Finset is equivalent to the same run expressed via `headAt`. -/
lemma streakS_all_heads_iff (n t i : ℕ) (h : i + t ≤ n) (a : CoinFlip n) :
    (∀ x ∈ streakS n t i h, a x = (1 : Fin 2)) ↔ (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)) := by
  constructor
  · intro hS j hj
    have hj_lt_t : (j : ℕ) < t := Finset.mem_range.1 hj
    have hpos : i + j < n := by omega
    let j_fin : Fin t := ⟨j, hj_lt_t⟩
    have hmem : (⟨i + j, hpos⟩ : Fin n) ∈ streakS n t i h := by
      apply Finset.mem_image.mpr
      exact ⟨j_fin, Finset.mem_univ _, rfl⟩
    rw [headAt_eq_of_lt n a (i + j) hpos]
    exact hS ⟨i + j, hpos⟩ hmem
  · intro hheads x hx
    rcases Finset.mem_image.mp hx with ⟨j_fin, _, hx_eq⟩
    have hj_val_lt_t : j_fin.val < t := j_fin.isLt
    have hj_val_mem_range : j_fin.val ∈ Finset.range t := Finset.mem_range.mpr hj_val_lt_t
    have hpos : i + j_fin.val < n := by omega
    subst hx_eq
    rw [← headAt_eq_of_lt n a (i + j_fin.val) hpos]
    exact hheads (j_fin.val) hj_val_mem_range

/-- Bijection between sequences where every position in a Finset `S` is heads and
functions on the complement of `S`.  Used to count sequences with a fixed pattern
of heads. -/
noncomputable def headsSetBijection {n : ℕ} (S : Finset (Fin n)) :
    {a : CoinFlip n // ∀ x ∈ S, a x = (1 : Fin 2)} ≃ (↥(Finset.univ \ S) → Fin 2) where
  toFun a := λ x : ↥(Finset.univ \ S) => a.1 x.val
  invFun f :=
    { val := λ x : Fin n =>
        if h : x ∈ S then (1 : Fin 2) else f ⟨x, by
          have hmem : x ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ x
          exact Finset.mem_sdiff.mpr ⟨hmem, h⟩
        ⟩
      property := by
        intro x hx; simp [hx] }
  left_inv a := by
    apply Subtype.ext
    funext x
    dsimp
    split_ifs with hx
    · exact (a.property x hx).symm
    · rfl
  right_inv f := by
    ext x
    dsimp
    have hx : x.val ∉ S := by
      have hx_mem : x.val ∈ Finset.univ \ S := x.property
      exact (Finset.mem_sdiff.mp hx_mem).2
    simp [hx]

/-- The probability that the `t` consecutive positions `{i, ..., i + t - 1}` are
all heads in a sequence of `n` fair coin flips (given `i + t ≤ n`) is exactly
`1 / 2^t`. -/
lemma prob_run_at (n t i : ℕ) (h : i + t ≤ n) :
    fintypeExpect (fun (a : CoinFlip n) => indicator (∀ x ∈ streakS n t i h, a x = (1 : Fin 2)))
    = 1 / ((2 : ℝ) ^ t) := by
  let S := streakS n t i h
  have hScard : S.card = t := card_streakS n t i h
  have h_total_card : (Fintype.card (CoinFlip n) : ℝ) = (2 : ℝ) ^ n := by
    have h_nat : Fintype.card (CoinFlip n) = 2 ^ n := by
      calc
        Fintype.card (CoinFlip n) = Fintype.card (Fin n → Fin 2) := rfl
        _ = (Fintype.card (Fin 2)) ^ (Fintype.card (Fin n)) := by rw [Fintype.card_fun]
        _ = 2 ^ n := by simp
    rw [h_nat]; simp
  have h_heads_card : (Fintype.card {a : CoinFlip n // ∀ x ∈ S, a x = (1 : Fin 2)} : ℝ) = (2 : ℝ) ^ (n - t) := by
    have h_card_nat : Fintype.card {a : CoinFlip n // ∀ x ∈ S, a x = (1 : Fin 2)} = 2 ^ (n - t) := by
      calc
        Fintype.card {a : CoinFlip n // ∀ x ∈ S, a x = (1 : Fin 2)}
            = Fintype.card (↥(Finset.univ \ S) → Fin 2) :=
              Fintype.card_congr (headsSetBijection S)
        _ = (Fintype.card (Fin 2)) ^ Fintype.card (↥(Finset.univ \ S)) := by rw [Fintype.card_fun]
        _ = 2 ^ (Finset.card (Finset.univ \ S)) := by
          rw [Fintype.card_coe, Fintype.card_fin]
        _ = 2 ^ (n - t) := by
          have htle : t ≤ n := by omega
          have huniv : (Finset.univ : Finset (Fin n)).card = n := by simp
          have hsub : S ⊆ Finset.univ := Finset.subset_univ _
          have hsum : (Finset.univ \ S).card + S.card = (Finset.univ : Finset (Fin n)).card :=
            Finset.card_sdiff_add_card_eq_card hsub
          rw [hScard, huniv] at hsum
          have : (Finset.univ \ S).card = n - t :=
            (Nat.add_right_cancel
              (calc
                (Finset.univ \ S).card + t = n := hsum
                _ = (n - t) + t := by rw [Nat.sub_add_cancel htle]))
          rw [this]
    simpa using congrArg (fun (x : ℕ) => (x : ℝ)) h_card_nat
  calc
    fintypeExpect (fun (a : CoinFlip n) => indicator (∀ x ∈ S, a x = (1 : Fin 2)))
        = (∑ a : CoinFlip n, indicator (∀ x ∈ S, a x = (1 : Fin 2))) / (Fintype.card (CoinFlip n) : ℝ) := rfl
    _ = ((Fintype.card {a : CoinFlip n // ∀ x ∈ S, a x = (1 : Fin 2)} : ℝ)) / (Fintype.card (CoinFlip n) : ℝ) := by
      simp [indicator, Fintype.card_subtype]
    _ = ((2 : ℝ) ^ (n - t)) / ((2 : ℝ) ^ n) := by rw [h_heads_card, h_total_card]
    _ = 1 / ((2 : ℝ) ^ t) := by
      have hpos' : (2 : ℝ) ^ t ≠ 0 := by positivity
      field_simp [hpos']
      have h_eq : (n - t) + t = n := Nat.sub_add_cancel (by omega)
      calc
        ((2 : ℝ) ^ (n - t)) * ((2 : ℝ) ^ t) = (2 : ℝ) ^ ((n - t) + t) := by rw [pow_add]
        _ = (2 : ℝ) ^ n := by rw [h_eq]



lemma hasRunOfLength_mono (n m t : ℕ) (a : CoinFlip n) (hmn : m ≤ t) (h : hasRunOfLength n t a) : hasRunOfLength n m a := by
  rcases h with ⟨hn_t, i, hi, hiadd, hrun⟩
  refine ⟨by omega, i, hi, by omega, ?_⟩
  intro j hj
  have : j ∈ Finset.range t := Finset.mem_range.mpr (by
    have hjt : j < m := Finset.mem_range.1 hj
    omega)
  exact hrun j this

lemma longestStreak_ge_iff_hasRunOfLength (n t : ℕ) (a : CoinFlip n) :
    longestStreak n a ≥ t ↔ hasRunOfLength n t a := by
  constructor
  · intro hge
    have h_m_exists : ∃ t', ¬ hasRunOfLength n t' a := ⟨n+1, by
      intro h; rcases h with ⟨hle, hi⟩; omega⟩
    set m := Nat.find h_m_exists with hm
    have hm_spec : ¬ hasRunOfLength n m a := Nat.find_spec h_m_exists
    have hm_min : ∀ k < m, hasRunOfLength n k a := λ k hk => by
      by_contra hnk
      exact (Nat.find_min h_m_exists hk) hnk
    have hm_pos : 0 < m := by
      by_contra! hzero
      have hmzero : m = 0 := by omega
      have : hasRunOfLength n 0 a := by
        refine ⟨by omega, ?_⟩
        refine ⟨0, by simp, by omega, ?_⟩
        simp
      rw [hmzero] at hm_spec
      exact hm_spec this
    have hpred : longestStreak n a = m.pred := rfl
    have hge' : m.pred ≥ t := by
      rw [← hpred]; exact hge
    have hm_gt_t : m > t := by
      by_contra! hle
      have h_eq : m = m.pred + 1 := (Nat.succ_pred_eq_of_pos hm_pos).symm
      have h_ge : m ≥ t + 1 := by
        linarith
      linarith
    exact hm_min t (by omega)
  · intro hrun
    have h_m_exists : ∃ t', ¬ hasRunOfLength n t' a := ⟨n+1, by
      intro h; rcases h with ⟨hle, hi⟩; omega⟩
    set m := Nat.find h_m_exists with hm
    have hm_spec : ¬ hasRunOfLength n m a := Nat.find_spec h_m_exists
    have hm_min : ∀ k < m, hasRunOfLength n k a := λ k hk => by
      by_contra hnk
      exact (Nat.find_min h_m_exists hk) hnk
    have hm_pos : 0 < m := by
      by_contra! hzero
      have hmzero : m = 0 := by omega
      have : hasRunOfLength n 0 a := by
        refine ⟨by omega, ?_⟩
        refine ⟨0, by simp, by omega, ?_⟩
        simp
      rw [hmzero] at hm_spec
      exact hm_spec this
    have hm_gt_t : m > t := by
      by_contra! hle
      have : hasRunOfLength n m a := hasRunOfLength_mono n m t a hle hrun
      exact hm_spec this
    have hpred : longestStreak n a = m.pred := rfl
    rw [hpred]
    have : m.pred ≥ t := by
      have h_ge : t + 1 ≤ m := Nat.succ_le_of_lt hm_gt_t
      have h_succ : m.pred + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
      have h_sum : t + 1 ≤ m.pred + 1 := by
        calc
          t + 1 ≤ m := h_ge
          _ = m.pred + 1 := h_succ.symm
      exact Nat.le_of_add_le_add_right h_sum
    exact this

lemma fintypeExpect_mono {Ω : Type} [Fintype Ω] [DecidableEq Ω] {X Y : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω) (hXY : ∀ ω, X ω ≤ Y ω) :
    fintypeExpect X ≤ fintypeExpect Y := by
  have h_nonneg_diff : ∀ ω, 0 ≤ Y ω - X ω := by
    intro ω; have h := hXY ω; linarith
  have h_nonneg_expect_diff : 0 ≤ fintypeExpect (Y - X) :=
    fintypeExpect_nonneg h_nonneg_diff
  have h_add : fintypeExpect (X + (Y - X)) =
      fintypeExpect X + fintypeExpect (Y - X) :=
    fintypeExpect_add X (Y - X)
  have h_eq : X + (Y - X) = Y := by
    ext ω; dsimp; ring
  rw [h_eq] at h_add
  linarith

lemma prob_run_at_bound (n t i : ℕ) :
    fintypeExpect (fun (a : CoinFlip n) => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)))
    ≤ 1 / ((2 : ℝ) ^ t) := by
  by_cases h : i + t ≤ n
  · have h_equiv : (fun (a : CoinFlip n) => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2))) =
      (fun a => indicator (∀ x ∈ streakS n t i h, a x = (1 : Fin 2))) := by
      ext a; simp [streakS_all_heads_iff n t i h a]
    rw [h_equiv]
    linarith [prob_run_at n t i h]
  · by_cases ht0 : 0 < t
    · have h_impossible : ∀ a : CoinFlip n, ¬ (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)) := by
        intro a hall
        by_cases hi_lt_n : i < n
        · have hn_minus_i_lt_t : n - i < t := by omega
          have hj_mem : n - i ∈ Finset.range t := Finset.mem_range.mpr hn_minus_i_lt_t
          have h_val : headAt n a (i + (n - i)) = (0 : Fin 2) := by
            have : i + (n - i) = n := Nat.add_sub_cancel' (by omega)
            rw [this]
            exact headAt_eq_zero_of_ge n a n (le_refl n)
          have h_should : headAt n a (i + (n - i)) = (1 : Fin 2) := hall (n - i) hj_mem
          have : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
          apply this
          calc
            (0 : Fin 2) = headAt n a (i + (n - i)) := Eq.symm h_val
            _ = (1 : Fin 2) := h_should
        · have hi_ge_n : n ≤ i := by omega
          have h0_mem : 0 ∈ Finset.range t := Finset.mem_range.mpr ht0
          have h_val : headAt n a (i + 0) = (0 : Fin 2) := by
            simp
            exact headAt_eq_zero_of_ge n a i hi_ge_n
          have h_should : headAt n a (i + 0) = (1 : Fin 2) := by
            simpa using hall 0 h0_mem
          have : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
          apply this
          calc
            (0 : Fin 2) = headAt n a (i + 0) := Eq.symm h_val
            _ = (1 : Fin 2) := h_should
      have h_zero : fintypeExpect (fun (a : CoinFlip n) => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2))) = 0 := by
        have h_sum_zero : (∑ a : CoinFlip n, indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2))) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          have h_not : ¬ (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)) := h_impossible a
          simp [indicator]
          classical
          have h_exists := not_forall.mp h_not
          rcases h_exists with ⟨j, hj⟩
          rcases Classical.not_imp.mp hj with ⟨hj_mem, hj_neq⟩
          have hj_lt : j < t := Finset.mem_range.1 hj_mem
          refine ⟨j, hj_lt, hj_neq⟩
        unfold fintypeExpect
        rw [h_sum_zero, zero_div]
      rw [h_zero]
      positivity
    · have h_t0 : t = 0 := by omega
      subst h_t0
      haveI : Nonempty (CoinFlip n) := ⟨fun _ => (0 : Fin 2)⟩
      have h_one : fintypeExpect (fun (a : CoinFlip n) => (1 : ℝ)) = 1 :=
        fintypeExpect_const Fintype.card_ne_zero 1
      calc
        fintypeExpect (fun (a : CoinFlip n) => indicator (∀ j ∈ Finset.range 0, headAt n a (i + j) = (1 : Fin 2)))
            = fintypeExpect (fun (a : CoinFlip n) => (1 : ℝ)) := by simp [indicator]
        _ = 1 := h_one
        _ ≤ 1 / (1 : ℝ) := by norm_num
        _ = 1 / ((2 : ℝ) ^ 0) := by norm_num

theorem longestStreak_upperBound (n t : ℕ) (ht : 0 < t) :
    fintypeExpect (fun (a : CoinFlip n) => indicator (longestStreak n a ≥ t))
    ≤ (n : ℝ) / ((2 : ℝ) ^ t) := by
  by_cases hnt : t ≤ n
  · have h_union_bound : ∀ a : CoinFlip n,
        indicator (longestStreak n a ≥ t) ≤
        Finset.sum (Finset.range n) (λ i => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2))) := by
      intro a
      by_cases hge : longestStreak n a ≥ t
      · have hrun : hasRunOfLength n t a := (longestStreak_ge_iff_hasRunOfLength n t a).mp hge
        rcases hrun with ⟨hle, i, himem, hiadd, hi_run⟩
        have hi_lt_n : i < n := by
          have : i < n+1 := Finset.mem_range.1 himem
          omega
        have hi_mem : i ∈ Finset.range n := Finset.mem_range.mpr hi_lt_n
        have h_all' : ∀ j : ℕ, j < t → headAt n a (i + j) = (1 : Fin 2) := by
          intro j hj; apply hi_run; exact Finset.mem_range.mpr hj
        have h_run_val : indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)) = 1 := by
          simp [indicator]; exact h_all'
        have h_nonneg_indic : ∀ (k : ℕ), 0 ≤ indicator (∀ j ∈ Finset.range t, headAt n a (k + j) = (1 : Fin 2)) := by
          intro k; unfold indicator; split <;> norm_num
        have h_single : indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)) ≤
            Finset.sum (Finset.range n) (λ k => indicator (∀ j ∈ Finset.range t, headAt n a (k + j) = (1 : Fin 2))) :=
          Finset.single_le_sum (s := Finset.range n) (f := λ k => indicator (∀ j ∈ Finset.range t, headAt n a (k + j) = (1 : Fin 2)))
            (λ k hk => h_nonneg_indic k) hi_mem
        calc
          indicator (longestStreak n a ≥ t) = 1 := by
            simp [indicator, hge]
          _ = indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)) := by rw [h_run_val]
          _ ≤ Finset.sum (Finset.range n) (λ k => indicator (∀ j ∈ Finset.range t, headAt n a (k + j) = (1 : Fin 2))) := h_single
      · simp [indicator, hge]
    have h_expect_sum_le : fintypeExpect (fun a : CoinFlip n =>
        Finset.sum (Finset.range n) (λ i => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)))) ≤
        (n : ℝ) * (1 / ((2 : ℝ) ^ t)) := by
      calc
        fintypeExpect (fun a : CoinFlip n =>
            Finset.sum (Finset.range n) (λ i => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2))))
        = Finset.sum (Finset.range n) (λ i =>
            fintypeExpect (fun (a : CoinFlip n) => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)))) :=
          fintypeExpect_sum (Finset.range n) (λ i a => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)))
        _ ≤ Finset.sum (Finset.range n) (λ _ => 1 / ((2 : ℝ) ^ t)) := by
          refine Finset.sum_le_sum (λ i hi => ?_)
          exact prob_run_at_bound n t i
        _ = (n : ℝ) * (1 / ((2 : ℝ) ^ t)) := by simp [Finset.card_range]
    have h_expect_bound : fintypeExpect (fun a : CoinFlip n =>
        Finset.sum (Finset.range n) (λ i => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)))) ≤
        (n : ℝ) / ((2 : ℝ) ^ t) := by
      calc
        fintypeExpect (fun a : CoinFlip n =>
            Finset.sum (Finset.range n) (λ i => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2))))
        ≤ (n : ℝ) * (1 / ((2 : ℝ) ^ t)) := h_expect_sum_le
        _ = (n : ℝ) / ((2 : ℝ) ^ t) := by ring
    have h_nonneg_ind : ∀ a : CoinFlip n, 0 ≤ indicator (longestStreak n a ≥ t) := by
      intro a; unfold indicator; split <;> norm_num
    have h_nonneg_sum : ∀ a : CoinFlip n, 0 ≤ Finset.sum (Finset.range n) (λ i => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2))) := by
      intro a; apply Finset.sum_nonneg; intro i hi; unfold indicator; split <;> norm_num
    calc
      fintypeExpect (fun a : CoinFlip n => indicator (longestStreak n a ≥ t))
          ≤ fintypeExpect (fun a : CoinFlip n =>
              Finset.sum (Finset.range n) (λ i => indicator (∀ j ∈ Finset.range t, headAt n a (i + j) = (1 : Fin 2)))) :=
        fintypeExpect_mono h_nonneg_ind h_nonneg_sum h_union_bound
      _ ≤ (n : ℝ) / ((2 : ℝ) ^ t) := h_expect_bound
  · have : ∀ a : CoinFlip n, ¬ (longestStreak n a ≥ t) := by
      intro a
      rw [longestStreak_ge_iff_hasRunOfLength n t a]
      intro hrun
      rcases hrun with ⟨hle, _⟩
      omega
    have h_zero : fintypeExpect (fun (a : CoinFlip n) => indicator (longestStreak n a ≥ t)) = 0 := by
      have h_sum_zero : (∑ a : CoinFlip n, indicator (longestStreak n a ≥ t)) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have h_not : ¬ (longestStreak n a ≥ t) := this a
        simp [indicator, h_not]
      unfold fintypeExpect
      rw [h_sum_zero, zero_div]
    rw [h_zero]
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    positivity

/-! ## Expected longest streak

The expected longest streak of heads satisfies {lit}`E[L] = Θ(log n)`.  The
upper bound {lit}`O(log n)` follows from the tail bound
{name}`longestStreak_upperBound` via {lit}`E[L] = Σ_{t≥1} Pr[L ≥ t]`; the
matching lower bound {lit}`Ω(log n)` uses a block-partition argument.  Both
proofs are deferred to a future refinement.
-/

/--
Expected value of the longest streak of heads in {lit}`n` independent fair coin
flips.
-/
noncomputable def expectedLongestStreak (n : ℕ) : ℝ :=
  fintypeExpect (fun a : CoinFlip n => (longestStreak n a : ℝ))

end Chapter05
end CLRS
