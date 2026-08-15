import CLRSLean.FourthEdition.Chapter_03.Section_03_1_Asymptotic_Notation
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
{name}`longestStreak_upperBound` via the layer-cake identity
{lit}`E[L] = Σ_{t≥1} Pr[L ≥ t]` ({lit}`expectedLongestStreak_le`); the
matching lower bound {lit}`Ω(log n)` is proved below with a block-partition
argument: the `m = ⌊n/k⌋` disjoint blocks of size `k = ⌊log₂ n / 2⌋` are
independent, so the exact count
{lit}`prob_noFullHeadBlock` gives
{lit}`Pr[L ≥ k] ≥ 1 - (1 - 2^{-k})^m ≥ 1/2`, and the layer-cake lower bound
{lit}`expectedLongestStreak_ge_mul_tail` yields
{lit}`E[L] ≥ k/2 ≥ (log₂ n - 2)/4 ≥ log₂ n / 8`
({lit}`expectedLongestStreak_lowerBound`).
-/

/--
Expected value of the longest streak of heads in {lit}`n` independent fair coin
flips.
-/
noncomputable def expectedLongestStreak (n : ℕ) : ℝ :=
  fintypeExpect (fun a : CoinFlip n => (longestStreak n a : ℝ))

/-- The longest streak of heads never exceeds the number `n` of flips: a run of
`n + 1` heads would require `n + 1 ≤ n` positions. -/
lemma longestStreak_le (n : ℕ) (a : CoinFlip n) : longestStreak n a ≤ n := by
  by_contra h
  push_neg at h
  have hrun := (longestStreak_ge_iff_hasRunOfLength n (n + 1) a).mp h
  rcases hrun with ⟨hle, _⟩
  omega

/-- Pointwise layer-cake: every `m ≤ B` equals the number of thresholds
`t ∈ [1, B]` that it reaches. -/
lemma natCast_eq_sum_ite_Icc (m B : ℕ) (hm : m ≤ B) :
    (m : ℝ) = ∑ t ∈ Finset.Icc 1 B, (if m ≥ t then (1 : ℝ) else 0) := by
  have hfilter : (Finset.Icc 1 B).filter (fun t => m ≥ t) = Finset.Icc 1 m := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1t, -⟩, htm⟩
      exact ⟨h1t, htm⟩
    · rintro ⟨h1t, htm⟩
      exact ⟨⟨h1t, by omega⟩, htm⟩
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp

/-- The expected longest streak equals the sum of the tail probabilities
`Pr[L ≥ t]` over `t = 1, …, n` (the layer-cake / tail-sum formula for the
ℕ-valued random variable `longestStreak n`, which is bounded by `n`). -/
lemma expectedLongestStreak_eq_tailSum (n : ℕ) :
    expectedLongestStreak n =
      ∑ t ∈ Finset.Icc 1 n,
        fintypeExpect (fun a : CoinFlip n => indicator (longestStreak n a ≥ t)) := by
  have hpoint : ∀ a : CoinFlip n, (longestStreak n a : ℝ)
      = ∑ t ∈ Finset.Icc 1 n, indicator (longestStreak n a ≥ t) := by
    intro a
    show (longestStreak n a : ℝ)
      = ∑ t ∈ Finset.Icc 1 n, (if longestStreak n a ≥ t then (1 : ℝ) else 0)
    exact natCast_eq_sum_ite_Icc (longestStreak n a) n (longestStreak_le n a)
  unfold expectedLongestStreak
  rw [← fintypeExpect_sum (Finset.Icc 1 n)
    (fun t (a : CoinFlip n) => indicator (longestStreak n a ≥ t))]
  exact congrArg fintypeExpect (funext hpoint)

/-- **Expected longest streak upper bound** (CLRS §5.4.3): the expected length
of the longest run of heads in `n` independent fair coin flips is at most
`log₂ n + 2`.  The tail-sum formula {name}`expectedLongestStreak_eq_tailSum`
splits the thresholds at `Nat.log 2 n + 1`: thresholds below the split
contribute at most `1` each, and thresholds above it are summable thanks to
{name}`longestStreak_upperBound`, whose geometric tail adds at most `1`. -/
theorem expectedLongestStreak_le (n : ℕ) :
    expectedLongestStreak n ≤ Real.logb 2 n + 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [expectedLongestStreak_eq_tailSum,
      Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty]
    simp [Real.logb_zero]
  · have hcard : Fintype.card (CoinFlip n) ≠ 0 := by
      haveI : Nonempty (CoinFlip n) := ⟨fun _ => (0 : Fin 2)⟩
      exact Fintype.card_ne_zero
    -- Each tail probability is at most `1`, since an indicator is bounded by `1`.
    have hlow : ∀ t ∈ Finset.Icc 1 n, t ≤ Nat.log 2 n + 1 →
        fintypeExpect (fun a : CoinFlip n => indicator (longestStreak n a ≥ t)) ≤ 1 := by
      intro t _ _
      have h0 : ∀ a : CoinFlip n, (0 : ℝ) ≤ indicator (longestStreak n a ≥ t) := by
        intro a; unfold indicator; split <;> norm_num
      have h1 : ∀ a : CoinFlip n, indicator (longestStreak n a ≥ t) ≤ 1 := by
        intro a; unfold indicator; split <;> norm_num
      have hle := fintypeExpect_mono h0 (fun _ => zero_le_one) h1
      rwa [fintypeExpect_const hcard 1] at hle
    -- The partial geometric series `∑ k < m, 2⁻ᵏ` is bounded by `2`.
    have hgeo : ∀ m : ℕ, ∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ k ≤ 2 := by
      intro m
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      have hpos1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
      have heq : ((1 / 2 : ℝ) ^ m - 1) / ((1 / 2 : ℝ) - 1)
          = 2 * (1 - (1 / 2 : ℝ) ^ m) := by
        field_simp
        ring
      rw [heq]
      linarith
    -- The geometric tail past the split point is at most `2^{-(Nat.log 2 n + 1)}`.
    have htail : ∑ t ∈ Finset.Ioc (Nat.log 2 n + 1) n, (1 / 2 : ℝ) ^ t
        ≤ (1 / 2 : ℝ) ^ (Nat.log 2 n + 1) := by
      have hset : Finset.Ioc (Nat.log 2 n + 1) n
          = Finset.Ico (Nat.log 2 n + 1 + 1) (n + 1) := by
        ext t
        simp only [Finset.mem_Ioc, Finset.mem_Ico]
        omega
      rw [hset, Finset.sum_Ico_eq_sum_range]
      have hterm : ∀ i : ℕ, (1 / 2 : ℝ) ^ (Nat.log 2 n + 1 + 1 + i)
          = (1 / 2 : ℝ) ^ (Nat.log 2 n + 1 + 1) * (1 / 2 : ℝ) ^ i :=
        fun i => pow_add _ _ _
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
      calc (1 / 2 : ℝ) ^ (Nat.log 2 n + 1 + 1)
            * ∑ i ∈ Finset.range (n + 1 - (Nat.log 2 n + 1 + 1)), (1 / 2 : ℝ) ^ i
          ≤ (1 / 2 : ℝ) ^ (Nat.log 2 n + 1 + 1) * 2 :=
            mul_le_mul_of_nonneg_left (hgeo _) (by positivity)
        _ = (1 / 2 : ℝ) ^ (Nat.log 2 n + 1) := by rw [pow_succ]; ring
    -- Thresholds below the split contribute at most `Nat.log 2 n + 1` in total.
    have hsumlow : ∑ t ∈ (Finset.Icc 1 n).filter (fun t => t ≤ Nat.log 2 n + 1),
        fintypeExpect (fun a : CoinFlip n => indicator (longestStreak n a ≥ t))
          ≤ (Nat.log 2 n + 1 : ℝ) := by
      have hsub : (Finset.Icc 1 n).filter (fun t => t ≤ Nat.log 2 n + 1)
          ⊆ Finset.Icc 1 (Nat.log 2 n + 1) := by
        intro t ht
        rw [Finset.mem_filter, Finset.mem_Icc] at ht
        rw [Finset.mem_Icc]
        exact ⟨ht.1.1, ht.2⟩
      calc ∑ t ∈ (Finset.Icc 1 n).filter (fun t => t ≤ Nat.log 2 n + 1),
              fintypeExpect (fun a : CoinFlip n => indicator (longestStreak n a ≥ t))
          ≤ ∑ t ∈ (Finset.Icc 1 n).filter (fun t => t ≤ Nat.log 2 n + 1), (1 : ℝ) := by
            refine Finset.sum_le_sum (fun t ht => hlow t (Finset.mem_of_mem_filter t ht)
              (Finset.mem_filter.mp ht).2)
        _ = (((Finset.Icc 1 n).filter (fun t => t ≤ Nat.log 2 n + 1)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ (Nat.log 2 n + 1 : ℝ) := by
            have hcardle : ((Finset.Icc 1 n).filter (fun t => t ≤ Nat.log 2 n + 1)).card
                ≤ Nat.log 2 n + 1 := by
              calc _ ≤ (Finset.Icc 1 (Nat.log 2 n + 1)).card := Finset.card_le_card hsub
                _ = Nat.log 2 n + 1 := by simp
            exact_mod_cast hcardle
    -- Thresholds above the split contribute at most `1`, by the union bound
    -- `longestStreak_upperBound` and the geometric tail `htail`.
    have hsumhigh : ∑ t ∈ (Finset.Icc 1 n).filter (fun t => ¬ t ≤ Nat.log 2 n + 1),
        fintypeExpect (fun a : CoinFlip n => indicator (longestStreak n a ≥ t)) ≤ 1 := by
      have hsub : (Finset.Icc 1 n).filter (fun t => ¬ t ≤ Nat.log 2 n + 1)
          ⊆ Finset.Ioc (Nat.log 2 n + 1) n := by
        intro t ht
        rw [Finset.mem_filter, Finset.mem_Icc] at ht
        rw [Finset.mem_Ioc]
        exact ⟨Nat.lt_of_not_le ht.2, ht.1.2⟩
      have hn2 : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 n + 1) := by
        have h : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
        exact_mod_cast h.le
      calc ∑ t ∈ (Finset.Icc 1 n).filter (fun t => ¬ t ≤ Nat.log 2 n + 1),
              fintypeExpect (fun a : CoinFlip n => indicator (longestStreak n a ≥ t))
          ≤ ∑ t ∈ (Finset.Icc 1 n).filter (fun t => ¬ t ≤ Nat.log 2 n + 1),
              (n : ℝ) / (2 : ℝ) ^ t := by
            refine Finset.sum_le_sum (fun t ht => ?_)
            have htmem := Finset.mem_Icc.mp (Finset.mem_of_mem_filter t ht)
            exact longestStreak_upperBound n t htmem.1
        _ ≤ ∑ t ∈ Finset.Ioc (Nat.log 2 n + 1) n, (n : ℝ) / (2 : ℝ) ^ t :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => by positivity)
        _ = (n : ℝ) * ∑ t ∈ Finset.Ioc (Nat.log 2 n + 1) n, (1 / 2 : ℝ) ^ t := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [div_pow, one_pow, mul_one_div]
        _ ≤ (n : ℝ) * (1 / 2 : ℝ) ^ (Nat.log 2 n + 1) :=
            mul_le_mul_of_nonneg_left htail (by positivity)
        _ ≤ 1 := by
            have hpos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by positivity
            rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one hpos]
            exact hn2
    -- `Nat.log 2 n + 1 ≤ log₂ n + 1`, by monotonicity of `Real.logb`.
    have hlog : (Nat.log 2 n + 1 : ℝ) ≤ Real.logb 2 n + 1 := by
      have h2le : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
      have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n) h2le
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hmono
      linarith
    rw [expectedLongestStreak_eq_tailSum,
      ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (fun t => t ≤ Nat.log 2 n + 1)
        (fun t => fintypeExpect (fun a : CoinFlip n => indicator (longestStreak n a ≥ t)))]
    linarith [hsumlow, hsumhigh, hlog]

/-! ## Expected longest streak: lower bound (block partition)

The lower bound {lit}`E[L] ≥ c · log₂ n` uses the standard block-partition
argument.  Fix a block size {lit}`k` and let {lit}`m = ⌊n/k⌋`.  The `m` disjoint
blocks of `k` consecutive positions are independent; a block is *full* if all
its positions are heads.  The exact count of sequences with no full block is
`(2^k - 1)^m · 2^(n - m·k)` ({lit}`card_noFullHeadBlock`), witnessed by the
bijection {lit}`noFullHeadBlockBijection` that decomposes a sequence into its
`m` block restrictions plus a free tail.  Hence
`Pr[no full block] = (1 - 2^{-k})^m` ({lit}`prob_noFullHeadBlock`).
Since a full block is a run of `k` heads, `Pr[L < k] ≤ (1 - 2^{-k})^m`
({lit}`prob_longestStreak_lt_le`), so `Pr[L ≥ k] ≥ 1 - (1 - 2^{-k})^m`.  The
Bernoulli bound `(1 - 2^{-k})^m ≤ 1/(1 + m·2^{-k})`
({lit}`one_sub_pow_le_inv_one_add_mul`) gives
`Pr[L ≥ k] ≥ m·2^{-k}/(1 + m·2^{-k})` ({lit}`prob_longestStreak_ge_mul`), and
the layer-cake identity lower bound `E[L] ≥ k · Pr[L ≥ k]`
({lit}`expectedLongestStreak_ge_mul_tail`).

Choosing `k = ⌊log₂ n / 2⌋` and `m = ⌊n/k⌋`, the estimates `m ≥ 2^k` and
`2^k·(k+1) ≤ n` show `m·2^{-k} ≥ 1`, hence `Pr[L ≥ k] ≥ 1/2` and
`E[L] ≥ k/2`.  With `k ≥ (log₂ n - 2)/2`, this yields
`E[L] ≥ (log₂ n - 2)/4 ≥ log₂ n / 8` for `n ≥ 16`
({lit}`expectedLongestStreak_lowerBound`).
-/

/-- A block of `k` consecutive flips, viewed as a standalone sequence, is all heads. -/
def blockAllHeads (k : ℕ) (w : Fin k → Fin 2) : Prop :=
  ∀ r : Fin k, w r = (1 : Fin 2)

instance (k : ℕ) (w : Fin k → Fin 2) : Decidable (blockAllHeads k w) := by
  unfold blockAllHeads; infer_instance

/-- Restriction of a sequence to the block of `k` consecutive positions starting at `j * k`. -/
def blockRestriction (n k j : ℕ) (a : CoinFlip n) : Fin k → Fin 2 :=
  fun r => headAt n a (j * k + r.val)

/-- The block of `k` consecutive positions starting at `j * k` is all heads. -/
def blockIsAllHeads (n k j : ℕ) (a : CoinFlip n) : Prop :=
  blockAllHeads k (blockRestriction n k j a)

/-- Among the first `m` blocks of size `k` (positions `0..m*k-1`), none is all heads. -/
def noFullHeadBlock (n k m : ℕ) (a : CoinFlip n) : Prop :=
  ∀ j : Fin m, ¬ blockIsAllHeads n k j.val a

instance (n k m : ℕ) (a : CoinFlip n) : Decidable (noFullHeadBlock n k m a) := by
  unfold noFullHeadBlock blockIsAllHeads blockRestriction headAt
  infer_instance

/-- A full block inside the first `m*k` positions gives a run of `k` heads. -/
lemma blockIsAllHeads_hasRunOfLength (n k j : ℕ) (a : CoinFlip n)
    (hj : j * k + k ≤ n) : blockIsAllHeads n k j a → hasRunOfLength n k a := by
  intro hblock
  refine ⟨by omega, j * k, ?_, ?_, ?_⟩
  · exact Finset.mem_range.mpr (by omega)
  · simpa using hj
  · intro t ht
    exact hblock ⟨t, Finset.mem_range.mp ht⟩

/-- If the longest streak is below `k`, then none of the first `m` blocks is full. -/
lemma noFullHeadBlock_of_lt (n k m : ℕ) (hmk : m * k ≤ n) (a : CoinFlip n) :
    longestStreak n a < k → noFullHeadBlock n k m a := by
  intro hl j hblock
  have hjm : j.val + 1 ≤ m := Nat.succ_le_of_lt j.isLt
  have hjmk : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k hjm
  have hcalc : j.val * k + k ≤ m * k := by simpa [Nat.succ_mul] using hjmk
  have hjk : j.val * k + k ≤ n := le_trans hcalc hmk
  have hrun := blockIsAllHeads_hasRunOfLength n k j.val a hjk hblock
  have hge : longestStreak n a ≥ k := (longestStreak_ge_iff_hasRunOfLength n k a).mpr hrun
  omega

/-- The number of non-all-heads block sequences of length `k` is `2^k - 1`. -/
lemma card_notBlockAllHeads (k : ℕ) :
    Fintype.card {w : Fin k → Fin 2 // ¬ blockAllHeads k w} = 2 ^ k - 1 := by
  classical
  let constOne : Fin k → Fin 2 := fun _ => (1 : Fin 2)
  have hcard_all : Fintype.card {w : Fin k → Fin 2 // blockAllHeads k w} = 1 := by
    have hbio : {w : Fin k → Fin 2 // blockAllHeads k w} ≃
        {w : Fin k → Fin 2 // w = constOne} :=
      { toFun := fun w => ⟨w.1, by
          funext r
          change w.1 r = (1 : Fin 2)
          exact w.2 r⟩
        invFun := fun w => ⟨w.1, by
          intro r
          have h := congrFun w.2 r
          change w.1 r = (1 : Fin 2)
          simpa [constOne] using h⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
    rw [Fintype.card_congr hbio]
    simp
  calc
    Fintype.card {w : Fin k → Fin 2 // ¬ blockAllHeads k w}
        = Fintype.card (Fin k → Fin 2) - Fintype.card {w : Fin k → Fin 2 // blockAllHeads k w} := by
          rw [Fintype.card_subtype_compl (fun w : Fin k → Fin 2 => blockAllHeads k w)]
    _ = 2 ^ k - 1 := by simp [hcard_all]

/-- The tuple of the first `m` block restrictions of a sequence. -/
def blocksOf (n k m : ℕ) (a : CoinFlip n) : Π j : Fin m, Fin k → Fin 2 :=
  fun j => blockRestriction n k j.val a

/-- The restriction of a sequence to the free tail positions `m*k, ..., n-1`. -/
def freeOf (n k m : ℕ) (a : CoinFlip n) : Fin (n - m * k) → Fin 2 :=
  fun t => headAt n a (m * k + t.val)

/-- Reconstruct a full sequence from the `m` block restrictions and the free tail. -/
def reconstructBlocks (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n)
    (w : Π j : Fin m, Fin k → Fin 2) (u : Fin (n - m * k) → Fin 2) : CoinFlip n :=
  fun x : Fin n =>
    if hx : x.val < m * k then
      (w ⟨x.val / k, by exact (Nat.div_lt_iff_lt_mul hk).mpr hx⟩) ⟨x.val % k, by exact Nat.mod_lt x.val hk⟩
    else
      u ⟨x.val - m * k, by omega⟩

/-- On a position inside block `j`, the reconstruction returns the block's own value. -/
lemma reconstruct_in_block (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n)
    (w : Π j : Fin m, Fin k → Fin 2) (u : Fin (n - m * k) → Fin 2)
    (j : Fin m) (r : Fin k) (h : j.val * k + r.val < n) :
    headAt n (reconstructBlocks n k m hk hmk w u) (j.val * k + r.val) = w j r := by
  rw [headAt_eq_of_lt n (reconstructBlocks n k m hk hmk w u) (j.val * k + r.val) h]
  have hxlt : j.val * k + r.val < m * k := by
    have hjm : j.val + 1 ≤ m := Nat.succ_le_of_lt j.isLt
    have hjmk : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k hjm
    have hcalc : j.val * k + k ≤ m * k := by simpa [Nat.succ_mul] using hjmk
    omega
  have hdiv : (j.val * k + r.val) / k = j.val := by
    calc
      (j.val * k + r.val) / k = (r.val + j.val * k) / k := by rw [Nat.add_comm]
      _ = r.val / k + j.val := Nat.add_mul_div_right r.val j.val hk
      _ = j.val := by rw [Nat.div_eq_of_lt r.isLt]; simp
  have hmod : (j.val * k + r.val) % k = r.val := Nat.mul_add_mod_of_lt r.isLt
  have hf_j : (⟨(j.val * k + r.val) / k, by exact (Nat.div_lt_iff_lt_mul hk).mpr hxlt⟩ : Fin m) = j := by
    apply Fin.ext
    change (j.val * k + r.val) / k = j.val
    rw [hdiv]
  have hf_r : (⟨(j.val * k + r.val) % k, by exact Nat.mod_lt (j.val * k + r.val) hk⟩ : Fin k) = r := by
    apply Fin.ext
    change (j.val * k + r.val) % k = r.val
    rw [hmod]
  unfold reconstructBlocks
  simp [hxlt, hf_j, hf_r, Nat.mod_eq_of_lt r.isLt]

/-- On a free position, the reconstruction returns the free tail's own value. -/
lemma reconstruct_out_block (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n)
    (w : Π j : Fin m, Fin k → Fin 2) (u : Fin (n - m * k) → Fin 2)
    (t : Fin (n - m * k)) (h : m * k + t.val < n) :
    headAt n (reconstructBlocks n k m hk hmk w u) (m * k + t.val) = u t := by
  rw [headAt_eq_of_lt n (reconstructBlocks n k m hk hmk w u) (m * k + t.val) h]
  have hge : m * k ≤ m * k + t.val := by omega
  have hsub : m * k + t.val - m * k = t.val := by omega
  have hf_t : (⟨t.val, by omega⟩ : Fin (n - m * k)) = t := by
    apply Fin.ext; rfl
  simp [reconstructBlocks, hge, hsub, hf_t]

/-- Bijection between sequences with no full block among the first `m` blocks and
tuples of `m` non-all-heads blocks plus a free tail.  This is the product
decomposition witnessing independence of the `m` disjoint blocks. -/
noncomputable def noFullHeadBlockBijection (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n) :
    {a : CoinFlip n // noFullHeadBlock n k m a} ≃
      (Π j : Fin m, {w : Fin k → Fin 2 // ¬ blockAllHeads k w}) × (Fin (n - m * k) → Fin 2) where
  toFun a :=
    ( (fun j : Fin m => ⟨blockRestriction n k j.val a.1, a.2 j⟩),
      (fun t : Fin (n - m * k) => headAt n a.1 (m * k + t.val)) )
  invFun wu :=
    ⟨ reconstructBlocks n k m hk hmk (fun j => (wu.1 j).1) wu.2, by
      intro j hblock
      have hw : blockAllHeads k (wu.1 j).1 := by
        intro r
        have hr := hblock r
        have hxlt' : j.val * k + r.val < n := by
          have hjm : j.val + 1 ≤ m := Nat.succ_le_of_lt j.isLt
          have hjmk : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k hjm
          have hcalc : j.val * k + k ≤ m * k := by simpa [Nat.succ_mul] using hjmk
          omega
        rw [blockRestriction] at hr
        rw [reconstruct_in_block n k m hk hmk (fun j => (wu.1 j).1) wu.2 j r hxlt'] at hr
        exact hr
      exact (wu.1 j).2 hw ⟩
  left_inv := by
    intro a
    apply Subtype.ext
    funext x
    by_cases hx : x.val < m * k
    · have hdiv : (x.val / k) * k + x.val % k = x.val := Nat.div_add_mod' x.val k
      have hxval : x.val / k < m := by exact (Nat.div_lt_iff_lt_mul hk).mpr hx
      have hmod : x.val % k < k := Nat.mod_lt x.val hk
      calc
        reconstructBlocks n k m hk hmk (blocksOf n k m a.1) (freeOf n k m a.1) x
            = (blocksOf n k m a.1) ⟨x.val / k, hxval⟩ ⟨x.val % k, hmod⟩ := by
              simp [reconstructBlocks, hx]
        _ = blockRestriction n k (x.val / k) a.1 ⟨x.val % k, hmod⟩ := by rfl
        _ = headAt n a.1 ((x.val / k) * k + (x.val % k)) := by rfl
        _ = headAt n a.1 (x.val) := by rw [hdiv]
        _ = a.1 x := by
          rw [headAt_eq_of_lt n a.1 x.val x.isLt]
    · have hge : m * k ≤ x.val := Nat.le_of_not_gt hx
      calc
        reconstructBlocks n k m hk hmk (blocksOf n k m a.1) (freeOf n k m a.1) x
            = (freeOf n k m a.1) ⟨x.val - m * k, by omega⟩ := by
              simp [reconstructBlocks, hx]
        _ = headAt n a.1 (m * k + (x.val - m * k)) := by rfl
        _ = headAt n a.1 (x.val) := by rw [Nat.add_sub_of_le hge]
        _ = a.1 x := by
          rw [headAt_eq_of_lt n a.1 x.val x.isLt]
  right_inv := by
    intro wu
    apply Prod.ext
    · funext j
      apply Subtype.ext
      funext r
      have hxlt' : j.val * k + r.val < n := by
        have hjm : j.val + 1 ≤ m := Nat.succ_le_of_lt j.isLt
        have hjmk : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k hjm
        have hcalc : j.val * k + k ≤ m * k := by simpa [Nat.succ_mul] using hjmk
        omega
      calc
        blockRestriction n k j.val (reconstructBlocks n k m hk hmk (fun j => (wu.1 j).1) wu.2) r
            = headAt n (reconstructBlocks n k m hk hmk (fun j => (wu.1 j).1) wu.2) (j.val * k + r.val) := rfl
        _ = (fun j => (wu.1 j).1) j r :=
          reconstruct_in_block n k m hk hmk (fun j => (wu.1 j).1) wu.2 j r hxlt'
        _ = (wu.1 j).1 r := rfl
    · funext t
      have hxlt' : m * k + t.val < n := by
        have ht : t.val < n - m * k := t.isLt
        omega
      calc
        headAt n (reconstructBlocks n k m hk hmk (fun j => (wu.1 j).1) wu.2) (m * k + t.val)
            = wu.2 t := reconstruct_out_block n k m hk hmk (fun j => (wu.1 j).1) wu.2 t hxlt'

/-- The number of sequences with no full block among the first `m` blocks is
`(2^k - 1)^m · 2^(n - m*k)`. -/
lemma card_noFullHeadBlock (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n) :
    Fintype.card {a : CoinFlip n // noFullHeadBlock n k m a}
    = (2 ^ k - 1) ^ m * 2 ^ (n - m * k) := by
  calc
    Fintype.card {a : CoinFlip n // noFullHeadBlock n k m a}
        = Fintype.card ((Π j : Fin m, {w : Fin k → Fin 2 // ¬ blockAllHeads k w}) × (Fin (n - m * k) → Fin 2)) :=
          Fintype.card_congr (noFullHeadBlockBijection n k m hk hmk)
    _ = Fintype.card (Π j : Fin m, {w : Fin k → Fin 2 // ¬ blockAllHeads k w}) * Fintype.card (Fin (n - m * k) → Fin 2) := by simp
    _ = (∏ j : Fin m, Fintype.card {w : Fin k → Fin 2 // ¬ blockAllHeads k w}) * Fintype.card (Fin (n - m * k) → Fin 2) := by rw [Fintype.card_pi]
    _ = (2 ^ k - 1) ^ m * 2 ^ (n - m * k) := by
      have hprod : (∏ j : Fin m, Fintype.card {w : Fin k → Fin 2 // ¬ blockAllHeads k w})
          = (2 ^ k - 1) ^ m := by
        rw [Finset.prod_const, card_notBlockAllHeads k]
        simp
      rw [hprod]
      simp [Fintype.card_fun]

/-- **Bernoulli-type bound**: for `0 ≤ x ≤ 1`, `(1 - x)^m ≤ 1 / (1 + m·x)`. -/
lemma one_sub_pow_le_inv_one_add_mul {m : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x) ^ m ≤ (1 + (m : ℝ) * x)⁻¹ := by
  have hx_pos : (0 : ℝ) < 1 + x := by nlinarith
  have hle1 : 1 - x ≤ (1 + x)⁻¹ := by
    have hdiv : 1 - x ≤ 1 / (1 + x) := by
      rw [le_div_iff₀ hx_pos]
      nlinarith [sq_nonneg x]
    simpa using hdiv
  have hle2 : (1 - x) ^ m ≤ (1 + x)⁻¹ ^ m := by
    exact pow_le_pow_left₀ (by linarith : 0 ≤ 1 - x) hle1 m
  have hbern : 1 + (m : ℝ) * x ≤ (1 + x) ^ m := by
    exact one_add_mul_le_pow (by nlinarith : -2 ≤ x) m
  have hpos : (0 : ℝ) < (1 + x) ^ m := by positivity
  have hpos2 : (0 : ℝ) < 1 + (m : ℝ) * x := by nlinarith
  calc
    (1 - x) ^ m ≤ (1 + x)⁻¹ ^ m := hle2
    _ = ((1 + x) ^ m)⁻¹ := by rw [← inv_pow]
    _ ≤ (1 + (m : ℝ) * x)⁻¹ := by
      rw [inv_le_inv₀ hpos hpos2]
      exact hbern

/-- If `x ≥ 1`, then `x/(1+x) ≥ 1/2`. -/
lemma half_le_self_div_one_add_self {x : ℝ} (hx : 1 ≤ x) :
    (1 / 2 : ℝ) ≤ x / (1 + x) := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have hnum : (1 / 2 : ℝ) * (1 + x) ≤ x := by nlinarith
  exact (le_div_iff₀ hpos).mpr hnum

/-- The probability that no full block appears among the first `m` blocks of size
`k` (within `n` flips) is exactly `(1 - 2^{-k})^m`. -/
lemma prob_noFullHeadBlock (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n) :
    fintypeExpect (fun a : CoinFlip n => indicator (noFullHeadBlock n k m a))
    = (1 - 1 / (2 : ℝ) ^ k) ^ m := by
  have htotal : (Fintype.card (CoinFlip n) : ℝ) = (2 : ℝ) ^ n := by
    have h_nat : Fintype.card (CoinFlip n) = 2 ^ n := by
      calc
        Fintype.card (CoinFlip n) = Fintype.card (Fin n → Fin 2) := rfl
        _ = (Fintype.card (Fin 2)) ^ (Fintype.card (Fin n)) := by rw [Fintype.card_fun]
        _ = 2 ^ n := by simp
    rw [h_nat]; simp
  have hcard := card_noFullHeadBlock n k m hk hmk
  have hcardsub : (Fintype.card {a : CoinFlip n // noFullHeadBlock n k m a} : ℝ)
      = ((2 ^ k - 1) ^ m * 2 ^ (n - m * k) : ℕ) := by
    exact_mod_cast hcard
  calc
    fintypeExpect (fun a => indicator (noFullHeadBlock n k m a))
        = (∑ a : CoinFlip n, indicator (noFullHeadBlock n k m a)) / (Fintype.card (CoinFlip n) : ℝ) := rfl
    _ = ((Fintype.card {a : CoinFlip n // noFullHeadBlock n k m a} : ℝ)) / (Fintype.card (CoinFlip n) : ℝ) := by
          simp [indicator, Fintype.card_subtype]
    _ = ((2 ^ k - 1) ^ m * 2 ^ (n - m * k) : ℕ) / ((2 : ℝ) ^ n) := by rw [hcardsub, htotal]
    _ = (1 - 1 / (2 : ℝ) ^ k) ^ m := by
      have hnat : (((2 ^ k - 1) ^ m * 2 ^ (n - m * k) : ℕ) : ℝ)
          = ((2 : ℝ) ^ k - 1) ^ m * (2 : ℝ) ^ (n - m * k) := by norm_num
      rw [hnat]
      have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (m * k) * (2 : ℝ) ^ (n - m * k) := by
        rw [← pow_add, Nat.add_sub_of_le hmk]
      rw [hpow]
      have hmain : (1 - 1 / (2 : ℝ) ^ k) ^ m = (((2 : ℝ) ^ k - 1) / (2 : ℝ) ^ k) ^ m := by
        congr 1
        field_simp
      rw [hmain]
      rw [show (2 : ℝ) ^ (m * k) = ((2 : ℝ) ^ k) ^ m by rw [mul_comm, pow_mul]]
      field_simp
      rw [div_pow]
      field_simp

/-- If the longest streak is below `k`, the indicator of `L < k` is bounded by
the indicator that no full block occurs. -/
lemma prob_longestStreak_lt_le (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n) :
    fintypeExpect (fun a => indicator (longestStreak n a < k))
    ≤ (1 - 1 / (2 : ℝ) ^ k) ^ m := by
  have hX : ∀ a : CoinFlip n, 0 ≤ indicator (longestStreak n a < k) := by
    intro a; unfold indicator; split <;> norm_num
  have hY : ∀ a : CoinFlip n, 0 ≤ indicator (noFullHeadBlock n k m a) := by
    intro a; unfold indicator; split <;> norm_num
  have hXY : ∀ a : CoinFlip n, indicator (longestStreak n a < k) ≤ indicator (noFullHeadBlock n k m a) := by
    intro a
    by_cases hL : longestStreak n a < k
    · have hnf : noFullHeadBlock n k m a := noFullHeadBlock_of_lt n k m hmk a hL
      simp [indicator, hL, hnf]
    · simp [indicator, hL]
      split <;> norm_num
  have hmono : fintypeExpect (fun a => indicator (longestStreak n a < k))
      ≤ fintypeExpect (fun a => indicator (noFullHeadBlock n k m a)) :=
    fintypeExpect_mono hX hY hXY
  rwa [prob_noFullHeadBlock n k m hk hmk] at hmono

/-- The tail probability `Pr[L ≥ k]` is at least `1 - (1 - 2^{-k})^m`. -/
lemma prob_longestStreak_ge_lower (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n) :
    1 - (1 - 1 / (2 : ℝ) ^ k) ^ m ≤ fintypeExpect (fun a => indicator (longestStreak n a ≥ k)) := by
  have hpoint : (fun a => indicator (longestStreak n a ≥ k)) =
      (fun a => 1 - indicator (longestStreak n a < k)) := by
    funext a
    by_cases h : longestStreak n a ≥ k
    · have hnot : ¬ longestStreak n a < k := by omega
      simp [indicator, h, hnot]
    · have hlt : longestStreak n a < k := by omega
      simp [indicator, h, hlt]
  have hcomp : fintypeExpect (fun a => indicator (longestStreak n a ≥ k)) =
      1 - fintypeExpect (fun a => indicator (longestStreak n a < k)) := by
    rw [hpoint]
    unfold fintypeExpect
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [sub_div]
    have hcard : (Fintype.card (CoinFlip n) : ℝ) ≠ 0 := by
      haveI : Nonempty (CoinFlip n) := ⟨fun _ => (0 : Fin 2)⟩
      exact_mod_cast (Fintype.card_ne_zero)
    field_simp [hcard]
  rw [hcomp]
  linarith [prob_longestStreak_lt_le n k m hk hmk]

/-- The tail probability `Pr[L ≥ k]` is at least `m·2^{-k} / (1 + m·2^{-k})`. -/
lemma prob_longestStreak_ge_mul (n k m : ℕ) (hk : 0 < k) (hmk : m * k ≤ n) :
    (m : ℝ) * (1 / (2 : ℝ) ^ k) / (1 + (m : ℝ) * (1 / (2 : ℝ) ^ k))
    ≤ fintypeExpect (fun a => indicator (longestStreak n a ≥ k)) := by
  let x : ℝ := 1 / (2 : ℝ) ^ k
  have hx0 : 0 ≤ x := by unfold x; positivity
  have hx1 : x ≤ 1 := by
    unfold x
    rw [one_div]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
      simpa using (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) k)
    exact inv_le_one_of_one_le₀ h2
  have hbern : (1 - x) ^ m ≤ (1 + (m : ℝ) * x)⁻¹ := one_sub_pow_le_inv_one_add_mul hx0 hx1
  have hlow : 1 - (1 - x) ^ m ≥ (m : ℝ) * x / (1 + (m : ℝ) * x) := by
    have hden : (0 : ℝ) < 1 + (m : ℝ) * x := by positivity
    have hcomp : 1 - (1 + (m : ℝ) * x)⁻¹ = (m : ℝ) * x / (1 + (m : ℝ) * x) := by
      field_simp [hden.ne']
      ring
    rw [← hcomp]
    linarith
  unfold x at hlow
  linarith [prob_longestStreak_ge_lower n k m hk hmk, hlow]

/-- Tail probabilities `Pr[L ≥ t]` are monotone in the threshold. -/
lemma tailProb_mono (n k t : ℕ) (htk : t ≤ k) :
    fintypeExpect (fun a => indicator (longestStreak n a ≥ k))
    ≤ fintypeExpect (fun a => indicator (longestStreak n a ≥ t)) := by
  have hX : ∀ a : CoinFlip n, 0 ≤ indicator (longestStreak n a ≥ k) := by
    intro a; unfold indicator; split <;> norm_num
  have hY : ∀ a : CoinFlip n, 0 ≤ indicator (longestStreak n a ≥ t) := by
    intro a; unfold indicator; split <;> norm_num
  have hXY : ∀ a : CoinFlip n, indicator (longestStreak n a ≥ k) ≤ indicator (longestStreak n a ≥ t) := by
    intro a
    by_cases hk : longestStreak n a ≥ k
    · have ht : longestStreak n a ≥ t := le_trans htk hk
      simp [indicator, hk, ht]
    · simp [indicator, hk]
      split <;> norm_num
  exact fintypeExpect_mono hX hY hXY

/-- The layer-cake identity lower bound: `E[L] ≥ k · Pr[L ≥ k]`. -/
lemma expectedLongestStreak_ge_mul_tail (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (k : ℝ) * fintypeExpect (fun a => indicator (longestStreak n a ≥ k))
    ≤ expectedLongestStreak n := by
  rw [expectedLongestStreak_eq_tailSum]
  have hsum_le : (k : ℝ) * fintypeExpect (fun a => indicator (longestStreak n a ≥ k))
      ≤ ∑ t ∈ Finset.Icc 1 k, fintypeExpect (fun a => indicator (longestStreak n a ≥ t)) := by
    calc
      (k : ℝ) * fintypeExpect (fun a => indicator (longestStreak n a ≥ k))
          = ∑ t ∈ Finset.Icc 1 k, fintypeExpect (fun a => indicator (longestStreak n a ≥ k)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t ∈ Finset.Icc 1 k, fintypeExpect (fun a => indicator (longestStreak n a ≥ t)) := by
            refine Finset.sum_le_sum (fun t ht => tailProb_mono n k t (Finset.mem_Icc.mp ht).2)
  have hsubset : ∑ t ∈ Finset.Icc 1 k, fintypeExpect (fun a => indicator (longestStreak n a ≥ t))
      ≤ ∑ t ∈ Finset.Icc 1 n, fintypeExpect (fun a => indicator (longestStreak n a ≥ t)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (by omega : k ≤ n))
      (fun t _ _ => fintypeExpect_nonneg (fun a => by unfold indicator; split <;> norm_num))
  linarith

/-- **Expected longest streak lower bound** (CLRS §5.4.3): for `n ≥ 16` flips the
expected longest run of heads is at least `log₂ n / 8`.  With `k = ⌊log₂ n / 2⌋`
and `m = ⌊n / k⌋`, the `m` disjoint blocks of size `k` give
`Pr[L ≥ k] ≥ 1/2` (via the exact count `(1 - 2^{-k})^m`), and the layer-cake
lower bound `E[L] ≥ k·Pr[L ≥ k]` yields `E[L] ≥ k/2 ≥ (log₂ n - 2)/4 ≥ log₂ n / 8`. -/
theorem expectedLongestStreak_lowerBound (n : ℕ) (hn : 16 ≤ n) :
    Real.logb 2 n / 8 ≤ expectedLongestStreak n := by
  let k : ℕ := Nat.log 2 n / 2
  let m : ℕ := n / k
  let ℓ : ℝ := Real.logb 2 n
  have hL2ge : 4 ≤ Nat.log 2 n := by
    have hmono := Nat.log_mono_right (b := 2) (by omega : 16 ≤ n)
    norm_num at hmono
    exact hmono
  have h1le_L2 : 1 ≤ Nat.log 2 n := by omega
  have hL2le : (Nat.log 2 n : ℝ) ≤ ℓ := by
    have hpow_n : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by
      exact_mod_cast (Nat.pow_log_le_self 2 (by omega : n ≠ 0))
    have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 n) hpow_n
    simpa [ℓ, Real.logb_pow, Real.logb_self_eq_one] using hmono
  have hlt : ℓ - 1 < (Nat.log 2 n : ℝ) := by
    have hlt_nat : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hmono := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (n : ℝ))
      (by exact_mod_cast hlt_nat : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1))
    have hrhs : Real.logb 2 (2 ^ (Nat.log 2 n + 1)) = (Nat.log 2 n + 1 : ℝ) := by
      simp [Real.logb_pow, Real.logb_self_eq_one]
    rw [hrhs] at hmono
    linarith
  have hk : 0 < k := by
    have : 0 < Nat.log 2 n / 2 := by omega
    simpa [k] using this
  have hkn : k ≤ n := by
    have hL2lt : Nat.log 2 n < n := by
      have h1 : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
      exact lt_of_lt_of_le h1 (Nat.pow_log_le_self 2 (by omega : n ≠ 0))
    have hk_le_L2 : k ≤ Nat.log 2 n := by
      have : Nat.log 2 n / 2 ≤ Nat.log 2 n := by omega
      simpa [k] using this
    omega
  have hmk : m * k ≤ n := by
    have : n / k * k ≤ n := Nat.div_mul_le_self n k
    simpa [m] using this
  have h2k_le_L2 : 2 * k ≤ Nat.log 2 n := by
    have : 2 * (Nat.log 2 n / 2) ≤ Nat.log 2 n := by omega
    simpa [k] using this
  have hk2k : k * 2 ^ k ≤ n := by
    have hpow_le : (2 : ℕ) ^ (2 * k) ≤ 2 ^ Nat.log 2 n :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) h2k_le_L2
    have hpow_n : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hle : 2 ^ (2 * k) ≤ n := le_trans hpow_le hpow_n
    have hk1 : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt Nat.lt_two_pow_self
    have hbound : k * 2 ^ k + k ≤ 2 ^ (2 * k) := by
      calc
        k * 2 ^ k + k ≤ k * 2 ^ k + 2 ^ k := by omega
        _ = (k + 1) * 2 ^ k := by ring
        _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) hk1
        _ = 2 ^ (2 * k) := by
          rw [← pow_two, ← pow_mul, mul_comm]
    omega
  have hmge2k : 2 ^ k ≤ m := by
    have hle : k * 2 ^ k ≤ n := hk2k
    have hdiv : 2 ^ k ≤ n / k := by
      exact (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hle)
    simpa [m] using hdiv
  have hP : (m : ℝ) * (1 / (2 : ℝ) ^ k) / (1 + (m : ℝ) * (1 / (2 : ℝ) ^ k))
      ≤ fintypeExpect (fun a => indicator (longestStreak n a ≥ k)) :=
    prob_longestStreak_ge_mul n k m hk hmk
  have hx : (1 : ℝ) ≤ (m : ℝ) * (1 / (2 : ℝ) ^ k) := by
    have hc : ((2 ^ k : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmge2k
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    calc
      (1 : ℝ) = ((2 ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k := by simp
      _ ≤ (m : ℝ) / (2 : ℝ) ^ k := by exact div_le_div_of_nonneg_right hc (le_of_lt h2k_pos)
      _ = (m : ℝ) * (1 / (2 : ℝ) ^ k) := by ring
  have hP2 : (1 / 2 : ℝ) ≤ fintypeExpect (fun a => indicator (longestStreak n a ≥ k)) := by
    have hdiv : (1 / 2 : ℝ) ≤ (m : ℝ) * (1 / (2 : ℝ) ^ k) / (1 + (m : ℝ) * (1 / (2 : ℝ) ^ k)) :=
      half_le_self_div_one_add_self hx
    linarith [hP, hdiv]
  have hE : (k : ℝ) / 2 ≤ expectedLongestStreak n := by
    have hmul : (k : ℝ) * (1 / 2 : ℝ) ≤ expectedLongestStreak n := by
      exact le_trans (mul_le_mul_of_nonneg_left hP2 (by positivity : 0 ≤ (k : ℝ)))
        (expectedLongestStreak_ge_mul_tail n k hk hkn)
    linarith
  have h2k_ge : Nat.log 2 n - 1 ≤ 2 * k := by
    have : Nat.log 2 n - 1 ≤ 2 * (Nat.log 2 n / 2) := by omega
    simpa [k] using this
  have hk_ge : (ℓ - 2) / 2 ≤ (k : ℝ) := by
    have hlt2 : ℓ - 2 < (2 * k : ℝ) := by
      have h1 : ℓ - 2 < (Nat.log 2 n : ℝ) - 1 := by linarith
      have h2 : (Nat.log 2 n : ℝ) - 1 ≤ (2 : ℝ) * (k : ℝ) := by
        have hcast : ((Nat.log 2 n - 1 : ℕ) : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast h2k_ge
        have hsub : ((Nat.log 2 n - 1 : ℕ) : ℝ) = (Nat.log 2 n : ℝ) - 1 := by
          rw [Nat.cast_sub h1le_L2]
          norm_num
        rwa [hsub, Nat.cast_mul] at hcast
      linarith
    have hdiv : (ℓ - 2) / 2 < (k : ℝ) := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have hlt2' : ℓ - 2 < (k : ℝ) * 2 := by
        simpa [mul_comm] using hlt2
      exact (div_lt_iff₀ h2pos).mpr hlt2'
    linarith
  have hℓ : (4 : ℝ) ≤ ℓ := by
    have hmono := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < (16 : ℝ))
      (by exact_mod_cast (by omega : (16 : ℕ) ≤ n) : (16 : ℝ) ≤ (n : ℝ))
    have h16 : Real.logb 2 (16 : ℝ) = 4 := by
      have hpow : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
      rw [hpow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
    rw [h16] at hmono
    simpa [ℓ] using hmono
  have hfinal : ℓ / 8 ≤ (ℓ - 2) / 4 := by
    nlinarith
  linarith


end Chapter05
end CLRS

/-! ## Root compatibility aliases

The streak development predated the `CLRS.Chapter05` namespace.  Keep its
original root-level proof surface available to downstream users while the new
chapter-facing declarations remain namespaced.
-/

abbrev CoinFlip := CLRS.Chapter05.CoinFlip
abbrev headAt := CLRS.Chapter05.headAt
abbrev hasRunOfLength := CLRS.Chapter05.hasRunOfLength
noncomputable abbrev longestStreak := CLRS.Chapter05.longestStreak
abbrev streakS := CLRS.Chapter05.streakS
noncomputable abbrev headsSetBijection {n : ℕ} (S : Finset (Fin n)) :=
  CLRS.Chapter05.headsSetBijection S

alias prob_first_t_heads := CLRS.Chapter05.prob_first_t_heads
alias headAt_eq_of_lt := CLRS.Chapter05.headAt_eq_of_lt
alias headAt_eq_zero_of_ge := CLRS.Chapter05.headAt_eq_zero_of_ge
alias card_streakS := CLRS.Chapter05.card_streakS
alias streakS_all_heads_iff := CLRS.Chapter05.streakS_all_heads_iff
alias prob_run_at := CLRS.Chapter05.prob_run_at
alias hasRunOfLength_mono := CLRS.Chapter05.hasRunOfLength_mono
alias longestStreak_ge_iff_hasRunOfLength :=
  CLRS.Chapter05.longestStreak_ge_iff_hasRunOfLength
alias fintypeExpect_mono := CLRS.Chapter05.fintypeExpect_mono
alias prob_run_at_bound := CLRS.Chapter05.prob_run_at_bound
alias longestStreak_upperBound := CLRS.Chapter05.longestStreak_upperBound
alias longestStreak_le := CLRS.Chapter05.longestStreak_le
alias natCast_eq_sum_ite_Icc := CLRS.Chapter05.natCast_eq_sum_ite_Icc
alias expectedLongestStreak_eq_tailSum := CLRS.Chapter05.expectedLongestStreak_eq_tailSum
alias expectedLongestStreak_le := CLRS.Chapter05.expectedLongestStreak_le
