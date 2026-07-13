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

end Chapter05
end CLRS

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
