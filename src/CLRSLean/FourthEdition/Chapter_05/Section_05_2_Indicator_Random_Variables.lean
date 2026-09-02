import CLRSLean.Probability.FiniteExpectation
import Mathlib

/-!
# 5.2. Indicator random variables

This section formalizes the CLRS §5.2 *indicator random variable* technique and
*linearity of expectation* as a general tool, with the **hat-check problem** as
the canonical worked example (CLRS eq. (5.1)-(5.2)).

The sample space is {lit}`Ω = Equiv.Perm (Fin n)`, a uniform random permutation
of {lit}`n` elements, evaluated with the shared finite-expectation toolkit
{lit}`CLRS.Probability.fintypeExpect` from
{lit}`CLRSLean/Probability/FiniteExpectation.lean`.  The key primitives reused
are {lit}`fintypeExpect_sum` (linearity over a finite indicator sum),
{lit}`fintypeExpect_const`, {lit}`fintypeExpect_equiv` (reindexing invariance),
and {lit}`fintypeExpect_indicator_singleton`.

Main results:

- Theorem {lit}`CLRS.Chapter05.permSendProb_eq`: the target {lit}`π i` of a fixed
  point {lit}`i` under a uniform random permutation is uniformly distributed;
  the probability of sending {lit}`i` to any {lit}`k` equals the probability of
  sending it to any {lit}`l`.  This is proved by translation invariance of the
  uniform measure on the permutation group under left multiplication by a
  transposition.
- Theorem {lit}`CLRS.Chapter05.probFixesPoint`: a uniform random permutation of
  {lit}`Fin n` fixes a given point {lit}`i` with probability exactly
  {lit}`1/n` (the indicator expectation of the event {lit}`π i = i`).
- Theorem {lit}`CLRS.Chapter05.expectedFixedPoints_eq_one`: the **hat-check
  problem** — the expected number of fixed points of a uniform random
  permutation of {lit}`Fin n` equals {lit}`1`, independent of {lit}`n` (for
  {lit}`n ≥ 1`), by linearity of expectation over the {lit}`n` fixed-point
  indicators.

Status: `proved` for the uniform-permutation model over {lit}`Equiv.Perm (Fin n)`.

Notation conventions used in this section:

- {lit}`π` : a permutation in {lit}`Equiv.Perm (Fin n)` (a bijection of
  {lit}`Fin n`)
- {lit}`i`, {lit}`k`, {lit}`l`, {lit}`q` : points of {lit}`Fin n`
- {lit}`indicator P` : the {lit}`0/1` indicator random variable of the event
  {lit}`P`
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/-! ## The uniform-permutation sample space

The hat-check problem draws a permutation {lit}`π` uniformly from
{lit}`Equiv.Perm (Fin n)` (customer {lit}`i` receives the hat {lit}`π i`).
Mathlib supplies the {lit}`Fintype` and {lit}`DecidableEq` instances for
{lit}`Equiv.Perm (Fin n)`, so the toolkit's {lit}`fintypeExpect` applies
directly. -/

/--
The probability that a uniform random permutation of {lit}`Fin n` sends the
point {lit}`i` to the point {lit}`k`, i.e. the expectation of the indicator
random variable of the event {lit}`π i = k`.
-/
noncomputable def permSendProb {n : ℕ} (i k : Fin n) : ℝ :=
  fintypeExpect (fun π : Equiv.Perm (Fin n) => indicator (π i = k))

/--
**Uniformity of the image of a point.**  Under a uniform random permutation, the
image {lit}`π i` of a fixed point {lit}`i` is uniformly distributed over
{lit}`Fin n`: the probability of sending {lit}`i` to {lit}`k` equals the
probability of sending {lit}`i` to {lit}`l`.

The proof is translation invariance of the uniform measure on the permutation
*group*: left multiplication by the transposition {lit}`swap k l` is a bijection
of the sample space (an {lit}`Equiv`), so by {lit}`fintypeExpect_equiv` it
preserves expectations, and it converts the event {lit}`π i = l` into the event
{lit}`π i = k`.
-/
theorem permSendProb_eq {n : ℕ} (i k l : Fin n) :
    permSendProb i k = permSendProb i l := by
  have hfun :
      (fun π : Equiv.Perm (Fin n) =>
          indicator ((Equiv.mulLeft (Equiv.swap k l) π) i = k))
        = (fun π : Equiv.Perm (Fin n) => indicator (π i = l)) := by
    funext π
    rw [Equiv.coe_mulLeft, Equiv.Perm.mul_apply]
    by_cases h : π i = l
    · rw [h]
      simp [indicator, Equiv.swap_apply_right]
    · have h2 : ¬ (Equiv.swap k l (π i) = k) := by
        intro hc
        exact h (by
          simpa [Equiv.swap_apply_self, Equiv.swap_apply_left]
            using congrArg (Equiv.swap k l) hc)
      simp [indicator, h, h2]
  have he := fintypeExpect_equiv (Equiv.mulLeft (Equiv.swap k l))
    (fun π : Equiv.Perm (Fin n) => indicator (π i = k))
  rw [hfun] at he
  unfold permSendProb
  rw [he]

/--
**Fixed-point probability = `1/n` (hat-check indicator, CLRS eq. (5.1)).**  A
uniform random permutation of {lit}`Fin n` fixes a given point {lit}`i` with
probability exactly {lit}`1/n`.

Because the {lit}`n` events {lit}`π i = k` (for {lit}`k : Fin n`) partition the
sample space, their probabilities sum to {lit}`1`; and by
{lit}`permSendProb_eq` they are all equal, so each equals {lit}`1/n`.
-/
theorem probFixesPoint {n : ℕ} (i : Fin n) :
    fintypeExpect (fun π : Equiv.Perm (Fin n) => indicator (π i = i)) = 1 / (n : ℝ) := by
  have hn : 0 < n := Fin.pos i
  haveI : Nonempty (Equiv.Perm (Fin n)) := ⟨1⟩
  -- The `n` events `π i = k` partition the sample space, so their indicators sum
  -- to `1` at every `π`.
  have hsum1 : ∀ π : Equiv.Perm (Fin n),
      (∑ k : Fin n, indicator (π i = k)) = 1 := by
    intro π
    rw [Finset.sum_eq_single (π i)]
    · simp [indicator]
    · intro b _ hb
      simp only [indicator, if_neg (Ne.symm hb)]
    · intro hmem
      exact absurd (Finset.mem_univ (π i)) hmem
  -- Linearity of expectation: the point probabilities sum to `1`.
  have hsumProb : (∑ k : Fin n, permSendProb i k) = 1 := by
    have hlin := fintypeExpect_sum (Ω := Equiv.Perm (Fin n)) (Finset.univ : Finset (Fin n))
      (fun (k : Fin n) (π : Equiv.Perm (Fin n)) => indicator (π i = k))
    have hconst :
        fintypeExpect (fun π : Equiv.Perm (Fin n) => ∑ k : Fin n, indicator (π i = k)) = 1 := by
      have hone : (fun π : Equiv.Perm (Fin n) => ∑ k : Fin n, indicator (π i = k))
          = (fun _ : Equiv.Perm (Fin n) => (1 : ℝ)) := by
        funext π; exact hsum1 π
      rw [hone, fintypeExpect_const Fintype.card_ne_zero]
    calc (∑ k : Fin n, permSendProb i k)
        = ∑ k : Fin n, fintypeExpect (fun π : Equiv.Perm (Fin n) => indicator (π i = k)) := rfl
      _ = fintypeExpect (fun π : Equiv.Perm (Fin n) => ∑ k : Fin n, indicator (π i = k)) :=
            hlin.symm
      _ = 1 := hconst
  -- All point probabilities are equal, hence each is `1/n`.
  have hall : ∀ k : Fin n, permSendProb i k = permSendProb i i := fun k =>
    permSendProb_eq i k i
  have hcollapse : (∑ k : Fin n, permSendProb i i) = 1 := by
    rw [← hsumProb]
    exact Finset.sum_congr rfl (fun k _ => (hall k).symm)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hcollapse
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgoal : permSendProb i i = 1 / (n : ℝ) := by
    rw [eq_div_iff hn', mul_comm]
    exact hcollapse
  exact hgoal

/--
**Hat-check problem (CLRS §5.2, eq. (5.2)).**  The expected number of customers
who get their own hat back — equivalently, the expected number of fixed points
of a uniform random permutation of {lit}`Fin n` — equals exactly {lit}`1`, for
every {lit}`n ≥ 1`, independent of {lit}`n`.

This is the paradigmatic application of **linearity of expectation**: the number
of fixed points is the sum {lit}`∑ i, indicator (π i = i)` of {lit}`n` indicator
random variables, each with expectation {lit}`1/n` by {lit}`probFixesPoint`, and
{lit}`fintypeExpect_sum` sums the expectations to {lit}`n · (1/n) = 1`.
-/
theorem expectedFixedPoints_eq_one {n : ℕ} (hn : 0 < n) :
    fintypeExpect (fun π : Equiv.Perm (Fin n) => ∑ i : Fin n, indicator (π i = i)) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [fintypeExpect_sum Finset.univ
    (fun (i : Fin n) (π : Equiv.Perm (Fin n)) => indicator (π i = i))]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => probFixesPoint i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Chapter05
end CLRS
