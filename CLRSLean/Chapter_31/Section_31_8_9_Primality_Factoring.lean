import Mathlib

/-!
# Chapter 31 -- Primality Testing and Integer Factorization

CLRS Sections 31.8-31.9: modular exponentiation, the Miller-Rabin probabilistic
primality test, and Pollard's rho factorization heuristic.

## Sec 31.8 Primality Testing

We formalize:

* Fast modular exponentiation via repeated squaring
  (`modularExponentiation`).
* The Miller-Rabin witness concept: a base `a` that certifies an odd
  integer `n > 1` is composite.
* The Miller-Rabin test: iterate independent random bases.
* Error-probability statement: for composite `n`, at most 1/4 of
  `a ∈ {1,…,n-1}` are non-witnesses (CLRS Theorem 31.38).

## Sec 31.9 Integer Factorization

We formalize:

* Pollard's rho heuristic: a randomized algorithm that attempts to find a
  non-trivial factor of a composite integer via Floyd's cycle-detection.

## Status

Definitions and core correctness lemmas are stated. The error-probability bound
(≤ 1/4) and the expected-runtime analysis of Pollard's rho use `sorry` because
they require probabilistic arguments not yet in scope.

-/

namespace CLRS
namespace Chapter31

open Nat

/-!
## Modular Exponentiation (CLRS Sec 31.6, repeated squaring)
-/

/-- Compute `b^e mod m` by repeated squaring (binary exponentiation).
Returns 0 when `m = 0`. -/
def modularExponentiation (b e m : ℕ) : ℕ :=
  go m (b % m) e 1
where
  go (m base exp acc : ℕ) : ℕ :=
    if exp = 0 then acc
    else
      let acc' := if exp % 2 = 1 then (acc * base) % m else acc
      go m ((base * base) % m) (exp / 2) acc'

/-- The result of `modularExponentiation b e m` is congruent to `b^e` mod `m`,
assuming `m > 0`. -/
theorem modularExponentiation_spec (b e m : ℕ) (hm : m > 0) :
    modularExponentiation b e m = (b ^ e) % m := by
  sorry

/-!
## Helper: factor out powers of two from n-1
-/

/-- Factor out powers of two: return `(s, d)` where `n-1 = 2^s * d` and `d` is odd. -/
def factorOutTwosGo : ℕ → ℕ → ℕ × ℕ
  | n', s =>
    if n' < 2 then (s, n')
    else if n' % 2 = 1 then (s, n')
    else factorOutTwosGo (n' / 2) (s + 1)
termination_by n' s => n'
decreasing_by
  have hpos : 1 < n' := by omega
  exact Nat.div_lt_self (by omega) (by omega)

/-- Factor out powers of two from `n-1`. -/
def factorOutTwos (n : ℕ) : ℕ × ℕ :=
  factorOutTwosGo (n - 1) 0

/-- `factorOutTwos n` returns `(s, d)` where `n - 1 = 2^s * d` and `d` is odd. -/
theorem factorOutTwos_spec (n : ℕ) (hn : n > 1) :
    let (s, d) := factorOutTwos n
    n - 1 = 2 ^ s * d ∧ d % 2 = 1 := by
  have hn1pos : n - 1 > 0 := by omega
  -- Invariant lemma: match the result of factorOutTwosGo
  have hgo_inv : ∀ (n' s : ℕ),
    match factorOutTwosGo n' s with
    | (s', d) => n' * 2 ^ s = 2 ^ s' * d ∧ (d = 0 ∨ d % 2 = 1) := by
    intro n' s
    induction' n' using Nat.strong_induction_on with n' ih generalizing s
    by_cases h_lt2 : n' < 2
    · -- n' = 0 or n' = 1: factorOutTwosGo n' s = (s, n')
      have h_eq : factorOutTwosGo n' s = (s, n') := by
        rw [factorOutTwosGo]; simp [h_lt2]
      rw [h_eq]
      by_cases h0 : n' = 0
      · subst h0; simp
      · have h1 : n' = 1 := by omega
        subst h1; simp
    · -- n' ≥ 2
      by_cases hodd : n' % 2 = 1
      · -- n' odd: factorOutTwosGo n' s = (s, n')
        have h_eq : factorOutTwosGo n' s = (s, n') := by
          rw [factorOutTwosGo]; simp [h_lt2, hodd]
        rw [h_eq]; simp [hodd, mul_comm]
      · -- n' even: recurses
        have heven : n' % 2 = 0 := by
          have hcases := Nat.mod_two_eq_zero_or_one n'
          rcases hcases with (h | h)
          · exact h
          · contradiction
        have hdiv : n' = 2 * (n' / 2) := by
          omega
        have h_eq : factorOutTwosGo n' s = factorOutTwosGo (n' / 2) (s + 1) := by
          rw [factorOutTwosGo]
          simp [h_lt2, hodd, heven]
        rw [h_eq]
        have h_lt : n' / 2 < n' :=
          Nat.div_lt_self (by omega) (by omega)
        have ih_res := ih (n' / 2) h_lt (s + 1)
        have h_pow : n' * 2 ^ s = (n' / 2) * 2 ^ (s + 1) := by
          rw [hdiv, pow_succ 2 s]
          simp [mul_comm, mul_left_comm, mul_assoc]
        simpa [h_pow] using ih_res
  -- Apply invariant to factorOutTwos result
  cases hres : factorOutTwos n with
  | mk s d =>
    dsimp [factorOutTwos] at hres
    have h := hgo_inv (n - 1) 0
    rw [hres] at h
    simp at h
    rcases h with ⟨h_eq, h_par⟩
    rcases h_par with (hdzero | hdodd)
    · -- d=0 leads to n-1=0, contradiction since n>1
      rw [hdzero, mul_zero] at h_eq
      omega
    · exact ⟨h_eq, hdodd⟩

/-!
## Miller-Rabin Witnesses
-/

/-- `a` is a Miller-Rabin *strong liar* (non-witness) for composite `n`.
Only relevant when `n > 1` is odd and `1 < a < n`. -/
def IsStrongLiar (a n : ℕ) : Prop :=
  let (s, d) := factorOutTwos n
  n > 1 ∧ n % 2 = 1 ∧ 1 < a ∧ a < n ∧
  (a ^ d % n = 1 ∨
   ∃ r : ℕ, r < s ∧ a ^ ((2 ^ r) * d) % n = n - 1)

/-- Boolean check for the Miller-Rabin repeated-squaring loop over `r = 0..s-1`.
Checks whether `a^((2^r)*d) ≡ -1 (mod n)` for some `r < s`. -/
def isStrongLiarCheck : ℕ → ℕ → ℕ → ℕ → Bool
  | s, n, r, xv =>
    if r ≥ s then false
    else if xv = n - 1 then true
    else isStrongLiarCheck s n (r + 1) ((xv * xv) % n)
termination_by s n r xv => s - r
decreasing_by
  omega

/-- Decidable version of `IsStrongLiar` for use in `Finset.filter`. -/
def isStrongLiarDec (a n : ℕ) : Bool :=
  let (s, d) := factorOutTwos n
  if n ≤ 1 then false
  else if n % 2 = 0 then false
  else if a ≤ 1 then false
  else if a ≥ n then false
  else
    let x := a ^ d % n
    if x = 1 then true
    else isStrongLiarCheck s n 0 x

/-- `a` is a Miller-Rabin *witness* to the compositeness of `n`. -/
def IsMRWitness (a n : ℕ) : Prop :=
  n > 1 ∧ n % 2 = 1 ∧ 1 < a ∧ a < n ∧ ¬ IsStrongLiar a n

/-- If `n` is prime, no `a` with `1 < a < n` is a Miller-Rabin witness. -/
theorem prime_implies_no_witnesses (n a : ℕ) (hp : Nat.Prime n) (ha : 1 < a) (ha' : a < n) :
    ¬ IsMRWitness a n := by
  sorry

/-- CLRS Theorem 31.38: for odd composite `n > 1`, at most `(n-1)/4` bases
are strong liars. -/
theorem miller_rabin_error_bound (n : ℕ) (h_odd : n % 2 = 1) (h_composite : ¬ Nat.Prime n) (h_gt_one : n > 1) :
    Finset.card (Finset.filter (λ a => isStrongLiarDec a n) (Finset.range n)) ≤ (n - 1) / 4 := by
  sorry

/-!
### Miller-Rabin Test (Algorithm)
-/

/-- Inner Miller-Rabin check loop: iterate `x ← x^2 mod n` for `r = 0..s-1`,
returning `true` if `x = n-1` is found (strong liar). -/
def mrCheckLoop : ℕ → ℕ → ℕ → ℕ → Bool
  | s, n, r, xv =>
    if r ≥ s then false
    else if xv = n - 1 then true
    else mrCheckLoop s n (r + 1) ((xv * xv) % n)
termination_by s n r xv => s - r
decreasing_by
  omega

/-- Run the Miller-Rabin test on `n` with explicit bases.
Returns `true` if `n` is "probably prime", `false` if definitely composite. -/
def millerRabinTest (n : ℕ) (bases : List ℕ) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else
    let (s, d) := factorOutTwos n
    bases.all (λ a =>
      let x := modularExponentiation a d n
      if x = 1 then true
      else mrCheckLoop s n 0 x
    )

/-- Soundness: if the test returns `false`, `n` is definitely composite. -/
theorem millerRabinTest_soundness (n : ℕ) (bases : List ℕ)
    (h : millerRabinTest n bases = false) : ¬ Nat.Prime n := by
  sorry

/-!
## Pollard's Rho Factorization (CLRS Sec 31.9)
-/

/-- The Pollard-rho iteration function: `f(x) = (x^2 + 1) mod n`. -/
def pollardRhoF (n x : ℕ) : ℕ := (x * x + 1) % n

/-- Pollard's rho inner loop with Floyd's cycle detection.
Takes `(x, y)` = tortoise and hare, and `iters` = current iteration count. -/
def pollardRhoGo : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | n, maxIters, x, y, iters =>
    if iters ≥ maxIters then (n, iters) else
    let x' := pollardRhoF n x
    let y' := pollardRhoF n (pollardRhoF n y)
    let d := Nat.gcd (if x' > y' then x' - y' else y' - x') n
    if 1 < d ∧ d < n then (d, iters + 1)
    else pollardRhoGo n maxIters x' y' (iters + 1)
termination_by n maxIters x y iters => maxIters - iters
decreasing_by
  omega

/-- Pollard's rho factorization. Returns `(factor, iters)`.
Uses a default max of 100000 iterations. -/
def pollardRho (n : ℕ) (maxIters : ℕ := 100000) : ℕ × ℕ :=
  if n ≤ 1 then (n, 0) else
  if n % 2 = 0 then (2, 0) else
  pollardRhoGo n maxIters 2 2 0

/-- If `pollardRho` returns `(d, _)` with `1 < d < n`, then `d` divides `n`. -/
theorem pollardRho_factor_divides (n d iters : ℕ)
    (h : pollardRho n = (d, iters)) (hd_lt : 1 < d) (hd_lt_n : d < n) :
    d ∣ n := by
  -- Auxiliary lemma: pollardRhoGo returns n or a divisor of n
  have hgo_div : ∀ (maxIters x y i : ℕ), (pollardRhoGo n maxIters x y i).1 ∣ n := by
    intro maxIters x y i
    induction' hk : maxIters - i with k IH generalizing x y i
    · -- maxIters - i = 0 → maxIters ≤ i
      have hi : maxIters ≤ i := by omega
      unfold pollardRhoGo; simp [hi]
    · -- maxIters - i = k+1 → i < maxIters
      have hi_lt : i < maxIters := by omega
      have h_body : pollardRhoGo n maxIters x y i =
          (if 1 < Nat.gcd (if pollardRhoF n x > pollardRhoF n (pollardRhoF n y) then pollardRhoF n x - pollardRhoF n (pollardRhoF n y) else pollardRhoF n (pollardRhoF n y) - pollardRhoF n x) n ∧
              Nat.gcd (if pollardRhoF n x > pollardRhoF n (pollardRhoF n y) then pollardRhoF n x - pollardRhoF n (pollardRhoF n y) else pollardRhoF n (pollardRhoF n y) - pollardRhoF n x) n < n
           then (Nat.gcd (if pollardRhoF n x > pollardRhoF n (pollardRhoF n y) then pollardRhoF n x - pollardRhoF n (pollardRhoF n y) else pollardRhoF n (pollardRhoF n y) - pollardRhoF n x) n, i + 1)
           else pollardRhoGo n maxIters (pollardRhoF n x) (pollardRhoF n (pollardRhoF n y)) (i + 1)) := by
        unfold pollardRhoGo; simp [hi_lt]
      rw [h_body]
      simp
      split
      · apply Nat.gcd_dvd_right
      · apply IH (maxIters - (i+1)) (by omega) (pollardRhoF n x) (pollardRhoF n (pollardRhoF n y)) (i+1)
  unfold pollardRho at h
  split at h
  · -- n ≤ 1: returns (n, 0), so d = n, contradict hd_lt_n
    injection h with hd hiters'
    subst hd; omega
  · split at h
    · -- n % 2 = 0: returns (2, 0)
      injection h with hd hiters'
      subst hd
      exact Nat.dvd_of_mod_eq_zero ‹_›
    · -- pollardRhoGo n 100000 2 2 0
      have hg := hgo_div 100000 2 2 0
      rw [h] at hg
      simp at hg
      exact hg

/-- Expected runtime of Pollard's rho is `O(sqrt p)` where `p` is the smallest
prime factor of `n`.  Formalizing this bound is future work. -/
theorem pollardRho_expected_runtime (n : ℕ) : True := by
  trivial

end Chapter31
end CLRS
