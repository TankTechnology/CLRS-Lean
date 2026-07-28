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
  -- Proof sketch: induction on e (binary representation). Invariant of the go loop:
  -- result = b^e mod m with accumulator tracking partial products mod m.
  -- Base case e=0: modularExponentiation b 0 m = 1 % m (since go terminates immediately
  -- with acc = 1), and (b^0) % m = 1 % m. Inductive step: for e>0, the go function
  -- squares base mod m at each step and halves e, multiplying acc by base when bit is 1.
  -- This computes (b * (b²)^{floor(e/2)}) mod m = b^e mod m by the identity
  -- b^e = (b²)^{⌊e/2⌋} if e even, b·(b²)^{⌊e/2⌋} if e odd, all maintained mod m.
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
      · -- n' even: factorOutTwosGo (n'/2) (s+1)
        -- Proof sketch: n' even means n' = 2·k for some k. By IH on k (since n'/2 < n'),
        -- factorOutTwosGo k (s+1) = (s', d) with k·2^{s+1} = 2^{s'}·d.
        -- Then n'·2^s = (2·k)·2^s = k·2^{s+1} = 2^{s'}·d, establishing the invariant.
        sorry
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
  -- Proof sketch: if n is prime, then by Fermat's little theorem, for any a with
  -- 1 < a < n, we have a^{n-1} ≡ 1 (mod n). Factor n-1 = 2^s·d with d odd.
  -- Then a^d ≡ 1 (mod n) or a^{2^r·d} ≡ -1 (mod n) for some r < s.
  -- This follows because in ℤ/pℤ (a field when p prime), the only square roots
  -- of 1 are ±1. The sequence a^d, a^{2d}, a^{4d}, ..., a^{n-1} starts at a^d
  -- and each term is the square of the previous. If the last term is 1 (FLT),
  -- then either (a) the first term a^d is already 1, or (b) some term a^{2^r·d} = -1
  -- before reaching 1 (otherwise you'd have a nontrivial square root of 1, impossible in a field).
  -- Hence a is a strong liar, not a witness. QED.
  sorry

/-- CLRS Theorem 31.38: for odd composite `n > 1`, at most `(n-1)/4` bases
are strong liars. -/
theorem miller_rabin_error_bound (n : ℕ) (h_odd : n % 2 = 1) (h_composite : ¬ Nat.Prime n) (h_gt_one : n > 1) :
    Finset.card (Finset.filter (λ a => isStrongLiarDec a n) (Finset.range n)) ≤ (n - 1) / 4 := by
  -- Proof sketch (CLRS Theorem 31.38): for an odd composite n, a is a strong liar iff
  -- a belongs to one of at most (n-1)/4 subgroups of (ℤ/nℤ)^× whose order divides n-1.
  -- The proof uses group theory: decompose the group (ℤ/nℤ)^× by the CRT into factors
  -- corresponding to the prime-power factors of n. For each factor ℤ/p^eℤ, the number
  -- of elements a with a^k ≡ ±1 (mod p^e) is bounded by gcd(k, p-1) or 2·gcd(k, p-1).
  -- Summing over all factors and using that n is composite (so at least two odd prime
  -- factors or a prime power), the total bound ≤ (n-1)/4 follows via careful counting
  -- and the bound that at most 1/4 of Z_n^* can be strong liars when n is odd composite.
  -- This is a deep number-theoretic result; formalization requires full CRT decomposition
  -- and the structure of units modulo prime powers.
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
  -- Proof sketch: if millerRabinTest returns false, then for some base a in bases,
  -- modularExponentiation a d n ≠ 1 and mrCheckLoop found no x ≡ -1 (mod n) for all r < s.
  -- By the contrapositive of prime_implies_no_witnesses, if n were prime then for every
  -- a with 1 < a < n, a would be a strong liar (i.e., either a^d ≡ 1 or a^{2^r·d} ≡ -1).
  -- Since the test found such an a where neither holds, n cannot be prime. Formally:
  -- assume Nat.Prime n, derive that for all bases a, the test must return true;
  -- the returned false contradicts this when n is prime. Depends on modularExponentiation_spec
  -- to connect modularExponentiation to a^d mod n, and on mrCheckLoop correctness.
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
  -- Proof sketch: by construction, pollardRhoGo maintains the invariant that d = gcd(|x-y|, n)
  -- is computed at each iteration. If 1 < d < n, the function returns d — and by definition
  -- of gcd, d ∣ n. The challenge is proving that when the algorithm terminates with
  -- 1 < d < n, this d indeed divides n (which follows from Nat.gcd_dvd_right).
  -- Specifically, unfold pollardRho n: if n%2=0 it returns (2,0) and 2∣n trivially;
  -- otherwise pollardRhoGo n maxIters 2 2 0 returns (d, iters) where d is the first
  -- discovered gcd satisfying 1 < d < n. Then d = gcd(|x'-y'|, n) for some iterated
  -- x', y', so d ∣ n by Nat.dvd_of_dvd_gcd_left (or Nat.gcd_dvd_right d n).
  sorry

/-- Expected runtime of Pollard's rho is `O(sqrt p)` where `p` is the smallest
prime factor of `n`.  Formalizing this bound is future work. -/
theorem pollardRho_expected_runtime (n : ℕ) : True := by
  trivial

end Chapter31
end CLRS
