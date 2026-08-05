# ch31 Error-Bound Handoff — Miller-Rabin (Theorem 31.8)

This document hands off the state and the verified roadmap for the **last
remaining hard theorem in Chapter 31**: the Miller-Rabin error bound (Rabin-
Monier: for odd composite `n`, at most `φ(n)/4` of the bases are strong
liars).  A fresh session should read this, then start attacking.

## Session context

- **Branch**: `feat/ch31-refinements` (already has all work below).
- **Working tree**: clean; every commit kernel-checked (`#print axioms` shows
  only `propext` / `Classical.choice` / `Quot.sound`, no `sorryAx`).
- **Repo checks**: `uv run python scripts/check_repository.py` passes; full
  `lake build CLRSLean` passes (8900 jobs).

### What is complete (committed)

| commit | content |
|--------|---------|
| `3fd0f17` | docs sync for general CRT / RSA (bookkeeping) |
| `9dce175` | **31.2 Lamé running-time analysis** complete (`euclidDivisions`, Lemma 31.10 `fib_le_of_euclidDivisions`, Thm 31.11 `euclidDivisions_lt`, Cor 31.12 `euclidDivisions_le_two_log`, plus `fib_two_step_ge_pow_two`, `pow_two_le_fib`) |
| `41fcc00` | **31.8 Carmichael numbers** (`isCarmichael`, `carmichael_fermatPseudoprime`, `isCarmichael_561`, helper `modeq_of_coprime_mul`) |
| `88fce0d` | **31.8 Miller-Rabin definitions** (`strongTestParams`, `strongPseudoprime`, `Witness`, `millerRabin`, `instDecidableStrongPseudoprime`) |
| `9ebf427` | **31.8 Miller-Rabin correctness** (`strongTestParams_spec`, `modeq_neg_one_of_sq_eq_one`, `strongPseudoprime_of_prime`, `not_witness_of_prime`, `witness_not_prime`) |
| `dfa14eb` | **31.9 full POLLARD-RHO** (`RhoState`, `pollardStep`, `pollardRhoLoop`, `pollardRho`, `pollardRho_sound`, `rho_collision_factor_dist`, `pollardStep_collision_factor`) |
| `005a7d2` | **31.8 error-bound foundation** (`strongPseudoprime_pow`: a strong pseudoprime satisfies `a^(n−1) ≡ 1 [MOD n]`; `modeq_pow_two_sub_one`) |

Progress CSV: `docs/clrs-proof-progress.csv` row 31 is `selected-section-complete`,
27/27 tracked theorems proved.  The only remaining deferred item of substance
is the error bound (the birthday-paradox heuristic for POLLARD-RHO is
documented as informal in CLRS and intentionally left unformalized).

## The error bound — verified roadmap

**Statement to prove** (`CLRS.Chapter31`): for odd composite `n`,
`#{a ∈ (Z/nZ)ˣ : strongPseudoprime n a} ≤ Nat.totient n / 4`
(or the CLRS form `≤ (n−1)/4`).

### ⚠️ Verified negative result (do NOT waste time on this)

Strong liars **do NOT form a subgroup of `(Z/nZ)ˣ`** in general.  Brute-force
verification (`#eval`, checked closure over all units) found counterexamples:
`n = 65, 85, 145, 185` (all with ≥ 2 distinct prime factors).  Prime powers
(9, 25, 27, 49, …) DO pass the subgroup check (cyclic unit group).  So any
"liars form a subgroup" argument is only valid for the `n = p^e` case.

### The correct structure (Rabin 1980 / Monier 1980)

Let `n − 1 = 2^s · t` with `t` odd, and let `n = ∏ p_i^{e_i}`.  Define

**ν(n) = max{ v : 2^v divides (p_i − 1) for every prime factor p_i of n }**
(the minimum over prime factors of the 2-adic valuation of `p_i − 1`).

Define the **good subgroup**

**S(n) = { x ∈ (Z/nZ)ˣ : x^(2^(ν(n)−1)·t) ≡ ±1 (mod n) }.**

Then:

1. **S(n) is a subgroup** — it is the union of the kernel of
   `x ↦ x^(2^(ν−1)·t) − 1`-style preimages of `{1}` and `{−1}` (preimage of a
   subgroup under a homomorphism), so it is a subgroup.
2. **Every liar lies in S(n)** — if `x^t ≡ 1` then `x^(2^(ν−1)·t) ≡ 1`; if
   `x^(2^i·t) ≡ −1` for some `i < s`, then `x^(2^(i+1)·t) ≡ 1`, and the order
   of `x` mod each prime `p_i` is a multiple of `2^(i+1)` (because
   `x^(2^i·t)` has order exactly 2 = `−1`, and `ord(x) | p_i − 1` by Fermat),
   so `i+1 ≤ ν`, hence `x^(2^(ν−1)·t) = (x^(2^i·t))^(2^(ν−1−i)) ≡ ±1`.
   This is the step that needs the **multiplicative order of elements in
   `(Z/p)ˣ`** (`Nat.orderOf` or the `ZMod` order).
3. **|S(n)| via CRT + cyclicity**: since each `(Z/p_i^{e_i})ˣ` is cyclic (odd
   prime powers), the number of solutions to `x^m ≡ 1 (mod p_i^{e_i})` is
   `gcd(m, φ(p_i^{e_i}))`.  Splitting S into the `≡ 1` and `≡ −1` parts (equal
   size), `|S| = 2 · 2^((ν−1)k) · ∏ gcd(t, φ(p_i^{e_i}))` for `k` prime
   factors.
4. **Three-case bound `|S| ≤ φ(n)/4`**:
   - **≥ 3 prime factors**: `φ(n)/|S| ≥ 8`.
   - **`n = pq` (p < q)**: hardest case (parity/manipulation of `n−1 = pq−1`);
     uses `q′ ∤ t` forcing `q′/gcd(t,q′) ≥ 3`.
   - **`n = p²`**: `φ(n)/|S| = p(p−1)/(2^ν·gcd(t,p−1)) ≥ 5` for `p > 3`
     (n = 9 is the exceptional case, ratio 3, handled directly).
5. **Conclusion**: `|liars| ≤ |S| ≤ φ(n)/4 ≤ (n−1)/4`.

Sources: Rabin (1980) J. Number Theory 12(1) 128–138; Monier (1980) TCS
12(1) 97–108.  Expositions: Codeforces blog by randop; Androma theorem
page #1770.

## Milestone 0 findings (verified this session — de-risks the attack)

**Cyclicity of `(Z/p)ˣ` for prime `p` IS available in Mathlib — for free.**

- `example (p) [Fact (Nat.Prime p)] : IsCyclic (ZMod p)ˣ := by infer_instance`
  works (compiles).  `ZMod p` is a finite field, and Mathlib's
  `Mathlib/FieldTheory/Finite/Basic.lean` provides cyclicity of the unit group
  of a finite field.
- Generator: `IsCyclic.exists_generator (α := (ZMod p)ˣ)` gives
  `∃ g, ∀ x, x ∈ Subgroup.zpowers g` (every unit is a power of `g`).
- `orderOf g = Nat.card (ZMod p)ˣ` via
  `orderOf_eq_card_of_forall_mem_zpowers hx`.

**Gaps that remain:**

- `(Z/p^e)ˣ` cyclicity (primitive roots mod odd prime powers, e ≥ 2) is NOT
  in Mathlib (`ZMod p^e` is not a field, so the finite-field theorem does not
  apply).  This is needed for the prime-power count
  `|{x ∈ (Z/p^e)ˣ : x^m = 1}| = gcd(m, φ(p^e)) = gcd(m, p−1)`.
  Two options: (a) prove primitive roots mod odd prime powers (classical,
  substantial); or (b) **avoid it via a Hensel-style lifting argument**: for
  `m` coprime to `p`, the number of solutions to `x^m ≡ 1 (mod p^e)` equals
  the number mod `p` (unique lift), reducing to `(Z/p)ˣ` which IS cyclic.
- `Nat.card (ZMod n)ˣ = Nat.totient n` is NOT a named lemma
  (`Nat.card_units_zmod` does not exist), but the pieces exist:
  `Nat.card_units [GroupWithZero α]`, `Nat.totient` is
  `φ n = #{a ∈ range n | n.Coprime a}` (so prove units of `ZMod n` ≃ coprime
  elements of `{0,…,n−1}`).

**Suggested milestone order (revised):**

0. Cyclicity of `(Z/p)ˣ` — DONE (Mathlib instance).  Set up the generator +
   order + `Nat.card (ZMod n)ˣ = φ(n)` bridge lemmas in 31.8.
1. Decide prime-power strategy: (a) prove `(Z/p^e)ˣ` cyclic, or (b) the
   Hensel-lifting reduction.  Either is a substantial sub-battle.
2. ν(n), S(n), S is a subgroup, L ⊆ S.
3. |S| counting via CRT + the p-cyclic counts.
4. Three-case bound ≤ φ(n)/4.

## Concrete attack order (next session)

1. **Milestone 0 — infrastructure**: explore and, if needed, prove
   cyclicity of `(Z/p)ˣ` (units mod a prime form a cyclic group).  This is
   the foundation everything else needs.
2. **Milestone 1 — ν(n) and S(n)**: define `ν(n)` (min over prime factors of
   `v_2(p−1)`, via `Nat.factorization`), define `S(n)` in `(ZMod n)ˣ`, prove
   **S is a subgroup**.
3. **Milestone 2 — L ⊆ S**: prove every strong liar is in `S(n)`, using
   `strongPseudoprime_pow` (already proved) and the order-of-element argument
   modulo each prime divisor.
4. **Milestone 3 — |S| counting**: via CRT and cyclicity, prove
   `|S| = 2 · 2^((ν−1)k) · ∏ gcd(t, φ(p_i^{e_i}))`.
5. **Milestone 4 — three-case bound**: prove `|S| ≤ φ(n)/4` (or `≤ (n−1)/4`)
   in the three cases.
6. **Wrap-up**: update `docs/clrs-proof-progress.csv` (bump tracked count,
   move `isCarmichael`-era note), `docs/proof-map.md`, chapter guide
   `CLRSLean/Chapter_31.lean` (remove the deferred item), regenerate
   `CLRSLean/Progress.lean`, run `check_repository.py`, then the PR.

## Key repo facts already in place (reuse these)

In `CLRSLean/Chapter_31/Section_31_8_Primality_Testing.lean`:

- `strongTestParams n : ℕ × ℕ` = `(Nat.factorization (n−1) 2, (n−1)/2^…)`.
- `strongTestParams_spec n (hn : n ≠ 0) : n = 2^(n.factorization 2) * (n / 2^(n.factorization 2))`
  (so `n−1 = 2^s·t`).
- `strongPseudoprime n a` (the liar predicate, `a^d ≡ 1 ∨ ∃ i : Fin s, a^(2^i·d) ≡ n−1`).
- `strongPseudoprime_pow {n a} (h) : a^(n−1) ≡ 1 [MOD n]` (liars ⊆ Fermat kernel).
- `modeq_neg_one_of_sq_eq_one` (prime: `x² ≡ 1, x ≢ 1 → x ≡ −1`).
- `strongPseudoprime_of_prime`, `not_witness_of_prime`, `witness_not_prime`.
- Imports: `Mathlib`, `Section_31_5_Chinese_Remainder_Theorem` (CRT),
  `Section_31_6_Powers_Of_An_Element`.

## Mathlib API discovered (worth re-verifying)

- `Nat.Prime.pow_dvd_iff_le_factorization`, `Nat.mul_div_cancel'`,
  `Nat.ModEq.pow`, `Nat.ModEq.add_right_cancel`, `Nat.modEq_iff_dvd'`,
  `Nat.sq_sub_sq`, `Nat.Prime.dvd_mul`, `Nat.find_spec`/`find_min`/`find_le`,
  `one_le_pow₀`, `Nat.ModEq.refl`, `Nat.sub_add_cancel`.
- `ZMod.natCast_eq_natCast_iff`, `ZMod.intCast_eq_intCast_iff`,
  `sq_eq_one_iff` (fields), `Subgroup.index`, `Subgroup.card_mul_index`.
- `Nat.factorization` works; `Nat.padicValNat` / `Nat.ord_compl` names do NOT
  exist as such.
- **Do NOT use `nlinarith` for `(n−1)^2 = n(n−2)+1`** with `2 ≤ n` (it
  fails); use `Nat.sq_sub_sq` + `omega` instead (as in `modeq_pow_two_sub_one`).

## Deferred / intentionally informal

- POLLARD-RHO birthday-paradox expected-`O(√p)` running time (heuristic in
  CLRS; documented as informal in `Section_31_9_Integer_Factorization.lean`).
