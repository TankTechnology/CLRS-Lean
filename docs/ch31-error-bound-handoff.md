# ch31 Error-Bound Handoff — Miller-Rabin (Theorem 31.39)

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
`#{a ∈ (Z/nZ)ˣ : strongPseudoprime n a} ≤ (n−1)/4`.

> ⚠️ **CORRECTION (verified 2026-08-05): do NOT target `≤ Nat.totient n / 4`.**
> It is FALSE for `n = 9`: liars(9) = {1, 8}, |L| = 2 > φ(9)/4 = 6/4 = 1.
> The `(n−1)/4` form holds for all odd composite `n` (n=9 gives equality:
> 2 ≤ 8/4).  Rationale: φ(n)/4 fails exactly when the "good subgroup"
> index is 3, which happens only for `n = 3²` (see Milestone 4 notes).
> Since `φ(n) ≤ n−1`, bounding by `(n−1)/4` is the right, exception-free
> target and is strictly stronger than CLRS Theorem 31.39 (witnesses ≥ (n−1)/2).

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

- `Nat.card (ZMod n)ˣ = Nat.totient n` is NOT a named lemma
  (`Nat.card_units_zmod` does not exist), but the pieces exist:
  `Nat.card_units [GroupWithZero α]`, `Nat.totient` is
  `φ n = #{a ∈ range n | n.Coprime a}` (so prove units of `ZMod n` ≃ coprime
  elements of `{0,…,n−1}`).

> ✅ **UPDATE (verified 2026-08-05) — the two big gaps are CLOSED in Mathlib:**
>
> 1. **`(Z/p^e)ˣ` cyclicity for odd prime powers IS in Mathlib.**
>    `RingTheory/ZMod/UnitsCyclic.lean` (added 2025, after this handoff was
>    written):
>    - `ZMod.isCyclic_units_of_prime_pow (p) (hp : p.Prime) (hp2 : p ≠ 2) (e : ℕ) :
>      IsCyclic (ZMod (p ^ e))ˣ`
>    - `ZMod.isCyclic_units_prime (p) (hp : p.Prime) : IsCyclic (ZMod p)ˣ`
>    - `ZMod.orderOf_one_add_mul_prime`, `ZMod.orderOf_five` (for `2^n`)
>    **No Hensel lifting needed.**  Milestone-3 per-prime-power counts can use
>    cyclicity of `(Z/p^e)ˣ` directly.
>
> 2. **`ZMod.card_units_eq_totient (n) [NeZero n] [Fintype (ZMod n)ˣ] :
>    Fintype.card (ZMod n)ˣ = φ n`** exists (`Data/Nat/Totient.lean`).  So
>    `Nat.card (ZMod n)ˣ = φ n` is one `Nat.card_eq_fintype_card` step away.
>    (Note: `Fintype (ZMod n)ˣ` is NOT an automatic instance — add
>    `letI := Fintype.ofFinite (ZMod n)ˣ` or prove it; `ZMod n` needs
>    `[NeZero n]` for `.val` and `Fintype`.)
>
> 3. **Verified counting formulas** (re-derived and checked on n = 9, 15, 25,
>    65, 561):
>    - `|S(n)| = 2^(k(ν−1)+1) · ∏ gcd(t, d_i)` where `p_i − 1 = 2^(s_i)·d_i`
>      (d_i odd), `k` = # distinct prime factors.  The handoff's original
>      formula was correct — a naive re-count that mixed the "≡ 1" and "≡ −1"
>      CRT components over-counted; the `±1` is a *global* condition mod n, so
>      S splits into the all-`+1` part and all-`−1` part, each a product over
>      prime powers of the single-congruence count `#(x^m ≡ ε mod p^e) =
>      gcd(m, φ(p^e))`.
>    - Exact liar count `|L| = G · (1 + 2^k + … + 2^(k(ν−1))) =
>      G · (2^(kν)−1)/(2^k−1)`, `G = ∏ gcd(t, d_i)`; each "≡ −1 at index i"
>      set has size `G·2^(ki)` for `i < ν`, and 0 for `i ≥ ν`.
>    - `|S(n)| ≤ (n−1)/4` for ALL odd composite n (the three-case analysis of
>      Milestone 4; k=1 gives |S| = 2^ν·gcd(t,d) ≤ p−1 ≤ (p^e−1)/4; k=2 uses
>      the `q′ ∤ t ⟹ q′/gcd(t,q′) ≥ 3` parity step; k≥3 is easy via
>      `∏(p_i−1) ≤ (n−1)/2`).

**Suggested milestone order (revised, 2026-08-05):**

0. **DONE (Mathlib)** — cyclicity of `(Z/p)ˣ` *and* `(Z/p^e)ˣ` (odd prime
   powers), plus `ZMod.card_units_eq_totient`.  No Hensel, no primitive-root
   proof needed.
1. **Milestone 1 — ν(n) and S(n)**: define `ν(n)` (min over prime factors of
   `v_2(p−1)`), define `S(n)` in `(ZMod n)ˣ`, prove **S is a subgroup**.
2. **Milestone 2 — L ⊆ S**: every strong liar lies in `S(n)` (order-of-element
   argument mod each prime divisor; `strongPseudoprime_pow` already proved).
3. **Milestone 3 — |S| counting**: `|S(n)| = 2^(k(ν−1)+1) · ∏ gcd(t, d_i)` via
   CRT + cyclicity of `(Z/p^e)ˣ`.  The single-congruence count
   `#(x^m ≡ ε mod p^e) = gcd(m, φ(p^e))` in a cyclic group is NOT in Mathlib
   (`IsCyclic.card_pow_eq_one_le` only gives `≤ n`) — write it
   (`Nat.card {x : α // x^n = 1} = Nat.gcd n (Fintype.card α)`, via
   `IsCyclic.image_range_card` + generator parametrization).
4. **Milestone 4 — three-case bound**: prove `|S| ≤ (n−1)/4` (NOT `≤ φ(n)/4`,
   which fails at n=9): k≥3 easy; k=2 parity case (`q′ ∤ t ⟹ ≥ 3`); k=1 via
   `p−1 ≤ (p^e−1)/4`.

## Concrete attack order (next session)

> **Milestones 1–3 are DONE (committed on `feat/ch31-refinements`).**
> Remaining: **Milestone 4 only** — the three-case arithmetic bound.

### Milestone 4 — the three-case bound (the only remaining work)

Everything is in place except the final arithmetic.  The available lemmas
(31.8) give, for `m = 2^(ν(n)−1)·t` (`t` odd), `k = n.primeFactors.card`:

- `goodSet_card_le`: `|S(n)| ≤ 2·|{x : x^m = 1}|` (the "≡ −1" part is a fiber).
- `mTorsion_le_prod_half`: `|{x : x^m = 1}| ≤ ∏_{p|n} (p−1)/2`.
- So **`|S(n)| ≤ 2^(1−k)·∏_{p|n} (p−1)`**, and the target is
  `2·∏ (p−1)/2 ≤ (n−1)/4`.

**Cases** (verify the arithmetic, then formalize):

- **k ≥ 3**: `∏(p−1) ≤ n−1` (each `p−1 < p`, `∏p ≤ n`) and `2^(1−k) ≤ 1/4`.  Easy.
- **k = 1** (`n = p^e`): `|S| ≤ 2·(p−1)/2 = p−1 ≤ (p^e−1)/4` (uses `e ≥ 2`, `p ≥ 3`).  Easy.
- **k = 2** (`n = pq`, `s = v₂(p−1)`, `r = v₂(q−1)`, `ν = min(s,r)`):
  `|S| = 2·gcd(m,p−1)·gcd(m,q−1) ≤ 2^(2ν−1)·gcd(t,d_p)·gcd(t,d_q)`.
  - **Sub-case s < r** (ν = s): `|S| ≤ 2^(2ν−1)·d_p·d_q`, and
    `pq−1 ≥ 2^(s+r)d_p·d_q ≥ 2^(2ν+1)d_p·d_q`, so `|S| ≤ (pq−1)/4`.  Easy —
    no `d/gcd` analysis needed.
  - **Sub-case s = r = ν**: `d_p | t` and `d_q | t` both ⟹ `d_p = d_q` ⟹ `p = q`
    (contradiction), so at least one of `gcd(t,d_p)`, `gcd(t,d_q)` is `≤ d/3`
    (odd, proper divisor).  Then `|S| ≤ 2^(2ν−1)·d_p·d_q/3` and
    `pq−1 ≥ 2^(2ν)·d_p·d_q`, giving `|S| ≤ (pq−1)/4`.
  - Key sub-lemma to prove: **`d_p | t ∧ d_q | t ⟹ d_p = d_q`** for `n = pq`
    (from `t = (pq−1)/2^v`, `pq−1 = 2^(s+r)d_p d_q + 2^s d_p + 2^r d_q`,
    divisibility of `t` by `d_p` forces `d_p | d_q`).

**Wrap-up after Milestone 4**: update `docs/clrs-proof-progress.csv` (bump
tracked count), `docs/proof-map.md`, chapter guide `CLRSLean/Chapter_31.lean`
(remove the deferred item), regenerate `CLRSLean/Progress.lean`, run
`check_repository.py`, then the PR.
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
