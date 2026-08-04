# Randomized treap: expected-height bound (complete)

Record of completing `E[height] ≤ c · H_n = O(log n)` in
`CLRSLean/Extensions/TreapHeight.lean` (prototype, unregistered in
`literate.toml`).  Completed 2026-08-04 on `feat/extensions`.

## Goal (achieved)

For the uniform random treap on `n` keys (model in `TreapRandom.lean`):

```lean
theorem expectedTreapHeight_le {n : ℕ} :
    expectedTreapHeight (n := n) ≤ 30 * (harmonic n : ℝ)
```

`expectedTreapHeight n = fintypeExpect (fun σ : PrioPerm n => (treapHeight σ : ℝ))`
and `treapHeight σ = (Finset.univ.sup (fun b : Fin n => depth σ b))`.

The route is an **exponential tail on the depth of a single key**, then a union
bound over keys, then a tail sum split at `k ≈ 12 · ⌈H_n⌉`.

## What is proved (kernel-clean, `[propext, Classical.choice, Quot.sound]`)

All in `TreapHeight.lean` unless noted:

- `treapHeight`, `expectedTreapHeight` — the height and its expectation.
- `depth_eq_left_add_right` — `depth σ b = leftAncestors σ b + rightAncestors σ b + 1`.
- `maxExtend_uniform` — nested-max independence: given that all keys of `T`
  are left-ancestors of `b` (each strictly below `c`), the maximum priority of
  `Icc c b` is equally likely to sit at any of its keys.
- `leftAncestors_product` — `P[all keys of S are left-ancestors of b] =
  ∏ a ∈ S, 1/|[a,b]|` (strong induction peeling the largest element).
- `eSymm_le` — `(∑ s ∈ powersetCard k C, ∏ a ∈ s, x a) ≤ (Σ a ∈ C, x a)^k / k!`.
- `leftAncestors_tail` — `P[L(b) ≥ k] ≤ (Σ a, if a<b then 1/|[a,b]| else 0)^k / k!`
  via the union bound over `powersetCard k C` (covered by the product formula)
  and `eSymm_le`.
- `left_sum_le_harmonicReal` — the left interval sum `Σ_{a<b} 1/|[a,b]| ≤ harmonicReal n`,
  so `P[L(b) ≥ k] ≤ (harmonicReal n)^k / k!` and `harmonicReal n = (harmonic n : ℝ)`.

### Step 1 — right-ancestor tail via reflection (done)

- `revCompEquiv` — `σ ↦ σ * Fin.revPerm` is an involution (bijection) on
  `PrioPerm n`.
- `ancestor_rev_perm` — for `b < a`, `Ancestor (σ * Fin.revPerm) (revPerm a) (revPerm b)
  ↔ Ancestor σ a b`.
- `rightAncestors_eq_left_rev` — `rightAncestors σ b = leftAncestors (σ * Fin.revPerm)
  (revPerm b)` (via `Finset.card_nbij` on the reflecting map `a ↦ revPerm a`).
- `leftAncestors_tail_le_harmonic` / `rightAncestors_tail_le_harmonic` —
  `P[L(b) ≥ k] ≤ H_n^k / k!` and `P[R(b) ≥ k] ≤ H_n^k / k!`.
- `harmonic_pow_div_le` (private) — `S ≤ H_n ∧ S ≥ 0 → S^k/k! ≤ H_n^k/k!`.

**Gotchas hit and resolved:**
- `Ancestor` unfolds to `Icc (min a b) (max a b)`; for `b < a` rewrite with
  `min_eq_left`/`max_eq_right` to `Icc b a` on the `σ`-side and `Icc (rev a) (rev b)`
  on the reflected side, then bridge the two `∀`-over-interval conditions by
  `revPerm k ↦ k` reindexing.
- `Fin.revPerm x` is not definitionally `x.rev`; use `simp [Fin.revPerm_apply]`
  (and `Fin.rev_rev`, `inv_pow`).
- `Fin.rev_le_rev`, `Fin.rev_le_iff`, `Fin.le_rev_iff`, `Fin.lt_rev_iff` need
  explicit `(i := ...) (j := ...)` arguments.
- `Fin.revPerm` is injective (`Fin.revPerm.injective`); `Fin.rev_lt_rev` gives
  `rev a < rev b ↔ b < a`.
- `Finset.card_bij` in this Mathlib takes a dependent function; use
  `Finset.card_nbij` for a plain `α → β`.

### Step 2 — depth tail (done)

```lean
lemma depth_tail {n : ℕ} (b : Fin n) (k : ℕ) :
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ depth σ b)) ≤
      2 * (harmonicReal n)^((k - 1) / 2) / (Nat.factorial ((k - 1) / 2) : ℝ)
```

Split: `depth = L + R + 1`, so `depth ≥ k` forces `L ≥ t` or `R ≥ t` with
`t = (k-1)/2` (contrapositive: `L < t ∧ R < t` gives `L+R+1 ≤ 2t-1 ≤ k-1`,
using `2·((k-1)/2) ≤ k`).  Then `P[depth ≥ k] ≤ P[L ≥ t] + P[R ≥ t]`, each
`≤ H_n^t / t!` via the Step-1 tail lemmas.

### Step 3 — expected height (done)

```lean
theorem expectedTreapHeight_le {n : ℕ} :
    expectedTreapHeight (n := n) ≤ 30 * (harmonic n : ℝ)
```

- `depth_le_n`, `treapHeight_le_n` — `depth σ b ≤ n`, `treapHeight σ ≤ n`.
- `nat_eq_sum_indicator` (private) — `h ≤ n` implies `(h : ℝ) =
  Σ_{k ∈ Icc 1 n} indicator (k ≤ h)`, giving the tail-sum formula
  `E[height] = Σ_{k=1}^n P[height ≥ k]` (`expectedTreapHeight_eq_sum`).
- `height_tail` — union bound: `P[height ≥ k] ≤ Σ_b P[depth(b) ≥ k] ≤
  n · (2 H_n^t / t!)` with `t = (k-1)/2`.
- `nat_le_exp_harmonicReal` (private) — `n ≤ exp(H_n)` from
  `log(n+1) ≤ H_n` (`Real.log_add_one_le_harmonic`).
- `pow_div_factorial_le_three` (private, with its binomial helpers) — `t^t/t! ≤ 3^t`
  for `t ≥ 1`, proved from `(1+1/n)^n ≤ 3` via `Nat.choose_le_pow_div` and the
  `Σ 1/2^i ≤ 2` geometric sum.
- `pow_div_factorial_le_inv_two` (private) — `H^t/t! ≤ (1/2)^t` when `t ≥ 6H`.
- `n_sq_mul_inv_pow_le_one` (private) — `n² · (1/2)^(6·Kh) ≤ 1` when
  `H_n ≤ Kh`, via `n² ≤ exp(2H_n)` and `exp 2 < 64` (`Real.exp_one_lt_d9`).
- Main: split `Σ_{k=1}^n P[height ≥ k]` at `K = 12·⌈H_n⌉`.  Head `≤ K ≤ 12H_n + 12`;
  tail: for `k > K`, `t ≥ 6⌈H_n⌉` so `H^t/t! ≤ (1/2)^t ≤ (1/2)^T` with `T = 6⌈H_n⌉`,
  hence `tail ≤ 2n²·(1/2)^T ≤ 2`; total `≤ 12H_n + 14 ≤ 30 H_n`.

## Verification checklist (all passing)

- `lake lean CLRSLean/Extensions/TreapHeight.lean` clean (0 errors).
- `#print axioms expectedTreapHeight_le` shows only
  `[propext, Classical.choice, Quot.sound]`.
- `uv run python scripts/check_repository.py` and `lake build CLRSLean` pass.
- No `sorry`/`admit`.
