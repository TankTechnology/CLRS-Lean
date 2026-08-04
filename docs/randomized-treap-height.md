# Randomized treap: completing the expected-height bound

Handoff notes for finishing `E[height] ≤ c · H_n = O(log n)` in
`CLRSLean/Extensions/TreapHeight.lean` (prototype, unregistered in
`literate.toml`).  Written 2026-08-04 on `feat/extensions`.

## Goal

For the uniform random treap on `n` keys (model in `TreapRandom.lean`), prove:

```lean
theorem expectedTreapHeight_le {n : ℕ} :
    expectedTreapHeight n ≤ c * (harmonic n : ℝ)
```

for an explicit constant `c`.  `expectedTreapHeight n =
fintypeExpect (fun σ : PrioPerm n => (treapHeight σ : ℝ))` and
`treapHeight σ = (Finset.univ.sup (fun b : Fin n => depth σ b))`.

The route is an **exponential tail on the depth of a single key**, then a union
bound over keys, then a tail sum.

## What is already proved (kernel-clean, `[propext, Classical.choice, Quot.sound]`)

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

## Step 1 — right-ancestor tail via reflection

`rightAncestors σ b = |{a | b < a ∧ Ancestor σ a b}|`.  By the order-reversing
involution, `rightAncestors σ b = leftAncestors (σ * Fin.revPerm) (Fin.revPerm b)`,
because for `b < a`:

- `Fin.revPerm a < Fin.revPerm b`, and
- `Ancestor (σ * Fin.revPerm) (Fin.revPerm a) (Fin.revPerm b) ↔ Ancestor σ a b`
  (`σ * Fin.revPerm` applies the reflection to the key first, then reads the old
  priority; `Equiv.Perm.mul_apply : (f * g) x = f (g x)`).

Then `σ ↦ σ * Fin.revPerm` is a bijection on the sample space, so
`P[R(b) ≥ k] = P[L(revPerm b) ≥ k]`, and `leftAncestors_tail (Fin.revPerm b) k`
gives `P[R(b) ≥ k] ≤ (H_n)^k / k!` (the reflected left sum equals the right sum
by reindexing `a ↦ revPerm a`).

**Gotchas already hit** (in `ancestor_rev_perm`, currently unfinished):
- `Ancestor` unfolds to `Icc (min a b) (max a b)`.  For `b < a`, first prove and
  `rw` the conversion `Finset.Icc (min a b) (max a b) = Finset.Icc b a` via
  `min_eq_left (le_of_lt hab)` / `max_eq_right (le_of_lt hab)`.
- `Fin.revPerm x` is not definitionally `x.rev`; use `simp [Fin.revPerm_apply]`.
- `Fin.rev_le_rev (i := i) (j := j) : i.rev ≤ j.rev ↔ j ≤ i` needs explicit
  `(i := ...) (j := ...)` arguments.
- `Fin.revPerm` is injective (`Fin.revPerm.injective`); `Fin.rev_lt_iff` gives
  `rev a < rev b ↔ b < a`.

## Step 2 — depth tail

```lean
lemma depth_tail {n : ℕ} (b : Fin n) (k : ℕ) :
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ depth σ b)) ≤
      2 * (harmonicReal n)^((k - 1) / 2) / (Nat.factorial ((k - 1) / 2) : ℝ) := ...
```

Split: `depth = L + R + 1`, so `depth ≥ k` implies `L ≥ t` or `R ≥ t` with
`t = (k-1)/2` (if `L < t` and `R < t` then `L + R ≤ 2t - 2 ≤ k - 2`).  Then
`P[depth ≥ k] ≤ P[L ≥ t] + P[R ≥ t]`, each `≤ (H_n)^t / t!` by
`leftAncestors_tail` + `left_sum_le_harmonicReal` and Step 1.

## Step 3 — expected height

Union bound over keys, then a tail sum:

- `P[height ≥ k] ≤ Σ_b P[depth(b) ≥ k] ≤ 2n · (H_n)^t / t!` with `t = (k-1)/2`.
- `E[height] = Σ_{k≥1} P[height ≥ k] ≤ Σ_{k≥1} min(1, 2n (H_n)^t / t!)`.
- The head `k ≤ c·H_n` contributes `O(H_n)`; the tail decays (the `t!` dominates
  once `t ≥ e·H_n`-ish), so the total is `c·H_n + O(1)`.  Use a generous explicit
  `c` (e.g. `c = 12`) to keep the algebra clean.

The tail-sum bound needs: `Σ_{t ≥ t₀} 2n(H_n)^t/t! ≤ O(1)` for
`t₀ ≈ (1+ε)·e·H_n`-ish, via the ratio test / `t! ≥ (t/e)^t`.

## Verification checklist

- `lake lean CLRSLean/Extensions/TreapHeight.lean` clean (0 errors/warnings).
- `#print axioms` on `expectedTreapHeight_le` shows only
  `[propext, Classical.choice, Quot.sound]`.
- `uv run python scripts/check_repository.py` and `lake build CLRSLean` pass.
- No `sorry`/`admit`.
