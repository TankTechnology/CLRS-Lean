# CLRS Chapter 4 — Master Theorem: Complete Proof Design

Date: 2026-06-24
Status: in progress
Reference: CLRS 4th ed., Sections 4.5-4.6

## Goal

Complete formal proof of the Master Theorem (Theorem 4.1) including both the
exact-powers case and the extension to general n via floor/ceiling.

## Architecture

```
CLRSLean/Chapter_04/
  Chapter_04.lean                                    ← chapter landing page
  Section_04_5_Master_Theorem.lean                   ← statement + proof
```

All content in one file: the recurrence definition, the theorem statement,
and the full proof.  The proof follows CLRS Section 4.6 closely.

## Key definitions

1. **Recurrence sequence** T(n) defined by:
   - Base: T(0), ..., T(b-1) arbitrary (given as constants)
   - Step: T(n) = a·T(⌊n/b⌋) + f(n) for n ≥ b
   where a ≥ 1, b > 1 (natural numbers), f: ℕ → ℝ nonnegative.

2. **Master Theorem statement**: For a ≥ 1, b > 1, f: ℕ → ℝ (f ≥ 0), let
   T satisfy the recurrence above. Define crit = log_b(a) (as a real number).
   Then:
   - Case 1: if f(n) = O(n^{crit - ε}) for some ε > 0, then T(n) = Θ(n^{crit})
   - Case 2: if f(n) = Θ(n^{crit} · (log n)^k) for some k ≥ 0, then T(n) = Θ(n^{crit} · (log n)^{k+1})
   - Case 3: if f(n) = Ω(n^{crit + ε}) for some ε > 0, and af(n/b) ≤ cf(n) for
     some c < 1 (regularity), then T(n) = Θ(f(n))

## Proof structure (following CLRS 4.6)

### Part A: Exact powers (n = b^i)

1. Define g(i) = T(b^i), which satisfies g(i) = a·g(i-1) + f(b^i)
2. Lemma (unfolding): g(i) = a^i·g(0) + Σ_{j=0}^{i-1} a^j·f(b^{i-j})
3. Case 1 analysis: f(n) = O(n^{crit-ε}) → sum = Θ(a^i) = Θ(n^{crit})
4. Case 2 analysis: f(n) = Θ(n^{crit}·(log n)^k) → sum = Θ(a^i·i^{k+1}) = Θ(n^{crit}·(log n)^{k+1})
5. Case 3 analysis: f(n) = Ω(n^{crit+ε}) with regularity → sum = Θ(f(b^i)) = Θ(f(n))

### Part B: Extension to general n

6. Bounding T(n) between T(⌊n/b⌋) and T(⌈n/b⌉) using monotonicity
7. Using the exact-powers result on b^{⌊log_b n⌋} and b^{⌈log_b n⌉}
8. Connecting the bounds via the asymptotics framework

## Implementation notes

- All functions are ℕ → ℝ for consistency with Chapter 3
- Use `Nat` recursion for defining T
- `log_b(a)` is represented as `Real.log (a : ℝ) / Real.log (b : ℝ)`
- The critical exponent `crit` is a real number; comparisons with f use Chapter 3 asymptotics
- Floor/ceiling appear in the recurrence; use `Nat.div` for exact division when possible
- The "regularity condition" af(n/b) ≤ cf(n) is stated for all sufficiently large n

## File structure

```
CLRSLean/Chapter_04.lean                              ← landing page
CLRSLean/Chapter_04/Section_04_5_Master_Theorem.lean  ← everything
```

One file, approximately 400-600 lines of Lean.

## Expected lemmas needed

1. `unfold_recurrence` — closed form for g(i) on exact powers
2. `geometric_sum` — Σ_{j=0}^{i-1} r^j = (r^i - 1)/(r - 1) for r ≠ 1
3. `case1_sum_bound` — upper bound on Σ a^j·f(b^{i-j}) in Case 1
4. `case2_sum_bound` — upper and lower bounds in Case 2
5. `case3_sum_bound` — upper and lower bounds in Case 3
6. `floor_ceil_sandwich` — T(b^{⌊log_b n⌋}) ≤ T(n) ≤ T(b^{⌈log_b n⌉})
7. `extend_to_general` — from exact powers to general n
