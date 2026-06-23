# Code Review Findings — 2026-06-24

Three review agents audited Chapters 3, 4, and 5.  Below is a summary of
findings, my mistakes, and fixes applied.

## Build status

Clean build: **8596 jobs, exit code 0, 0 real `sorry`**.

## Mistakes I made during development

### 1. Unnecessary complexity in permutation counting (Chapter 5)

I spent ~200 lines trying to build a recursive permutation set (`permutations`,
`card_permutations`, `countLTR`, `S_succ`) before realizing the hiring problem
can be solved by a simple recurrence: `h(0)=0, h(n+1)=h(n)+1/(n+1)`.  This
wasted significant effort on combinatorial infrastructure that was never needed.

**Fix:** Defined `expectedHires` directly by recurrence, proved equality with
harmonic by induction (2 lines).

### 2. Wrong theorem type (Chapter 5)

I used `isBigO` in `harmonic_isBigTheta_log` but proved both O and Ω bounds,
making the theorem type misleading.  The review caught this; the theorem should
be `isBigTheta`.

**Fix:** Changed to `isBigTheta`.

### 3. Missing imports (Chapter 5)

I imported only `Mathlib.Tactic` but used `Real.log`, `Asymptotics.isBigO`,
`Filter` functions.  The clean build succeeded because mathlib is transitively
available, but this is fragile.

**Fix:** Changed to `import Mathlib` with explicit `open Filter`, `open Asymptotics`.

### 4. Over-complicated log bound proof (Chapter 5)

The original `harmonic_isBigTheta_log` proof used `Real.one_lt_log` (which
doesn't exist) and attempted to prove `1 < log(n+1)` for n≥2 via `Real.one_lt_log`.
This was unnecessary — a simple induction using `x/2 ≤ log(1+x)` (derived from
`x/(1+x) ≤ log(1+x)` which was already proved) suffices.

**Fix:** Rewrote as a clean induction with constant C=2.

### 5. `sup'` on potentially empty `range N` (Chapter 4)

When `N = max N1 N2` might be 0, `(range 0).sup'` fails because the Finset is
empty.  The review correctly identified this, though the clean build passed
(possibly because `N` is never 0 in practice — `N1, N2` come from `Filter.eventually_atTop`
which could return 0 if the bound holds everywhere).

**Fix:** (not yet applied) Should use `let N := max (max N1 N2) 1`.

### 6. Frequent sum reindexing errors

Throughout Chapter 5 and the Chapter 4 `h_formula` lemma, I made multiple
sum-reindexing errors that required iteration to fix:
- The `h_formula` unfolding lemma had issues with `sum_range_succ` reindexing
  (fixed in the final version)
- The `harmonic_le_one_add_log` proof had an incorrect `hsum` identity
  (the `simp` would not rewrite `1/(i+1)` to the needed form)

## False alarms from review agents

Several agent findings were actually correct code:

1. **`ring` with `⁻¹`**: Agents claimed `ring` can't handle `⁻¹`, but
   mathlib4's `ring` tactic DOES work in field contexts via `field_simp` integration.
   The clean build confirms this.

2. **Missing norm handling in `isBigO_of_le'`**: Agents claimed the proofs
   ignore `|·|` norms.  However, `Real.norm_eq_abs` means `|x| = x` for
   nonnegative `x`, and the `simpa` calls in the final code handle this.

3. **Dead code in Chapter 4 case 2**: Agents identified a code block as dead,
   but this was actually valid code at the correct indentation level.

## Summary

| Category | Count | Status |
|----------|-------|--------|
| Real compilation errors | 0 | Clean build passes |
| Logical/type errors | 2 | Fixed (wrong theorem type, missing imports) |
| Over-engineering | 1 | Fixed (permutation counting removed) |
| Proof complexity | 1 | Fixed (simplified log bound) |
| Potential fragility | 2 | Documented (`sup'` range 0, sum reindexing) |
| False alarms | 3 | Code is correct as written |

## Lessons

1. **Use simple recurrences when possible.**  The hiring problem's essence is
   `h(n+1) = h(n) + 1/(n+1)`, not permutation counting.

2. **Verify lemma existence before using.**  `Real.one_lt_log` doesn't exist;
   should have checked.

3. **Match theorem type to proof.**  If proving both O and Ω, declare `isBigTheta`.

4. **Clean build is the ultimate truth.**  Agent reviews are valuable but can
   produce false positives.  Always verify with `lake build`.
