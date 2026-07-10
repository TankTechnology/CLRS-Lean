# Issue #1 — Build a reusable finite discrete probability/expectation toolkit and close the randomized expected-time analysis

**Labels (suggested)**: `proof`, `probability`, `chapter-07`, `infrastructure`, `extreme-difficulty`
**Chapters involved**: Ch5, Ch7.3, Ch8.4, Ch9, Ch11.2
**Flagship target**: Ch7 randomized quicksort `E[#comparisons] = Θ(n log n)`

---

## 1. Background & Motivation

CLRS's randomized-algorithm analyses (randomized quicksort, bucket sort, randomized SELECT, chained hashing) currently have **no genuine probability space** in this repository. Four sections each hand-roll their own "finite uniform average," none of them shared, and all of them stop at a "recurrence / abstract cost" level — the conclusions are never connected to the **true expectation of a random variable over a probability space**.

Current state:

| Location | Hand-rolled definition | What is proved | What is actually missing |
|---|---|---|---|
| Ch5 hiring | `uniformAverageRange` (over `range m`) | ✅ **end-to-end complete**: `E[X]=H_n` (indicator singleton + linearity) | nothing — **the only complete expectation argument, usable as a template** |
| Ch7.3 randomized quicksort | `expectedComparisons` (closed form over ℚ) | closed form satisfies recurrence (7.4), bounded by `2n·H_n`, `n²` | **no probability space**: never proved "true expectation under random pivots = this recurrence" |
| Ch8.4 bucket sort | `uniformAverageFin` / `uniformAverageFin2` | collision prob `1/m`, second moment `E[Σnᵢ²]=n+n(n-1)/m`, abstract `≤3n` | missing an **explicit independent input distribution** connecting to the second moment |
| Ch9 selection | — | only deterministic median-of-medians | **randomized SELECT entirely absent**, zero scaffolding |
| Ch11.2 chained hashing | `uniformAverageFin` (verbatim duplicate of Ch8) | `E[chain length]=α`, `E[unsuccessful search]=1+α` | missing **random key / random hash + independence** |

**Core problem**: these "expectations" are **definitional averages**, not expectations of random variables. `uniformAverageFin` is duplicated verbatim between Ch8 and Ch11; `indicator` / `probabilityIndicator`, linearity `_add`, `_nonneg`, `_indicator_singleton` are re-proved in each section. This is exactly what the Extreme-Difficulty queue in `proof-status-board.md` calls out: "Generalize the finite-uniform average layer into a reusable probability toolkit, then use it for one randomized theorem end-to-end."

## 2. Goal

1. Extract a **unified, reusable finite discrete expectation library** (self-built `Finset` expectation layer as the base, borrowing Mathlib in a few spots).
2. Use it to **deduplicate** and refactor the existing hand-rolled averages in Ch5 / Ch8.4 / Ch11.2 (keeping public theorem semantics unchanged).
3. Use it to prove the **flagship theorem, Ch7 randomized quicksort, end-to-end at the "true expectation" level**: build an explicit probability model, prove the true expected comparison count equals a harmonic-number expression, and bridge it to `Θ(n log n)`.

## 3. Decisions (confirmed)

- **Probability foundation = hybrid**: the expectation layer is self-built (a weighted/uniform average over `Finset`, returning `ℝ` or `ℚ`), staying lightweight and consistent with existing code; Mathlib is referenced only for uniform-distribution construction, `Fintype`/`Equiv.Perm` instances, and (later) independence. Collaborators do **not** need any Mathlib measure theory / `MeasureTheory` integration.
- **Flagship = Ch7**: its closed form `expectedComparisons n = 2(n+1)Hₙ - 4n` already exists; the only missing piece is the "probability space → conclusion" connection, giving the best return on effort.
- **Random model (first one) = uniformly random permutation of the input + indicator Xᵢⱼ**: this matches the classic CLRS 7.3 argument (`zᵢ` and `zⱼ` are compared ⟺ the first element of `{zᵢ,…,zⱼ}` chosen as a pivot is `zᵢ` or `zⱼ`). The **"recursive PMF with an independent uniform pivot at each step" model is deferred to a follow-up issue**; it is the natural base for a future Ch9 randomized SELECT.

## 4. Scope

**In scope**
- A new unified expectation library file (e.g. `CLRSLean/Probability/FiniteExpectation.lean`, namespace `CLRS.Probability`).
- Migrating the hand-rolled averages of Ch5 / Ch8.4 / Ch11.2 to the unified library (without changing public theorem names or statements).
- Ch7 flagship: the random-permutation model + the `2/(j-i+1)` comparison-probability lemma + `E = Σ` + the asymptotic bridge.

**Out of scope**
- **True RAM / step-count cost semantics** → belongs to **Issue #2**. In this issue "expected time" means **expected comparison count / expected abstract cost**.
- Continuous probability, heavy measure-theory machinery.
- End-to-end randomized theorems for Ch8 / Ch9 / Ch11 (this issue only **migrates their hand-rolled averages to the toolkit**; the end-to-end proofs are follow-up issues, see §8).
- **Verbatim equality** with the existing `expectedComparisons` closed form is **not required** — an asymptotic bridge (`Θ(n log n)`, at least `O(n log n)`) is enough for acceptance.

## 5. Technical Approach

### 5.1 Expectation toolkit API (self-built, returning `ℝ`)

Over a finite sample space `Ω` (`[Fintype Ω]`), with the uniform distribution as the default; reserve general weights so independence/PMF extensions remain possible.

```lean
namespace CLRS.Probability

/-- Uniform expectation over a finite sample space: `(∑ ω, X ω) / |Ω|`. -/
noncomputable def expect {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ := ...

/-- Uniform probability of an event: `|{ω | P ω}| / |Ω|` (= expectation of its indicator). -/
noncomputable def prob {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] : ℝ := ...

theorem expect_add   : expect (fun ω => X ω + Y ω) = expect X + expect Y
theorem expect_const : expect (fun _ => (c : ℝ)) = c
theorem expect_nonneg (h : ∀ ω, 0 ≤ X ω) : 0 ≤ expect X
theorem expect_sum   : expect (fun ω => ∑ k ∈ s, X k ω) = ∑ k ∈ s, expect (X k ·)   -- workhorse for indicator decomposition
theorem expect_indicator (P) : expect (fun ω => indicator (P ω)) = prob P            -- expectation of indicator = probability
end CLRS.Probability
```

> **Design requirement (leave room for a later independence extension)**: `expect` should hold for a general `Fintype` sample space, where the space can be `Equiv.Perm (Fin n)`, `Fin m`, a product type, etc. The product-of-independent-variables expectation `expect_mul_of_indep` is **not a hard acceptance criterion of this issue**, but the toolkit structure must not prevent adding it later (it is needed by the Ch8/Ch11 follow-up issues).

### 5.2 Ch7 flagship: the random-permutation model

- **Sample space**: `Ω = Equiv.Perm (Fin n)`, uniform (using Mathlib's `Fintype (Equiv.Perm _)` instance). Interpret the input as a random permutation of the ranks `{0,…,n-1}`.
- **Random variables**: for `i < j`, `Xᵢⱼ : Ω → ℝ` = indicator "ranks `i` and `j` are compared during quicksort". Total comparisons `X = Σ_{i<j} Xᵢⱼ`.
- **Key lemma** (the hard part of this issue):
  `compared_prob : prob (fun π => compared π i j) = 2 / (j - i + 1)`.
  Reduce it to the combinatorial fact: under a uniform random permutation, among the `(j-i+1)` ranks in `{i,…,j}` the probability that a specified one appears first is `1/(j-i+1)`; there are 2 favorable outcomes (`i` or `j`), hence `2/(j-i+1)`.
- **Summation + bridge**:
  `E[X] = Σ_{i<j} 2/(j-i+1)` (from `expect_sum` + `expect_indicator`),
  then prove `Σ_{i<j} 2/(j-i+1)` is sandwiched by harmonic numbers, bridging to `Chapter03.isBigTheta (fun n => E[X] n) (fun n => (n:ℝ) * Real.log n)` (at least the `isBigO` upper bound `2n·Hₙ`).

## 6. Acceptance Criteria

> Every item must **`lake build` clean and be sorry-free**.

- [ ] **AC-1 (toolkit)** A new file `CLRSLean/Probability/FiniteExpectation.lean` exists, defining `expect` / `prob` / `indicator` and proving `expect_add`, `expect_const`, `expect_nonneg`, `expect_sum`, `expect_indicator`.
- [ ] **AC-2 (dedup migration)** Ch5 `uniformAverageRange`, Ch8.4 `uniformAverageFin`/`uniformAverageFin2`, Ch11.2 `uniformAverageFin`, and their duplicated `indicator`/`probabilityIndicator`/`_add`/`_nonneg`/`_indicator_singleton` are refactored to reuse the unified toolkit (duplicates removed). **The public theorem names and statements in these three sections stay unchanged** (no regressions).
- [ ] **AC-3a (comparison probability)** In the Ch7 random-permutation model, prove `compared_prob : prob(compared · i j) = 2/(j-i+1)` (`i<j`).
- [ ] **AC-3b (expectation as a sum)** `expected_comparisons_eq_sum : E[X n] = Σ_{0≤i<j<n} 2/(j-i+1)`, derived via `expect_sum` + `expect_indicator`.
- [ ] **AC-3c (asymptotic bridge)** `expected_comparisons_bigO_nlogn` (at minimum) proving `Chapter03.isBigO (E[X ·]) (fun n => (n:ℝ)*Real.log n)`; aim for `isBigTheta`.
- [ ] **AC-4 (docs sync)** Update the Ch7.3 entry in `proof-map.md`, the `Chapter 7 randomized probability semantics` row in "Deferred And Blocked Items", and the corresponding Extreme-Difficulty row in `proof-status-board.md` to "expectation = Θ(n log n) under the random-permutation model, proved," removing the "missing probability model" gap text.
- [ ] **AC-5 (conventions)** New/changed code follows the `CLAUDE.md` skeleton (module-level `/-! -/`, `/-- -/` doc on every def/theorem, `namespace … end`). If a new section file is added, it is registered in `literate.toml` (`[order_children]` + `[modules.…]` title) and imported in `CLRSLean.lean`.

## 7. Milestone Breakdown (suggested for the collaborator)

| Milestone | Deliverable | Acceptance |
|---|---|---|
| **M1** | Toolkit file + linearity/indicator/nonneg; use Ch5 (simplest, already end-to-end) as the first migration validation | AC-1, AC-2(Ch5) |
| **M2** | Migrate Ch8.4 + Ch11.2 to the shared toolkit, preserving the public API | AC-2(Ch8/Ch11) |
| **M3** | Ch7 flagship: random-permutation model + `2/(j-i+1)` lemma + `E=Σ` + asymptotic bridge | AC-3a/b/c |
| **M4** | Docs sync + regression cleanup (`lake build` clean) | AC-4, AC-5 |

## 8. Dependencies & Risks

- **Main design difficulty / risk**: proving `compared_prob`. It needs a combinatorial lemma about **relative order under a uniform random permutation** ("the probability that a specified one of `k` elements appears first = 1/k"). First check whether Mathlib has an existing result about `Equiv.Perm` relative order / the first-appearing element of a `Finset`; if not, prove it directly. **Recommend a feasibility spike on this lemma before starting M3.**
- **Follow-up issues (unlocked after this issue, out of scope here)**:
  - The recursive-PMF model with an independent uniform pivot at each step (connecting to the existing `expectedComparisons` recurrence; reusable for a future Ch9 randomized SELECT).
  - Add `expect_mul_of_indep` (independence) to the toolkit, then close Ch8 bucket-sort expected-linear and Ch11 chained-hash expected-search end-to-end.
  - Ch9 randomized SELECT `E = O(n)`.

## 9. Relevant Files

- `CLRSLean/Chapter_05/Section_05_1_Hiring_Problem.lean` — `uniformAverageRange`, the complete expectation template
- `CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort.lean` — `expectedComparisons`, harmonic bounds (flagship landing spot)
- `CLRSLean/Chapter_08/Section_08_4_Bucket_Sort.lean` — `uniformAverageFin`/`uniformAverageFin2`, second moment
- `CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean` — `uniformAverageFin` (duplicate of Ch8), load factor
- `docs/proof-map.md`, `docs/proof-status-board.md` — the status ledgers (must be synced for AC-4)
