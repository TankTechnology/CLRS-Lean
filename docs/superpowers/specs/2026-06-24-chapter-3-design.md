# CLRS Chapter 3 — Growth of Functions: Design Spec

Date: 2026-06-24
Status: ready for implementation
Reference: CLRS 4th ed., Chapter 3; mathlib `Analysis/Asymptotics/Defs.lean`

## Architecture

Chapter 3 bridges CLRS's discrete asymptotic notation to mathlib's
filter-based asymptotics.  No new deep mathematics — the value is:

1. **CLRS-compatible wrappers** for readers coming from the textbook.
2. **Equivalence proofs** between the CLRS `∃ c n₀` style and mathlib's `atTop` filter.
3. **Specific comparison lemmas** useful for algorithm analysis (polynomials,
   logs, exponentials, factorials).

```
CLRSLean/Chapter_03/
  Section_03_1_Asymptotic_Notation.lean   ← wrappers + equivalence + properties
  Section_03_2_Standard_Functions.lean    ← concrete growth comparisons
```

Dependency: `import Mathlib` (brings in `Analysis/Asymptotics/Defs` transitively).

## Section 3.1 — Asymptotic Notation

### Wrapper definitions

All work on `ℕ → ℝ` (or `ℕ → ℕ`) with the `atTop` filter.

```lean
/-- CLRS O-notation: f(n) = O(g(n)).  There exist c > 0 and n₀ such that
    |f(n)| ≤ c * |g(n)| for all n ≥ n₀. -/
def isBigO (f g : ℕ → ℝ) : Prop := f =O[atTop] g

/-- CLRS Ω-notation: f(n) = Ω(g(n))  ↔  g(n) = O(f(n)). -/
def isBigOmega (f g : ℕ → ℝ) : Prop := g =O[atTop] f

/-- CLRS Θ-notation: f(n) = Θ(g(n))  ↔  f = O(g) ∧ f = Ω(g). -/
def isBigTheta (f g : ℕ → ℝ) : Prop := isBigO f g ∧ isBigOmega f g

/-- CLRS o-notation: f(n) = o(g(n)).  For every c > 0, eventually |f(n)| ≤ c * |g(n)|. -/
def isLittleO (f g : ℕ → ℝ) : Prop := f =o[atTop] g

/-- CLRS ω-notation: f(n) = ω(g(n))  ↔  g(n) = o(f(n)). -/
def isLittleOmega (f g : ℕ → ℝ) : Prop := g =o[atTop] f
```

### Equivalence theorems

Prove that the CLRS discrete definition is equivalent to mathlib's filter definition.

```
theorem isBigO_iff : isBigO f g ↔
    ∃ (c : ℝ), c > 0 ∧ ∃ (n₀ : ℕ), ∀ n, n ≥ n₀ → |f n| ≤ c * |g n| := ...
```

Analogous `isLittleO_iff`, `isBigOmega_iff`, `isLittleOmega_iff`.

### Algebraic properties (inherited from mathlib)

| Property | Theorem |
|----------|---------|
| Reflexivity | `isBigO_refl f : isBigO f f` |
| Transitivity | `isBigO_trans : isBigO f g → isBigO g h → isBigO f h` |
| Sum rule | `isBigO_add : isBigO f₁ g → isBigO f₂ g → isBigO (f₁ + f₂) g` |
| Product with constant | `isBigO_smul : isBigO (λ n, c * f n) g ↔ isBigO f g` |
| Maximum rule | `isBigOmega_max : isBigOmega (λ n, max (f n) (g n)) f` |

### Notation for the site

Keep notation in prose, not Lean `notation` commands (avoid clashes with
mathlib's global `=O[atTop]`).  Use lemma names like `isBigO_of_poly` for
reader friendliness.

## Section 3.2 — Standard Functions

### Target lemmas

These are the concrete comparisons that CLRS readers use when analyzing
divide-and-conquer recurrences:

1. **Polynomial growth**:
   ```
   isBigO_of_poly: n^a = O(n^b) when a ≤ b
   isLittleO_of_poly: n^a = o(n^b) when a < b
   ```

2. **Log vs polynomial**:
   ```
   isLittleO_log_vs_poly: log(n) = o(n^ε) for any ε > 0
   isBigO_poly_vs_exp: n^k = o(2^n) for any k
   ```

3. **Exponential dominance**:
   ```
   isLittleO_exp_vs_exp: a^n = o(b^n) when 1 ≤ a < b
   ```

4. **Factorial bounds** (weaker Stirling, just monotonic + exponential bounds):
   ```
   factorial_lower_bound: 2^n ≤ n! for n ≥ 4  (or n ≤ 2^(n-1))
   factorial_upper_bound: n! ≤ n^n
   isLittleO_exp_vs_factorial: a^n = o(n!) for any a
   ```

5. **Floor / ceiling** (useful for recurrences):
   ```
   floor_half_isTheta: ⌊n/2⌋ = Θ(n)
   ceil_half_isTheta: ⌈n/2⌉ = Θ(n)
   ```

6. **Harmonic numbers** (optional, useful for expected-case analysis):
   ```
   harmonic_isTheta_log: H_n = Θ(log n)
   ```

### Implementation strategy

Most of these lemmas already exist in mathlib (e.g., in
`Analysis/SpecificAsymptotics.lean`).  The job is to:

1. Find the existing lemma in mathlib.
2. Specialize it to `ℕ → ℝ` and `atTop`.
3. Give it a CLRS-friendly name.
4. Write a short doc comment linking it to CLRS.

Where mathlib has no lemma, write a direct proof using the asymptotics API.

## File structure

```
CLRSLean/Chapter_03/
  Section_03_1_Asymptotic_Notation.lean
  Section_03_2_Standard_Functions.lean
```

Each file follows the standard skeleton: `import Mathlib`, `/-!` module doc,
`namespace CLRS.Chapter03`, theorems, `end CLRS.Chapter03`.

## literate.toml additions

```toml
[order_children]
"CLRSLean" = [
  "CLRSLean.Chapter_01",
  "CLRSLean.Chapter_03",
  "CLRSLean.Chapter_02",
  ...
]

[order_children]
"CLRSLean.Chapter_03" = [
  "CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation",
  "CLRSLean.Chapter_03.Section_03_2_Standard_Functions",
]

[modules."CLRSLean.Chapter_03"]
title = "Chapter 3. Growth of Functions"

[modules."CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation"]
title = "3.1. Asymptotic Notation"

[modules."CLRSLean.Chapter_03.Section_03_2_Standard_Functions"]
title = "3.2. Standard Notations and Common Functions"
```

## What is NOT in scope

- Limit-based proofs with `tendsto` (use mathlib filter API instead of ε-N).
- Full Stirling's approximation (only simple factorial bounds).
- The iterated logarithm `log*` (too specialized, add later if needed).
- Integration with Chapter 4 recurrences (deferred to Chapter 4 work).
