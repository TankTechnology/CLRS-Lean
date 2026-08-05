# Chapter 29 SIMPLEX/PIVOT Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize CLRS slack-form dictionaries, their basic solutions, the textbook PIVOT transformation, and the one-step feasibility and objective-progress theorems that underpin SIMPLEX.

**Architecture:** Keep coefficient matrices in fixed `Fin m × Fin n` slots and carry variable identity through an equivalence between basic/nonbasic positions and original/slack variable names.  PIVOT swaps one basic and one nonbasic label, applies the CLRS algebraic update formulas, and is proved to preserve the represented equations and objective.  A separate minimum-ratio certificate supplies the textbook feasibility argument.

**Tech Stack:** Lean 4, Mathlib `Matrix`, finite sums, ordered-field arithmetic, `linarith`/`nlinarith`/`ring`, focused Lake builds, and interface tests with axiom audits.

---

## File Map

Create these focused source files:

```text
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/Definitions.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/Semantics.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/BasicSolution.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/InitialDictionary.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Definitions.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Algebra.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/SemanticEquivalence.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Feasibility.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Objective.lean
Tests/Chapter_29_Simplex_Interface.lean
```

Modify the Chapter 29 aggregators, literate navigation, progress/status ledger,
proof map, and issue #84 only after the theorem layer is green.

## Task 1: Dictionary Data And Variable Labels

**Files:**

- Create: `CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/Definitions.lean`
- Create: `CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary.lean`
- Create: `Tests/Chapter_29_Simplex_Interface.lean`

- [ ] **Step 1: Add the RED dictionary interface**

Create the test with:

```lean
import CLRSLean.Chapter_29

namespace CLRS
namespace Chapter29

#check LPVar
#check Dictionary
#check Dictionary.basicVar
#check Dictionary.nonbasicVar
#check Dictionary.rowRhs
#check Dictionary.objectiveRhs
#check Dictionary.Satisfies
#check Dictionary.IsBasicFeasible

end Chapter29
end CLRS
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake env lean Tests/Chapter_29_Simplex_Interface.lean
```

Expected: unknown dictionary declarations only.

- [ ] **Step 3: Define the fixed-slot dictionary model**

`Definitions.lean` contains:

```lean
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

abbrev LPVar (m n : ℕ) := Fin n ⊕ Fin m

structure Dictionary (m n : ℕ) where
  labels : (Fin m ⊕ Fin n) ≃ LPVar m n
  b : Fin m → ℝ
  a : Matrix (Fin m) (Fin n) ℝ
  v : ℝ
  c : Fin n → ℝ

namespace Dictionary

def basicVar (D : Dictionary m n) (i : Fin m) : LPVar m n :=
  D.labels (.inl i)

def nonbasicVar (D : Dictionary m n) (j : Fin n) : LPVar m n :=
  D.labels (.inr j)

def rowRhs (D : Dictionary m n) (x : LPVar m n → ℝ) (i : Fin m) : ℝ :=
  D.b i - ∑ j, D.a i j * x (D.nonbasicVar j)

def objectiveRhs (D : Dictionary m n) (x : LPVar m n → ℝ) : ℝ :=
  D.v + ∑ j, D.c j * x (D.nonbasicVar j)

def Satisfies (D : Dictionary m n) (x : LPVar m n → ℝ) : Prop :=
  ∀ i, x (D.basicVar i) = D.rowRhs x i

def IsBasicFeasible (D : Dictionary m n) : Prop :=
  ∀ i, 0 ≤ D.b i

end Dictionary
end Chapter29
end CLRS
```

Give every public declaration a doc comment and add the reader-facing module
header required by the chapter skill.

`Dictionary.lean` imports `Dictionary.Definitions` and explains the split.

- [ ] **Step 4: Import the dictionary aggregator temporarily from Chapter 29**

Add:

```lean
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary
```

to `CLRSLean/Chapter_29.lean`.  The final Section 29.3 aggregator replaces this
temporary direct import in Task 8.

- [ ] **Step 5: Verify GREEN and commit**

Run:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Simplex_Interface.lean
git diff --check
```

Commit:

```bash
git add CLRSLean/Chapter_29.lean CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/Definitions.lean \
  Tests/Chapter_29_Simplex_Interface.lean
git commit -m "feat(ch29): define simplex dictionaries"
```

## Task 2: Dictionary Semantics And Basic Solutions

**Files:**

- Create: `.../Dictionary/Semantics.lean`
- Create: `.../Dictionary/BasicSolution.lean`
- Modify: `.../Dictionary.lean`
- Modify: `Tests/Chapter_29_Simplex_Interface.lean`

- [ ] **Step 1: Extend the interface before implementation**

Append:

```lean
#check Dictionary.IsNonnegativeAssignment
#check Dictionary.basicAssignment
#check Dictionary.basicAssignment_basicVar
#check Dictionary.basicAssignment_nonbasicVar
#check Dictionary.basicAssignment_satisfies
#check Dictionary.basicAssignment_nonnegative_iff

example {m n : ℕ} (D : Dictionary m n) :
    D.Satisfies D.basicAssignment :=
  D.basicAssignment_satisfies
```

- [ ] **Step 2: Verify RED**

Run the interface test and confirm only the new declarations are unknown.

- [ ] **Step 3: Add small semantic helper theorems**

`Semantics.lean` imports `Definitions` and proves:

```lean
namespace Dictionary

def IsNonnegativeAssignment (x : LPVar m n → ℝ) : Prop :=
  ∀ q, 0 ≤ x q

theorem labels_basic_ne_nonbasic (D : Dictionary m n)
    (i : Fin m) (j : Fin n) : D.basicVar i ≠ D.nonbasicVar j := by
  intro h
  have := D.labels.injective h
  cases this

theorem exists_basic_or_nonbasic (D : Dictionary m n) (q : LPVar m n) :
    (∃ i, q = D.basicVar i) ∨ (∃ j, q = D.nonbasicVar j) := by
  obtain ⟨p, rfl⟩ := D.labels.surjective q
  cases p with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr j => exact Or.inr ⟨j, rfl⟩

end Dictionary
```

- [ ] **Step 4: Define and prove the basic solution API**

`BasicSolution.lean` imports `Semantics` and contains:

```lean
namespace Dictionary

def basicAssignment (D : Dictionary m n) : LPVar m n → ℝ := fun q =>
  match D.labels.symm q with
  | .inl i => D.b i
  | .inr _ => 0

@[simp] theorem basicAssignment_basicVar (D : Dictionary m n) (i : Fin m) :
    D.basicAssignment (D.basicVar i) = D.b i := by
  simp [basicAssignment, basicVar]

@[simp] theorem basicAssignment_nonbasicVar (D : Dictionary m n) (j : Fin n) :
    D.basicAssignment (D.nonbasicVar j) = 0 := by
  simp [basicAssignment, nonbasicVar]

theorem basicAssignment_satisfies (D : Dictionary m n) :
    D.Satisfies D.basicAssignment := by
  intro i
  simp [Satisfies, rowRhs]

theorem basicAssignment_nonnegative_iff (D : Dictionary m n) :
    IsNonnegativeAssignment D.basicAssignment ↔ D.IsBasicFeasible := by
  constructor
  · intro h i
    simpa using h (D.basicVar i)
  · intro h q
    rcases D.exists_basic_or_nonbasic q with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simpa using h i
    · simp

end Dictionary
```

- [ ] **Step 5: Wire imports, verify, and commit**

Import `Semantics` and `BasicSolution` from `Dictionary.lean`, then run the
focused build, interface test, and diff check.

Commit:

```bash
git add CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/Semantics.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/BasicSolution.lean \
  Tests/Chapter_29_Simplex_Interface.lean
git commit -m "feat(ch29): prove dictionary basic solution semantics"
```

## Task 3: Initial Dictionary Bridge

**Files:**

- Create: `.../Dictionary/InitialDictionary.lean`
- Modify: `.../Dictionary.lean`
- Modify: `Tests/Chapter_29_Simplex_Interface.lean`

- [ ] **Step 1: Add RED bridge declarations**

Append:

```lean
#check StandardLP.initialDictionary
#check StandardLP.combinedAssignment
#check StandardLP.initialDictionary_satisfies_iff
#check StandardLP.initialDictionary_satisfies_of_slackExtension
#check StandardLP.initialDictionary_objectiveRhs
#check StandardLP.initialDictionary_isBasicFeasible_iff
```

- [ ] **Step 2: Verify RED**

Run the interface test and confirm the bridge names are absent.

- [ ] **Step 3: Implement the standard/slack bridge**

`InitialDictionary.lean` imports `BasicSolution` and Section 29.1.  Define:

```lean
namespace StandardLP

def initialDictionary (P : StandardLP m n) : Dictionary m n where
  labels := Equiv.sumComm (Fin m) (Fin n)
  b := P.b
  a := P.A
  v := 0
  c := P.c

def combinedAssignment (x : Fin n → ℝ) (s : Fin m → ℝ) : LPVar m n → ℝ
  | .inl j => x j
  | .inr i => s i

@[simp] theorem initialDictionary_basicVar (P : StandardLP m n) (i : Fin m) :
    P.initialDictionary.basicVar i = Sum.inr i := by
  rfl

@[simp] theorem initialDictionary_nonbasicVar (P : StandardLP m n) (j : Fin n) :
    P.initialDictionary.nonbasicVar j = Sum.inl j := by
  rfl

theorem initialDictionary_satisfies_iff (P : StandardLP m n)
    (x : Fin n → ℝ) (s : Fin m → ℝ) :
    P.initialDictionary.Satisfies (combinedAssignment x s) ↔
      ∀ i, (P.A *ᵥ x) i + s i = P.b i := by
  simp only [Dictionary.Satisfies, Dictionary.rowRhs,
    initialDictionary_basicVar, initialDictionary_nonbasicVar,
    combinedAssignment, initialDictionary, Matrix.mulVec, dotProduct]
  constructor <;> intro h i
  · have := h i
    linarith
  · have := h i
    linarith

theorem initialDictionary_satisfies_of_slackExtension
    {P : StandardLP m n} {x : Fin n → ℝ} {s : Fin m → ℝ}
    (h : P.IsSlackExtension x s) :
    P.initialDictionary.Satisfies (combinedAssignment x s) :=
  (P.initialDictionary_satisfies_iff x s).2 h.2.2

theorem initialDictionary_objectiveRhs (P : StandardLP m n)
    (x : Fin n → ℝ) (s : Fin m → ℝ) :
    P.initialDictionary.objectiveRhs (combinedAssignment x s) = P.objective x := by
  simp [Dictionary.objectiveRhs, initialDictionary, combinedAssignment,
    StandardLP.objective, dotProduct]

theorem initialDictionary_isBasicFeasible_iff (P : StandardLP m n) :
    P.initialDictionary.IsBasicFeasible ↔ ∀ i, 0 ≤ P.b i :=
  Iff.rfl

end StandardLP
```

If `rfl` does not expose `Equiv.sumComm` applications in the installed Mathlib,
replace those two projection proofs with `by simp [initialDictionary,
Dictionary.basicVar]` and the analogous nonbasic proof.

- [ ] **Step 4: Add the nonnegativity bridge**

Add and test:

```lean
theorem combinedAssignment_nonnegative_iff
    (x : Fin n → ℝ) (s : Fin m → ℝ) :
    Dictionary.IsNonnegativeAssignment (combinedAssignment x s) ↔
      IsNonnegative x ∧ IsNonnegative s := by
  constructor
  · intro h
    exact ⟨fun j => h (.inl j), fun i => h (.inr i)⟩
  · rintro ⟨hx, hs⟩ q
    cases q with
    | inl j => exact hx j
    | inr i => exact hs i
```

- [ ] **Step 5: Verify and commit**

Run the focused chapter build and interface test.  Commit as:

```bash
git add CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/InitialDictionary.lean \
  Tests/Chapter_29_Simplex_Interface.lean
git commit -m "feat(ch29): connect initial dictionaries to standard form"
```

## Task 4: PIVOT Data Transformation And Formula API

**Files:**

- Create: `.../Pivot/Definitions.lean`
- Create: `.../Pivot/Algebra.lean`
- Create: `.../Pivot.lean`
- Modify: `Tests/Chapter_29_Simplex_Interface.lean`

- [ ] **Step 1: Add RED PIVOT checks**

Append checks for `pivotSwap`, `pivotRowB`, `pivotRowCoeff`, `pivot`, and the
basic/nonbasic label plus coefficient projection theorems.

- [ ] **Step 2: Verify RED**

Run the interface test and confirm only the new PIVOT API is absent.

- [ ] **Step 3: Implement the CLRS formulas**

`Definitions.lean` imports `Dictionary` and defines:

```lean
namespace Dictionary

def pivotSwap (l : Fin m) (e : Fin n) :
    (Fin m ⊕ Fin n) ≃ (Fin m ⊕ Fin n) :=
  Equiv.swap (.inl l) (.inr e)

def pivotRowB (D : Dictionary m n) (l : Fin m) (e : Fin n) : ℝ :=
  D.b l / D.a l e

def pivotRowCoeff (D : Dictionary m n) (l : Fin m) (e j : Fin n) : ℝ :=
  if j = e then 1 / D.a l e else D.a l j / D.a l e

def pivot (D : Dictionary m n) (l : Fin m) (e : Fin n)
    (_h : D.a l e ≠ 0) : Dictionary m n where
  labels := (pivotSwap l e).trans D.labels
  b := fun i =>
    if i = l then D.pivotRowB l e
    else D.b i - D.a i e * D.pivotRowB l e
  a := fun i j =>
    if i = l then D.pivotRowCoeff l e j
    else if j = e then -D.a i e * D.pivotRowCoeff l e e
    else D.a i j - D.a i e * D.pivotRowCoeff l e j
  v := D.v + D.c e * D.pivotRowB l e
  c := fun j =>
    if j = e then -D.c e * D.pivotRowCoeff l e e
    else D.c j - D.c e * D.pivotRowCoeff l e j

end Dictionary
```

- [ ] **Step 4: Prove projection theorems**

`Algebra.lean` proves `[simp]` theorems for the leaving row/entering column and
`*_of_ne` theorems for other rows/columns.  The central examples are:

```lean
@[simp] theorem pivot_b_leaving (D : Dictionary m n) (l : Fin m) (e : Fin n)
    (h : D.a l e ≠ 0) :
    (D.pivot l e h).b l = D.b l / D.a l e := by
  simp [pivot, pivotRowB]

theorem pivot_b_of_ne (D : Dictionary m n) (l i : Fin m) (e : Fin n)
    (h : D.a l e ≠ 0) (hi : i ≠ l) :
    (D.pivot l e h).b i = D.b i - D.a i e * (D.b l / D.a l e) := by
  simp [pivot, pivotRowB, hi]

@[simp] theorem pivot_v_apply (D : Dictionary m n) (l : Fin m) (e : Fin n)
    (h : D.a l e ≠ 0) :
    (D.pivot l e h).v = D.v + D.c e * (D.b l / D.a l e) := by
  rfl
```

Also prove label projections and all four matrix branches.  Use the installed
`Equiv.swap_apply_left`, `Equiv.swap_apply_right`, and
`Equiv.swap_apply_of_ne_of_ne` simp behavior; inspect `#check` output before
choosing explicit lemma names.

- [ ] **Step 5: Add a concrete sign-convention example**

In the interface test, construct a `Dictionary 1 1` with `b=6`, `a=2`, `v=1`,
and `c=3`, pivot its sole row/column, and prove by `norm_num` that the new row
constant is `3` and new objective constant is `10`.

- [ ] **Step 6: Verify and commit**

Run the focused build, interface test, and diff check.  Commit as:

```bash
git add CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Definitions.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Algebra.lean \
  Tests/Chapter_29_Simplex_Interface.lean
git commit -m "feat(ch29): implement textbook pivot formulas"
```

## Task 5: PIVOT Semantic Equivalence

**Files:**

- Create: `.../Pivot/SemanticEquivalence.lean`
- Modify: `.../Pivot.lean`
- Modify: `Tests/Chapter_29_Simplex_Interface.lean`

- [ ] **Step 1: Add RED semantic checks**

Append:

```lean
#check Dictionary.pivot_satisfies_iff
#check Dictionary.pivot_objectiveRhs_eq
```

and a downstream theorem-shape example using `D.pivot_satisfies_iff`.

- [ ] **Step 2: Verify RED**

Run the interface test.

- [ ] **Step 3: Prove finite-sum splitting helpers**

Inside `SemanticEquivalence.lean`, define the erased-column sum and prove:

```lean
def sumExcept (e : Fin n) (f : Fin n → ℝ) : ℝ :=
  ∑ j in Finset.univ.erase e, f j

theorem sum_eq_term_add_sumExcept (e : Fin n) (f : Fin n → ℝ) :
    (∑ j, f j) = f e + sumExcept e f := by
  rw [← Finset.univ.add_sum_erase f (Finset.mem_univ e)]
```

Prove companion `sumExcept` congruence, addition, subtraction, and scalar
distribution lemmas with `Finset.sum_congr`, `Finset.sum_add_distrib`,
`Finset.sum_sub_distrib`, and `Finset.mul_sum`.

- [ ] **Step 4: Prove the leaving-row equivalence**

For `p ≠ 0`, prove that the old leaving-row equation is equivalent to the new
entering-variable equation.  Expand the two sums with
`sum_eq_term_add_sumExcept`; use the label projection theorems and finish the
cleared-denominator identity with `field_simp [h]` followed by `ring`.

Expose it as:

```lean
theorem pivot_leaving_equation_iff (D : Dictionary m n)
    (x : LPVar m n → ℝ) (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    x (D.basicVar l) = D.rowRhs x l ↔
      x ((D.pivot l e h).basicVar l) = (D.pivot l e h).rowRhs x l := by
  -- split the column sum at e, rewrite labels/formulas, clear h, and ring
  simp only [rowRhs]
  rw [sum_eq_term_add_sumExcept e, sum_eq_term_add_sumExcept e]
  simp only [pivot_basicVar_leaving, pivot_nonbasicVar_entering,
    pivot_a_leaving_entering, pivot_b_leaving]
  -- `sumExcept` terms rewrite pointwise using the `j ≠ e` projections.
  constructor
  · intro hold
    field_simp [h] at hold ⊢
    ring_nf at hold ⊢
    linarith
  · intro hnew
    field_simp [h] at hnew ⊢
    ring_nf at hnew ⊢
    linarith
```

- [ ] **Step 5: Prove all-row semantic equivalence**

Use the leaving-row theorem plus substitution for every `i ≠ l` to prove:

```lean
theorem pivot_satisfies_iff (D : Dictionary m n)
    (x : LPVar m n → ℝ) (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    D.Satisfies x ↔ (D.pivot l e h).Satisfies x := by
  constructor
  · intro hx i
    by_cases hi : i = l
    · subst i
      exact (D.pivot_leaving_equation_iff x l e h).1 (hx l)
    · exact D.pivot_other_row_of_old_rows x l e h hi (hx l) (hx i)
  · intro hx i
    by_cases hi : i = l
    · subst i
      exact (D.pivot_leaving_equation_iff x l e h).2 (hx l)
    · exact D.old_other_row_of_pivot_rows x l e h hi (hx l) (hx i)
```

The two `other_row` helpers expand the sum at `e`, rewrite pointwise on the
erased set, and finish with `field_simp [h]` and `ring`.

- [ ] **Step 6: Prove objective-expression preservation**

For assignments satisfying the dictionary, substitute the leaving-row
equation into the objective update and prove:

```lean
theorem pivot_objectiveRhs_eq (D : Dictionary m n)
    (x : LPVar m n → ℝ) (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0)
    (hx : D.Satisfies x) :
    (D.pivot l e h).objectiveRhs x = D.objectiveRhs x := by
  -- split both objective sums at e and use `hx l`.
  rw [objectiveRhs, objectiveRhs]
  rw [sum_eq_term_add_sumExcept e, sum_eq_term_add_sumExcept e]
  have hl := hx l
  -- rewrite label/coefficient projections and normalize.
  field_simp [h] at hl ⊢
  ring_nf at hl ⊢
  linarith
```

- [ ] **Step 7: Axiom audit, verify, and commit**

Append:

```lean
#print axioms Dictionary.pivot_satisfies_iff
#print axioms Dictionary.pivot_objectiveRhs_eq
```

Run the focused build/test and ensure no `sorryAx`.  Commit as:

```bash
git add CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/SemanticEquivalence.lean \
  Tests/Chapter_29_Simplex_Interface.lean
git commit -m "feat(ch29): prove pivot semantic equivalence"
```

## Task 6: Minimum-Ratio Feasibility Preservation

**Files:**

- Create: `.../Pivot/Feasibility.lean`
- Modify: `.../Pivot.lean`
- Modify: `Tests/Chapter_29_Simplex_Interface.lean`

- [ ] **Step 1: Add RED feasibility checks**

Append checks for `Dictionary.IsMinimumRatio`, its positivity/minimality
projections, and `Dictionary.pivot_isBasicFeasible`.

- [ ] **Step 2: Verify RED**

Run the interface test.

- [ ] **Step 3: Define the exact CLRS ratio certificate**

```lean
def IsMinimumRatio (D : Dictionary m n) (e : Fin n) (l : Fin m) : Prop :=
  0 < D.a l e ∧
    ∀ i, 0 < D.a i e →
      D.b l / D.a l e ≤ D.b i / D.a i e
```

Add namespace projections `pivotCoefficient_pos` and `ratio_le`.

- [ ] **Step 4: Prove every new right-hand side nonnegative**

```lean
theorem pivot_b_nonnegative (D : Dictionary m n)
    (hD : D.IsBasicFeasible) (hmin : D.IsMinimumRatio e l)
    (i : Fin m) :
    0 ≤ (D.pivot l e hmin.pivotCoefficient_pos.ne').b i := by
  by_cases hi : i = l
  · subst i
    rw [pivot_b_leaving]
    exact div_nonneg (hD l) hmin.pivotCoefficient_pos.le
  · rw [pivot_b_of_ne _ _ _ _ _ hi]
    by_cases hie : 0 < D.a i e
    · have hratio := hmin.ratio_le i hie
      have hmul : (D.b l / D.a l e) * D.a i e ≤ D.b i :=
        (le_div_iff₀ hie).1 hratio
      nlinarith
    · have ha : D.a i e ≤ 0 := le_of_not_gt hie
      have hratio0 : 0 ≤ D.b l / D.a l e :=
        div_nonneg (hD l) hmin.pivotCoefficient_pos.le
      have hprod : D.a i e * (D.b l / D.a l e) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ha hratio0
      linarith [hD i]

theorem pivot_isBasicFeasible (D : Dictionary m n)
    (hD : D.IsBasicFeasible) (hmin : D.IsMinimumRatio e l) :
    (D.pivot l e hmin.pivotCoefficient_pos.ne').IsBasicFeasible :=
  D.pivot_b_nonnegative hD hmin
```

- [ ] **Step 5: Audit, verify, and commit**

Add `#print axioms Dictionary.pivot_isBasicFeasible`, run the focused checks,
and commit:

```bash
git add CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Feasibility.lean \
  Tests/Chapter_29_Simplex_Interface.lean
git commit -m "feat(ch29): prove ratio pivot preserves feasibility"
```

## Task 7: Objective Progress

**Files:**

- Create: `.../Pivot/Objective.lean`
- Modify: `.../Pivot.lean`
- Modify: `Tests/Chapter_29_Simplex_Interface.lean`

- [ ] **Step 1: Add RED objective checks**

Append:

```lean
#check Dictionary.pivot_v_eq
#check Dictionary.pivot_v_mono
#check Dictionary.pivot_v_strict
```

- [ ] **Step 2: Verify RED**

Run the interface test.

- [ ] **Step 3: Prove non-strict and strict progress**

`Objective.lean` imports `Feasibility` and proves:

```lean
theorem pivot_v_eq (D : Dictionary m n) (l : Fin m) (e : Fin n)
    (h : D.a l e ≠ 0) :
    (D.pivot l e h).v = D.v + D.c e * (D.b l / D.a l e) :=
  rfl

theorem pivot_v_mono (D : Dictionary m n)
    (hD : D.IsBasicFeasible) (hc : 0 < D.c e)
    (hmin : D.IsMinimumRatio e l) :
    D.v ≤ (D.pivot l e hmin.pivotCoefficient_pos.ne').v := by
  rw [pivot_v_eq]
  have hratio : 0 ≤ D.b l / D.a l e :=
    div_nonneg (hD l) hmin.pivotCoefficient_pos.le
  exact le_add_of_nonneg_right (mul_nonneg hc.le hratio)

theorem pivot_v_strict (D : Dictionary m n)
    (hc : 0 < D.c e) (hbl : 0 < D.b l)
    (hmin : D.IsMinimumRatio e l) :
    D.v < (D.pivot l e hmin.pivotCoefficient_pos.ne').v := by
  rw [pivot_v_eq]
  exact lt_add_of_pos_right
    (mul_pos hc (div_pos hbl hmin.pivotCoefficient_pos))
```

- [ ] **Step 4: Audit, verify, and commit**

Add axiom prints for both progress theorems, run the focused checks, and commit:

```bash
git add CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot.lean \
  CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Objective.lean \
  Tests/Chapter_29_Simplex_Interface.lean
git commit -m "feat(ch29): prove pivot objective progress"
```

## Task 8: Chapter, Book, Status, And Issue Integration

**Files:**

- Create: `CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm.lean`
- Modify: `CLRSLean/Chapter_29.lean`
- Modify: `CLRSLean.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/clrs-proof-progress.csv`
- Regenerate: `CLRSLean/Progress.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-map.md`
- Modify: `docs/proof-status-board.md`

- [ ] **Step 1: Create the Section 29.3 reader aggregator**

Import `Dictionary` and `Pivot`; document the represented PIVOT theorem layer
and explicitly list SIMPLEX control flow, Bland termination, and optimality as
the remaining Section 29.3 gap.

- [ ] **Step 2: Replace the temporary Chapter 29 import**

Import the Section 29.3 reader aggregator and every hidden child module in
literate depth-first order, matching the repository navigation test.

- [ ] **Step 3: Register all new modules**

Add the Section 29.3 hierarchy and titles to `literate.toml`, all source paths
to `docs/index.md`, and implementation-detail links from reader aggregators to
every hidden page.

- [ ] **Step 4: Update the honest progress row**

Change Chapter 29 represented sections to `29.1;29.3;29.4`, add one tracked
PIVOT theorem group, and name the exact remaining SIMPLEX/initialization/
duality/formulation work.  Regenerate with:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
```

- [ ] **Step 5: Update reader-facing status and proof map**

Record dictionary/basic-solution semantics, initial-dictionary refinement,
PIVOT semantic equivalence, minimum-ratio feasibility preservation, and
objective progress.  Do not call Section 29.3 complete.

- [ ] **Step 6: Run the final focused gate**

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
lake env lean Tests/Chapter_29_Simplex_Interface.lean
lake build CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm:literate
uv run python scripts/check_repository.py
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_29 Tests/Chapter_29_Interface.lean Tests/Chapter_29_Simplex_Interface.lean
git diff --check
git status --short --branch
```

The marker scan should return no matches.  The only accepted literate warning
is an unchanged dependency warning outside Chapter 29.

- [ ] **Step 7: Commit integration**

```bash
git add CLRSLean.lean CLRSLean/Chapter_29.lean CLRSLean/Chapter_29 \
  CLRSLean/Progress.lean CLRSLean/Status.lean Tests/Chapter_29_Simplex_Interface.lean \
  docs/clrs-proof-progress.csv docs/index.md docs/proof-map.md \
  docs/proof-status-board.md literate.toml
git commit -m "docs(ch29): register simplex pivot milestone"
```

- [ ] **Step 8: Respond to issue #84 after verification**

Post a concise comment listing the proved dictionary/PIVOT theorem layer, the
focused verification commands, and the next milestone: executable SIMPLEX
selection, unboundedness, Bland termination, and exit optimality.  Keep the
issue open.

## Final Review Gate

Review every change from `main` to `HEAD` for CLRS faithfulness, correct signs,
no hidden assumptions, small-file boundaries, interface stability, and honest
status prose.  Re-run the focused gate after any review fix.  Then use
`superpowers:finishing-a-development-branch` for integration.
