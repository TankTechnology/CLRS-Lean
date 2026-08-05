# Chapter 29 Foundation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Represent CLRS standard-form linear programs, prove exact slack-variable feasibility equivalence, and prove CLRS Theorem 29.8 (weak duality).

**Architecture:** Use real matrices indexed by `Fin m` and `Fin n`.  Keep Section 29.1 and Section 29.4 as reader-facing aggregators over focused definition and theorem modules; protect every public tranche with a red-green interface test before wiring global documentation.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib matrices and finite sums, Verso literate documentation, Python repository consistency checks.

---

## File Map

Create these focused theorem modules:

```text
CLRSLean/Chapter_29.lean
CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean
CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Definitions.lean
CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SlackVariables.lean
CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Equivalence.lean
CLRSLean/Chapter_29/Section_29_4_Duality.lean
CLRSLean/Chapter_29/Section_29_4_Duality/Definitions.lean
CLRSLean/Chapter_29/Section_29_4_Duality/WeakDuality.lean
Tests/Chapter_29_Interface.lean
```

Modify these integration and status files only after the theorem interface is
green:

```text
CLRSLean.lean
CLRSLean/Progress.lean
CLRSLean/Status.lean
docs/clrs-proof-progress.csv
docs/index.md
docs/proof-map.md
docs/proof-status-board.md
literate.toml
```

## Task 1: Standard-Form Model

**Files:**

- Create: `Tests/Chapter_29_Interface.lean`
- Create: `CLRSLean/Chapter_29.lean`
- Create: `CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean`
- Create: `CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Definitions.lean`

- [ ] **Step 1: Write the failing public-interface test**

Create `Tests/Chapter_29_Interface.lean` with:

```lean
import CLRSLean.Chapter_29

/-!
# Chapter 29 Interface Test

Verifies that the represented Chapter 29 standard/slack and weak-duality
declarations are available through the chapter guide.
-/

namespace CLRS
namespace Chapter29

#check IsNonnegative
#check StandardLP
#check StandardLP.IsFeasible
#check StandardLP.objective

example {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) :
    P.objective x = P.c ⬝ᵥ x := rfl

end Chapter29
end CLRS
```

- [ ] **Step 2: Run the test and verify RED**

Run:

```bash
lake env lean Tests/Chapter_29_Interface.lean
```

Expected: failure at the import because module `CLRSLean.Chapter_29` does not
exist.  Any syntax error in the test must be fixed before proceeding.

- [ ] **Step 3: Add the standard-form definitions**

Create
`CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Definitions.lean`:

```lean
import Mathlib

/-!
# 29.1 Standard-form linear programs

This module defines the finite real matrix model used by Chapter 29.  A
standard-form program maximizes {lit}`cᵀx` subject to {lit}`Ax ≤ b` and
{lit}`0 ≤ x`.

Main declarations:

- {lit}`IsNonnegative`: pointwise nonnegativity of a finite vector.
- {lit}`StandardLP`: coefficients, bounds, and objective coefficients.
- {lit}`StandardLP.IsFeasible`: primal standard-form feasibility.
- {lit}`StandardLP.objective`: the value {lit}`cᵀx`.

Current gaps:

- Slack-variable equivalence is proved in later Section 29.1 modules.
- Basic/nonbasic dictionaries and SIMPLEX are not represented in this milestone.
-/

namespace CLRS
namespace Chapter29

open Matrix

/-- A finite real vector is nonnegative when every coordinate is nonnegative. -/
def IsNonnegative {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j, 0 ≤ x j

/-- A maximization linear program in CLRS standard form:
maximize {lit}`cᵀx` subject to {lit}`Ax ≤ b` and {lit}`0 ≤ x`. -/
structure StandardLP (m n : ℕ) where
  /-- The constraint coefficient matrix. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- The constraint right-hand side. -/
  b : Fin m → ℝ
  /-- The objective coefficient vector. -/
  c : Fin n → ℝ

namespace StandardLP

/-- A vector is primal feasible when it is nonnegative and satisfies every
row inequality of the standard-form program. -/
def IsFeasible {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) : Prop :=
  IsNonnegative x ∧ ∀ i, (P.A *ᵥ x) i ≤ P.b i

/-- The objective value {lit}`cᵀx` of a standard-form assignment. -/
def objective {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) : ℝ :=
  P.c ⬝ᵥ x

end StandardLP
end Chapter29
end CLRS
```

- [ ] **Step 4: Add the section and chapter aggregators**

Create `CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Definitions

/-!
# 29.1 Standard and slack forms

The represented foundation defines standard-form maximization programs over
finite real matrices.  Subsequent child modules add slack variables and prove
their exact feasibility equivalence.

The full CLRS basic/nonbasic dictionary model remains outside this milestone.
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
```

Create `CLRSLean/Chapter_29.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms

/-!
# Chapter 29 - Linear Programming

Chapter 29 develops linear-programming representations, SIMPLEX, and duality.
The current milestone represents standard/slack feasibility and weak duality.

## Represented sections

* 29.1 Standard and slack forms: standard-form definitions and the
  slack-variable feasibility bridge.

## Current gaps

Sections 29.2, 29.3, and 29.5 are not represented.  Section 29.4 will initially
contain weak duality only.  Basic/nonbasic dictionaries, PIVOT, SIMPLEX, strong
duality, complementary slackness, and INITIALIZE-SIMPLEX remain explicit gaps.
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
```

- [ ] **Step 5: Build the chapter and verify GREEN**

Run in order:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
git diff --check
```

Expected: Chapter 29 builds; the interface test prints the four declarations
and exits zero; the diff check has no output.

- [ ] **Step 6: Commit the standard-form tranche**

```bash
git add Tests/Chapter_29_Interface.lean CLRSLean/Chapter_29.lean \
  CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean \
  CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Definitions.lean
git commit -m "feat(ch29): define standard-form linear programs"
```

## Task 2: Canonical Slack Variables

**Files:**

- Modify: `Tests/Chapter_29_Interface.lean`
- Modify: `CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean`
- Create: `CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SlackVariables.lean`

- [ ] **Step 1: Extend the interface test before implementation**

Insert after the standard-form checks:

```lean
#check StandardLP.slack
#check StandardLP.IsSlackExtension
#check StandardLP.slack_nonnegative_of_feasible
#check StandardLP.slack_equation
#check StandardLP.slackExtension_of_feasible
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake env lean Tests/Chapter_29_Interface.lean
```

Expected: unknown identifiers beginning with `StandardLP.slack` because the
slack module does not exist.

- [ ] **Step 3: Implement the canonical slack construction**

Create
`CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SlackVariables.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Definitions

/-!
# 29.1 Slack-variable construction

The canonical slack vector for an assignment {lit}`x` is {lit}`b - Ax`.
Primal feasibility makes this vector nonnegative and converts every row
inequality into an equality.

Main results:

- {lit}`slack_nonnegative_of_feasible`.
- {lit}`slack_equation`.
- {lit}`slackExtension_of_feasible`.
-/

namespace CLRS
namespace Chapter29

open Matrix

namespace StandardLP

/-- The canonical slack vector {lit}`b - Ax`. -/
def slack {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => P.b i - (P.A *ᵥ x) i

/-- A nonnegative slack extension satisfies {lit}`Ax + s = b` coordinatewise. -/
def IsSlackExtension {m n : ℕ} (P : StandardLP m n)
    (x : Fin n → ℝ) (s : Fin m → ℝ) : Prop :=
  IsNonnegative x ∧ IsNonnegative s ∧
    ∀ i, (P.A *ᵥ x) i + s i = P.b i

/-- A feasible assignment has a nonnegative canonical slack vector. -/
theorem slack_nonnegative_of_feasible {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} (hx : P.IsFeasible x) :
    IsNonnegative (P.slack x) := by
  intro i
  exact sub_nonneg.mpr (hx.2 i)

/-- The canonical slack vector satisfies {lit}`Ax + slack(x) = b`. -/
theorem slack_equation {m n : ℕ} (P : StandardLP m n) (x : Fin n → ℝ) :
    ∀ i, (P.A *ᵥ x) i + P.slack x i = P.b i := by
  intro i
  simp [slack]

/-- Every primal-feasible assignment extends canonically to a nonnegative
equality-form assignment. -/
theorem slackExtension_of_feasible {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} (hx : P.IsFeasible x) :
    P.IsSlackExtension x (P.slack x) := by
  exact ⟨hx.1, slack_nonnegative_of_feasible hx, P.slack_equation x⟩

end StandardLP
end Chapter29
end CLRS
```

- [ ] **Step 4: Import the new module from the section aggregator**

Add this import after `Definitions`:

```lean
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.SlackVariables
```

- [ ] **Step 5: Verify GREEN and commit**

Run:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
git diff --check
```

Expected: all commands exit zero.

Commit:

```bash
git add Tests/Chapter_29_Interface.lean \
  CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean \
  CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SlackVariables.lean
git commit -m "feat(ch29): construct canonical slack variables"
```

## Task 3: Standard/Slack Feasibility Equivalence

**Files:**

- Modify: `Tests/Chapter_29_Interface.lean`
- Modify: `CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean`
- Create: `CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Equivalence.lean`

- [ ] **Step 1: Add the intended theorem interface**

Append these checks:

```lean
#check StandardLP.feasible_of_slackExtension
#check StandardLP.isFeasible_iff_exists_slackExtension
#check StandardLP.slackExtension_eq_slack
#check StandardLP.existsUnique_slackExtension_iff
```

Add this downstream-use example:

```lean
example {m n : ℕ} {P : StandardLP m n} {x : Fin n → ℝ} :
    P.IsFeasible x ↔ ∃! s, P.IsSlackExtension x s :=
  P.existsUnique_slackExtension_iff
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake env lean Tests/Chapter_29_Interface.lean
```

Expected: unknown equivalence theorem identifiers.

- [ ] **Step 3: Prove the converse, equivalence, and uniqueness**

Create
`CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Equivalence.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.SlackVariables

/-!
# 29.1 Standard/slack feasibility equivalence

This module proves the exact semantic bridge
{lit}`Ax ≤ b ↔ ∃ s ≥ 0, Ax + s = b` for nonnegative decision variables.
The slack vector is uniquely determined by the decision assignment.

Main results:

- {lit}`isFeasible_iff_exists_slackExtension`.
- {lit}`slackExtension_eq_slack`.
- {lit}`existsUnique_slackExtension_iff`.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- Eliminating nonnegative slack variables recovers primal feasibility. -/
theorem feasible_of_slackExtension {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} {s : Fin m → ℝ} (hxs : P.IsSlackExtension x s) :
    P.IsFeasible x := by
  refine ⟨hxs.1, ?_⟩
  intro i
  have hs : 0 ≤ s i := hxs.2.1 i
  have heq := hxs.2.2 i
  linarith

/-- Standard-form feasibility is equivalent to the existence of a nonnegative
slack vector satisfying the equality system. -/
theorem isFeasible_iff_exists_slackExtension {m n : ℕ}
    (P : StandardLP m n) {x : Fin n → ℝ} :
    P.IsFeasible x ↔ ∃ s, P.IsSlackExtension x s := by
  constructor
  · intro hx
    exact ⟨P.slack x, slackExtension_of_feasible hx⟩
  · rintro ⟨s, hxs⟩
    exact feasible_of_slackExtension hxs

/-- Every slack extension equals the canonical vector {lit}`b - Ax`. -/
theorem slackExtension_eq_slack {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} {s : Fin m → ℝ} (hxs : P.IsSlackExtension x s) :
    s = P.slack x := by
  funext i
  have heq := hxs.2.2 i
  simp only [slack]
  linarith

/-- A standard-form assignment is feasible exactly when it has a unique
nonnegative slack extension. -/
theorem existsUnique_slackExtension_iff {m n : ℕ}
    (P : StandardLP m n) {x : Fin n → ℝ} :
    P.IsFeasible x ↔ ∃! s, P.IsSlackExtension x s := by
  constructor
  · intro hx
    refine ⟨P.slack x, slackExtension_of_feasible hx, ?_⟩
    intro s hxs
    exact slackExtension_eq_slack hxs
  · rintro ⟨s, hxs, _⟩
    exact feasible_of_slackExtension hxs

end StandardLP
end Chapter29
end CLRS
```

- [ ] **Step 4: Import the equivalence module**

Add to the Section 29.1 aggregator:

```lean
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Equivalence
```

- [ ] **Step 5: Verify GREEN and the theorem axioms**

Temporarily add to the end of the interface namespace:

```lean
#print axioms StandardLP.isFeasible_iff_exists_slackExtension
#print axioms StandardLP.existsUnique_slackExtension_iff
```

Run:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
git diff --check
```

Expected: zero exits; axiom output contains no `sorryAx` or project axiom.

- [ ] **Step 6: Commit the equivalence tranche**

```bash
git add Tests/Chapter_29_Interface.lean \
  CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean \
  CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Equivalence.lean
git commit -m "feat(ch29): prove standard slack feasibility equivalence"
```

## Task 4: Dual Feasibility Definitions

**Files:**

- Modify: `Tests/Chapter_29_Interface.lean`
- Modify: `CLRSLean/Chapter_29.lean`
- Create: `CLRSLean/Chapter_29/Section_29_4_Duality.lean`
- Create: `CLRSLean/Chapter_29/Section_29_4_Duality/Definitions.lean`

- [ ] **Step 1: Add the dual interface checks**

Append:

```lean
#check StandardLP.IsDualFeasible
#check StandardLP.dualObjective
#check StandardLP.IsDualFeasible.nonnegative
#check StandardLP.IsDualFeasible.coefficient_le
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake env lean Tests/Chapter_29_Interface.lean
```

Expected: unknown dual declarations.

- [ ] **Step 3: Define dual feasibility and objective**

Create `CLRSLean/Chapter_29/Section_29_4_Duality/Definitions.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms

/-!
# 29.4 Dual linear programs

For a primal maximization program {lit}`max cᵀx` with {lit}`Ax ≤ b` and
{lit}`x ≥ 0`, a dual assignment satisfies {lit}`y ≥ 0` and
{lit}`Aᵀy ≥ c`; its objective is {lit}`bᵀy`.

Main declarations:

- {lit}`StandardLP.IsDualFeasible`.
- {lit}`StandardLP.dualObjective`.

Current gaps:

- Weak duality is proved in the next module.
- Strong duality and complementary slackness remain unrepresented.
-/

namespace CLRS
namespace Chapter29

open Matrix

namespace StandardLP

/-- A nonnegative vector satisfying {lit}`c ≤ Aᵀy` is dual feasible. -/
def IsDualFeasible {m n : ℕ} (P : StandardLP m n) (y : Fin m → ℝ) : Prop :=
  IsNonnegative y ∧ ∀ j, P.c j ≤ (P.A.transpose *ᵥ y) j

/-- The dual objective value {lit}`bᵀy`. -/
def dualObjective {m n : ℕ} (P : StandardLP m n) (y : Fin m → ℝ) : ℝ :=
  P.b ⬝ᵥ y

namespace IsDualFeasible

/-- A dual-feasible assignment is coordinatewise nonnegative. -/
theorem nonnegative {m n : ℕ} {P : StandardLP m n} {y : Fin m → ℝ}
    (hy : P.IsDualFeasible y) : IsNonnegative y :=
  hy.1

/-- A dual-feasible assignment bounds each primal objective coefficient by
the corresponding coordinate of {lit}`Aᵀy`. -/
theorem coefficient_le {m n : ℕ} {P : StandardLP m n} {y : Fin m → ℝ}
    (hy : P.IsDualFeasible y) :
    ∀ j, P.c j ≤ (P.A.transpose *ᵥ y) j :=
  hy.2

end IsDualFeasible
end StandardLP
end Chapter29
end CLRS
```

- [ ] **Step 4: Add the Section 29.4 and chapter imports**

Create `CLRSLean/Chapter_29/Section_29_4_Duality.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_4_Duality.Definitions

/-!
# 29.4 Duality

The represented layer defines dual feasibility and the dual objective.  The
next child module proves CLRS Theorem 29.8, weak duality.

Strong duality and complementary slackness remain explicit gaps.
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
```

Add to `CLRSLean/Chapter_29.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_4_Duality
```

Update its represented-sections list with:

```text
* 29.4 Duality: dual feasibility and weak duality.
```

- [ ] **Step 5: Verify GREEN and commit**

Run:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
git diff --check
```

Expected: zero exits.

Commit:

```bash
git add Tests/Chapter_29_Interface.lean CLRSLean/Chapter_29.lean \
  CLRSLean/Chapter_29/Section_29_4_Duality.lean \
  CLRSLean/Chapter_29/Section_29_4_Duality/Definitions.lean
git commit -m "feat(ch29): define dual feasibility"
```

## Task 5: CLRS Theorem 29.8 Weak Duality

**Files:**

- Modify: `Tests/Chapter_29_Interface.lean`
- Modify: `CLRSLean/Chapter_29/Section_29_4_Duality.lean`
- Create: `CLRSLean/Chapter_29/Section_29_4_Duality/WeakDuality.lean`

- [ ] **Step 1: Add the weak-duality interface before its proof**

Append:

```lean
#check StandardLP.dotProduct_mono_right_of_nonnegative
#check StandardLP.dotProduct_mono_left_of_nonnegative
#check StandardLP.transpose_mulVec_dotProduct
#check StandardLP.weak_duality
```

Add the downstream theorem-shape example:

```lean
example {m n : ℕ} {P : StandardLP m n}
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y) :
    P.objective x ≤ P.dualObjective y :=
  P.weak_duality hx hy
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake env lean Tests/Chapter_29_Interface.lean
```

Expected: unknown weak-duality and helper theorem identifiers.

- [ ] **Step 3: Prove the finite-sum monotonicity helpers and transpose identity**

Create `CLRSLean/Chapter_29/Section_29_4_Duality/WeakDuality.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_4_Duality.Definitions

/-!
# 29.4 Weak duality

This module proves CLRS Theorem 29.8.  For every primal-feasible {lit}`x` and
dual-feasible {lit}`y`, the primal objective is bounded by the dual objective:
{lit}`cᵀx ≤ bᵀy`.

The proof follows the CLRS calculation
{lit}`cᵀx ≤ (Aᵀy)ᵀx = yᵀAx ≤ yᵀb`.

Main result:

- {lit}`StandardLP.weak_duality`: CLRS Theorem 29.8.

Current gaps:

- Strong duality (Theorem 29.9) and complementary slackness (Theorem 29.10).
-/

namespace CLRS
namespace Chapter29

open Matrix

namespace StandardLP

/-- Increasing the left factor of a dot product preserves order when the right
factor is coordinatewise nonnegative. -/
theorem dotProduct_mono_right_of_nonnegative {n : ℕ}
    {a b x : Fin n → ℝ} (hab : ∀ i, a i ≤ b i) (hx : IsNonnegative x) :
    a ⬝ᵥ x ≤ b ⬝ᵥ x := by
  simp only [dotProduct]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hab i) (hx i)

/-- Increasing the right factor of a dot product preserves order when the left
factor is coordinatewise nonnegative. -/
theorem dotProduct_mono_left_of_nonnegative {n : ℕ}
    {a b y : Fin n → ℝ} (hab : ∀ i, a i ≤ b i) (hy : IsNonnegative y) :
    y ⬝ᵥ a ≤ y ⬝ᵥ b := by
  simp only [dotProduct]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hab i) (hy i)

/-- Moving a matrix transpose across a finite dot product exchanges the order
of summation: {lit}`(Aᵀy)ᵀx = yᵀ(Ax)`. -/
theorem transpose_mulVec_dotProduct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ) :
    (A.transpose *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (A *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **CLRS Theorem 29.8 (weak duality).**  Every primal-feasible objective
value is at most every dual-feasible objective value. -/
theorem weak_duality {m n : ℕ} (P : StandardLP m n)
    {x : Fin n → ℝ} {y : Fin m → ℝ}
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y) :
    P.objective x ≤ P.dualObjective y := by
  calc
    P.objective x = P.c ⬝ᵥ x := rfl
    _ ≤ (P.A.transpose *ᵥ y) ⬝ᵥ x :=
      dotProduct_mono_right_of_nonnegative hy.coefficient_le hx.1
    _ = y ⬝ᵥ (P.A *ᵥ x) := transpose_mulVec_dotProduct P.A y x
    _ ≤ y ⬝ᵥ P.b :=
      dotProduct_mono_left_of_nonnegative hx.2 hy.nonnegative
    _ = P.dualObjective y := by
      simp only [dualObjective, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring

end StandardLP
end Chapter29
end CLRS
```

- [ ] **Step 4: Import the weak-duality module**

Add to `CLRSLean/Chapter_29/Section_29_4_Duality.lean`:

```lean
import CLRSLean.Chapter_29.Section_29_4_Duality.WeakDuality
```

- [ ] **Step 5: Add the final axiom audit and verify GREEN**

Append to the interface test:

```lean
#print axioms StandardLP.weak_duality
```

Run in order:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_29 Tests/Chapter_29_Interface.lean || true
git diff --check
```

Expected: build and interface test exit zero; axiom output has no `sorryAx` or
project axiom; the marker scan and diff check have no output.

- [ ] **Step 6: Commit weak duality**

```bash
git add Tests/Chapter_29_Interface.lean \
  CLRSLean/Chapter_29/Section_29_4_Duality.lean \
  CLRSLean/Chapter_29/Section_29_4_Duality/WeakDuality.lean
git commit -m "feat(ch29): prove weak duality"
```

## Task 6: Wire Chapter 29 Into The Book And Status Ledger

**Files:**

- Modify: `CLRSLean.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/clrs-proof-progress.csv`
- Regenerate: `CLRSLean/Progress.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-map.md`
- Modify: `docs/proof-status-board.md`

- [ ] **Step 1: Import Chapter 29 from the library root**

Insert after Chapter 28:

```lean
import CLRSLean.Chapter_29
```

- [ ] **Step 2: Register the exact literate navigation tree**

Add `CLRSLean.Chapter_29` between Chapters 28 and 32 in the root order.
Add these parent-child relations:

```toml
"CLRSLean.Chapter_29" = [
  "CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms",
  "CLRSLean.Chapter_29.Section_29_4_Duality",
]
"CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms" = [
  "CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Definitions",
  "CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.SlackVariables",
  "CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Equivalence",
]
"CLRSLean.Chapter_29.Section_29_4_Duality" = [
  "CLRSLean.Chapter_29.Section_29_4_Duality.Definitions",
  "CLRSLean.Chapter_29.Section_29_4_Duality.WeakDuality",
]
```

Add these titles:

```toml
[modules."CLRSLean.Chapter_29"]
title = "Chapter 29. Linear Programming"

[modules."CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms"]
title = "29.1. Standard and Slack Forms"

[modules."CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Definitions"]
title = "29.1. Standard-Form Definitions"

[modules."CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.SlackVariables"]
title = "29.1. Canonical Slack Variables"

[modules."CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Equivalence"]
title = "29.1. Standard/Slack Equivalence"

[modules."CLRSLean.Chapter_29.Section_29_4_Duality"]
title = "29.4. Duality"

[modules."CLRSLean.Chapter_29.Section_29_4_Duality.Definitions"]
title = "29.4. Dual Feasibility"

[modules."CLRSLean.Chapter_29.Section_29_4_Duality.WeakDuality"]
title = "29.4. Weak Duality"
```

- [ ] **Step 3: Add every new module to `docs/index.md`**

Insert after the Chapter 28 entries:

```text
CLRSLean/Chapter_29.lean
CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean
CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Definitions.lean
CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SlackVariables.lean
CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Equivalence.lean
CLRSLean/Chapter_29/Section_29_4_Duality.lean
CLRSLean/Chapter_29/Section_29_4_Duality/Definitions.lean
CLRSLean/Chapter_29/Section_29_4_Duality/WeakDuality.lean
```

- [ ] **Step 4: Replace the Chapter 29 progress row exactly**

Use this CSV row:

```csv
29,Linear Programming,partial,29.1;29.4,2,2,1,"Standard-form maximization programs, canonical nonnegative slack variables, exact standard/slack feasibility equivalence with unique slack, dual feasibility, and CLRS Theorem 29.8 weak duality are kernel-checked",isFeasible_iff_exists_slackExtension; weak_duality (Theorem 29.8),"Add basic/nonbasic dictionaries and executable PIVOT/SIMPLEX; formalize Sections 29.2 and 29.5; prove strong duality (Theorem 29.9) and complementary slackness (Theorem 29.10)",CLRSLean/Chapter_29.lean; CLRSLean/Chapter_29/Section_29_1_Standard_And_Slack_Forms.lean; CLRSLean/Chapter_29/Section_29_4_Duality.lean; Tests/Chapter_29_Interface.lean,"Sections 29.1 and 29.4 are partial: the slack-variable semantic bridge and weak duality are proved, while dictionaries/SIMPLEX and the strong-duality layer remain."
```

Regenerate the dashboard:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
```

Expected summary: 35 chapters, 1709 tracked theorem entries, 1709 proved.

- [ ] **Step 5: Add honest reader-facing status prose**

Add Chapter 29 to `Structured But Partial` in `CLRSLean/Status.lean`:

```text
* **Chapter 29:** Sections 29.1 and 29.4 represent standard-form feasibility,
  the unique nonnegative slack-variable extension, dual feasibility, and weak
  duality (Theorem 29.8).  The chapter remains partial pending basic/nonbasic
  dictionaries, PIVOT/SIMPLEX, Sections 29.2 and 29.5, strong duality, and
  complementary slackness.
```

Change the not-represented list to Chapters 30--31 and 34--35.

Add this row to the partial table in `docs/proof-status-board.md`:

```text
| 29 | Standard-form/slack feasibility equivalence and CLRS Theorem 29.8 weak duality | Add basic/nonbasic dictionaries, executable PIVOT/SIMPLEX, strong duality, complementary slackness, and INITIALIZE-SIMPLEX |
```

Change its not-represented list to Chapters 30--31 and 34--35.

- [ ] **Step 6: Add the detailed proof-map entry**

Insert a `Chapter 29 - Linear Programming` section between Chapters 28 and 32.
Record:

```text
### Section 29.1 - Standard and Slack Forms

- Status: `partial`.
- Model: `StandardLP`, `IsNonnegative`, `StandardLP.IsFeasible`, and
  `StandardLP.objective` over `Fin`-indexed real matrices.
- Proved: `slack_nonnegative_of_feasible`, `slack_equation`,
  `slackExtension_of_feasible`, `feasible_of_slackExtension`,
  `isFeasible_iff_exists_slackExtension`, `slackExtension_eq_slack`, and
  `existsUnique_slackExtension_iff`.
- Exact gap: CLRS basic/nonbasic dictionaries and their standard-form semantic
  refinement are not represented.

### Section 29.4 - Duality

- Status: `partial`.
- Model: `StandardLP.IsDualFeasible` and `StandardLP.dualObjective`.
- Proved: dot-product monotonicity, `transpose_mulVec_dotProduct`, and
  `weak_duality` (CLRS Theorem 29.8).
- Exact gap: strong duality (Theorem 29.9) and complementary slackness
  (Theorem 29.10).

### Unrepresented main-text sections

- 29.2 graph problems as linear programs.
- 29.3 PIVOT, SIMPLEX, and Bland-rule termination.
- 29.5 auxiliary LP and INITIALIZE-SIMPLEX.
```

- [ ] **Step 7: Verify book wiring before committing**

Run:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
uv run python scripts/check_repository.py
lake build CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms:literate
lake build CLRSLean.Chapter_29.Section_29_4_Duality:literate
git diff --check
```

Expected: all commands exit zero.  Literate warnings from new Chapter 29 files
must be fixed; unrelated dependency warnings may be recorded but do not require
out-of-scope edits.

- [ ] **Step 8: Commit the book integration**

```bash
git add CLRSLean.lean CLRSLean/Progress.lean CLRSLean/Status.lean \
  docs/clrs-proof-progress.csv docs/index.md docs/proof-map.md \
  docs/proof-status-board.md literate.toml
git commit -m "docs(ch29): register foundation milestone"
```

## Task 7: Final Focused Verification And Review Handoff

**Files:**

- Inspect: all files changed from `origin/main`

- [ ] **Step 1: Run the final focused gate fresh**

Run in this order so the interface test never reads a stale chapter object:

```bash
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
lake build CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms:literate
lake build CLRSLean.Chapter_29.Section_29_4_Duality:literate
uv run python scripts/check_repository.py
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_29 Tests/Chapter_29_Interface.lean || true
git diff --check origin/main...HEAD
git status --short --branch
```

Expected:

- Chapter 29 build exits zero.
- Interface test exits zero and both axiom audits contain no `sorryAx` or
  project axiom.
- Both focused literate modules build with no new Chapter 29 warnings.
- Repository checks pass with 1709/1709 represented theorem entries.
- Marker scan and diff check have no output.
- Worktree is clean and ahead of `origin/main` only by the planned commits.

- [ ] **Step 2: Review the complete scope diff**

Run:

```bash
git diff --name-status origin/main...HEAD
git diff --stat origin/main...HEAD
git log --oneline origin/main..HEAD
```

Confirm that the diff contains only the design/plan, Chapter 29 source and
interface test, and the enumerated book/status files.  Confirm no Chapter 28 or
Chapter 30 production file changed.

- [ ] **Step 3: Prepare the review summary**

Report:

- the two proved reader-facing groups;
- the exact partial boundary for Sections 29.1 and 29.4;
- the focused verification commands and exit results;
- the commit list; and
- the recommendation that the next milestone introduce dictionary semantics
  before executable PIVOT.
