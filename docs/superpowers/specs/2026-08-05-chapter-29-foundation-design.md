# Chapter 29 Foundation Milestone Design

## Goal

Establish the first theorem-bearing Chapter 29 boundary for CLRS third-edition
linear programming:

- represent maximization linear programs in standard form over finite real
  vectors;
- prove that standard-form feasibility is equivalent to the existence of
  nonnegative slack variables satisfying the corresponding equality system;
- represent dual feasibility and the dual objective; and
- prove CLRS Theorem 29.8, weak duality.

This milestone deliberately creates the stable mathematical interface that
later SIMPLEX, strong-duality, and application reductions will consume.  It
does not claim that Chapter 29, Section 29.1, or Section 29.4 is complete.

## Full Chapter Inventory

Every main-text section is accounted for even though this milestone implements
only the first foundation tranche.

| Section | Main CLRS content | Best current Lean target | Status after this milestone |
| --- | --- | --- | --- |
| 29.1 | Standard form, slack form, basic and nonbasic variables | Standard-form model; nonnegative slack-variable extension; feasibility equivalence | `partial` |
| 29.2 | Shortest paths, maximum flow, and minimum-cost flow as linear programs | Exact reductions from the existing Chapter 24 and Chapter 26 models, preserving feasible solutions and objective values | `not-represented` |
| 29.3 | PIVOT and SIMPLEX | Executable dictionary pivot, invariant preservation, objective monotonicity, optimality at termination, and Bland-rule termination | `not-represented` |
| 29.4 | Dual construction, weak duality, strong duality, complementary slackness | Dual-feasibility interface and weak duality in this milestone; strong duality and complementary slackness in later milestones | `partial` |
| 29.5 | Auxiliary LP and INITIALIZE-SIMPLEX | Executable auxiliary problem, feasibility detection, and valid initial dictionary | `not-represented` |

The chapter progress row remains `partial` with one aggregated remaining core
group.  The proof map names the exact unrepresented algorithms and theorems.

## Scope

### Included

- Finite-dimensional real matrices and vectors indexed by `Fin m` and `Fin n`.
- Maximization standard form

  ```text
  maximize cᵀx subject to Ax ≤ b and 0 ≤ x.
  ```

- A slack-variable extension represented by a pair of vectors `(x, s)` with

  ```text
  0 ≤ x, 0 ≤ s, and Ax + s = b.
  ```

- The canonical slack vector `b - Ax`.
- Existence, construction, elimination, and uniqueness facts for slack
  extensions.
- Dual feasibility

  ```text
  0 ≤ y and c ≤ Aᵀy.
  ```

- The dual objective `bᵀy`.
- The matrix/dot-product bridge used by weak duality.
- CLRS Theorem 29.8: every primal-feasible objective value is at most every
  dual-feasible objective value.
- Chapter guide, literate navigation, progress/status records, proof map, and a
  focused public-interface/axiom test.

### Excluded

- The full CLRS slack dictionary with disjoint basic and nonbasic variable
  index sets.
- Basic solutions, feasible dictionaries, PIVOT, SIMPLEX, Bland's rule, and
  running-time claims.
- Strong duality, Farkas certificates, separating hyperplanes, and
  complementary slackness.
- The Section 29.2 graph-problem reductions.
- The Section 29.5 auxiliary linear program and initialization algorithm.
- Mutable arrays, numerical stability, floating-point arithmetic, rational
  certificates, solver extraction, and RAM-cost accounting.
- Chapter-end exercises and problems.

These exclusions must be visible in the Chapter 29 guide, progress row, proof
map, and reader-facing status page.  In particular, the slack-variable
extension is mathematical scaffolding for the later dictionary model and must
not be described as complete SIMPLEX infrastructure.

## Representation Boundary

### Scalar and indices

The public model is specialized to `ℝ`.  Ordered feasibility and objective
comparison are central to this milestone, and real scalars keep the public API
aligned with CLRS while avoiding unused ordered-field generality.  A later
generalization to a linear ordered field is permitted only if it does not
complicate the CLRS-facing theorem names.

Constraints use `Fin m`; variables use `Fin n`.  This matches Chapter 28's
matrix representation and gives later executable SIMPLEX code concrete finite
indices without reindexing an arbitrary `Fintype` at every pivot.

### Standard-form program

The foundational structure is:

```lean
structure StandardLP (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
```

The program owns no solution or decidability evidence.  Its semantic interface
is defined in the namespace `StandardLP`:

```lean
def IsNonnegative (x : Fin n → ℝ) : Prop :=
  ∀ j, 0 ≤ x j

def StandardLP.IsFeasible (P : StandardLP m n) (x : Fin n → ℝ) : Prop :=
  IsNonnegative x ∧ ∀ i, (P.A *ᵥ x) i ≤ P.b i

def StandardLP.objective (P : StandardLP m n) (x : Fin n → ℝ) : ℝ :=
  P.c ⬝ᵥ x
```

`IsNonnegative` is a chapter-level definition shared by primal variables,
slack variables, and dual variables.  It avoids three locally different
spellings of pointwise nonnegativity.

### Slack-variable extension

The canonical slack vector and its semantic relation are:

```lean
def StandardLP.slack (P : StandardLP m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => P.b i - (P.A *ᵥ x) i

def StandardLP.IsSlackExtension
    (P : StandardLP m n) (x : Fin n → ℝ) (s : Fin m → ℝ) : Prop :=
  IsNonnegative x ∧ IsNonnegative s ∧
    ∀ i, (P.A *ᵥ x) i + s i = P.b i
```

This relation is intentionally independent of the objective.  Adding slack
variables changes the constraint representation but not the decision-variable
objective `cᵀx`.

All functions are total.  Invalid assignments are represented by the failure
of `IsFeasible` or `IsSlackExtension`, not by exceptions or `Option` results.

### Dual semantics

The first dual layer belongs to the primal program rather than a second program
structure with sign-negated coefficients:

```lean
def StandardLP.IsDualFeasible
    (P : StandardLP m n) (y : Fin m → ℝ) : Prop :=
  IsNonnegative y ∧ ∀ j, P.c j ≤ (P.A.transpose *ᵥ y) j

def StandardLP.dualObjective
    (P : StandardLP m n) (y : Fin m → ℝ) : ℝ :=
  P.b ⬝ᵥ y
```

This directly exposes the CLRS dual conditions and avoids encoding a
minimization problem as a maximization problem by negation.  A later explicit
`DualLP` construction may wrap these semantics when strong duality needs a
program-to-program involution theorem.

## Module Layout

```text
CLRSLean/Chapter_29.lean

CLRSLean/Chapter_29/
  Section_29_1_Standard_And_Slack_Forms.lean
  Section_29_1_Standard_And_Slack_Forms/
    Definitions.lean
    SlackVariables.lean
    Equivalence.lean

  Section_29_4_Duality.lean
  Section_29_4_Duality/
    Definitions.lean
    WeakDuality.lean

Tests/Chapter_29_Interface.lean
```

The two section files are reader-facing aggregators.  Each theorem-bearing
submodule has one responsibility and should normally stay below 300 lines.
If a proof exceeds that size, it is split at a genuine theorem dependency,
such as dot-product monotonicity versus the final weak-duality composition.

All declarations live in `CLRS.Chapter29`.  Section 29.4 imports the represented
standard/slack foundation from Section 29.1; Section 29.1 never imports Section
29.4 or Chapter 28.  This milestone therefore proceeds independently while
another contributor continues Chapter 28.

## Section 29.1 Public Theorem Surface

### Definitions module

`Definitions.lean` owns only `IsNonnegative`, `StandardLP`, `IsFeasible`, and
`objective`, plus small simplification lemmas that expose their definitions.
The interface test checks the public types before any downstream proof is
written.

### Slack construction module

`SlackVariables.lean` owns `slack`, `IsSlackExtension`, and these public facts:

```lean
theorem slack_nonnegative_of_feasible
    (hx : P.IsFeasible x) : IsNonnegative (P.slack x)

theorem slack_equation
    (P : StandardLP m n) (x : Fin n → ℝ) :
    ∀ i, (P.A *ᵥ x) i + P.slack x i = P.b i

theorem slackExtension_of_feasible
    (hx : P.IsFeasible x) : P.IsSlackExtension x (P.slack x)
```

The construction theorem is the forward semantic refinement from inequalities
to equalities with nonnegative slack.

### Equivalence module

`Equivalence.lean` owns the converse and the strong public specification:

```lean
theorem feasible_of_slackExtension
    (hxs : P.IsSlackExtension x s) : P.IsFeasible x

theorem isFeasible_iff_exists_slackExtension
    (P : StandardLP m n) :
    P.IsFeasible x ↔ ∃ s, P.IsSlackExtension x s

theorem slackExtension_eq_slack
    (hxs : P.IsSlackExtension x s) : s = P.slack x

theorem existsUnique_slackExtension_iff
    (P : StandardLP m n) :
    P.IsFeasible x ↔ ∃! s, P.IsSlackExtension x s
```

The existential equivalence is the reader-facing standard/slack theorem.  The
uniqueness theorem prevents later dictionary work from carrying arbitrary
slack vectors that are already determined by `x`.

## Section 29.4 Weak-Duality Surface

### Dual definitions module

`Definitions.lean` owns `IsDualFeasible` and `dualObjective`.  It also proves
direct wrappers for the two projections:

```lean
theorem IsDualFeasible.nonnegative
theorem IsDualFeasible.coefficient_le
```

These wrappers prevent downstream proofs from unfolding a conjunction.

### Weak-duality module

`WeakDuality.lean` proves the reusable finite-sum lemmas needed for the CLRS
calculation:

```lean
theorem dotProduct_mono_right_of_nonnegative
theorem dotProduct_mono_left_of_nonnegative
theorem transpose_mulVec_dotProduct
```

Their intended composition is:

```text
cᵀx ≤ (Aᵀy)ᵀx = yᵀ(Ax) ≤ yᵀb.
```

The headline theorem is:

```lean
/-- CLRS Theorem 29.8, weak duality. -/
theorem weak_duality
    (P : StandardLP m n)
    (hx : P.IsFeasible x) (hy : P.IsDualFeasible y) :
    P.objective x ≤ P.dualObjective y
```

The proof must use the represented primal and dual predicates directly.  A
theorem assuming the middle inequalities as opaque hypotheses would be a helper,
not completion of this milestone.

Useful consequences may be added only after `weak_duality` is green:

```lean
theorem objective_le_of_dualFeasible
theorem dualObjective_ge_of_primalFeasible
```

These wrappers are acceptable when they remove repeated argument ordering in
later strong-duality work; they do not count as separate textbook groups.

## TDD And Interface Verification

`Tests/Chapter_29_Interface.lean` is written before production declarations.
The first run must fail because `CLRSLean.Chapter_29` or the requested public
names do not exist.  Each proof tranche follows this loop:

1. add the intended `#check` or a small type-correct example;
2. run `lake env lean Tests/Chapter_29_Interface.lean` and confirm the expected
   missing import or identifier;
3. add the smallest production definition or theorem that satisfies the
   interface;
4. build only the affected Chapter 29 module;
5. rerun the interface test; and
6. commit the green tranche before starting the next theorem family.

The final interface test includes:

```lean
#check StandardLP
#check StandardLP.IsFeasible
#check StandardLP.objective
#check StandardLP.slack
#check StandardLP.IsSlackExtension
#check StandardLP.isFeasible_iff_exists_slackExtension
#check StandardLP.existsUnique_slackExtension_iff
#check StandardLP.IsDualFeasible
#check StandardLP.dualObjective
#check StandardLP.weak_duality

#print axioms StandardLP.isFeasible_iff_exists_slackExtension
#print axioms StandardLP.weak_duality
```

The accepted axiom list is restricted to Lean/Mathlib foundations such as
`propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` and project axioms are
forbidden.

## Documentation And Status

The implementation wires:

- `CLRSLean.lean`;
- `CLRSLean/Chapter_29.lean`;
- both section aggregators and their child order in `literate.toml`;
- `docs/index.md`;
- `docs/clrs-proof-progress.csv`;
- regenerated `CLRSLean/Progress.lean`;
- `CLRSLean/Status.lean`;
- `docs/proof-map.md`; and
- `docs/proof-status-board.md`.

The progress row records Sections 29.1 and 29.4 as represented and Chapter 29
as `partial`.  It tracks the slack-equivalence group and weak-duality group as
proved, while retaining one aggregated missing core group for Sections 29.2,
29.3, the strong-duality/complementary-slackness layer of 29.4, and 29.5.

No prose may call Section 29.1 complete because basic/nonbasic dictionaries are
not represented.  No prose may call Section 29.4 complete because Theorems
29.9 and 29.10 remain.

## Verification Boundary

Development verification is intentionally focused rather than repository-wide
compilation:

```text
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
lake build CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms:literate
lake build CLRSLean.Chapter_29.Section_29_4_Duality:literate
uv run python scripts/check_repository.py
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_29 Tests/Chapter_29_Interface.lean
git diff --check
```

A full library or full site build is not part of the ordinary milestone gate.
It is reserved for a release boundary or a change to shared build/navigation
infrastructure.

## Acceptance Criteria

The milestone is ready for review when all of the following hold:

1. The public structures and predicates match the signatures in this design.
2. Standard feasibility is equivalent to a unique nonnegative slack extension.
3. `weak_duality` proves the CLRS primal/dual objective inequality from the
   represented feasibility predicates.
4. The focused interface and axiom audit compile without placeholders.
5. Chapter 29 is imported and visible in literate navigation.
6. Progress, proof map, status board, and chapter guide agree that the chapter
   is partial.
7. All Chapter 29 source files remain focused; no theorem-bearing file grows
   into a chapter-sized monolith.

## Next Milestone Order

After this foundation lands, the recommended order is:

1. introduce basic/nonbasic variable dictionaries and prove standard/slack
   semantic refinement;
2. define executable PIVOT and prove equation, feasibility, and objective
   invariants;
3. prove SIMPLEX correctness at termination and then Bland-rule termination;
4. use Mathlib's convex-cone/Farkas infrastructure for strong duality and prove
   complementary slackness;
5. implement INITIALIZE-SIMPLEX; and
6. add the Chapter 24/26 application reductions.

This order keeps algebraic optimality certificates independent of Chapter 28
while allowing a later concrete pivot implementation to reuse the matrix and
linear-system layer as it stabilizes.
