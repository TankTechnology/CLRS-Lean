# Chapter 29 SIMPLEX/PIVOT Design

Date: 2026-08-05

## Objective

Advance the Chapter 29 formalization from standard/slack feasibility and weak
duality into the central CLRS algorithm.  This milestone formalizes slack-form
dictionaries, their basic solutions, the textbook PIVOT transformation, and
the one-step feasibility and objective theorems used by SIMPLEX.

The milestone is not presented as completion of Section 29.3.  Executable
entering/leaving selection, the unbounded branch, the SIMPLEX loop, Bland-rule
termination, and optimality at loop exit remain the immediately following
milestone.

The overall chapter continues until every main-text section in issue #84 has
an honest theorem-bearing account:

1. Section 29.1: standard/slack forms and basic/nonbasic dictionaries.
2. Section 29.2: shortest paths, maximum flow, and minimum-cost flow as LPs.
3. Section 29.3: PIVOT, SIMPLEX, Bland termination, and optimality.
4. Section 29.4: weak/strong duality and complementary slackness.
5. Section 29.5: auxiliary LP and INITIALIZE-SIMPLEX.

## Current Starting Point

The existing Chapter 29 foundation provides:

- `StandardLP`, `StandardLP.IsFeasible`, and the objective `cᵀx` over `ℝ`;
- canonical slack variables and exact standard/slack feasibility equivalence;
- uniqueness of the canonical slack extension;
- dual feasibility, the dual objective, and CLRS Theorem 29.8 weak duality.

The new dictionary layer must refine these declarations instead of introducing
an unrelated simplex-only model.

## Chosen Representation

### Variable names and fixed slots

For an LP with `m` constraints and `n` original variables, define

```lean
abbrev LPVar (m n : ℕ) := Fin n ⊕ Fin m
```

Original variables use the left injection and slack variables use the right
injection.  A dictionary has `m` basic slots and `n` nonbasic slots throughout
every pivot.  Variable identities are carried by an equivalence:

```lean
labels : (Fin m ⊕ Fin n) ≃ LPVar m n
```

The basic variable in row `i` is `labels (.inl i)`; the nonbasic variable in
column `j` is `labels (.inr j)`.  PIVOT composes `labels` with a swap of the
leaving row position and entering column position.

This fixed-slot representation avoids dependent matrix transports after every
pivot while retaining the stable variable identities required later by
Bland's rule.

### Dictionary data

```lean
structure Dictionary (m n : ℕ) where
  labels : (Fin m ⊕ Fin n) ≃ LPVar m n
  b : Fin m → ℝ
  a : Matrix (Fin m) (Fin n) ℝ
  v : ℝ
  c : Fin n → ℝ
```

The row and objective conventions match CLRS:

```text
x_basic(i) = b_i - Σ_j a_ij x_nonbasic(j)
z          = v   + Σ_j c_j  x_nonbasic(j)
```

The definitions expose `basicVar`, `nonbasicVar`, `rowRhs`, and
`objectiveRhs` rather than requiring downstream proofs to unfold label and
finite-sum details repeatedly.

## Semantic Interface

`Dictionary.Satisfies D x` states every row equation for a complete assignment
`x : LPVar m n → ℝ`.  `Dictionary.objectiveAt D x` evaluates the dictionary's
objective expression.

The basic assignment is defined through `D.labels.symm`:

- a variable in a basic position receives the corresponding `D.b` value;
- a variable in a nonbasic position receives zero.

The public basic-solution interface proves:

- the basic assignment satisfies every dictionary row;
- its nonbasic variables are zero;
- its basic variables equal `D.b`;
- it is coordinatewise nonnegative exactly when every `D.b i` is nonnegative.

`Dictionary.IsBasicFeasible` abbreviates the last row-wise nonnegativity
condition.  It is deliberately a property of the dictionary rather than a
proof field, so PIVOT remains a data transformation and theorem hypotheses stay
explicit.

## Bridge From Standard Form

`StandardLP.initialDictionary` uses the label equivalence that places slack
variables in basic slots and original variables in nonbasic slots:

```text
b = P.b,  a = P.A,  v = 0,  c = P.c.
```

For an original assignment `x` and slack vector `s`, define their combined
`LPVar` assignment.  Prove:

- the initial dictionary rows are satisfied exactly when `Ax + s = b`;
- a `StandardLP.IsSlackExtension x s` yields nonnegative combined values that
  satisfy the initial dictionary;
- the initial dictionary objective equals `P.objective x`;
- the initial dictionary's basic solution is feasible exactly when `P.b` is
  coordinatewise nonnegative.

The final fact explains why Section 29.5 is necessary when some right-hand side
is negative.

## PIVOT Definition

For leaving row `l : Fin m`, entering column `e : Fin n`, and
`h : D.a l e ≠ 0`, define the pivot ratio data and update formulas exactly as
in CLRS.  With `p = D.a l e`:

```text
b'_l     = b_l / p
a'_l,e   = 1 / p                         -- column e now names the old basic var
a'_l,j   = a_l,j / p                     -- j ≠ e

b'_i     = b_i - a_i,e * b'_l            -- i ≠ l
a'_i,e   = -a_i,e * a'_l,e               -- i ≠ l
a'_i,j   = a_i,j - a_i,e * a'_l,j        -- i ≠ l, j ≠ e

v'       = v + c_e * b'_l
c'_e     = -c_e * a'_l,e
c'_j     = c_j - c_e * a'_l,j            -- j ≠ e
```

The fixed matrix column `e` becomes the coefficient column for the old leaving
variable after the label swap.  This convention is documented next to the
definition to prevent later algorithms from treating slots as permanent
variable identities.

## PIVOT Algebra And Semantics

Small projection theorems record each branch of the formula, including the
leaving row, every other row, the entering column, and every other column.
These are used instead of repeatedly simplifying nested `if` expressions.

The main algebraic theorem is semantic equivalence:

```lean
D.Satisfies x ↔ (D.pivot l e h).Satisfies x
```

The proof is split into:

1. solving the leaving row for the entering variable;
2. substituting that equality in every other row;
3. the reverse substitution that recovers the old leaving row and old rows.

The objective-expression theorem states that old and new dictionary objective
expressions agree on assignments satisfying the dictionary.  PIVOT therefore
changes neither the feasible set nor the objective function; it only changes
which variables are basic.

## Minimum Ratio And Feasibility

Define a certificate:

```lean
def IsMinimumRatio (D : Dictionary m n) (e : Fin n) (l : Fin m) : Prop :=
  0 < D.a l e ∧
    ∀ i, 0 < D.a i e → D.b l / D.a l e ≤ D.b i / D.a i e
```

For a basic-feasible dictionary and such a certificate, prove all new right-
hand sides nonnegative:

- the new leaving-row value is nonnegative because `b_l ≥ 0` and the pivot
  coefficient is positive;
- a row with positive entering coefficient follows from the minimum-ratio
  inequality after clearing positive denominators;
- a row with nonpositive entering coefficient cannot decrease.

This yields `pivot_isBasicFeasible`.

No hidden generic certificate replaces the ratio-test argument: the public
theorem explicitly consumes the same positivity and minimum-ratio facts used
by CLRS.

## Objective Progress

The new basic objective value is its constant term.  Prove:

```text
v' = v + c_e * (b_l / a_l,e).
```

If `c_e > 0`, old basic feasibility and a positive pivot coefficient imply
`v ≤ v'`.  If additionally `b_l > 0`, then `v < v'`.

The non-strict theorem is the primary result because degenerate pivots with
`b_l = 0` occur in the textbook algorithm.  Strict improvement is exposed as
a strengthening, not assumed by the later termination proof.

## File Layout

Keep theorem-bearing files narrow:

```text
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm.lean
CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/
  Dictionary.lean
  Dictionary/Definitions.lean
  Dictionary/Semantics.lean
  Dictionary/BasicSolution.lean
  Dictionary/InitialDictionary.lean
  Pivot.lean
  Pivot/Definitions.lean
  Pivot/Algebra.lean
  Pivot/SemanticEquivalence.lean
  Pivot/Feasibility.lean
  Pivot/Objective.lean
```

No implementation file should approach the earlier multi-thousand-line shape.
If a proof file grows beyond roughly 200 lines, split it by theorem role before
adding the next public layer.

## Public Acceptance Interface

`Tests/Chapter_29_Simplex_Interface.lean` checks:

- dictionary construction and variable-label projections;
- row/objective semantics;
- basic-assignment equations and feasibility characterization;
- initial-dictionary bridge to `StandardLP` and slack extensions;
- every public PIVOT formula projection;
- semantic equivalence and objective-expression preservation;
- minimum-ratio feasibility preservation;
- non-strict and strict objective progress;
- `#print axioms` for the semantic, feasibility, and objective main theorems.

The test includes a small concrete one-row/one-variable pivot example so that
the coefficient-sign convention is checked independently of the general proof.

## Verification

Use focused commands only:

```text
lake build CLRSLean.Chapter_29
lake env lean Tests/Chapter_29_Interface.lean
lake env lean Tests/Chapter_29_Simplex_Interface.lean
lake build CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm:literate
uv run python scripts/check_repository.py
```

Also scan Chapter 29 and both interface tests for `sorry`, `admit`, and `axiom`,
run `git diff --check`, and confirm the worktree is clean after commits.  A full
library or full-site build is intentionally not part of this milestone.

## Status And Issue Discipline

After the milestone, Chapter 29 remains `partial`.  The reader-facing status
must say that dictionary semantics and PIVOT are proved, while the following
main-text work remains:

- executable SIMPLEX selection and its unbounded branch;
- Bland-rule anti-cycling and termination;
- SIMPLEX optimality at exit;
- Sections 29.2 and 29.5;
- strong duality and complementary slackness.

Issue #84 receives a milestone comment only after the focused verification
gate passes.  The issue remains open until all of those main-text obligations
are completed.

## Subsequent Chapter Milestones

The continuation order is fixed by dependency rather than convenience:

1. finish Section 29.3 control flow: entering selection, ratio selection,
   unbounded ray, SIMPLEX state transition, Bland termination, and optimality;
2. formalize Section 29.5 auxiliary LP and INITIALIZE-SIMPLEX so arbitrary
   standard-form instances reach the feasible-dictionary precondition;
3. derive strong duality and complementary slackness in Section 29.4 from the
   completed primal/dual algorithmic interface;
4. connect the existing shortest-path and max-flow developments, and a new
   minimum-cost-flow model, to the LP formulations of Section 29.2;
5. perform the complete chapter inventory audit and close issue #84 only when
   every advertised theorem boundary is represented and verified.
