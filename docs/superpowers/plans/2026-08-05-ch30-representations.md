# Chapter 30 Polynomial Representations Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the Section 30.1 coefficient-vector, Horner-evaluation, point-value interpolation, representation-operation, and schoolbook-multiplication foundation, with executable costs and a stable Chapter 30 import surface.

**Architecture:** Keep `Polynomial K` as the mathematical representation and use total fixed-capacity vectors `Fin n → K` for algorithms.  Conversion and interpolation modules establish the semantic bridges; operation implementations expose their own arithmetic counters so later FFT comparisons use costs attached to actual executions.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib `Polynomial`/`Lagrange`/`Finset` APIs, Lake, Verso module registration, CLRS-Lean interface tests.

---

## File Map

- Create `CLRSLean/Chapter_30.lean` as the chapter aggregator and reader guide.
- Create `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials.lean` as the Section 30.1 aggregator.
- Create `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors.lean` for fixed-capacity vectors, polynomial conversion, Horner execution, and costs.
- Create `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S2_PointValueInterpolation.lean` for evaluation vectors and Lagrange interpolation.
- Create `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S3_RepresentationOperations.lean` for pointwise operations, explicit schoolbook execution, correctness, and costs.
- Create `Tests/Chapter_30_Interface.lean` for the public Section 30.1 surface and exact examples.
- Modify `literate.toml` and `docs/index.md` to register the new source files.
- Modify `docs/clrs-proof-progress.csv`, `docs/proof-map.md`, and `CLRSLean/Status.lean`, then regenerate `CLRSLean/Progress.lean` and the README table so the new Section 30.1 source is never mislabeled `not-started`.

### Task 1: Record the RED Section 30.1 Contract

**Files:**
- Create: `Tests/Chapter_30_Interface.lean`

- [ ] **Step 1: Confirm Chapter 30 is absent and the worktree is clean enough to proceed**

Run:

```bash
git status --short
test ! -e CLRSLean/Chapter_30.lean
test ! -d CLRSLean/Chapter_30
```

Expected: the two `test` commands exit 0.  Preserve unrelated user changes if `git status` reports any; do not fold them into Chapter 30 commits.

- [ ] **Step 2: Add the intended public interface test**

Create `Tests/Chapter_30_Interface.lean` importing only `CLRSLean.Chapter_30` and checking:

```lean
import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check CoeffVector
#check PowTwoVec
#check coeffVector
#check vectorToPolynomial
#check vectorToPolynomial_coeff
#check coeffVector_vectorToPolynomial
#check vectorToPolynomial_coeffVector
#check hornerEvalExec
#check hornerEval
#check hornerEval_correct
#check hornerEvalWork_exact
#check pointValues
#check interpolateVector
#check pointValues_injective
#check interpolate_pointValues
#check interpolate_unique
#check interpolate_pointValues_roundTrip
#check pointValues_add
#check pointValues_mul
#check VectorArithmeticExecution
#check vectorAddExec
#check vectorAddWork_exact
#check pointwiseMulExec
#check pointwiseMulWork_exact
#check schoolbookMulExec
#check schoolbookMul
#check schoolbookMul_correct
#check schoolbookMul_degreeBound
#check schoolbookMulWork_exact

end CLRS.Chapter30
```

- [ ] **Step 3: Verify the expected RED failure**

Run:

```bash
lake env lean Tests/Chapter_30_Interface.lean
```

Expected: nonzero exit because `CLRSLean.Chapter_30` does not exist.

- [ ] **Step 4: Commit the RED contract**

```bash
git add Tests/Chapter_30_Interface.lean
git commit -m "test(ch30): specify polynomial representation interface"
```

### Task 2: Implement Fixed-Capacity Coefficient Vectors

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors.lean`
- Test: `Tests/Chapter_30_Interface.lean`

- [ ] **Step 1: Create the module and representation boundary**

Import `Mathlib.Algebra.Polynomial.Eval.Defs`, `Mathlib.Algebra.Polynomial.Degree.Definitions`, and `Mathlib.Tactic`.  Open `Polynomial` and use the standard namespaces:

```lean
namespace CLRS
namespace Chapter30

/-- A total coefficient vector with fixed capacity `n`. -/
abbrev CoeffVector (K : Type*) (n : Nat) := Fin n → K

/-- A coefficient vector whose capacity is a power of two. -/
abbrev PowTwoVec (K : Type*) (k : Nat) := CoeffVector K (2 ^ k)

/-- Read and zero-pad the first `n` coefficients of a polynomial. -/
def coeffVector [Semiring K] (n : Nat) (p : K[X]) : CoeffVector K n :=
  fun i => p.coeff i

/-- Reconstruct a polynomial from every slot of a fixed vector. -/
def vectorToPolynomial [Semiring K] {n : Nat} (a : CoeffVector K n) : K[X] :=
  ∑ i : Fin n, Polynomial.monomial i.1 (a i)
```

Every declaration gets a doc comment.  Keep `CoeffVector` independent of any roots-of-unity or FFT imports.

- [ ] **Step 2: Prove coefficient reconstruction at an in-range index**

Add:

```lean
theorem vectorToPolynomial_coeff [Semiring K] {n : Nat}
    (a : CoeffVector K n) (i : Fin n) :
    (vectorToPolynomial a).coeff i = a i := by
  -- Expand the finite sum, use `Polynomial.coeff_monomial`, and collapse the
  -- unique `i` term with `Finset.sum_eq_single`.
```

Then prove the vector round trip by `funext`:

```lean
theorem coeffVector_vectorToPolynomial [Semiring K] {n : Nat}
    (a : CoeffVector K n) :
    coeffVector n (vectorToPolynomial a) = a := by
  funext i
  exact vectorToPolynomial_coeff a i
```

- [ ] **Step 3: Prove the support and degree capacity bounds**

First prove that coefficients at indices `n ≤ i` vanish, then expose a degree form usable downstream:

```lean
theorem vectorToPolynomial_coeff_eq_zero_of_ge [Semiring K] {n i : Nat}
    (a : CoeffVector K n) (hi : n ≤ i) :
    (vectorToPolynomial a).coeff i = 0 := by
  -- Every monomial exponent comes from `Fin n`, contradicting `hi`.

theorem vectorToPolynomial_degree_lt [Semiring K] {n : Nat}
    (a : CoeffVector K n) :
    (vectorToPolynomial a).degree < n := by
  -- Use the coefficient-vanishing characterization of degree.
```

Use `WithBot`/`Polynomial.degree` in the public capacity theorem.  Add a `natDegree` corollary only with a nonzero premise; do not encode the zero polynomial through a false `natDegree < 0` statement.

- [ ] **Step 4: Prove the polynomial round trip under the exact capacity premise**

Add the extensional theorem:

```lean
theorem vectorToPolynomial_coeffVector [Semiring K] {n : Nat} (p : K[X])
    (hp : p.degree < n) :
    vectorToPolynomial (coeffVector n p) = p := by
  ext i
  by_cases hi : i < n
  · obtain ⟨j, rfl⟩ := Fin.exists_iff_lt.mpr hi
    exact vectorToPolynomial_coeff (coeffVector n p) j
  · rw [vectorToPolynomial_coeff_eq_zero_of_ge]
    · exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by simp [Nat.le_of_not_gt hi]))
    · exact Nat.le_of_not_gt hi
```

Adjust only the final library lemma spelling if Lean reports an API mismatch; retain the theorem statement and the explicit degree premise.

- [ ] **Step 5: Compile the focused module**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S1_CoefficientVectors
```

Expected: exit 0 with no unfinished-proof warnings.

- [ ] **Step 6: Commit the coefficient-vector bridge**

```bash
git add CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors.lean
git commit -m "feat(ch30): add coefficient vector polynomial bridge"
```

### Task 3: Add Canonical Horner Execution and Exact Cost

**Files:**
- Modify: `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors.lean`
- Test: `Tests/Chapter_30_Interface.lean`

- [ ] **Step 1: Add the tail view and execution record**

Define the low-coefficient-first tail and a canonical result/counter object:

```lean
def tailCoeffs {K : Type*} {n : Nat} (a : CoeffVector K (n + 1)) :
    CoeffVector K n := fun i => a i.succ

structure ArithmeticExecution (K : Type*) where
  value : K
  additions : Nat
  multiplications : Nat

def ArithmeticExecution.work (r : ArithmeticExecution K) : Nat :=
  r.additions + r.multiplications
```

If this record is also useful for scalar operations in S3, keep it at namespace level rather than nesting it under Horner.

- [ ] **Step 2: Define Horner once, with the value as a projection**

Use structural recursion on the capacity:

```lean
def hornerEvalExec [Semiring K] : {n : Nat} → CoeffVector K n → K → ArithmeticExecution K
  | 0, _, _ => ⟨0, 0, 0⟩
  | n + 1, a, x =>
      let child := hornerEvalExec (tailCoeffs a) x
      ⟨a 0 + x * child.value, child.additions + 1, child.multiplications + 1⟩

def hornerEval [Semiring K] {n : Nat} (a : CoeffVector K n) (x : K) : K :=
  (hornerEvalExec a x).value
```

Do not add a second recurrence used only by the cost proof.

- [ ] **Step 3: Prove the Horner polynomial split and correctness**

Prove the helper identity for `vectorToPolynomial a` at capacity `n + 1` and then:

```lean
theorem hornerEval_correct [CommSemiring K] {n : Nat}
    (a : CoeffVector K n) (x : K) :
    hornerEval a x = (vectorToPolynomial a).eval x := by
  induction n with
  | zero => simp [hornerEval, hornerEvalExec, vectorToPolynomial]
  | succ n ih =>
      -- Rewrite with the low-coefficient split and apply `ih` to `tailCoeffs a`.
```

- [ ] **Step 4: Prove exact additions, multiplications, and work**

Add:

```lean
theorem hornerEvalExec_additions [Semiring K] {n : Nat}
    (a : CoeffVector K n) (x : K) : (hornerEvalExec a x).additions = n := by
  induction n <;> simp [hornerEvalExec, *]

theorem hornerEvalExec_multiplications [Semiring K] {n : Nat}
    (a : CoeffVector K n) (x : K) : (hornerEvalExec a x).multiplications = n := by
  induction n <;> simp [hornerEvalExec, *]

theorem hornerEvalWork_exact [Semiring K] {n : Nat}
    (a : CoeffVector K n) (x : K) :
    (hornerEvalExec a x).work = 2 * n := by
  rw [ArithmeticExecution.work, hornerEvalExec_additions,
    hornerEvalExec_multiplications]
  omega
```

- [ ] **Step 5: Verify and commit Horner execution**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S1_CoefficientVectors
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors.lean
```

Expected: build exit 0 and the scan has no matches.

```bash
git add CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors.lean
git commit -m "feat(ch30): verify Horner evaluation and work"
```

### Task 4: Implement Point-Value Extraction and Interpolation

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S2_PointValueInterpolation.lean`
- Test: `Tests/Chapter_30_Interface.lean`

- [ ] **Step 1: Inspect the exact Lagrange API before fixing proof terms**

Run:

```bash
rg -n 'eq_of_degrees_lt_of_eval_index_eq|def interpolate|degree_interpolate_lt|eval_interpolate_at_node|eq_interpolate_iff' \
  .lake/packages/mathlib/Mathlib/LinearAlgebra/Lagrange.lean
```

Expected: locate every named declaration and confirm that the indexed equality theorem takes the sample `Finset` and an `InjOn` proof, while interpolation specializes cleanly to `Finset.univ : Finset (Fin n)`.

- [ ] **Step 2: Define point values and the Mathlib-backed interpolant**

Import S1 and `Mathlib.LinearAlgebra.Lagrange`, then add:

```lean
def pointValues [Semiring K] {n : Nat} (points : Fin n → K) (p : K[X]) :
    CoeffVector K n := fun i => p.eval (points i)

noncomputable def interpolateVector [Field K] {n : Nat}
    (points values : Fin n → K) : K[X] :=
  Lagrange.interpolate Finset.univ points values
```

- [ ] **Step 3: Prove equality from distinct samples**

Expose the precise degree boundary:

```lean
theorem pointValues_injective [Field K] {n : Nat}
    {points : Fin n → K} (hpoints : Function.Injective points)
    {p q : K[X]} (hp : p.degree < n) (hq : q.degree < n)
    (hvalues : pointValues points p = pointValues points q) : p = q := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    hpoints.injOn hp hq
  intro i _
  exact congrFun hvalues i
```

If Mathlib expects `natDegree < n` plus nonzero cases, split zero polynomials explicitly and keep the public `degree < n` theorem as the wrapper.

- [ ] **Step 4: Prove interpolation existence, degree, uniqueness, and round trip**

Add this theorem family:

```lean
theorem interpolate_pointValues [Field K] {n : Nat}
    {points values : Fin n → K} (hpoints : Function.Injective points) (i : Fin n) :
    (interpolateVector points values).eval (points i) = values i := by
  -- Convert injectivity to `Set.InjOn points Finset.univ` and apply
  -- `Lagrange.eval_interpolate_at_node`.

theorem interpolateVector_degree_lt [Field K] {n : Nat}
    (points values : Fin n → K) :
    (interpolateVector points values).degree < n := by
  -- Use `Lagrange.degree_interpolate_lt` and `Finset.card_univ`.

theorem interpolate_unique [Field K] {n : Nat}
    {points values : Fin n → K} (hpoints : Function.Injective points)
    {p : K[X]} (hp : p.degree < n)
    (heval : ∀ i, p.eval (points i) = values i) :
    p = interpolateVector points values := by
  apply pointValues_injective hpoints hp (interpolateVector_degree_lt points values)
  funext i
  simpa [pointValues, heval] using (interpolate_pointValues hpoints i).symm

theorem interpolate_pointValues_roundTrip [Field K] {n : Nat}
    {points : Fin n → K} (hpoints : Function.Injective points)
    {p : K[X]} (hp : p.degree < n) :
    interpolateVector points (pointValues points p) = p := by
  exact (interpolate_unique hpoints hp (fun i => rfl)).symm
```

- [ ] **Step 5: Verify the module and edge cases**

Add focused examples for `n = 0`, `n = 1`, and a two-point affine polynomial.  The empty case should demonstrate uniqueness only under the resulting degree premise; do not claim that zero sample points determine an arbitrary polynomial.

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S2_PointValueInterpolation
```

Expected: exit 0.

- [ ] **Step 6: Commit interpolation**

```bash
git add CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S2_PointValueInterpolation.lean
git commit -m "feat(ch30): formalize point-value interpolation"
```

### Task 5: Implement Representation Operations and Explicit Schoolbook Execution

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S3_RepresentationOperations.lean`
- Test: `Tests/Chapter_30_Interface.lean`

- [ ] **Step 1: Define canonical vector-operation executions and their semantic laws**

Import S2 and define one shared vector execution record:

```lean
structure VectorArithmeticExecution (K : Type*) (n : Nat) where
  value : CoeffVector K n
  additions : Nat
  multiplications : Nat

def VectorArithmeticExecution.work (r : VectorArithmeticExecution K n) : Nat :=
  r.additions + r.multiplications

def vectorAddExec [AddMonoid K] {n : Nat}
    (a b : CoeffVector K n) : VectorArithmeticExecution K n :=
  ⟨fun i => a i + b i, n, 0⟩

def vectorAdd [AddMonoid K] {n : Nat}
    (a b : CoeffVector K n) : CoeffVector K n :=
  (vectorAddExec a b).value

def pointwiseMulExec [Mul K] {n : Nat}
    (a b : CoeffVector K n) : VectorArithmeticExecution K n :=
  ⟨fun i => a i * b i, 0, n⟩

def pointwiseMul [Mul K] {n : Nat}
    (a b : CoeffVector K n) : CoeffVector K n :=
  (pointwiseMulExec a b).value
```

Prove the exact linear costs by unfolding these executions:

```lean
theorem vectorAddWork_exact [AddMonoid K] {n : Nat}
    (a b : CoeffVector K n) :
    (vectorAddExec a b).work = n := by
  simp [vectorAddExec, VectorArithmeticExecution.work]

theorem pointwiseMulWork_exact [Mul K] {n : Nat}
    (a b : CoeffVector K n) :
    (pointwiseMulExec a b).work = n := by
  simp [pointwiseMulExec, VectorArithmeticExecution.work]
```

Then prove:

```lean
theorem vectorToPolynomial_vectorAdd [CommSemiring K] {n : Nat}
    (a b : CoeffVector K n) :
    vectorToPolynomial (vectorAdd a b) =
      vectorToPolynomial a + vectorToPolynomial b := by
  ext i
  by_cases hi : i < n
  · obtain ⟨j, rfl⟩ := Fin.exists_iff_lt.mpr hi
    simp [vectorAdd, vectorToPolynomial_coeff]
  · simp [vectorToPolynomial_coeff_eq_zero_of_ge, Nat.le_of_not_gt hi]

theorem pointValues_add [Semiring K] {n : Nat} (points : Fin n → K)
    (p q : K[X]) :
    pointValues points (p + q) =
      vectorAdd (pointValues points p) (pointValues points q) := by
  funext i
  simp [pointValues, vectorAdd]

theorem pointValues_mul [CommSemiring K] {n : Nat} (points : Fin n → K)
    (p q : K[X]) :
    pointValues points (p * q) =
      pointwiseMul (pointValues points p) (pointValues points q) := by
  funext i
  simp [pointValues, pointwiseMul]
```

- [ ] **Step 2: Define bucket insertion and the double-loop schoolbook execution**

The value algorithm must traverse coefficient pairs exactly once.  Define:

```lean
def productIndex {m n : Nat} (i : Fin m) (j : Fin n) : Fin (m + n) :=
  ⟨i.1 + j.1, by omega⟩

def addToBucket [AddMonoid K] {n : Nat} (out : CoeffVector K n)
    (i : Fin n) (v : K) : CoeffVector K n :=
  Function.update out i (out i + v)

def schoolbookMulExec [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    VectorArithmeticExecution K (m + n) :=
  -- Fold over `Finset.univ ×ˢ Finset.univ`, inserting
  -- `a i * b j` into `productIndex i j`; increment both counters once.

def schoolbookMul [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) : CoeffVector K (m + n) :=
  (schoolbookMulExec a b).value
```

Do not define `schoolbookMul` through `Polynomial.mul`, and do not charge a closed-form recurrence detached from the fold.

- [ ] **Step 3: Prove the fold invariant before the final correctness theorem**

State an invariant for an arbitrary processed pair finset `s`:

```lean
vectorToPolynomial (bucketFold a b s) =
  ∑ ij ∈ s, Polynomial.monomial (ij.1.1 + ij.2.1) (a ij.1 * b ij.2)
```

Prove it by `Finset.induction`, using the coefficient effect of `addToBucket`.  Then specialize to the full Cartesian product and rewrite the double sum to polynomial multiplication.

- [ ] **Step 4: Prove schoolbook correctness, capacity, and exact cost**

Add:

```lean
theorem schoolbookMul_correct [CommSemiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    vectorToPolynomial (schoolbookMul a b) =
      vectorToPolynomial a * vectorToPolynomial b := by
  -- Apply the full-pair fold invariant and distribute both finite sums.

theorem schoolbookMul_degreeBound [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (vectorToPolynomial (schoolbookMul a b)).degree < m + n :=
  vectorToPolynomial_degree_lt _

theorem schoolbookMulExec_additions [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (schoolbookMulExec a b).additions = m * n := by
  -- Rewrite the fold counter and `Finset.card_product`.

theorem schoolbookMulExec_multiplications [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (schoolbookMulExec a b).multiplications = m * n := by
  -- Same traversal count as additions.

theorem schoolbookMulWork_exact [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (schoolbookMulExec a b).work = 2 * (m * n) := by
  rw [VectorArithmeticExecution.work, schoolbookMulExec_additions,
    schoolbookMulExec_multiplications]
  omega
```

Reuse the `VectorArithmeticExecution.work` defined in Step 1; do not create a second cost record for schoolbook multiplication.

- [ ] **Step 5: Add exact examples that exercise the implementation**

In `Tests/Chapter_30_Interface.lean`, add examples for:

- empty input capacity;
- multiplying constants;
- internal zero coefficients; and
- `(1 + X) * (1 + X)` where the coefficient of `X^2` reaches the last used bucket while the declared `m + n` output still has one legal zero-padding slot.

Use `native_decide` only for decidable finite-vector equalities over exact values such as `ℤ` or `ℚ`; use `norm_num`/`ext` for polynomial equalities.

- [ ] **Step 6: Verify and commit representation operations**

Run:

```bash
lake build +CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S3_RepresentationOperations
```

Expected: exit 0.

```bash
git add CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials/S3_RepresentationOperations.lean \
  Tests/Chapter_30_Interface.lean
git commit -m "feat(ch30): verify representation operations and schoolbook work"
```

### Task 6: Assemble the Section and Chapter Import Surface

**Files:**
- Create: `CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials.lean`
- Create: `CLRSLean/Chapter_30.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Status.lean`
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: `README.md`
- Test: `Tests/Chapter_30_Interface.lean`

- [ ] **Step 1: Create the Section 30.1 aggregator**

Import S1, S2, and S3 in dependency order.  The module doc comment must summarize coefficient and point-value representations, name the headline theorems, and state that roots-of-unity specialization belongs to Section 30.2.

- [ ] **Step 2: Create the Chapter 30 aggregator**

Initially import only Section 30.1:

```lean
import CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials

/-! # Chapter 30 - Polynomials and the FFT

Section 30.1 is represented by fixed coefficient vectors, polynomial bridges,
Horner evaluation, interpolation, and operation/cost theorems.  Section 30.2
is added by the next implementation plans.  Section 30.3 remains deferred.
-/

namespace CLRS
namespace Chapter30

end Chapter30
end CLRS
```

This intermediate guide must not claim the milestone or chapter complete.

- [ ] **Step 3: Register source modules**

Add the chapter, section aggregator, and S1-S3 modules to `literate.toml` in dependency order, with matching titles.  Add their paths to the source catalog in `docs/index.md`.

- [ ] **Step 4: Record the truthful intermediate Section 30.1 status**

Add a Chapter 30 / Section 30.1 entry to `docs/proof-map.md`.  Change the Chapter 30 CSV row to `partial`, represented sections `30.1`, with reviewed public theorem-group counts from `Tests/Chapter_30_Interface.lean`.  Record two remaining core groups: Section 30.2 DFT/FFT and Section 30.3 efficient implementations.  Add Chapter 30 under `Structured But Partial` in `CLRSLean/Status.lean` and change `Not Represented On Main` to name Chapters 28-29 and 31 explicitly.

Regenerate derived files:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/gen_readme_table.py
```

Expected: both exit 0.  Do not claim Section 30.2 or the milestone complete.

- [ ] **Step 5: Turn the interface GREEN**

Run:

```bash
lake env lean Tests/Chapter_30_Interface.lean
lake build +CLRSLean.Chapter_30
uv run python scripts/check_repository.py
git diff --check
```

Expected: all commands exit 0.

- [ ] **Step 6: Scan the Section 30.1 boundary**

Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials.lean \
  CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials \
  Tests/Chapter_30_Interface.lean
```

Expected: no matches.

- [ ] **Step 7: Commit the Section 30.1 assembly**

```bash
git add CLRSLean/Chapter_30.lean \
  CLRSLean/Chapter_30/Section_30_1_Representing_Polynomials.lean \
  literate.toml docs/index.md docs/proof-map.md \
  docs/clrs-proof-progress.csv CLRSLean/Status.lean \
  CLRSLean/Progress.lean README.md
git commit -m "feat(ch30): assemble polynomial representation section"
```

## Plan 1 Acceptance Gate

- [ ] `Tests/Chapter_30_Interface.lean` imports only `CLRSLean.Chapter_30` and exits 0.
- [ ] Coefficient round trips and interpolation uniqueness use explicit capacity/distinctness premises.
- [ ] Horner and schoolbook work are read from their canonical executions.
- [ ] Fixed-capacity vector addition and pointwise multiplication expose canonical executions with exact linear work.
- [ ] Schoolbook multiplication traverses coefficient pairs and does not call `Polynomial.mul` to compute its output.
- [ ] Empty, constant, zero-padded, internal-zero, and last-used-coefficient examples pass.
- [ ] Section 30.1 contains no unfinished proofs or project-defined axioms.
- [ ] Repository progress truthfully reports Chapter 30 as `partial`, represents only 30.1, and names Sections 30.2 and 30.3 as the two remaining core groups.
