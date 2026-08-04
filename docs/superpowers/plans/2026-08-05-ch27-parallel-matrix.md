# Chapter 27 Parallel Matrix Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement CLRS parallel matrix addition and race-free temporary-matrix multiplication over depth-indexed square matrices, prove functional correctness, and attach `Theta(n^2)`/`Theta(log n)` and `Theta(n^3)`/`Theta(log^2 n)` work/span bounds.

**Architecture:** First split the current recurrence monolith and introduce a small `Costed` execution wrapper.  P-ADD evaluates four recursive additions in a balanced fixed-arity parallel tree; P-MATMUL evaluates eight recursive products in parallel and sequentially composes the resulting two block products with P-ADD, reproducing the main-text span recurrence.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib matrices, `CLRS.Chapter04.SqMat`, Chapter 3 asymptotics, Chapter 4 all-input transfer, Lake, Verso.

---

## Prerequisite

Complete `2026-08-05-ch27-foundation-scheduler.md`.  Start from a clean
worktree where `Tests/Chapter_27_Interface.lean` and
`Tests/Chapter_27_Scheduler_Interface.lean` pass.

## File Map

- Replace `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean` with an aggregator and corrected reader guide.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S1_CostModel.lean`.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S2_Recurrences.lean` for existing recurrence definitions, unfold theorems, and exact-power forms.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S3_AllInputBounds.lean` for existing monotonicity, sandwiches, and all-input bounds.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Definitions.lean`.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Correctness.lean`.
- Create `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs.lean`.
- Create `Tests/Chapter_27_Matrix_Interface.lean`.
- Modify `literate.toml` and `docs/index.md` for every new module.

### Task 1: Split the Existing Recurrence Analysis

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S2_Recurrences.lean`
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S3_AllInputBounds.lean`
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [ ] **Step 1: Save the pre-split green boundary**

```bash
lake env lean Tests/Chapter_27_Interface.lean
```

Expected: exit 0.

- [ ] **Step 2: Move recurrence definitions and exact-power theorems to S2**

Move the private power helpers and the definitions/unfold/exact-power theorems
for `pMatMulWork`, `pMatMulSpan`, `pMergeWork`, `pMergeSpan`,
`pMergeSortWork`, `pMergeSortSpan`, `strassenWork`, and `strassenSpan`.
Preserve every name and namespace.  The closure plan later extracts the
Strassen-only extension after all legacy imports are green.

- [ ] **Step 3: Move arbitrary-input analysis to S3**

Import S2 plus Chapter 4's all-input module.  Move all successor-monotonicity,
public monotonicity, power-sandwich, exact-power `isBigTheta`, and public
all-input theorems.  Preserve declaration order where a later proof consumes
an earlier monotonicity theorem.

- [ ] **Step 4: Make the historical file a recurrence aggregator**

Import S2 and S3 only at this checkpoint.  Its prose must say that the
historical `2_4` module name is retained for compatibility and that the main
text covers Sections 27.2-27.3.  Later tasks add S1 and each executable family
only after the corresponding module exists.

- [ ] **Step 5: Register and verify the split**

Add S2-S3 paths/titles to `literate.toml` and `docs/index.md`, then run:

```bash
lake env lean Tests/Chapter_27_Interface.lean
uv run python scripts/check_repository.py
```

Expected: exit 0 with identical legacy theorem types.

- [ ] **Step 6: Commit the recurrence split**

```bash
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S2_Recurrences.lean \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S3_AllInputBounds.lean \
  literate.toml docs/index.md
git commit -m "refactor(ch27): split parallel recurrence analysis"
```

### Task 2: Specify and Implement the Shared Costed Interface

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S1_CostModel.lean`
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `Tests/Chapter_27_Matrix_Interface.lean`

- [ ] **Step 1: Create the RED test surface**

Create the test with:

```lean
import CLRSLean.Chapter_27

namespace CLRS.Chapter27

#check Costed
#check Costed.pure
#check Costed.charge
#check Costed.map
#check Costed.seq
#check Costed.par
#check Costed.par4
#check Costed.par8

end CLRS.Chapter27
```

Run `lake env lean Tests/Chapter_27_Matrix_Interface.lean` and expect
`Unknown constant CLRS.Chapter27.Costed`.

- [ ] **Step 2: Define the cost wrapper and primitive combinators**

Create S1 with:

```lean
import Mathlib.Tactic

namespace CLRS
namespace Chapter27

universe u v

/-- An executable value paired with mathematical work and span charges. -/
structure Costed (α : Type u) where
  value : α
  work : ℕ
  span : ℕ
deriving Repr, DecidableEq

namespace Costed

def pure (x : α) : Costed α := ⟨x, 0, 0⟩

def charge (work span : ℕ) (x : α) : Costed α := ⟨x, work, span⟩

def map (f : α → β) (x : Costed α) : Costed β :=
  ⟨f x.value, x.work, x.span⟩

def seq (x : Costed α) (f : α → Costed β) : Costed β :=
  let y := f x.value
  ⟨y.value, x.work + y.work, x.span + y.span⟩

def par (x : Costed α) (y : Costed β) : Costed (α × β) :=
  ⟨(x.value, y.value), x.work + y.work + 1, max x.span y.span + 1⟩
```

Define `par4` as a balanced tree of three `par` calls and `par8` as two
`par4` calls joined by `par`.  Add `[simp]` theorems for every value/work/span
projection.

- [ ] **Step 3: Import and register the cost model**

Add the S1 import to the historical aggregator and register its title/path in
`literate.toml` and `docs/index.md`.  Do not import a future algorithm module.

- [ ] **Step 4: Run GREEN and commit**

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S1_CostModel
lake env lean Tests/Chapter_27_Matrix_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S1_CostModel.lean \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  Tests/Chapter_27_Matrix_Interface.lean literate.toml docs/index.md
git commit -m "feat(ch27): add execution-attached work span model"
```

### Task 3: Lock the Parallel-Matrix Public Surface in RED

**Files:**
- Modify: `Tests/Chapter_27_Matrix_Interface.lean`

- [ ] **Step 1: Add the matrix declaration checks**

Append:

```lean
#check pAdd
#check pAdd_value
#check pAdd_correct
```

- [ ] **Step 2: Verify RED and commit the contract**

Run the focused test; expect `Unknown constant CLRS.Chapter27.pAdd`.  Commit:

```bash
git add Tests/Chapter_27_Matrix_Interface.lean
git commit -m "test(ch27): specify parallel matrix algorithms"
```

### Task 4: Implement P-ADD and Prove Correctness

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Definitions.lean`
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Correctness.lean`
- Modify: `Tests/Chapter_27_Matrix_Interface.lean`

- [ ] **Step 1: Define recursive parallel addition**

Import `S1_CostModel` and Chapter 4's Strassen module.  Define:

```lean
def pAdd (R : Type u) [Ring R] :
    ∀ k, Chapter04.SqMat R k → Chapter04.SqMat R k →
      Costed (Chapter04.SqMat R k)
  | 0, x, y => Costed.charge 1 1 (x + y)
  | k + 1, A, B =>
      Costed.map
        (fun q => !![q.1.1, q.1.2; q.2.1, q.2.2])
        (Costed.par4
          (pAdd R k (A 0 0) (B 0 0))
          (pAdd R k (A 0 1) (B 0 1))
          (pAdd R k (A 1 0) (B 1 0))
          (pAdd R k (A 1 1) (B 1 1)))
```

This uses the balanced `((q00, q01), (q10, q11))` tuple shape produced by
`par4`; assert that projection shape in the cost-model interface test.

- [ ] **Step 2: Prove erasure and correctness**

Prove by induction on `k`:

```lean
theorem pAdd_value (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pAdd R k A B).value = A + B := by
  induction k with
  | zero => rfl
  | succ k ih =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pAdd, ih]

theorem pAdd_correct (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pAdd R k A B).value = A + B :=
  pAdd_value R k A B
```

- [ ] **Step 3: Add scalar and one-level executable examples**

Use `Int` matrices and `native_decide`/`norm_num` to check the scalar base and
a concrete `2 x 2` block addition.

- [ ] **Step 4: Build, test, and commit**

Import ParallelMatrix Definitions and Correctness from the historical
aggregator and register both modules before running the interface:

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Correctness
lake env lean Tests/Chapter_27_Matrix_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  Tests/Chapter_27_Matrix_Interface.lean literate.toml docs/index.md
git commit -m "feat(ch27): prove parallel matrix addition correct"
```

### Task 5: Implement Race-Free P-MATMUL and Prove Correctness

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Definitions.lean`
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Correctness.lean`
- Modify: `Tests/Chapter_27_Matrix_Interface.lean`

- [ ] **Step 1: Extend the interface and verify RED**

Append `#check pMatMul`, `#check pMatMul_value`, and
`#check pMatMul_correct`.  Run the focused interface and expect a nonzero exit
at `CLRS.Chapter27.pMatMul`, after all P-ADD checks resolve.

- [ ] **Step 2: Define eight-way recursive multiplication**

Define `pMatMul` with scalar base `Costed.charge 1 1 (x * y)`.  At depth
`k+1`, run these eight calls through `Costed.par8`:

```lean
pMatMul R k (A 0 0) (B 0 0)
pMatMul R k (A 0 0) (B 0 1)
pMatMul R k (A 1 0) (B 0 0)
pMatMul R k (A 1 0) (B 0 1)
pMatMul R k (A 0 1) (B 1 0)
pMatMul R k (A 0 1) (B 1 1)
pMatMul R k (A 1 1) (B 1 0)
pMatMul R k (A 1 1) (B 1 1)
```

Map the first four values to `C`, the second four to `T`, then sequentially
compose with `pAdd R (k+1) C T`.  This functional temporary matrix prevents
the write race in the in-place eight-call formulation.

- [ ] **Step 3: Prove the value theorem**

Induct on depth, rewrite all eight recursive values with the induction
hypothesis, rewrite P-ADD with `pAdd_value`, and close the four entries with
`Matrix.mul_apply`, `Fin.sum_univ_two`, and ring normalization:

```lean
theorem pMatMul_value (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pMatMul R k A B).value = A * B

theorem pMatMul_correct (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pMatMul R k A B).value = A * B :=
  pMatMul_value R k A B
```

- [ ] **Step 4: Add concrete multiplication examples**

Check the scalar base and one recursive level against ordinary multiplication.

- [ ] **Step 5: Build, test, and commit**

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Correctness
lake env lean Tests/Chapter_27_Matrix_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix \
  Tests/Chapter_27_Matrix_Interface.lean
git commit -m "feat(ch27): prove parallel matrix multiplication correct"
```

### Task 6: Attach Exact Cost Recurrences

**Files:**
- Create: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs.lean`
- Modify: `Tests/Chapter_27_Matrix_Interface.lean`

- [ ] **Step 1: Extend the exact-cost interface and verify RED**

Append checks for `pAddWork`, `pAddSpan`, `pAdd_work_eq`, `pAdd_span_eq`,
`pMatMulExecWork`, `pMatMulExecSpan`, `pMatMul_work_eq`, and
`pMatMul_span_eq`.  Run the interface and expect a nonzero exit at `pAddWork`.

- [ ] **Step 2: Define corrected natural-valued cost functions**

Define total recurrences with base `n ≤ 1`:

```lean
def pAddWork (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else 4 * pAddWork (n / 2) + 3

def pAddSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else pAddSpan (n / 2) + 2

def pMatMulExecWork (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else 8 * pMatMulExecWork (n / 2) + 7 + pAddWork n

def pMatMulExecSpan (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else pMatMulExecSpan (n / 2) + 3 + pAddSpan n
```

Supply `termination_by n` proofs using `Nat.div_lt_self`.

- [ ] **Step 3: Prove execution equality on power-of-two matrices**

Induct on depth and normalize `Costed.par4`, `Costed.par8`, and `Costed.seq`:

```lean
theorem pAdd_work_eq (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pAdd R k A B).work = pAddWork (2 ^ k)

theorem pAdd_span_eq (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pAdd R k A B).span = pAddSpan (2 ^ k)

theorem pMatMul_work_eq (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pMatMul R k A B).work = pMatMulExecWork (2 ^ k)

theorem pMatMul_span_eq (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) :
    (pMatMul R k A B).span = pMatMulExecSpan (2 ^ k)
```

- [ ] **Step 4: Import costs, run GREEN, and commit**

Import ParallelMatrix Costs from the historical aggregator and register it in
`literate.toml` and `docs/index.md`, then run:

```bash
lake env lean Tests/Chapter_27_Matrix_Interface.lean
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs.lean \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  Tests/Chapter_27_Matrix_Interface.lean literate.toml docs/index.md
git commit -m "feat(ch27): connect matrix execution to work span costs"
```

### Task 7: Prove Matrix Work and Span Main Theorems

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs.lean`
- Modify: `Tests/Chapter_27_Matrix_Interface.lean`

- [ ] **Step 1: Extend the asymptotic interface and verify RED**

Append checks for `pAddWork_allInput_bigTheta`,
`pAddSpan_allInput_bigTheta`, `pMatMulExecWork_allInput_bigTheta`, and
`pMatMulExecSpan_allInput_bigTheta`.  Run the interface and expect a nonzero
exit at the first newly added name.

- [ ] **Step 2: Prove monotonicity and exact-power bounds**

For all four functions prove successor monotonicity by parity-split strong
induction, publish `Monotone` theorems, and expose adjacent-power sandwiches.
On powers of two prove constant-factor bounds against:

```text
pAddWork:          4^k
pAddSpan:          k + 1
pMatMulExecWork:   8^k
pMatMulExecSpan:   (k + 1)^2
```

Use inequalities rather than forcing cumbersome closed forms when constant
factors suffice for `isBigTheta`.

- [ ] **Step 3: Publish all-input asymptotic theorems**

Use Chapter 4's exact-power-to-all-input bridge and these exact signatures:

```lean
theorem pAddWork_allInput_bigTheta :
  Chapter03.isBigTheta (fun n : ℕ => (pAddWork n : ℝ))
    (Chapter04.polynomialScale 2)

theorem pAddSpan_allInput_bigTheta :
  Chapter03.isBigTheta (fun n : ℕ => (pAddSpan n : ℝ))
    (Chapter04.polynomialLogScale 2 0)

theorem pMatMulExecWork_allInput_bigTheta :
  Chapter03.isBigTheta (fun n : ℕ => (pMatMulExecWork n : ℝ))
    (Chapter04.polynomialScale 3)

theorem pMatMulExecSpan_allInput_bigTheta :
  Chapter03.isBigTheta (fun n : ℕ => (pMatMulExecSpan n : ℝ))
    (Chapter04.criticalPowerLogPolylogScale 1 2 1)
```

The comparison scales must be checked against existing Chapter 4 definitions;
`pAddSpan` represents `Theta(log n)` and `pMatMulExecSpan` represents
`Theta(log^2 n)`.

- [ ] **Step 4: Add interface instantiations and axiom prints**

Add one odd-input sandwich example and `#print axioms` for `pAdd_correct`,
`pMatMul_correct`, `pAddWork_allInput_bigTheta`, and
`pMatMulExecSpan_allInput_bigTheta`.

- [ ] **Step 5: Verify and commit**

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs
lake env lean Tests/Chapter_27_Matrix_Interface.lean
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix -g '*.lean'
git diff --check
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs.lean \
  Tests/Chapter_27_Matrix_Interface.lean
git commit -m "feat(ch27): prove parallel matrix asymptotics"
```

### Task 8: Verify the Matrix Phase

**Files:**
- All matrix-phase files.

- [ ] **Step 1: Check module registration**

Confirm Definitions, Correctness, and Costs occur in dependency order in
Chapter 27's navigation and source catalog, with titles `27.2 S1-S3`.

- [ ] **Step 2: Run phase verification**

```bash
lake env lean Tests/Chapter_27_Interface.lean
lake env lean Tests/Chapter_27_Scheduler_Interface.lean
lake env lean Tests/Chapter_27_Matrix_Interface.lean
uv run python scripts/check_repository.py
git diff --check
```

Expected: all commands exit 0.

- [ ] **Step 3: Confirm a clean phase checkpoint**

Run `git status --short`; expected output is empty.
