# Chapter 27 All-Input Cost Bounds Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove monotonicity, adjacent-power sandwiches, and all-input asymptotic bounds for the six P-MERGE, P-MERGE-SORT, and parallel-Strassen work/span recurrences.

**Architecture:** Keep the natural recurrences and their chapter-specific proofs in `Section_27_2_4_Algorithms.lean`.  Reuse Chapter 4's `MonotoneAbs`, adjacent-power transfer, and comparison-scale theorems; expose a natural monotonicity theorem, a natural sandwich theorem, and a real-valued `isBigTheta` theorem for each cost function.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib, CLRS Chapter 3 asymptotic predicates, CLRS Chapter 4 all-input Master-theorem transfer, Verso-facing Lean documentation.

---

### Task 1: Lock the public interface and observe RED

**Files:**
- Modify: `Tests/Chapter_27_Interface.lean:64-76`

- [ ] **Step 1: Add the missing public declaration checks**

Insert these checks after the existing P-MERGE/Strassen declaration block:

```lean
#check pMergeWork_monotone
#check pMergeSpan_monotone
#check pMergeSortWork_monotone
#check pMergeSortSpan_monotone
#check strassenWork_monotone
#check strassenSpan_monotone
#check pMergeWork_power_sandwich
#check pMergeSpan_power_sandwich
#check pMergeSortWork_power_sandwich
#check pMergeSortSpan_power_sandwich
#check strassenWork_power_sandwich
#check strassenSpan_power_sandwich
#check pMergeWork_allInput_bigTheta
#check pMergeSpan_allInput_bigTheta
#check pMergeSortWork_allInput_bigTheta
#check pMergeSortSpan_allInput_bigTheta
#check strassenWork_allInput_bigTheta
#check strassenSpan_allInput_bigTheta
```

- [ ] **Step 2: Run the interface and verify the expected failure**

Run:

```bash
lake env lean Tests/Chapter_27_Interface.lean
```

Expected: nonzero exit with `Unknown identifier pMergeWork_monotone`.  A parse,
namespace, or import error is not the expected RED state and must be corrected
before production proof code is added.

### Task 2: Add the Chapter 4 bridge and local transfer helpers

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean:1-66`

- [ ] **Step 1: Import the established all-input API**

Add:

```lean
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input
```

- [ ] **Step 2: Add private cast and sandwich helpers**

Place these after `two_pow_succ_mul`:

```lean
private theorem natCost_monotoneAbs {T : ℕ → ℕ} (hT : Monotone T) :
    Chapter04.MonotoneAbs (fun n => (T n : ℝ)) := by
  intro m n hmn
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hT hmn

private theorem natCost_power_sandwich {T : ℕ → ℕ} (hT : Monotone T)
    (n : ℕ) (hn : 0 < n) :
    T (2 ^ Nat.log 2 n) ≤ T n ∧
      T n ≤ T (2 ^ (Nat.log 2 n + 1)) := by
  rcases Chapter04.powerInterval_of_pos 2 n (by norm_num) hn.ne' with ⟨hlo, hhi⟩
  exact ⟨hT hlo, hT (Nat.le_of_lt hhi)⟩
```

- [ ] **Step 3: Compile the focused module**

Run:

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms
```

Expected: success with only existing Verso documentation warnings.

### Task 3: Prove all six natural monotonicity theorems

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean:145-303`

- [ ] **Step 1: Prove P-MERGE work successor monotonicity**

After `pMergeWork_pow_two`, add a private theorem
`pMergeWork_le_succ (n)`.  Use strong induction on `n`, discharge `n = 0,1`
with `interval_cases`/`native_decide`, unfold both sides for `2 ≤ n`, and split
the midpoint using:

```lean
rcases (by omega :
    (n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1) with hsame | hnext
```

In `hsame`, use the induction hypothesis on `n - n / 2` and rewrite
`(n + 1) - n / 2 = (n - n / 2) + 1`.  In `hnext`, use it on `n / 2` and
rewrite `(n + 1) - (n / 2 + 1) = n - n / 2`.  In both branches use:

```lean
have hlog : Nat.log 2 n ≤ Nat.log 2 (n + 1) :=
  Nat.log_mono_right (Nat.le_succ n)
```

Finish with `omega`, then publish:

```lean
/-- P-MERGE work is nondecreasing with the input size. -/
theorem pMergeWork_monotone : Monotone pMergeWork :=
  monotone_nat_of_le_succ pMergeWork_le_succ
```

- [ ] **Step 2: Prove P-MERGE span monotonicity**

Repeat the same midpoint split after `pMergeSpan_pow_two`.  Only the ceiling
half recurses: use the induction hypothesis in `hsame`; in `hnext` the ceiling
half is unchanged.  Use `Nat.log_mono_right` in both branches.  Publish:

```lean
/-- P-MERGE span is nondecreasing with the input size. -/
theorem pMergeSpan_monotone : Monotone pMergeSpan :=
  monotone_nat_of_le_succ pMergeSpan_le_succ
```

- [ ] **Step 3: Prove P-MERGE-SORT work and span monotonicity**

For work, reuse the two-half parity proof without a logarithm term and account
for the top-level `n ≤ n + 1`.  For span, use the ceiling-half induction plus:

```lean
have hmerge : pMergeSpan n ≤ pMergeSpan (n + 1) :=
  pMergeSpan_monotone (Nat.le_succ n)
```

Publish:

```lean
theorem pMergeSortWork_monotone : Monotone pMergeSortWork :=
  monotone_nat_of_le_succ pMergeSortWork_le_succ

theorem pMergeSortSpan_monotone : Monotone pMergeSortSpan :=
  monotone_nat_of_le_succ pMergeSortSpan_le_succ
```

- [ ] **Step 4: Prove parallel-Strassen work and span monotonicity**

For each recurrence, split whether `(n + 1) / 2` equals `n / 2` or its
successor.  Work additionally uses:

```lean
have hsquare : n * n ≤ (n + 1) * (n + 1) := by nlinarith
```

Publish `strassenWork_monotone` and `strassenSpan_monotone` through
`monotone_nat_of_le_succ`.

- [ ] **Step 5: Compile and commit the monotonicity layer**

Run:

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms
```

Expected: success.  Then commit:

```bash
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean
git commit -m "feat(ch27): prove cost recurrence monotonicity"
```

### Task 4: Expose the adjacent-power sandwich layer

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`

- [ ] **Step 1: Add six direct natural-number wrappers**

Place each wrapper after its public monotonicity theorem.  Use this exact
pattern for the corresponding function:

```lean
/-- Every positive P-MERGE work cost lies between its adjacent power-of-two costs. -/
theorem pMergeWork_power_sandwich (n : ℕ) (hn : 0 < n) :
    pMergeWork (2 ^ Nat.log 2 n) ≤ pMergeWork n ∧
      pMergeWork n ≤ pMergeWork (2 ^ (Nat.log 2 n + 1)) :=
  natCost_power_sandwich pMergeWork_monotone n hn
```

Add the analogous `pMergeSpan_power_sandwich`,
`pMergeSortWork_power_sandwich`, `pMergeSortSpan_power_sandwich`,
`strassenWork_power_sandwich`, and `strassenSpan_power_sandwich` wrappers.

- [ ] **Step 2: Add odd-input interface examples**

Append to the cost section of `Tests/Chapter_27_Interface.lean`:

```lean
example : pMergeWork 3 ≤ pMergeWork 4 :=
  pMergeWork_monotone (by omega)

example : pMergeSortSpan (2 ^ Nat.log 2 5) ≤ pMergeSortSpan 5 :=
  (pMergeSortSpan_power_sandwich 5 (by omega)).1

example : strassenWork 5 ≤ strassenWork (2 ^ (Nat.log 2 5 + 1)) :=
  (strassenWork_power_sandwich 5 (by omega)).2
```

- [ ] **Step 3: Run the interface**

Run:

```bash
lake env lean Tests/Chapter_27_Interface.lean
```

Expected: the monotonicity and sandwich checks pass; the first missing
all-input theorem remains RED.

- [ ] **Step 4: Commit the sandwich layer**

```bash
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean Tests/Chapter_27_Interface.lean
git commit -m "feat(ch27): expose adjacent-power cost sandwiches"
```

### Task 5: Prove exact-power asymptotic witnesses and transfer them

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean`

- [ ] **Step 1: Establish private exact-power comparison facts**

Prove the following private `Chapter03.isBigTheta` statements directly from the
existing closed forms with `Chapter03.isBigO_iff`,
`Chapter03.isBigOmega_iff`, `norm_num`, `push_cast`, and `nlinarith`:

```lean
private theorem pMergeWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k => (pMergeWork (2 ^ k) : ℝ))
      (fun k => (2 : ℝ) ^ k)

private theorem pMergeSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k => (pMergeSpan (2 ^ k) : ℝ))
      (fun k => ((k : ℝ) + 1) ^ 2)

private theorem pMergeSortWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k => (pMergeSortWork (2 ^ k) : ℝ))
      (fun k => ((k : ℝ) + 1) * (2 : ℝ) ^ k)

private theorem pMergeSortSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k => (pMergeSortSpan (2 ^ k) : ℝ))
      (fun k => ((k : ℝ) + 1) ^ 3)

private theorem strassenWork_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k => (strassenWork (2 ^ k) : ℝ))
      (fun k => (7 : ℝ) ^ k)

private theorem strassenSpan_exactPower_bigTheta :
    Chapter03.isBigTheta
      (fun k => (strassenSpan (2 ^ k) : ℝ))
      (fun k => (k : ℝ) + 1)
```

Use these stable algebraic comparisons:

- `pMergeWork`: `2^k ≤ T(2^k) ≤ 4·2^k`;
- `pMergeSpan`: `((k+1)^2)/2 ≤ T(2^k) ≤ (k+1)^2`;
- `pMergeSortWork`: equality with `(k+1)·2^k`;
- `pMergeSortSpan`: rewrite the numerator as `(k+1)(k+2)(k+3)`, then
  `((k+1)^3)/6 ≤ T(2^k) ≤ (k+1)^3`;
- `strassenWork`: `7^k ≤ T(2^k) ≤ 3·7^k`; and
- `strassenSpan`: equality with `k+1`.

- [ ] **Step 2: Transfer P-MERGE bounds**

Apply `Chapter04.allInput_bigTheta_of_criticalPowerScale` to P-MERGE work,
then compose with
`Chapter04.criticalPowerScale_isBigTheta_polynomialScale 2 1`.  Apply
`Chapter04.allInput_bigTheta_of_powerStep` directly to P-MERGE span using
`criticalPowerLogPolylogScale 1 2 1`.  Publish the signatures fixed in the
design:

```lean
theorem pMergeWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n => (pMergeWork n : ℝ))
      (Chapter04.polynomialScale 1)

theorem pMergeSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n => (pMergeSpan n : ℝ))
      (Chapter04.criticalPowerLogPolylogScale 1 2 1)
```

- [ ] **Step 3: Transfer P-MERGE-SORT bounds**

Apply `allInput_bigTheta_of_criticalPowerLogScale` to work and compose with
`criticalPowerLogScale_isBigTheta_polynomialLogScale 2 1`.  Apply
`allInput_bigTheta_of_powerStep` to span at
`criticalPowerLogPolylogScale 1 2 2`.  Publish the two fixed signatures.

- [ ] **Step 4: Transfer parallel-Strassen bounds**

Apply `allInput_bigTheta_of_criticalPowerScale` to work and compose with
`criticalPowerScale_isBigTheta_realLogScale 7 2`.  Apply
`allInput_bigTheta_of_criticalPowerLogScale` to span and compose with
`criticalPowerLogScale_isBigTheta_polynomialLogScale 2 0`.  Publish the two
fixed signatures.

- [ ] **Step 5: Make the interface GREEN and commit**

Run:

```bash
lake build +CLRSLean.Chapter_27.Section_27_2_4_Algorithms
lake env lean Tests/Chapter_27_Interface.lean
```

Expected: both commands succeed.  Then commit:

```bash
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean Tests/Chapter_27_Interface.lean
git commit -m "feat(ch27): prove all-input parallel cost bounds"
```

### Task 6: Synchronize the chapter boundary and theorem ledger

**Files:**
- Modify: `CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean:20-40`
- Modify: `CLRSLean/Chapter_27.lean:40-62`
- Modify: `CLRSLean/Status.lean:132-141`
- Modify: `docs/proof-map.md:3694-3735`
- Modify: `docs/proof-status-board.md:45-66`
- Modify: `docs/clrs-proof-progress.csv:28`
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: `README.md`

- [ ] **Step 1: Update reader-facing Lean prose**

List the six monotonicity, sandwich, and all-input theorem families in the
section/chapter main-result summaries.  Replace the all-input deferred item
with the single remaining statement:

```text
Executable P-MERGE / P-MERGE-SORT implementations refining the recurrences.
```

Keep Chapter 27 under `Structured But Partial` in `CLRSLean/Status.lean`.

- [ ] **Step 2: Update the machine-readable progress row**

Change Chapter 27 from `48` tracked/proved declarations to `66`, preserve
`repo_status=partial` and `missing_core_groups=1`, add the 18 new public theorem
names to `strongest_lean_statement`, and set `remaining_core_groups` to the
executable P-MERGE/P-MERGE-SORT refinement only.

- [ ] **Step 3: Update planning documents**

In `docs/proof-map.md`, record the six all-input asymptotic scales and the
monotonicity/sandwich proof pattern.  In `docs/proof-status-board.md`, remove
#121 from the remaining Chapter 27 gap and promote #122 to priority 1.

- [ ] **Step 4: Regenerate derived artifacts**

Run:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
python3 scripts/gen_readme_table.py
```

Expected total: `1676` tracked and proved declarations repository-wide.

- [ ] **Step 5: Commit documentation and ledger updates**

```bash
git add CLRSLean/Chapter_27/Section_27_2_4_Algorithms.lean \
  CLRSLean/Chapter_27.lean CLRSLean/Status.lean CLRSLean/Progress.lean \
  Tests/Chapter_27_Interface.lean README.md docs/clrs-proof-progress.csv \
  docs/proof-map.md docs/proof-status-board.md
git commit -m "docs(ch27): record all-input cost completion"
```

### Task 7: Run the completion gate and prepare review

**Files:**
- Verify all files changed on `codex/ch27-all-input-bounds`

- [ ] **Step 1: Run focused Lean verification**

```bash
lake build CLRSLean.Chapter_27
lake env lean Tests/Chapter_27_Interface.lean
```

Expected: success; existing Verso documentation-role warnings are acceptable.

- [ ] **Step 2: Run proof hygiene and axiom checks**

```bash
rg -n '\b(sorry|admit)\b|^axiom ' CLRSLean/Chapter_27 Tests/Chapter_27_Interface.lean
git diff origin/main...HEAD --check
```

Expected: the first command finds no forbidden proof term and `diff --check`
is clean.  Use a temporary Lean check file outside the repository or a focused
`#print axioms` command for all six `*_allInput_bigTheta` theorems; expected
axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 3: Run repository metadata checks**

```bash
uv run python scripts/check_progress_csv.py
python3 scripts/gen_readme_table.py --check
uv run python scripts/check_repository.py
```

Expected: all checks pass.  Do not run `lake build :literateHtml` for this
proof-only iteration.

- [ ] **Step 4: Inspect the complete branch diff**

```bash
git status --short --branch
git log --oneline origin/main..HEAD
git diff --stat origin/main...HEAD
git diff origin/main...HEAD -- CLRSLean/Chapter_27 Tests/Chapter_27_Interface.lean
```

Confirm no public theorem was removed or weakened, Chapter 27 remains partial
only because of #122, and the worktree is clean before requesting review.
