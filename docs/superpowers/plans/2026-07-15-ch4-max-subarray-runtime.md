# Chapter 4 Executable Maximum-Subarray Runtime Plan

**Goal:** Repair PR #87 by connecting a genuine divide-and-conquer
maximum-subarray execution to an exact abstract cost recurrence and an
all-input `Θ(n log n)` theorem.

**Scope:** Abstract control steps only.  Lean list allocation and RAM-level
refinement remain outside the claim.

## 1. Rebase and establish the red interface

Files:

- Create `Tests/Chapter_04_Interface.lean`.
- Inspect `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean`.

Steps:

1. Fetch and rebase the PR branch onto the latest `origin/main`.
2. Confirm the existing Chapter 4 module still compiles.
3. Add `#check` declarations and small executable examples for the planned
   prefix, suffix, crossing, costed divide, correctness, cost recurrence, and
   asymptotic interfaces.
4. Run the interface file and record the expected unknown-identifier failure.

## 2. Prove the linear crossing selector

File:

- Modify `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean`.

Steps:

1. Define a tie-stable two-candidate chooser.
2. Define the maximum nonempty-prefix scan and prove its membership and
   optimality contract.
3. Derive the maximum nonempty suffix through reverse traversal and prove the
   reverse/specification bridge.
4. Combine the selected suffix and prefix into a crossing selector.
5. Prove the selector returns an optimal crossing subarray or that no crossing
   candidate exists.
6. Compile the Chapter 4 source and advance the interface test to the next
   missing declaration.

## 3. Connect divide-and-conquer execution to correctness

File:

- Modify `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean`.

Steps:

1. Prove that `midpointSplitTree xs.length xs` has only empty or singleton
   leaves.
2. Define the singleton leaf solver and a combine operation using the linear
   crossing selector.
3. Define the corresponding split-tree execution.
4. Reuse the existing maximum-subarray specification decomposition to prove
   the executable result satisfies `IsMaxSubarrayResult`.
5. Add a costed tree execution returning `(result, Nat)`.
6. Prove that erasing the cost component recovers the executable result.

## 4. Derive the real cost recurrence

File:

- Modify `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean`.

Steps:

1. Give the prefix/suffix/crossing scans explicit abstract transition costs.
2. Prove those costs depend only on list length and are linear.
3. Define the length-indexed cost for the fully expanded midpoint tree.
4. Prove the measured execution cost equals that length-indexed function.
5. Prove the nontrivial unfolding equation uses both `n / 2` and
   `n - n / 2`.
6. Remove or rename PR #87's disconnected symmetric-floor recurrence so no
   theorem can be mistaken for the executable algorithm's runtime.

## 5. Prove the all-input asymptotic result

File:

- Modify `CLRSLean/Chapter_04/Section_04_1_Maximum_Subarray.lean`.

Steps:

1. Establish monotonicity or comparison lemmas for the actual cost.
2. Bound it below and above by proved balanced floor/ceiling recurrences, or
   equivalently by adjacent powers of two.
3. Apply the existing Chapter 4 Master-theorem/log-scale infrastructure to the
   comparison functions.
4. Transfer `isBigOmega` and `isBigO` through the pointwise comparisons.
5. Export the executable-cost `Θ(n log n)` theorem and audit its axioms.

## 6. Synchronize documentation and progress

Files:

- Modify `CLRSLean/Chapter_04.lean`.
- Modify `CLRSLean/Status.lean`.
- Modify `docs/chapters/chapter-04.md`.
- Modify `docs/proof-map.md`.
- Modify `docs/status/blocked-and-deferred.md` as needed.
- Modify `docs/clrs-proof-progress.csv` and regenerate derived dashboards.

Steps:

1. List the executable selector, erasure, correctness, recurrence, and
   asymptotic theorems.
2. Mark the Chapter 4 algorithm-level runtime layer complete.
3. Retain an explicit note that full RAM/list-allocation refinement is outside
   the theorem.
4. Regenerate and validate the progress dashboard.

## 7. Completion gate and PR update

Run:

```text
lake env lean Tests/Chapter_04_Interface.lean
lake build CLRSLean.Chapter_04.Section_04_1_Maximum_Subarray
python3 scripts/check_repository.py
python3 scripts/check_progress_csv.py
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_04 Tests/Chapter_04_Interface.lean
git diff --check
lake build CLRSLean
lake build :literateHtml
```

Then:

1. Inspect the complete diff and commits.
2. Push with `--force-with-lease` only because the PR branch is rebased.
3. Update PR #87's description/comment with the exact semantic bridge and
   cost-model boundary.
4. Observe required CI checks to completion and repair any failure before
   handing off.
