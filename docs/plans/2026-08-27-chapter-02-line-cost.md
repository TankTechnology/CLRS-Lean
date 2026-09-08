# Chapter 2 Insertion-Sort Line-Cost Implementation Plan

**Goal:** Close issues #310 and #314 with a kernel-checked execution-count table
and complete CLRS Section 2.2 running-time formula.

**Architecture:** Split definitions, the generic formula, and best/worst
specializations into separate Lean modules.  Import them through one facade so
the reader page stays small and recompilation remains focused.

## Task 1: Pin the interface

- Add `Tests/Chapter_02_LineCost_Interface.lean`.
- Check the two records, aggregation functions, generic formula theorem, and
  best/worst specialization theorems.
- Run the file once and record the expected unknown-declaration failure.

## Task 2: Define the table

- Move the existing `triangular` definition into
  `LineCost/Definitions.lean` without changing its public name.
- Define `InsertionSortLineCosts`, `InsertionSortLineCounts`,
  `insertionSortLineCounts`, and `insertionSortRunningTime`.
- Build only the definitions module.

## Task 3: Prove the generic formula

- Prove `insertionSortRunningTime_eq_textbook_sum` by expanding the cost-table
  evaluator and the trace-derived count record.
- Keep the theorem statement in the same seven-term order as the textbook.
- Build only `LineCost/Formula.lean`.

## Task 4: Prove best and worst substitutions

- Define the constant-one best trace and identity worst trace.
- Prove their exact line-count records.
- Prove their complete running-time formulas.
- Build only `LineCost/BestWorst.lean`.

## Task 5: Wire, document, and audit

- Import the facade from Section 2.2 and remove the stale line-cost gap text.
- Add public checks to `Tests/Chapter_02_Interface.lean` and the two headline
  formulas to `Tests/Trust/Chapter_02.lean`.
- Register the split modules in `literate.toml` and link hidden support pages.
- Update the edition map, progress ledger, dashboard, README, and audit report.

## Task 6: Verify and integrate

- Build the canonical and compatibility Chapter 2 roots.
- Run focused and general Chapter 2 interfaces.
- Run the Chapter 2 native trust gate and `scripts/check_repository.py`.
- Run `git diff --check`, commit the milestone, fast-forward it to `main`,
  verify again on `main`, push, and close #310/#314 with explicit evidence.
