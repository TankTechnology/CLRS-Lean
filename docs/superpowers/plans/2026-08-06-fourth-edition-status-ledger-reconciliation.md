# Fourth-edition status-ledger reconciliation implementation plan

> **For Codex:** Execute this plan task by task, preserving the evidence-first
> completion rule in the approved design.

**Goal:** Correct stale fourth-edition section states, retain genuine gaps, and
make the README distinguish kernel-checked tracked entries from complete
fourth-edition section coverage.

**Architecture:** `docs/clrs-fourth-edition-map.csv` remains the section-level
contract. `scripts/check_progress_csv.py` conservatively rolls section gaps into
chapter status, and `docs/clrs-proof-progress.csv` supplies the reader-facing
chapter summaries. Generated README and Progress pages present those two layers
without conflating them.

**Tech stack:** Lean 4, Python 3 standard-library scripts/tests, Markdown, CSV.

---

## Task 1: Lock the two-layer README terminology with tests

**Files:**

- Modify: `scripts/test_gen_readme_table.py`
- Modify: `scripts/test_check_progress_csv.py`
- Modify: `scripts/gen_readme_table.py`
- Modify: `scripts/check_progress_csv.py`

1. Add a README-generator test requiring the snapshot and total to say that
   proved entries are a selected inventory and are not a complete-edition
   claim. Require the partial badge to read `partial coverage`.
2. Add a dashboard test requiring the same distinction between tracked-entry
   proof completion and edition-section coverage.
3. Run the two focused test files and confirm the new expectations fail.
4. Update the two generators with the minimum wording changes.
5. Rerun the focused tests and confirm they pass.

Commands:

```bash
python3 scripts/test_gen_readme_table.py
python3 scripts/test_check_progress_csv.py
```

## Task 2: Reconcile section evidence and states

**Files:**

- Modify: `docs/clrs-fourth-edition-map.csv`
- Modify: `docs/proof-map.md`
- Modify as evidence requires: `CLRSLean/Chapter_03.lean`
- Modify as evidence requires: `CLRSLean/Chapter_13.lean`
- Modify as evidence requires: `CLRSLean/Chapter_14.lean`
- Modify as evidence requires: `CLRSLean/Chapter_15.lean`
- Modify as evidence requires: `CLRSLean/Chapter_29.lean`
- Modify as evidence requires: `CLRSLean/FourthEdition/Chapter_03.lean`
- Modify as evidence requires: `CLRSLean/FourthEdition/Chapter_13.lean`
- Modify as evidence requires: `CLRSLean/FourthEdition/Chapter_14.lean`
- Modify as evidence requires: `CLRSLean/FourthEdition/Chapter_17.lean`
- Modify as evidence requires: `CLRSLean/FourthEdition/Chapter_29.lean`

1. Integrate the three independent audit reports for Chapters 3/13, 14, and
   17/29.
2. Resolve every cited theorem name and location directly with `rg` and source
   inspection.
3. For each section, write an exact coverage note naming proved obligations and
   any remaining central gap.
4. Change `partial` to `facade` only where all central obligations are
   theorem-backed at the documented abstraction level.
5. Update stale proof-map or chapter-guide prose so it agrees with declarations.
6. Run the edition-map tests and checker.

Commands:

```bash
python3 scripts/test_check_edition_map.py
python3 scripts/check_edition_map.py
```

## Task 3: Reconcile chapter roll-ups and exact remaining work

**Files:**

- Modify: `docs/clrs-proof-progress.csv`
- Regenerate: `CLRSLean/Progress.lean`
- Review/modify: `CLRSLean/Status.lean`

1. Update only audited chapter rows whose section contract changed or whose
   remaining-work prose was generic/stale.
2. Keep `tracked_key_theorems` and `proved_tracked_theorems` unchanged unless
   source-inventory evidence shows a counting error.
3. Set `missing_core_groups` to zero only when the map contains no `partial` or
   `not-started` section for that chapter.
4. Regenerate the progress dashboard.
5. Run focused progress validation and tests.

Commands:

```bash
python3 scripts/check_progress_csv.py --write-dashboard
python3 scripts/test_check_progress_csv.py
python3 scripts/check_progress_csv.py --check-dashboard
```

## Task 4: Regenerate README and verify affected Lean interfaces

**Files:**

- Regenerate: `README.md`
- Verify: affected fourth-edition and legacy chapter modules

1. Regenerate the README from the reconciled CSV.
2. Check that every remaining partial row shows a concrete central gap.
3. Build the affected chapter guides/modules together so Lean can reuse the
   shared build cache.
4. Run generated-file freshness checks.

Commands:

```bash
python3 scripts/gen_readme_table.py
python3 scripts/gen_readme_table.py --check
lake build \
  CLRSLean.FourthEdition.Chapter_03 \
  CLRSLean.FourthEdition.Chapter_13 \
  CLRSLean.FourthEdition.Chapter_14 \
  CLRSLean.FourthEdition.Chapter_17 \
  CLRSLean.FourthEdition.Chapter_29
```

## Task 5: Repository verification and independent review

**Files:**

- Verify all changed files

1. Run the complete lightweight repository checker; do not run a full Verso
   render because the literate graph and renderer are unchanged.
2. Run whitespace and generated-diff checks.
3. Ask an independent reviewer to look specifically for unsupported status
   promotions and map/progress contradictions.
4. Fix any findings and repeat focused/full checks.
5. Commit the implementation and push `main` only after all checks pass.

Commands:

```bash
python3 scripts/check_repository.py
git diff --check
git status --short
```
