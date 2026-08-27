# Whole-Book Proof-Gap Audit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce an evidence-backed 35-chapter proof-gap audit, repair confirmed status drift, and create exact Lean closure targets for every genuine main-text gap.

**Architecture:** Extend the existing canonical progress validator rather than creating a second live ledger.  Record the complete assessment in one dated immutable audit report, keep unresolved work in GitHub issues, and give each substantive proof gap its own focused design and implementation plan.

**Tech Stack:** Lean 4.32, Mathlib, Python standard-library validation scripts, CLRS-Lean progress and edition-map CSVs, native axiom audit, GitHub issues.

---

## File structure

- `scripts/check_progress_csv.py`: reusable extraction and validation of numeric theorem-count claims and fully-proved section-range claims.
- `scripts/test_check_progress_csv.py`: red-green regression tests for the Chapter 31 inconsistencies.
- `docs/clrs-proof-progress.csv`: corrected Chapter 31 count and fourth-edition section range.
- `CLRSLean/FourthEdition/Chapter_32/Section_32_2_Rabin_Karp.lean`: remove the stale rolling-recurrence gap sentence and document the proved bridge.
- `docs/audits/2026-08-28-whole-book-proof-gap-audit.md`: immutable per-chapter evidence matrix and ranked closure queue.
- `docs/audits/INDEX.md`: link the new audit snapshot without turning it into a live status ledger.
- `docs/superpowers/specs/2026-08-28-ch02-executable-merge-sort-design.md`: focused design created only if the audit confirms the Chapter 2 bridge gap.
- `docs/superpowers/plans/2026-08-28-ch02-executable-merge-sort.md`: red-green Chapter 2 implementation plan.
- `docs/superpowers/specs/2026-08-28-ch11-uniform-probe-space-design.md`: focused design created only if the audit confirms the Chapter 11 probability-provenance gap.
- `docs/superpowers/plans/2026-08-28-ch11-uniform-probe-space.md`: red-green Chapter 11 implementation plan.

### Task 1: Make progress prose machine-checkable

**Files:**
- Modify: `scripts/test_check_progress_csv.py`
- Modify: `scripts/check_progress_csv.py`

- [ ] **Step 1: Add failing count-claim tests**

Add tests that mutate a valid row and require rejection:

```python
def test_rejects_completion_read_tracked_count_drift(self) -> None:
    rows = [row.copy() for row in load_rows()]
    rows[30]["completion_read"] = (
        "The fourth-edition native source proves 17 tracked theorem groups"
    )
    with self.assertRaisesRegex(SystemExit, "claims 17 tracked theorem groups"):
        validate(rows)

def test_accepts_completion_read_without_numeric_tracked_claim(self) -> None:
    rows = [row.copy() for row in load_rows()]
    rows[30]["completion_read"] = "Native proof boundary documented in source"
    validate(rows)
```

- [ ] **Step 2: Add a failing fully-proved range test**

```python
def test_rejects_fully_proved_range_outside_represented_sections(self) -> None:
    rows = [row.copy() for row in load_rows()]
    rows[30]["notes"] = "Sections 31.1-31.9 fully proved."
    with self.assertRaisesRegex(SystemExit, "fully proved section 31.9"):
        validate(rows)
```

- [ ] **Step 3: Run the tests and confirm the intended RED failures**

Run:

```text
python3 scripts/test_check_progress_csv.py
```

Expected: the two rejection tests fail because `validate` currently accepts
both contradictions; all pre-existing tests remain green.

- [ ] **Step 4: Implement count and section-range extraction**

Add these helpers to `scripts/check_progress_csv.py`:

```python
TRACKED_COUNT_CLAIM = re.compile(
    r"\b(\d+)\s+tracked theorem (?:entries|groups)\b", re.IGNORECASE
)
FULLY_PROVED_RANGE = re.compile(
    r"\bSections?\s+(\d+)\.(\d+)\s*[-–]\s*(\d+)\.(\d+)\s+fully proved\b",
    re.IGNORECASE,
)

def tracked_count_claims(text: str) -> tuple[int, ...]:
    return tuple(int(match.group(1)) for match in TRACKED_COUNT_CLAIM.finditer(text))

def fully_proved_sections(text: str) -> tuple[str, ...]:
    sections: list[str] = []
    for match in FULLY_PROVED_RANGE.finditer(text):
        low_chapter, low, high_chapter, high = map(int, match.groups())
        if low_chapter != high_chapter or high < low:
            continue
        sections.extend(f"{low_chapter}.{index}" for index in range(low, high + 1))
    return tuple(sections)
```

Import `re`.  In `validate`, require every numeric tracked-count claim in
`completion_read` to equal `tracked`, and require every section returned from
`fully_proved_sections(row["notes"])` to belong to `expected_sections`.

- [ ] **Step 5: Run the focused tests**

Run:

```text
python3 scripts/test_check_progress_csv.py
python3 scripts/check_progress_csv.py --check-dashboard
```

Expected: the unit test currently reports the live Chapter 31 contradiction;
the second command exits nonzero naming the Chapter 31 count.

- [ ] **Step 6: Commit the red-to-green validator unit**

Do not commit until Task 2 corrects the live data and both commands pass; then
commit Tasks 1 and 2 together as one consistency-gate checkpoint.

### Task 2: Correct confirmed Chapter 31 and Chapter 32 drift

**Files:**
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/FourthEdition/Chapter_32/Section_32_2_Rabin_Karp.lean`

- [ ] **Step 1: Correct the Chapter 31 completion prose**

In the Chapter 31 row:

- replace `proves 17 tracked theorem groups` with
  `proves 18 tracked theorem groups`;
- replace `Sections 31.1-31.9 fully proved` with
  `Sections 31.1-31.8 fully proved`.

Do not change the numeric 18/18 fields or promote the online-material
factorization section into canonical Chapter 31.

- [ ] **Step 2: Correct the Rabin--Karp source overview**

Replace the stale paragraph with:

```text
The CLRS window-slide recurrence (eq. (32.3)) is proved as `hash_slide`.
`rabinKarpRollingMatches_correct` connects the rolling execution to the
all-occurrences specification, while `rabinKarpRollingCost_eq` and
`rabinKarpRollingCost_le` attach the deterministic work bound to that
execution.
```

- [ ] **Step 3: Verify the consistency gate**

Run:

```text
python3 scripts/test_check_progress_csv.py
python3 scripts/check_progress_csv.py --check-dashboard
python3 scripts/check_repository.py
git diff --check
```

Expected: all commands exit 0.

- [ ] **Step 4: Commit the consistency checkpoint**

```text
git add scripts/check_progress_csv.py scripts/test_check_progress_csv.py \
  docs/clrs-proof-progress.csv \
  CLRSLean/FourthEdition/Chapter_32/Section_32_2_Rabin_Karp.lean
git commit -m "fix(audit): reject and repair proof-ledger prose drift"
```

### Task 3: Produce the 35-chapter evidence matrix

**Files:**
- Create: `docs/audits/2026-08-28-whole-book-proof-gap-audit.md`
- Modify: `docs/audits/INDEX.md`

- [ ] **Step 1: Inventory every chapter using the six-lane contract**

For each chapter, read its canonical aggregator, mapped section modules,
progress row, fourth-edition map rows, interface test, and trust file.  Add one
audit-table row with these exact columns:

```text
Chapter | Semantics | Correctness/invariants | Optimality/lower bound |
Cost attachment | Model provenance | Public evidence | Verdict | Next target
```

Every `proved` cell must name at least one theorem or an exact source module.
Every non-proved cell must name the missing definition, theorem, invariant, or
bridge; labels such as “hard” or “needs more work” are not acceptable.

- [ ] **Step 2: Separate main-path gaps from scope exclusions**

Use `deferred-implementation` only for the exclusions enumerated in
`docs/scope.md`.  Use `semantic-bridge-gap` when both endpoints exist but no
theorem connects them.  Use `core-proof-gap` when a central CLRS claim has no
adequate theorem at all.

- [ ] **Step 3: Cross-check all claimed theorem names**

For every name in a nontrivial or disputed row, run `rg` against source and
`#check` it through the canonical fourth-edition chapter import.  Record the
interface or trust file that pins the result.  A declaration mentioned only in
prose is insufficient evidence.

- [ ] **Step 4: Add the ranked closure queue**

Rank findings by:

1. centrality to a named CLRS theorem or algorithm;
2. severity of model drift;
3. whether the missing bridge affects a public completion claim;
4. dependency value for later chapters;
5. estimated proof risk.

The initial candidates to confirm or reject are Chapter 2 top-level MERGE
composition, Chapter 4 arbitrary-input branching recurrence transfer, Chapter
11 explicit probe-order probability, Chapter 18 executable/specification shape
compatibility, and Chapter 21 incremental union-find/Kruskal integration.

- [ ] **Step 5: Link the immutable snapshot from the audit index**

Add a dated row to `docs/audits/INDEX.md` and state explicitly that the new
report is an evidence snapshot, while current unresolved work is tracked in
GitHub issues.

- [ ] **Step 6: Verify and commit the report**

Run:

```text
python3 scripts/check_repository.py
git diff --check
```

Expected: both commands exit 0 and every one of Chapters 1--35 appears exactly
once in the new report.

Commit:

```text
git add docs/audits/2026-08-28-whole-book-proof-gap-audit.md docs/audits/INDEX.md
git commit -m "docs(audit): assess proof obligations across all 35 chapters"
```

### Task 4: Turn genuine findings into independently closable proof work

**Files:**
- Create only the focused spec and plan files justified by Task 3.
- Update: GitHub issues for every unresolved `semantic-bridge-gap` or
  `core-proof-gap`.

- [ ] **Step 1: Create one issue per independent proof gap**

Each issue body must include:

```text
Textbook obligation
Current Lean endpoints
Exact missing theorem or definition
Rejected shortcut that would evade the obligation
Acceptance theorem signatures
Focused verification commands
```

Do not create issues for merely stale prose fixed in Task 2.  Group shared RAM
or pointer-model work into one infrastructure issue rather than duplicating it
across chapters.

- [ ] **Step 2: Write the Chapter 2 proof design and plan if confirmed**

The design must select a terminating recursion representation for top-level
merge sort, reuse `mergeWithCost`, and state exact sortedness, permutation,
erasure, and cost-attachment theorems.  The implementation plan must begin with
failing `#check` declarations in a focused Chapter 2 interface test.

- [ ] **Step 3: Write the Chapter 11 probability design and plan if confirmed**

The design must define the finite permutation sample space, the event that the
first `i` positions lie in a fixed occupied set, and the exact equality to
`probeTail`.  The plan must not redefine `probeTail` to make the equality
definitional.

- [ ] **Step 4: Verify issue/report consistency and commit the plans**

Run:

```text
gh issue list --state open --limit 200
python3 scripts/check_repository.py
git diff --check
```

Expected: every unresolved main-path finding links to one open issue, every
issue links back to the dated audit, and repository checks pass.

Commit the focused spec/plan files with:

```text
git commit -m "docs(proof): plan highest-risk textbook closure batches"
```

### Task 5: Execute proof batches in ranked order

**Files:**
- Modify only the source, interface, trust, guide, and ledger files named by
  each focused proof plan.

- [ ] **Step 1: Execute the Chapter 2 plan through its green interface**

Run each new small Lean module directly while developing.  After the public
bridge is green, run the Chapter 2 interface and trust files, then commit the
independently checkable closure.

- [ ] **Step 2: Execute the Chapter 11 plan through its green interface**

Keep finite counting, probability normalization, and public expectation
transport in separate modules.  Run each module directly and commit only after
the Chapter 11 interface and trust checks pass.

- [ ] **Step 3: Continue down the audited closure queue**

For every remaining main-path finding, follow its focused plan.  If a proof
attempt reveals that the finding is actually a scope exclusion, update the
issue with exact evidence and correct the audit classification; do not weaken
the intended theorem merely to close the issue.

- [ ] **Step 4: Run the final whole-project verification gate**

Run:

```text
rg -n '\b(sorry|admit|axiom)\b' CLRSLean Tests --glob '*.lean'
python3 scripts/check_repository.py
python3 scripts/check_v1_trust_gate.py
git diff --check
lake build CLRSLean
```

Expected: no unfinished proof markers beyond explanatory prose, all repository
and native trust checks pass, and the full Lean build exits 0.

- [ ] **Step 5: Update the audit closure record and integrate**

Append a dated closure table to the immutable audit report listing each issue,
theorem evidence, verification commands, and commit.  Merge the clean branch
only after every finding classified as a required main-path gap is either
proved or reclassified with source evidence.
