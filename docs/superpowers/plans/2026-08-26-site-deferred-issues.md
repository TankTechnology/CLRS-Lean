# Deferred Site Issues Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the mobile-unfriendly progress matrix, remove the oversized-chapter render straggler, and publish correct canonical crawler metadata.

**Architecture:** Keep CSV generation, Verso rendering, and four-shard deployment intact.  Change only the generated matrix representation, the planner's unit construction for oversized affinity groups, and final-site metadata assembly.

**Tech Stack:** Python `unittest`, Lean/Verso Markdown, CSS, Playwright/Chrome.

---

### Task 1: Semantic responsive Progress matrix

**Files:**
- Modify: `scripts/test_check_progress_csv.py`
- Modify: `scripts/check_progress_csv.py`
- Modify: `scripts/test_prepare_literate_site.py`
- Modify: `docs/literate/clrs-literate.css`
- Generate: `CLRSLean/Progress.lean`

- [ ] **Step 1: Write failing generator and stylesheet tests**

Require a `CLRS-PROGRESS-MATRIX` marker followed by tab-delimited fields, reject
the old fixed-width header, and require mobile selectors scoped through
`.clrs-progress-matrix`.

- [ ] **Step 2: Verify RED**

Run `uv run python scripts/test_check_progress_csv.py` and
`uv run python scripts/test_prepare_literate_site.py`.  Expected: failures for
the missing Markdown table and missing matrix-specific mobile rules.

- [ ] **Step 3: Implement the minimal generator and CSS changes**

Emit one tab-delimited row per CSV chapter.  Add a tested optimizer transform
from the marked `<pre>` to a semantic table with `scope="col"` headers and
`data-label` cells, then add narrow-screen row-card rules using those labels.

- [ ] **Step 4: Regenerate and verify GREEN**

Run `uv run python scripts/check_progress_csv.py --write-dashboard`, then both
focused test files.  Expected: all tests pass.

- [ ] **Step 5: Commit**

Commit as `fix(site): make progress matrix responsive`.

### Task 2: Adaptive oversized-affinity shard planning

**Files:**
- Modify: `scripts/test_plan_literate_shards.py`
- Modify: `scripts/plan_literate_shards.py`

- [ ] **Step 1: Write the failing oversized-group test**

Construct two small chapter groups and one chapter larger than
`sum(size_bytes) / shard_count`; require the large chapter to span shards, the
small groups to remain intact, deterministic output, and reduced maximum load.

- [ ] **Step 2: Verify RED**

Run `uv run python scripts/test_plan_literate_shards.py`.  Expected: the large
chapter remains in one shard and the balance assertion fails.

- [ ] **Step 3: Implement adaptive planning units**

Compute the ideal ceiling load, keep normal affinity groups intact, expand only
oversized groups to per-module units, and schedule all units largest-first to
the lightest shard with stable tie breaking.

- [ ] **Step 4: Verify GREEN and measure the real plan**

Run the focused test and plan the current `.lake/build/literate-module-map` into
a temporary directory.  Expected: tests pass and the real estimated skew is
materially below the previous `495735022` bytes.

- [ ] **Step 5: Commit**

Commit as `perf(site): balance oversized literate chapters`.

### Task 3: Canonical crawler metadata

**Files:**
- Modify: `scripts/test_prepare_literate_site.py`
- Modify: `scripts/prepare_literate_site.py`

- [ ] **Step 1: Write failing canonical and robots tests**

For a two-page fixture, require exactly one page-specific
`<link rel="canonical">` per HTML file and a `robots.txt` containing
`User-agent: *`, `Allow: /`, and the canonical sitemap URL.

- [ ] **Step 2: Verify RED**

Run `uv run python scripts/test_prepare_literate_site.py`.  Expected: canonical
links and `robots.txt` are absent.

- [ ] **Step 3: Implement final-site metadata assembly**

Derive canonical URLs with the existing `page_url` function, replace or insert
one canonical tag before `</head>`, and generate `robots.txt` from the normalized
base URL.

- [ ] **Step 4: Verify GREEN**

Run the focused test twice against the same fixture behavior.  Expected: all
tests pass and each page contains one canonical tag.

- [ ] **Step 5: Commit**

Commit as `fix(site): publish canonical crawler metadata`.

### Task 4: Integrated verification

**Files:**
- Verify all modified source and generated files.

- [ ] **Step 1: Run repository checks**

Run `uv run python scripts/check_repository.py` and `git diff --check`.

- [ ] **Step 2: Render the affected reader page**

Build the Progress literate target, prepare a temporary deployable site, and
run the rendering checks.

- [ ] **Step 3: Run desktop/mobile browser regression**

Require a semantic table on desktop, labeled card rows on 390-pixel mobile, no
global horizontal overflow, correct canonical URL, and zero console errors.

- [ ] **Step 4: Report external boundary**

State that repository-controlled indexing signals are fixed while crawler cache
refresh timing remains external.  Do not push or deploy without authorization.
