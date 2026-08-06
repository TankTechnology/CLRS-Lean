# CLRS Fourth-Edition Primary Migration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make CLRS fourth-edition Chapters 1--35 the canonical repository and website view, preserve the current third-edition API through a documented compatibility window, and replace serial Verso publishing with an atomically merged four-shard renderer.

**Architecture:** Add a `CLRSLean.FourthEdition` facade over the current theorem-bearing modules, backed by a machine-readable edition map and fourth-edition progress ledger. Keep existing modules as compatibility sources and collect moved material under `CLRSLean.OnlineMaterial`. Extend the narrow Verso patch so every renderer receives the full site graph but emits a disjoint module subset; validate and merge shard artifacts before one Pages deployment.

**Tech Stack:** Lean 4.32, Mathlib, Verso literate HTML, Python 3.11 standard library, GitHub Actions, CSV/TOML metadata.

---

## File structure

- `CLRSLean/FourthEdition.lean`: canonical fourth-edition aggregator and reader contract.
- `CLRSLean/FourthEdition/Chapter_01.lean` through `Chapter_35.lean`: small fourth-edition chapter facades with exact reused source and gap statements.
- `CLRSLean/OnlineMaterial.lean`: catalog/import aggregator for proof content moved online or out of the fourth-edition main chapters.
- `docs/clrs-fourth-edition-map.csv`: section/chapter edition bridge and migration state.
- `docs/clrs-proof-progress.csv`: fourth-edition chapter progress rows.
- `docs/migrations/clrs4.md`: user-facing import migration and deprecation policy.
- `scripts/check_edition_map.py`: validate the edition map, facade guides, titles, sources, and progress rows.
- `scripts/test_check_edition_map.py`: focused validator regression tests.
- `patches/verso/sharded-literate-html.patch`: scoped upstream renderer extension.
- `scripts/apply_verso_patch.py`: apply both tracked Verso patches idempotently.
- `scripts/plan_literate_shards.py`: deterministic balanced module partitioning.
- `scripts/merge_literate_shards.py`: digest/page/metadata validation and atomic shard merge.
- `scripts/test_plan_literate_shards.py`, `scripts/test_merge_literate_shards.py`: fast sharding tests.
- `.github/workflows/pages.yml`: prepare once, render four matrix shards, merge, validate, deploy once.
- `literate.toml`, `scripts/literate_navigation.py`: fourth-edition reader navigation policy.
- `README.md`, `CLRSLean.lean`, `CLRSLean/Status.lean`, `CLRSLean/Workflow.lean`, `docs/index.md`, `docs/proof-map.md`: fourth-edition-primary prose and links.

### Task 1: Lock the edition-map contract with failing tests

**Files:**
- Create: `scripts/test_check_edition_map.py`
- Create: `scripts/check_edition_map.py`
- Modify: `scripts/check_repository.py`

- [ ] **Step 1: Write the failing validator tests**

Create fixture-driven tests that require: official Chapters 1--35 in order,
unique chapter/section keys, valid states, existing mapped sources, zero proof
counts for `not-started`, and matching facade/progress titles.  Use temporary
directories and this public entry point:

```python
errors = validate_repository(root)
self.assertEqual([], errors)
```

- [ ] **Step 2: Run the focused test and verify failure**

Run: `python3 scripts/test_check_edition_map.py`

Expected: FAIL because `scripts/check_edition_map.py` and the map do not exist.

- [ ] **Step 3: Implement the validator**

Define `MAP_HEADER` and `VALID_STATES` exactly as follows.  Add
`validate_repository(root: Path) -> list[str]`, which returns every
deterministically sorted contract violation, and `main() -> int`, which prints
them before returning status 1 (or prints `Fourth-edition map OK` and returns
0):

```python
MAP_HEADER = [
    "chapter_no", "section_no", "chapter_title", "section_title",
    "migration_state", "source_modules", "legacy_location", "coverage_note",
]
VALID_STATES = {"native", "facade", "partial", "not-started", "online-material"}
```

Collect every validation error in deterministic order instead of stopping on
the first error.  Add `scripts/check_edition_map.py` and its unit test to
`CHECK_COMMANDS` in `scripts/check_repository.py`.

- [ ] **Step 4: Run tests**

Run: `python3 scripts/test_check_edition_map.py`

Expected: fixture tests PASS; the real validator still reports missing
repository artifacts until Tasks 2--4 land.

- [ ] **Step 5: Commit**

```bash
git add scripts/check_edition_map.py scripts/test_check_edition_map.py scripts/check_repository.py
git commit -m "test: define fourth-edition mapping contract"
```

### Task 2: Add the canonical fourth-edition map and facades

**Files:**
- Create: `docs/clrs-fourth-edition-map.csv`
- Create: `CLRSLean/FourthEdition.lean`
- Create: `CLRSLean/FourthEdition/Chapter_01.lean` through `Chapter_35.lean`
- Modify: `CLRSLean.lean`

- [ ] **Step 1: Write the edition map**

Add all official fourth-edition chapter/section rows.  Use `facade` for reused
content, `partial` when only some fourth-edition obligations are represented,
and `not-started` for new or absent sections.  Map chapter shifts exactly:

```text
4e 14 <- current 15    4e 19 <- current 21    4e 24 <- current 26
4e 15 <- current 16    4e 20 <- current 22    4e 26 <- current 27
4e 16 <- current 17    4e 21 <- current 23
4e 17 <- current 14    4e 22 <- current 24
                       4e 23 <- current 25
```

- [ ] **Step 2: Add chapter facades**

Each facade imports only its current source guide(s), carries a module docstring
with the official title, and records `Current source` plus `Fourth-edition
gaps`.  For example:

```lean
import CLRSLean.Chapter_21

/-!
# Chapter 19 — Data Structures for Disjoint Sets

Fourth-edition canonical guide.  During the compatibility period, the proved
content is supplied by the third-edition-numbered `CLRSLean.Chapter_21` module.

Current source: Sections 19.1--19.4 are represented by the existing disjoint-set
development.  Declaration names remain under `CLRS.Chapter21` until the
chapter-by-chapter namespace migration.

Fourth-edition gaps: none inside the currently advertised pure-functional and
amortized-cost model; pointer/RAM refinements remain outside that boundary.
-/
```

New Chapters 25, 27, and 33 import `Mathlib` only and explicitly state
`Status: not-started`.

- [ ] **Step 3: Add the fourth-edition aggregator**

Import all 35 guides in numerical order and state that the prefix is
transitional.  Add `import CLRSLean.FourthEdition` to `CLRSLean.lean` while
retaining all existing imports.

- [ ] **Step 4: Verify focused Lean builds**

Run:

```bash
lake build +CLRSLean.FourthEdition.Chapter_19
lake build +CLRSLean.FourthEdition.Chapter_25
lake build +CLRSLean.FourthEdition
```

Expected: all targets build without unfinished-proof warnings or errors.

- [ ] **Step 5: Commit**

```bash
git add docs/clrs-fourth-edition-map.csv CLRSLean/FourthEdition.lean CLRSLean/FourthEdition CLRSLean.lean
git commit -m "feat: add fourth-edition canonical chapter facades"
```

### Task 3: Add online-material and compatibility policy

**Files:**
- Create: `CLRSLean/OnlineMaterial.lean`
- Create: `docs/migrations/clrs4.md`
- Create: `Tests/FourthEdition_Compatibility.lean`
- Modify: `CLRSLean.lean`

- [ ] **Step 1: Write the compatibility test**

Import representative old and new paths and check declarations across shifted
chapters:

```lean
import CLRSLean.FourthEdition
import CLRSLean.Chapter_19
import CLRSLean.Chapter_21
import CLRSLean.Chapter_27

#check CLRS.Chapter19.FH.extractMin_correct
#check CLRS.Chapter21.Forest.singletonForest_size
#check CLRS.Chapter27.CompDAG.greedySchedule
```

Use real public declarations for every shifted source chapter.

- [ ] **Step 2: Add the online-material catalog**

Import the existing Fibonacci heap, van Emde Boas, and geometry guides plus
the theorem-bearing modules for moved maximum-subarray, perfect-hashing,
matroid/task-scheduling, simplex, iterative-FFT, and integer-factorization
material.  The docstring must distinguish official fourth-edition online
material from project supplements and must not claim that old chapter numbers
remain canonical.

- [ ] **Step 3: Document deprecation**

`docs/migrations/clrs4.md` must include the mapping table, new import examples,
the all-`1.x`/six-month compatibility guarantee, the `2.0` cleanup gate, and a
statement that declaration namespaces migrate chapter-by-chapter.

- [ ] **Step 4: Build compatibility surfaces**

Run:

```bash
lake build +CLRSLean.OnlineMaterial
lake lean Tests/FourthEdition_Compatibility.lean
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add CLRSLean/OnlineMaterial.lean docs/migrations/clrs4.md Tests/FourthEdition_Compatibility.lean CLRSLean.lean
git commit -m "feat: preserve CLRS3 compatibility and catalog online material"
```

### Task 4: Switch progress and public prose to fourth-edition primary

**Files:**
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `scripts/check_progress_csv.py`
- Modify: `scripts/test_check_progress_csv.py`
- Modify: `scripts/gen_readme_table.py`
- Modify: `scripts/test_gen_readme_table.py`
- Regenerate: `CLRSLean/Progress.lean`
- Modify: `README.md`
- Modify: `CLRSLean.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `CLRSLean/Workflow.lean`
- Modify: `CLAUDE.md`
- Modify: `docs/index.md`
- Modify: `docs/proof-map.md`

- [ ] **Step 1: Rewrite the progress rows**

Use official fourth-edition titles and remap existing counts to their reused
chapter.  Chapters 25, 27, 33, 34, and 35 have zero canonical tracked theorems
unless an explicit fourth-edition facade row maps a represented section.
Remove the obsolete Chapters 1--29 third-edition milestone logic and replace it
with fourth-edition snapshot language plus a separate online-material total.

- [ ] **Step 2: Adapt progress validation**

Validate guides under `CLRSLean/FourthEdition/Chapter_NN.lean` and use the
edition map for represented-section/source checks rather than inferring
fourth-edition sections from legacy filenames.

- [ ] **Step 3: Regenerate generated surfaces**

Run:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
python3 scripts/gen_readme_table.py
```

Expected: the dashboard and README show fourth-edition Chapters 1--35.

- [ ] **Step 4: Update reader and contributor prose**

State the fourth-edition-primary policy in the opening paragraph of README and
the website landing page.  Link the migration guide.  Remove claims that the
third-edition Chapters 1--29 prefix is the current public milestone.  Update
Status, Workflow, CLAUDE, the docs index, and the proof-map preamble so chapter
numbers are interpreted through the edition map.

- [ ] **Step 5: Run metadata tests**

Run:

```bash
python3 scripts/check_edition_map.py
python3 scripts/check_progress_csv.py --check-dashboard
python3 scripts/gen_readme_table.py --check
```

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add docs/clrs-proof-progress.csv scripts/check_progress_csv.py scripts/test_check_progress_csv.py scripts/gen_readme_table.py scripts/test_gen_readme_table.py CLRSLean/Progress.lean README.md CLRSLean.lean CLRSLean/Status.lean CLRSLean/Workflow.lean CLAUDE.md docs/index.md docs/proof-map.md
git commit -m "docs: make CLRS4 the primary progress view"
```

### Task 5: Switch reader navigation to the fourth-edition facade

**Files:**
- Modify: `literate.toml`
- Modify: `scripts/literate_navigation.py`
- Modify: `scripts/test_literate_navigation.py`
- Modify: `scripts/test_literate_config.py`

- [ ] **Step 1: Write failing navigation tests**

Require sidebar visibility for `CLRSLean.FourthEdition`, its 35 direct chapter
children, `CLRSLean.OnlineMaterial`, Progress, Status, and Workflow.  Require
legacy unqualified `CLRSLean.Chapter_XX` aggregators and deep helper modules to
be hidden.

- [ ] **Step 2: Run tests and verify failure**

Run:

```bash
python3 scripts/test_literate_navigation.py
python3 scripts/test_literate_config.py
```

Expected: FAIL because the current sidebar recognizes only unqualified
chapters.

- [ ] **Step 3: Update policy and TOML**

Teach `is_reader_sidebar_module` this shape:

```python
parts == ["CLRSLean", "FourthEdition"]
or (len(parts) == 3 and parts[:2] == ["CLRSLean", "FourthEdition"]
    and CHAPTER_MODULE_RE.fullmatch(parts[2]))
```

Order the root pages as Fourth Edition, Online Material, Proof Patterns,
Probability, Extensions, Progress, Status, Workflow.  Add all 35 official
chapter titles under `CLRSLean.FourthEdition`.  Keep legacy module title blocks
for direct URLs but remove them from the reader sidebar.

- [ ] **Step 4: Run navigation tests**

Run:

```bash
python3 scripts/test_literate_navigation.py
python3 scripts/test_literate_config.py
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add literate.toml scripts/literate_navigation.py scripts/test_literate_navigation.py scripts/test_literate_config.py
git commit -m "site: navigate by fourth-edition chapters"
```

### Task 6: Define sharding behavior with tests

**Files:**
- Create: `scripts/test_plan_literate_shards.py`
- Create: `scripts/test_merge_literate_shards.py`
- Create: `scripts/plan_literate_shards.py`
- Create: `scripts/merge_literate_shards.py`
- Modify: `scripts/check_repository.py`

- [ ] **Step 1: Write planner tests**

Test deterministic largest-first assignment, full coverage, no duplicates,
four-shard default, configurable shard count, chapter affinity, and maximum
load skew reporting.  The CLI writes one module name per line under
`OUT/shard-N.txt` plus `OUT/manifest.json`.

- [ ] **Step 2: Write merger tests**

Build temporary shard directories and test matching digest success, digest
mismatch, duplicate module, missing module, unexpected module, unequal metadata
key collision, and deterministic merged output.

- [ ] **Step 3: Run tests and verify failure**

Run:

```bash
python3 scripts/test_plan_literate_shards.py
python3 scripts/test_merge_literate_shards.py
```

Expected: FAIL because the implementation scripts do not exist.

- [ ] **Step 4: Implement planner and merger**

The planner exposes `discover_modules(module_map: Path) -> list[ModuleCost]`,
which parses every tab-separated module-map row and reads the corresponding
JSON byte size, and `partition_modules(modules, shard_count)`, which validates a
positive shard count and performs deterministic largest-first assignment.  The
merger exposes `merge_shards(manifest, shard_roots, output) -> list[str]`; it
validates every shard before staging copied output and returns a deterministic
error list.

Use SHA-256 over toolchain, manifest, TOML, module map, and input JSON hashes.
Copy only after all validation succeeds; assemble in a temporary sibling and
rename it into place.

- [ ] **Step 5: Run tests**

Expected: all planner and merger tests PASS.

- [ ] **Step 6: Add tests to repository check and commit**

```bash
git add scripts/plan_literate_shards.py scripts/merge_literate_shards.py scripts/test_plan_literate_shards.py scripts/test_merge_literate_shards.py scripts/check_repository.py
git commit -m "build: add deterministic literate shard planning and merge"
```

### Task 7: Extend the scoped Verso patch for shard emission

**Files:**
- Create: `patches/verso/sharded-literate-html.patch`
- Modify: `scripts/apply_verso_patch.py`
- Modify: `scripts/test_apply_verso_patch.py`
- Create: `scripts/render_literate_shard.py`

- [ ] **Step 1: Extend patch-application tests**

Require both tracked patches to apply in order, reapply idempotently, and report
which patch drifted.  The result remains no-fetch/no-checkout/no-reset.

- [ ] **Step 2: Patch the renderer**

Add CLI options for `--emit-list`, `--metadata-out`, and `--coordinator`.  Load
and traverse the complete module map exactly once per process, filter only the
`emitDir` write loop, emit shard metadata for non-coordinators, and reserve
landing/search/xref/shared output for the coordinator.

- [ ] **Step 3: Add the shard runner**

`render_literate_shard.py` invokes the patched executable with the complete
module map and one emit list, then writes a shard record containing input
digest, module list, duration, byte count, and metadata path.

- [ ] **Step 4: Run patch and focused renderer tests**

Run:

```bash
python3 scripts/test_apply_verso_patch.py
python3 scripts/apply_verso_patch.py
lake build verso-literate-html
```

Expected: patch tests PASS, both patches report applied/already-applied, and the
renderer builds.

- [ ] **Step 5: Commit**

```bash
git add patches/verso/sharded-literate-html.patch scripts/apply_verso_patch.py scripts/test_apply_verso_patch.py scripts/render_literate_shard.py
git commit -m "build: enable full-context sharded Verso rendering"
```

### Task 8: Wire atomic parallel Pages publishing

**Files:**
- Modify: `.github/workflows/pages.yml`
- Modify: `scripts/test_workflow_policy.py`
- Modify: `docs/site-architecture.md`
- Modify: `README.md`
- Modify: `CLAUDE.md`

- [ ] **Step 1: Write failing workflow-policy tests**

Require jobs named `prepare`, `render`, `merge`, and `deploy`; a four-value
render matrix; artifact upload/download between stages; merge validation before
`upload-pages-artifact`; and `deploy` depending only on the successful merge.
Keep `workflow_dispatch` as the only trigger.

- [ ] **Step 2: Run the policy test and verify failure**

Run: `python3 scripts/test_workflow_policy.py`

Expected: FAIL against the serial workflow.

- [ ] **Step 3: Rewrite the workflow**

The prepare job checks metadata, prepares dependencies/patches, builds literate
JSON, creates the four-shard manifest, and uploads immutable inputs.  The matrix
render job renders exactly one shard and uploads it.  The merge job downloads
all shards, validates/merges, runs raw/freshness/rendering/preparation checks,
and uploads one Pages artifact.  Deploy remains restricted to `main`.

- [ ] **Step 4: Document the runbook**

Record the four-stage pipeline, serial fallback, digest invariant, maximum
four-way local concurrency, and first-deployment measurements in README,
CLAUDE, and site architecture.

- [ ] **Step 5: Run workflow tests and commit**

```bash
python3 scripts/test_workflow_policy.py
git add .github/workflows/pages.yml scripts/test_workflow_policy.py docs/site-architecture.md README.md CLAUDE.md
git commit -m "ci: render Verso pages in parallel shards"
```

### Task 9: Full migration and publishing verification

**Files:**
- Modify as needed only when verification exposes a scoped defect.

- [ ] **Step 1: Run fast repository checks**

Run: `uv run python scripts/check_repository.py`

Expected: `Repository checks passed.`

- [ ] **Step 2: Check proof placeholders and diff hygiene**

Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/FourthEdition CLRSLean/OnlineMaterial.lean Tests/FourthEdition_Compatibility.lean -g '*.lean'
git diff --check
```

Expected: no proof markers outside prose; no whitespace errors.

- [ ] **Step 3: Run the full Lean gate**

Run: `lake build CLRSLean`

Expected: successful full library build.

- [ ] **Step 4: Run one serial reference build**

Run:

```bash
python3 scripts/apply_verso_patch.py
lake build :literateHtml
```

Expected: successful reference output with no proof-state DOM and no page over
the raw size guard.

- [ ] **Step 5: Run the local four-shard build and compare inventories**

Run the planner, four shard renderers, and merger with `--jobs 4`.  Compare the
set of module `index.html` files to the serial reference.  Run:

```bash
python3 scripts/check_literate_html_weight.py <merged-output>
python3 scripts/check_literate_html_freshness.py <merged-output>
python3 scripts/prepare_literate_site.py <merged-output> _site-clrs4
```

Expected: identical expected module inventory and all validation commands PASS.

- [ ] **Step 6: Record measurements and final audit**

Add the measured preparation, slowest shard, merge, assembly, output-size, and
largest-page values to a dated audit under `docs/proof-audits/`.  Confirm all
35 guides, five not-started chapter rows, online-material entries, and legacy
compatibility tests.

- [ ] **Step 7: Commit verification fixes and audit**

```bash
git add docs/proof-audits
git commit -m "docs: audit fourth-edition migration and sharded publishing"
```
