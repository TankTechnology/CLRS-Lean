# Chapter 34 Reader Structure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give fourth-edition Chapter 34 the same five-section reader hierarchy and concise landing-page structure as neighboring chapters.

**Architecture:** Five documentation-only fourth-edition adapter modules import the existing proved Chapter 34 section aggregates. `literate.toml` registers those adapters as canonical sidebar children, while the chapter root becomes a compact map of the existing theorem chain.

**Tech Stack:** Lean 4 module documentation, Verso Literate configuration, Python `unittest`, Playwright with system Chrome.

---

### Task 1: Lock the canonical five-section navigation contract

**Files:**
- Modify: `scripts/test_literate_config.py`

- [ ] **Step 1: Write the failing navigation test**

Add a test that expects the following modules, in order, both in the imports of
`CLRSLean/FourthEdition/Chapter_34.lean` and under its `order_children` entry:

```python
expected = [
    "CLRSLean.FourthEdition.Chapter_34.Section_34_1_Polynomial_Time",
    "CLRSLean.FourthEdition.Chapter_34.Section_34_2_Polynomial_Time_Verification",
    "CLRSLean.FourthEdition.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility",
    "CLRSLean.FourthEdition.Chapter_34.Section_34_4_NP_Completeness_Proofs",
    "CLRSLean.FourthEdition.Chapter_34.Section_34_5_NP_Complete_Problems",
]
```

The same test must require a configured title for every module and a chapter
landing-page link whose URL is `module.replace(".", "/") + "/"`.

- [ ] **Step 2: Run the test and observe the intended failure**

Run:

```bash
uv run python scripts/test_literate_config.py
```

Expected: failure because Chapter 34 has no fourth-edition section imports,
children, titles, or links.

- [ ] **Step 3: Commit the red test with the implementation batch**

Keep the failing test uncommitted until Tasks 2 and 3 make it green.

### Task 2: Add thin fourth-edition section adapters

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_34/Section_34_1_Polynomial_Time.lean`
- Create: `CLRSLean/FourthEdition/Chapter_34/Section_34_2_Polynomial_Time_Verification.lean`
- Create: `CLRSLean/FourthEdition/Chapter_34/Section_34_3_NP_Completeness_And_Reducibility.lean`
- Create: `CLRSLean/FourthEdition/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean`
- Create: `CLRSLean/FourthEdition/Chapter_34/Section_34_5_NP_Complete_Problems.lean`

- [ ] **Step 1: Create one adapter for each textbook section**

Each file imports its matching existing section aggregate and contains only a
reader-facing module doc. For example, 34.1 begins:

```lean
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time

/-!
# 34.1 Polynomial Time

This canonical fourth-edition reader page presents the deterministic
polynomial-time framework used throughout Chapter 34.

## Main results

- Polynomial-time composition.
- Closure of `P` under complement, union, and intersection.

## Implementation source

The complete theorem-bearing module is available at
[the Chapter 34 compatibility source](CLRSLean/Chapter_34/Section_34_1_Polynomial_Time/).
-/
```

The remaining adapters use these complete reader contracts:

```lean
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification

/-!
# 34.2 Polynomial-Time Verification

This reader page presents polynomial-time verification, bounded certificates,
and the inclusion {lit}`P ⊆ NP`.

## Main results

- Deterministic polynomial-time decision procedures yield NP verifiers.
- Polynomially bounded certificates characterize the chapter's NP languages.

## Implementation source

See [the complete theorem-bearing source](CLRSLean/Chapter_34/Section_34_2_Polynomial_Time_Verification/).
-/
```

```lean
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility

/-!
# 34.3 NP-Completeness and Reducibility

This reader page presents polynomial-time many-one reducibility and the
transport principles used by every later NP-completeness proof.

## Main results

- Polynomial-time reductions compose transitively.
- NP-hardness transports through a polynomial-time reduction.
- A language in NP that is NP-hard is NP-complete.

## Implementation source

See [the complete theorem-bearing source](CLRSLean/Chapter_34/Section_34_3_NP_Completeness_And_Reducibility/).
-/
```

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs

/-!
# 34.4 NP-Completeness Proofs

This reader page presents Cook--Levin and the first concrete NP-completeness
reductions in the textbook chain.

## Main results

- Cook--Levin reduces every NP language to general circuit satisfiability.
- {lit}`CIRCUIT-SAT ≤_P SAT ≤_P 3-CNF-SAT ≤_P CLIQUE`.
- General circuit satisfiability and the public graph-plus-{lit}`k` CLIQUE
  language are NP-complete.

## Implementation source

See [the complete theorem-bearing source](CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/).
-/
```

```lean
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems

/-!
# 34.5 NP-Complete Problems

This reader page presents the selected textbook chain beyond CLIQUE.

## Main results

- VERTEX-COVER is NP-complete.
- HAM-CYCLE is NP-complete.
- Decision-TSP is NP-complete.
- SUBSET-SUM is NP-complete.

## Implementation source

See [the complete theorem-bearing source](CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/).
-/
```

- [ ] **Step 2: Build only the five adapters**

Run:

```bash
lake build \
  CLRSLean.FourthEdition.Chapter_34.Section_34_1_Polynomial_Time \
  CLRSLean.FourthEdition.Chapter_34.Section_34_2_Polynomial_Time_Verification \
  CLRSLean.FourthEdition.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility \
  CLRSLean.FourthEdition.Chapter_34.Section_34_4_NP_Completeness_Proofs \
  CLRSLean.FourthEdition.Chapter_34.Section_34_5_NP_Complete_Problems
```

Expected: all five targets compile without unfinished-proof markers.

### Task 3: Rebuild the Chapter 34 reader hierarchy

**Files:**
- Modify: `CLRSLean/FourthEdition/Chapter_34.lean`
- Modify: `literate.toml`

- [ ] **Step 1: Replace the aggregate-only chapter import surface**

Import the five adapter modules at the top of the Chapter 34 guide. Replace the
long migration report with three compact sections:

```markdown
## Chapter map
## Main theorem chain
## Coverage boundary
```

The chapter map links to all five canonical adapter URLs. The theorem chain
states Cook--Levin and the textbook reductions without repeating implementation
milestones. The coverage statement remains scope-qualified and names the one
optional direct SAT-verifier refinement.

- [ ] **Step 2: Register the children and titles**

Add this direct-parent block in `[order_children]`:

```toml
"CLRSLean.FourthEdition.Chapter_34" = [
  "CLRSLean.FourthEdition.Chapter_34.Section_34_1_Polynomial_Time",
  "CLRSLean.FourthEdition.Chapter_34.Section_34_2_Polynomial_Time_Verification",
  "CLRSLean.FourthEdition.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility",
  "CLRSLean.FourthEdition.Chapter_34.Section_34_4_NP_Completeness_Proofs",
  "CLRSLean.FourthEdition.Chapter_34.Section_34_5_NP_Complete_Problems",
]
```

Add the titles `34.1. Polynomial Time`, `34.2. Polynomial-Time Verification`,
`34.3. NP-Completeness and Reducibility`, `34.4. NP-Completeness Proofs`, and
`34.5. NP-Complete Problems`.

- [ ] **Step 3: Run the focused green tests and builds**

Run:

```bash
uv run python scripts/test_literate_config.py
uv run python scripts/check_site_consistency.py
lake build CLRSLean.FourthEdition.Chapter_34:literate
git diff --check
```

Expected: all commands exit successfully.

- [ ] **Step 4: Commit the reader structure**

```bash
git add CLRSLean/FourthEdition/Chapter_34.lean \
  CLRSLean/FourthEdition/Chapter_34 \
  literate.toml scripts/test_literate_config.py
git commit -m "fix(site): normalize chapter 34 reader structure"
```

### Task 4: Verify generated desktop and mobile pages

**Files:**
- No repository files; use generated site artifacts and a temporary Playwright script.

- [ ] **Step 1: Render the affected literate modules and prepare a site**

Run the affected module build, update the module map, render the shard that
contains Chapter 34, merge it with the already validated shard outputs, and
prepare a temporary site:

```bash
lake build CLRSLean.FourthEdition.Chapter_34:literate
python3 scripts/prepare_literate_module_map.py \
  .lake/build/literate .lake/build/literate-module-map --prune-orphans
python3 scripts/plan_literate_shards.py \
  .lake/build/literate-module-map .lake/build/literate-shards --shards 4 \
  --digest-input lean-toolchain --digest-input lake-manifest.json \
  --digest-input lakefile.lean --digest-input literate.toml
python3 scripts/render_literate_shards.py \
  --executable .lake/packages/verso/.lake/build/bin/verso-literate-html \
  --module-map .lake/build/literate-module-map --config literate.toml \
  --manifest .lake/build/literate-shards/manifest.json \
  --output .lake/build/literate-shard-output --jobs 4
python3 scripts/merge_literate_shards.py \
  .lake/build/literate-shards/manifest.json \
  .lake/build/literate-html-merged \
  .lake/build/literate-shard-output/shard-0 \
  .lake/build/literate-shard-output/shard-1 \
  .lake/build/literate-shard-output/shard-2 \
  .lake/build/literate-shard-output/shard-3
site_check_dir=$(mktemp -d /tmp/clrs-ch34-reader-XXXXXX)
python3 scripts/prepare_literate_site.py \
  .lake/build/literate-html-merged "$site_check_dir"
```

- [ ] **Step 2: Inspect in system Chrome**

At 1440px and 390px, assert:

```python
assert chapter34_sidebar_children == 5
assert chapter34_content_links == 5
assert document.documentElement.scrollWidth <= window.innerWidth
assert not console_errors
assert not page_errors
```

Take screenshots after scrolling Chapter 34 into view in the sidebar and
visually compare with Chapters 33 and 35.

- [ ] **Step 3: Run the final repository audit**

```bash
uv run python scripts/check_repository.py
git status --short
git diff --check
```

Expected: the repository audit passes and the worktree is clean after the
implementation commit.
