# Chapter 26 Status Truth Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the false Chapter 26 Lemma 26.7 completion claim, publish the
four actual core gaps, add a compiling Chapter 26 interface sentinel, and
reconcile nearby stale Chapters 7/14/17/19/24 status prose.

**Architecture:** Keep `docs/clrs-proof-progress.csv` as the chapter-level
source of truth, regenerate derived dashboard/README content, and let a Lean
interface test protect the declarations that really exist. Natural-language
ledgers describe missing work; they do not substitute for a compiling theorem.

**Tech Stack:** Lean 4, Mathlib, Markdown, CSV, repository Python generators,
Git, and `rg`.

---

## Preconditions and fixed scope

The approved design is
`docs/superpowers/specs/2026-07-31-ch26-truth-and-augmentation-design.md`.
Implementation occurs on the current clean `main`, as requested by the user.

This plan changes status/documentation and adds one interface test. It does not
implement Lemma 26.7, augmentation, BFS, matching, push-relabel, or
relabel-to-front. It does not downgrade the current CSV completion contracts
for Chapters 6 or 14.

The canonical Chapter 26 correction is:

```text
tracked/proved: 9/9 -> 8/8
missing core groups: 3 -> 4
status: partial (unchanged)
```

The four groups are exactly:

```text
Lemma 26.7 monotonic distance with its predecessor/prefix and augmentation-edge bridge;
concrete augmentation with strict value increase and the full Max-Flow Min-Cut converse/equivalence;
an executable BFS/Edmonds-Karp loop with the O(VE^2) theorem;
matching-to-feasible-flow, integral-flow-to-matching, and maximum matching/max-flow value equivalence (Theorem 26.12)
```

## Task 1: Add the honest current Chapter 26 interface

**Files:**

- Create: `Tests/Chapter_26_Interface.lean`

- [ ] **Step 1: Create the interface test with only existing declarations**

Add exactly:

```lean
import CLRSLean.Chapter_26

/-!
# Chapter 26 Interface Test

Verifies the public declarations present in the current partial Chapter 26
formalization. Missing proof targets are added only when their implementation
pass begins.
-/

-- Section 26.1
#check CLRS.Chapter26.FlowNetwork
#check CLRS.Chapter26.Flow
#check CLRS.Chapter26.Flow.value
#check CLRS.Chapter26.Flow.netFlowAcrossCut
#check CLRS.Chapter26.Flow.netFlow_eq_value
#check CLRS.Chapter26.Flow.residualCapacity
#check CLRS.Chapter26.Flow.residualEdge
#check CLRS.Chapter26.Flow.augmentingPathReachable
#check CLRS.Chapter26.Flow.hasAugmentingPath
#check CLRS.Chapter26.Flow.isMaximal
#check CLRS.Chapter26.Flow.value_le_cut_capacity
#check CLRS.Chapter26.Flow.maximal_of_noAugmentingPath

-- Section 26.2: currently present infrastructure
#check CLRS.Chapter26.ResidualPathLength
#check CLRS.Chapter26.IsShortestDist
#check CLRS.Chapter26.isShortestDist_self
#check CLRS.Chapter26.IsShortestDist.unique
#check CLRS.Chapter26.isShortestDist_triangle
#check CLRS.Chapter26.ShortestAugmentingPath

-- Section 26.3
#check CLRS.Chapter26.BipartiteGraph
#check CLRS.Chapter26.Matching
#check CLRS.Chapter26.Matching.size
#check CLRS.Chapter26.capFunc
#check CLRS.Chapter26.toFlowNetwork
#check CLRS.Chapter26.matchingFlowFun
#check CLRS.Chapter26.matchingToFlow_value

-- Theorem 26.6 support
#check CLRS.Chapter26.Flow.eq_cutCapacity_implies_maximal
```

- [ ] **Step 2: Compile the interface**

Run:

```bash
lake env lean -DwarningAsError=true Tests/Chapter_26_Interface.lean
```

Expected: exit 0. `shortest_path_nondec` must not appear in this file until its
proof pass begins.

## Task 2: Correct the machine-readable Chapter 26 row

**Files:**

- Modify: `docs/clrs-proof-progress.csv`
- Regenerate: `CLRSLean/Progress.lean`
- Regenerate: generated progress-table block in `README.md`

- [ ] **Step 1: Replace the Chapter 26 row fields**

Keep `repo_status=partial` and
`represented_sections=26.1;26.2;26.3;26.6`. Set the numeric fields to:

```csv
tracked_key_theorems,proved_tracked_theorems,missing_core_groups
8,8,4
```

Use this completion reading:

```text
The flow foundation residual-distance infrastructure one MFMC direction and a conditional Section 26.3 matching-flow value identity are proved
```

The proved groups must name only declarations present in
`Tests/Chapter_26_Interface.lean`. In particular, replace the old Lemma 26.7
entry with:

```text
residual path length; shortest-path distance with self uniqueness and triangle lemmas; ShortestAugmentingPath infrastructure
```

Use the four fixed missing groups from the preconditions. Add a note saying
that Section 26.2 does not currently contain Lemma 26.7 and that Sections 26.4
and 26.5 are deferred outside the selected milestone.

- [ ] **Step 2: Regenerate the dashboard and README table**

Run:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
python3 scripts/gen_readme_table.py
```

Expected:

```text
progress CSV OK: 35 chapters, 1497 tracked theorem entries, 1497 proved
```

The generated dashboard must report 13 remaining core groups globally and the
Chapter 26 row must show `8` tracked and `4` missing.

- [ ] **Step 3: Verify generated content**

Run:

```bash
rg -n '1497|26\. Maximum Flow|Lemma 26\.7' CLRSLean/Progress.lean README.md
python3 scripts/gen_readme_table.py --check
python3 scripts/check_progress_csv.py
```

Expected: generated files are current; any Lemma 26.7 occurrence is a missing
target, not a proved claim.

## Task 3: Correct the Chapter 26 Lean guides and titles

**Files:**

- Modify: `CLRSLean/Chapter_26.lean`
- Modify: `CLRSLean/Chapter_26/Section_26_2_Edmonds_Karp.lean`
- Modify: `CLRSLean/Chapter_26/Section_26_3_Bipartite_Matching.lean`
- Modify: `CLRSLean/Chapter_26/Section_26_6_MaxFlow_MinCut.lean`
- Modify: `literate.toml`

- [ ] **Step 1: Make the Section 26.2 docstring factual**

Its heading and summary must read:

```markdown
# 26.2. The Edmonds-Karp Algorithm (partial)

This section currently provides residual path-length and shortest-distance
infrastructure for the Edmonds-Karp proof.
```

List only `ResidualPathLength`, `IsShortestDist`,
`isShortestDist_self`, `IsShortestDist.unique`,
`isShortestDist_triangle`, and `ShortestAugmentingPath` as current results.
List predecessor/prefix lemmas, a bridge from concrete augmentation to newly
created reverse residual edges, Lemma 26.7, BFS, and the work theorem as gaps.

- [ ] **Step 2: Correct the Chapter 26 aggregator**

Remove `shortest_path_nondec` from current declarations. Replace the Section
26.2 current-shape paragraph with:

```markdown
Section 26.2 currently defines residual path length, shortest residual
distance, its self/uniqueness/triangle facts, and a shortest augmenting-path
certificate. Lemma 26.7 is a remaining theorem and is not present on `main`.
```

Explain that `matchingToFlow_value` assumes an already feasible `Flow` whose
function equals `matchingFlowFun`. Expand deferred work into the four fixed
groups. State that Sections 26.4 and 26.5 are outside the selected milestone.

- [ ] **Step 3: Correct Section 26.3 and Theorem 26.6 headings**

Section 26.3 must say:

```markdown
This section defines the bipartite reduction data and proves a conditional
value identity. It does not yet construct a feasible flow from a matching or
prove the integral-flow converse and maximum-value equivalence of Theorem
26.12.
```

Change the Section 26.6 file heading from `# 26.1` to:

```markdown
# Theorem 26.6. Max-Flow Min-Cut Theorem (partial)
```

Do not rename the legacy file in this pass.

- [ ] **Step 4: Mark partial page titles**

In `literate.toml`, use:

```toml
title = "26.2. The Edmonds-Karp Algorithm (partial)"
title = "26.3. Maximum Bipartite Matching (partial)"
title = "Theorem 26.6. Max-Flow Min-Cut (partial)"
```

- [ ] **Step 5: Compile Chapter 26 and its interface**

Run:

```bash
lake build CLRSLean.Chapter_26
lake env lean -DwarningAsError=true Tests/Chapter_26_Interface.lean
```

Expected: both exit 0.

## Task 4: Reconcile reader-facing status prose

**Files:**

- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-map.md`
- Modify: `docs/proof-status-board.md`
- Modify: `docs/chapters/chapter-17.md`
- Modify: `docs/chapters/chapter-19.md`
- Modify: `README.md` outside its generated table

- [ ] **Step 1: Replace the Chapter 26 proof-map block**

The Section 26.2 block must list only the six actual declarations from Task 3.
Delete the five phantom proved names:

```text
exists_pred_on_path
suffix_path
shortest_path_prefix
reachable_if_reachable_in_augmented
shortest_path_nondec
```

Record those concepts as the route to Lemma 26.7, not as existing theorems.
The Chapter 26 remaining-work order is concrete augmentation/MFMC, Lemma 26.7,
executable Edmonds--Karp/work, then full matching equivalence. Mention Sections
26.4/26.5 only as deferred outside the current milestone.

- [ ] **Step 2: Fix `CLRSLean/Status.lean`**

Remove Chapters 7 and 24 from `Structured But Partial`; their named bridges
already compile. Keep Chapter 14 in its advertised complete boundary and state
that only the generic `toRB_delete` erasure refinement remains. Describe
Chapter 17 as selected-section complete. Replace the Chapter 26 entry and
highest-value queue with the four fixed groups.

- [ ] **Step 3: Fix the planning board**

Move Chapter 7 out of `Structured But Partial`. Replace the Chapter 26 row with
the factual residual-distance infrastructure and the four fixed gaps. Narrow
the Chapter 14 high-difficulty item to the generic deletion erasure theorem,
not the already implemented deletion pipeline.

- [ ] **Step 4: Fix supplementary guides**

Set `docs/chapters/chapter-17.md` to `selected-section-complete` and describe
allocator/RAM work as optional refinement.

Extend `docs/chapters/chapter-19.md` with the actual Section 19.4 results:
`FTree.Wellformed`, `wellformed_size_ge_fibLowerBound`, logarithmic degree
bounds, `link_wellformed`, and the tight `minTree` witness. Remove the false
claim that the subtree-size induction and true logarithmic degree theorem are
still missing. Keep executable forest operations and amortization as central
gaps.

- [ ] **Step 5: Remove stale README prose**

Replace the statement that Chapter 24 final Dijkstra loop correctness remains
tracked with a statement that `dijkstraInit_invariant` and
`dijkstraLoop_correct` close the represented Dijkstra loop; only mutable/RAM
refinements remain.

## Task 5: Verify and commit the reconciliation

**Files:** all files changed by Tasks 1--4 plus the corrected approved design
and this plan.

- [ ] **Step 1: Prove no phantom completion claim remains**

Run:

```bash
rg -n 'Lemma 26\.7 proved|shortest_path_nondec.*proved|proves the Edmonds-Karp monotonic' \
  README.md CLRSLean docs literate.toml
```

Expected: no output. Occurrences of `shortest_path_nondec` may only describe a
missing target or historical candidate.

- [ ] **Step 2: Run the focused and repository gates**

Run:

```bash
lake build CLRSLean.Chapter_26
lake env lean -DwarningAsError=true Tests/Chapter_26_Interface.lean
python3 scripts/check_progress_csv.py
python3 scripts/gen_readme_table.py --check
python3 scripts/check_repository.py
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_26 Tests/Chapter_26_Interface.lean
git diff --check
```

Expected: all commands exit 0; the unfinished-marker search has no code-level
match (docstring prose must avoid those tokens in the edited Chapter 26 files).

- [ ] **Step 3: Inspect and commit only the reconciliation**

Run:

```bash
git status --short
git diff --stat
git diff -- docs/clrs-proof-progress.csv CLRSLean/Progress.lean README.md
git add \
  docs/superpowers/specs/2026-07-31-ch26-truth-and-augmentation-design.md \
  docs/superpowers/plans/2026-07-31-ch26-status-truth.md \
  Tests/Chapter_26_Interface.lean \
  docs/clrs-proof-progress.csv CLRSLean/Progress.lean README.md \
  CLRSLean/Chapter_26.lean \
  CLRSLean/Chapter_26/Section_26_2_Edmonds_Karp.lean \
  CLRSLean/Chapter_26/Section_26_3_Bipartite_Matching.lean \
  CLRSLean/Chapter_26/Section_26_6_MaxFlow_MinCut.lean \
  CLRSLean/Status.lean docs/proof-map.md docs/proof-status-board.md \
  docs/chapters/chapter-17.md docs/chapters/chapter-19.md literate.toml
git diff --cached --check
git commit -m "docs(progress): reconcile remaining Chapter 26 gaps"
```

Expected: one focused commit containing no new Chapter 26 theorem claim.
