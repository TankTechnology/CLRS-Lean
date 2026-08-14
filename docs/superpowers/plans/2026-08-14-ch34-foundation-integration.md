# Chapter 34 Foundation Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extract the compiler-clean Chapter 34 semantic Cook--Levin foundation from `origin/codex/ch15-fifo-trace-coupling` onto current `origin/main` without regressing later chapter, migration, or status work.

**Architecture:** Treat remote commit `3de47a674b342f4a00129586cb7a083adfd14780` as the source snapshot and exclude local-only commit `6942b07fab48f217ddd66c09cc00b2e0bd508b11`. Restore only the Chapter 34 source tree, Chapter 34 interface tests, the fourth-edition guide, and the focused proof audit. Reconcile shared ledgers and navigation by Chapter 34 fragment so current main remains authoritative for every other chapter.

**Tech Stack:** Lean 4, Lake, Python repository checks, Git worktrees, Verso navigation metadata.

---

### Task 1: Establish the integration baseline

**Files:**
- Verify: `scripts/check_repository.py`
- Verify: `CLRSLean/Chapter_34.lean`

- [x] **Step 1: Create the isolated integration branch**

  Run:

  ```bash
  git worktree add .worktrees/ch34-foundation-integration \
    -b codex/ch34-foundation-integration origin/main
  ```

  Expected: the worktree starts at `93af1d956c7c6e0bd790ee3d3db722b9b1a61c46` and tracks `origin/main`.

- [x] **Step 2: Verify repository metadata at the baseline**

  Run:

  ```bash
  python3 scripts/check_repository.py
  ```

  Expected: `Repository checks passed.`

- [x] **Step 3: Verify the current-main Chapter 34 build baseline**

  Run:

  ```bash
  lake build CLRSLean.Chapter_34
  ```

  Expected: exit status 0 after the new worktree initializes its dependencies.

### Task 2: Extract the remote Chapter 34 proof snapshot

**Files:**
- Modify: `CLRSLean/Chapter_34.lean`
- Modify/Create: `CLRSLean/Chapter_34/**/*.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_34.lean`
- Modify/Create: `Tests/Chapter_34*.lean`
- Create: `docs/proof-audits/2026-08-13-ch34-cook-levin-core-closure.md`

- [x] **Step 1: Restore the exact remote source tree and public guide**

  Run:

  ```bash
  git restore --source=3de47a674b342f4a00129586cb7a083adfd14780 -- \
    CLRSLean/Chapter_34.lean \
    CLRSLean/Chapter_34 \
    CLRSLean/FourthEdition/Chapter_34.lean
  ```

  Expected: GeneralCircuit, PolyBuilder, and CookLevin modules appear; no `GeneralCircuit/VerifierMachine` module appears.

- [x] **Step 2: Restore all Chapter 34 regression interfaces from the remote snapshot**

  Run:

  ```bash
  git restore --source=3de47a674b342f4a00129586cb7a083adfd14780 -- \
    ':(glob)Tests/Chapter_34*.lean'
  ```

  Expected: 27 Chapter 34 interface files are present, including `Chapter_34_CookLevin_Interface.lean` and `Chapter_34_GeneralCircuit_Verification.lean` but excluding `Chapter_34_GeneralCircuit_VerifierMachine.lean`.

- [x] **Step 3: Restore the concise proof-closure audit**

  Run:

  ```bash
  git restore --source=3de47a674b342f4a00129586cb7a083adfd14780 -- \
    docs/proof-audits/2026-08-13-ch34-cook-levin-core-closure.md
  ```

  Expected: the audit records theorem evidence and the remaining generator/checker boundary.

- [x] **Step 4: Check the extraction boundary**

  Run:

  ```bash
  test ! -e CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine.lean
  test ! -e Tests/Chapter_34_GeneralCircuit_VerifierMachine.lean
  git diff --name-only | rg -v '^(CLRSLean/Chapter_34|CLRSLean/FourthEdition/Chapter_34\.lean|Tests/Chapter_34|docs/proof-audits/2026-08-13-ch34-cook-levin-core-closure\.md|docs/superpowers/plans/2026-08-14-ch34-foundation-integration\.md)$'
  ```

  Expected: both absence checks pass and the final command prints nothing.

### Task 3: Reconcile the public ledger and navigation

**Files:**
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `CLRSLean/Progress.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-map.md`
- Modify: `docs/proof-status-board.md`
- Modify: `docs/clrs-fourth-edition-map.csv`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `CLRSLean.lean`
- Modify: `README.md`

- [x] **Step 1: Update only the Chapter 34 ledger records**

  Set Chapter 34 to `partial`, with 20 tracked and 20 proved theorem groups. Record the exact remaining boundary: concrete polynomial-time TM2 implementations of the Cook--Levin generator and GeneralCircuit certificate checker, final `GeneralCircuitSAT` NP wrappers, general graph-plus-`k` CLIQUE, and Section 34.5.

- [x] **Step 2: Regenerate the public progress dashboard and README table**

  Run:

  ```bash
  python3 scripts/check_progress_csv.py --write-dashboard
  python3 scripts/gen_readme_table.py
  ```

  Expected: only the generated Chapter 34 counts/status change in `CLRSLean/Progress.lean` and the README table; all later-main chapter rows remain unchanged.

- [x] **Step 3: Reconcile reader-facing prose**

  Update the Chapter 34 paragraphs in `CLRSLean/Status.lean`, `docs/proof-map.md`, and `docs/proof-status-board.md` from the remote theorem snapshot. Remove the stale root-page claim that Chapters 34--35 are unrepresented. Do not claim `GeneralCircuitSAT` NP-complete.

- [x] **Step 4: Register the new public modules**

  Add the GeneralCircuit, PolyBuilder, and CookLevin module hierarchy to the Chapter 34 `order_children` block and add a title for every registered module in `literate.toml`. Add the same reader-facing source list to `docs/index.md`.

- [x] **Step 5: Update only edition-map row 34.4**

  Mark §34.4 `partial` and list the exact proved reductions, semantic circuit result, polynomial size bounds, function-level map, and finite-certificate semantics. Preserve all non-Chapter-34 edition-map rows byte-for-byte.

### Task 4: Verify the integrated proof surface

**Files:**
- Verify: `CLRSLean/Chapter_34/**/*.lean`
- Verify: `Tests/Chapter_34*.lean`
- Verify: repository metadata files

- [x] **Step 1: Reject unfinished proof markers**

  Run:

  ```bash
  rg -n '^\s*(sorry|admit|axiom|proof_wanted)\b' CLRSLean/Chapter_34 Tests/Chapter_34*.lean
  ```

  Expected: no matches.

- [x] **Step 2: Compile the two public headline interfaces**

  Run:

  ```bash
  lake env lean Tests/Chapter_34_CookLevin_Interface.lean
  lake env lean Tests/Chapter_34_GeneralCircuit_Verification.lean
  ```

  Expected: both exit with status 0 and print the intended theorem signatures.

- [x] **Step 3: Compile every Chapter 34 interface**

  Run:

  ```bash
  for test_file in Tests/Chapter_34*.lean; do
    lake env lean "$test_file"
  done
  ```

  Expected: all 27 files exit with status 0.

- [x] **Step 4: Build the Chapter 34 aggregator**

  Run:

  ```bash
  lake build CLRSLean.Chapter_34
  ```

  Expected: exit status 0.

- [x] **Step 5: Run repository and whitespace checks**

  Run:

  ```bash
  python3 scripts/check_repository.py
  git diff --check
  ```

  Expected: repository checks pass and `git diff --check` prints nothing.

### Task 5: Review and publish the clean integration branch

**Files:**
- Review: every changed file

- [x] **Step 1: Confirm the scope and provenance**

  Run:

  ```bash
  git diff --stat origin/main...HEAD
  git diff --name-only origin/main...HEAD | rg -v '^(CLRSLean/Chapter_34(\.lean|/.*)|CLRSLean/FourthEdition/Chapter_34\.lean|Tests/Chapter_34.*\.lean|CLRSLean/Progress\.lean|CLRSLean/Status\.lean|CLRSLean\.lean|README\.md|docs/clrs-fourth-edition-map\.csv|docs/clrs-proof-progress\.csv|docs/index\.md|docs/proof-map\.md|docs/proof-status-board\.md|docs/proof-audits/2026-08-13-ch34-cook-levin-core-closure\.md|docs/superpowers/plans/2026-08-14-ch34-foundation-integration\.md|literate\.toml|scripts/test_check_progress_csv\.py)$'
  ```

  Expected: the scope check prints nothing.

- [x] **Step 2: Commit the clean integration**

  Run:

  ```bash
  git add CLRSLean CLRSLean.lean Tests README.md docs literate.toml \
    scripts/test_check_progress_csv.py
  git commit -m "feat(ch34): integrate Cook-Levin semantic foundation"
  ```

  Expected: one reviewable integration commit based on current main.

- [ ] **Step 3: Push and open a ready pull request**

  Run:

  ```bash
  git push -u origin codex/ch34-foundation-integration
  gh pr create --base main --head codex/ch34-foundation-integration \
    --title "feat(ch34): integrate Cook-Levin semantic foundation" \
    --body-file /tmp/ch34-foundation-pr-body.md
  ```

  Expected: a ready PR that states the verified results, remaining gaps, and focused verification evidence.
