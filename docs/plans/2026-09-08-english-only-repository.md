# English-Only Repository Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert repository-controlled text and reachable Git history to English and prevent new non-English repository text from being introduced.

**Architecture:** A focused Python policy checker scans tracked files, branch names, and reachable commit messages. A one-time migration translates current artifacts, rewrites known commit messages deterministically, and updates GitHub with recoverable, lease-protected operations.

**Tech Stack:** Python standard library, Git, GitHub CLI, Lean/Lake, Verso site tooling

---

### Task 1: Add the language policy checker

**Files:**
- Create: `scripts/check_english_only.py`
- Create: `scripts/test_check_english_only.py`
- Modify: `scripts/check_repository.py`
- Modify: `docs/workflows/chapter-workflow.md`

- [ ] Write unit tests that require actionable failures for CJK text, commit messages, and branch names while accepting English text and binary files.
- [ ] Run `uv run python scripts/test_check_english_only.py` and confirm the tests fail because the checker does not exist.
- [ ] Implement the scanner and command-line entry point with explicit repository and ref inputs.
- [ ] Run `uv run python scripts/test_check_english_only.py` and confirm every test passes.
- [ ] Add the checker to `CHECK_COMMANDS` in `scripts/check_repository.py` and document the English-only rule in the chapter workflow.

### Task 2: Translate the current repository tree

**Files:**
- Modify: every tracked text file reported by `scripts/check_english_only.py`

- [ ] Translate the semantic-fidelity skill and its reference material without changing its audit protocol.
- [ ] Translate dated chapter audits, repair records, release notes, research notes, and archived project reports while preserving links, identifiers, theorem names, and code.
- [ ] Run `uv run python scripts/check_english_only.py --skip-history` and confirm that no tracked text or branch-name violation remains.
- [ ] Run `uv run python scripts/check_repository.py` and fix any broken links or generated-file inconsistencies.
- [ ] Commit the migration with an English commit message.

### Task 3: Translate GitHub issue metadata

**External records:**
- Modify: GitHub issues whose title or body contains Chinese

- [ ] Export the original issue JSON to the recovery directory.
- [ ] Translate each affected title and body while preserving issue numbers, links, checklists, and closure state.
- [ ] Update issues through `gh issue edit`.
- [ ] Fetch all issues again and confirm no title or body contains CJK ideographs.

### Task 4: Rewrite reachable commit history

**External records:**
- Create: repository-external backup bundle and mapping files
- Rewrite: all local branches and all maintained remote branches that reach a mapped commit

- [ ] Record every remote branch tip and create a complete Git bundle before rewriting.
- [ ] Apply an exact message map for the 32 known commits; abort if a mapped source message is missing or an unexpected CJK commit message remains.
- [ ] Export the old-to-new commit map and verify tree identity for every rewritten commit.
- [ ] Run the English-only checker against all rewritten refs.
- [ ] Force-push each remote branch with an explicit old-tip lease and then fetch to verify the remote tips.

### Task 5: Verify the rewritten project

**Files:**
- No additional file changes expected

- [ ] Run `uv run python scripts/check_repository.py`.
- [ ] Run `lake build CLRSLean`.
- [ ] Run `python3 scripts/check_v1_trust_gate.py`.
- [ ] Run the Pages-equivalent literate build and site preparation commands used by `.github/workflows/pages.yml`.
- [ ] Confirm the worktree is clean, `main` matches `origin/main`, and no reachable commit message, branch name, tracked file, or GitHub issue contains CJK ideographs.
