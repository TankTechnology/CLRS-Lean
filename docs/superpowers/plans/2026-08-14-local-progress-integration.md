# Local Proof Progress Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Audit the remaining local branches and absorb only proof progress that is still absent from `main`, compiler-clean, and compatible with the fourth-edition source layout.

**Architecture:** Keep the integration on an isolated branch based on `main`. Add focused interface tests before each imported proof layer, port the smallest compatible source surface, and record superseded or incomplete branches in a proof audit instead of merging their stale trees. Preserve the current honest Chapter 34 `partial` boundary.

**Tech Stack:** Lean 4, Mathlib, Lake focused builds, Git worktrees, repository Python consistency checks.

---

### Task 1: Lock the three missing interfaces

**Files:**

- Create: `Tests/Chapter_34_GeneralCircuit_VerifierMachine.lean`
- Create: `Tests/ProofPatterns_ExchangeOptimality.lean`
- Create: `Tests/FourthEdition_Chapter_13_WellFormed.lean`

- [x] **Step 1:** Add the existing Ch34 verifier-machine executable and theorem interface test.
- [x] **Step 2:** Add checks and two examples for `ProofPatterns.Optimal` and `optimal_of_exchange`.
- [x] **Step 3:** Add checks for the bundled red-black `WellFormed` invariant and insertion/deletion correctness wrappers.
- [x] **Step 4:** Run each test and confirm it fails because its new import or declaration is absent.

### Task 2: Absorb the concrete GeneralCircuit verifier checkpoint

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/VerifierMachine/*.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit/Encoding.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/GeneralCircuit.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Machine.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Syntax.lean`
- Modify: `Tests/Chapter_34_PolyBuilder_Interface.lean`
- Create: `docs/superpowers/plans/2026-08-14-ch34-verifier-rejection-runtime.md`

- [x] **Step 1:** Apply the source portion of local commit `6942b07` without importing its stale status/progress prose, then import the compiler-clean verifier facade from `GeneralCircuit.lean`.
- [x] **Step 2:** Build the verifier facade.
- [x] **Step 3:** Run the verifier-machine, GeneralCircuit semantic, PolyBuilder, and Cook--Levin interfaces.
- [x] **Step 4:** Search the new theorem-bearing files for unfinished proof markers.

### Task 3: Port the reusable exchange-optimality kernel

**Files:**

- Modify: `CLRSLean/ProofPatterns/Exchange.lean`
- Test: `Tests/ProofPatterns_ExchangeOptimality.lean`

- [x] **Step 1:** Add `Optimal`, `Optimal.of_noWorse`, and `optimal_of_exchange` from local commit `b652ea6`.
- [x] **Step 2:** Run the focused interface test.
- [x] **Step 3:** Do not import the stale legacy Ch16/Ch23 refactors; current native fourth-edition sources already own those algorithms.

### Task 4: Port the red-black bundled invariant only

**Files:**

- Create: `CLRSLean/FourthEdition/Chapter_13/WellFormed.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_13.lean`
- Modify: `literate.toml`
- Test: `Tests/FourthEdition_Chapter_13_WellFormed.lean`

- [x] **Step 1:** Define `WellFormed t := RedBlackShape t ∧ BST t` against the current native §13.3/§13.4 theorems.
- [x] **Step 2:** Prove empty, insertion, deletion, and bundled correctness theorems using the current `bst_insert`, `bst_delete`, membership, and shape results.
- [x] **Step 3:** Build the Chapter 13 guide and run both Chapter 13 interfaces.
- [x] **Step 4:** Avoid copying the old inorder proof file, whose theorem names collide with stronger native theorems.

### Task 5: Record the branch audit and reconcile public boundaries

**Files:**

- Create: `docs/proof-audits/2026-08-14-local-progress-integration.md`
- Modify: `CLRSLean/Chapter_13.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/proof-map.md`

- [x] **Step 1:** Record absorbed, superseded, incomplete, dirty, and abandoned-route branches with exact reasons.
- [x] **Step 2:** Mention the concrete verifier checkpoint without claiming a uniform rejecting-path polynomial bound or GeneralCircuitSAT NP membership.
- [x] **Step 3:** Update the Chapter 13 prose to remove the stale claim that BST insertion/deletion preservation is absent.

### Task 6: Focused final verification

**Files:**

- Verify all files changed above.

- [x] **Step 1:** Build `CLRSLean.Chapter_34...GeneralCircuit.VerifierMachine`, `CLRSLean.Chapter_34`, and `CLRSLean.FourthEdition.Chapter_13`.
- [x] **Step 2:** Run all Ch34 focused tests plus the new exchange and Chapter 13 tests.
- [x] **Step 3:** Run `python3 scripts/check_repository.py` and `git diff --check`.
- [x] **Step 4:** Confirm the root `main` worktree remains clean and no dirty historical worktree was modified.

No full-repository Lean build or website build is part of this integration.
