# V1 Trust Gate Implementation Plan

> **For agentic workers:** execute this plan inline, one checked step at a time.
> Keep the Lean audit modules small and commit each independently verifiable
> chapter band.

**Goal:** Establish a kernel-checked v1 credibility gate covering one to three
flagship declarations for every canonical CLRS chapter, plus a fresh resolution
of every known MAJOR semantic-audit finding inside the advertised boundary.

**Architecture:** A small Lean metaprogramming module defines
`#assert_axioms`, which fails elaboration when a declaration depends on anything
outside `propext`, `Classical.choice`, and `Quot.sound`.  Independent
`Tests/Trust/Chapter_NN.lean` files import the canonical fourth-edition guide,
pin flagship signatures with `#check` or typed `example`s, invoke the axiom
gate, and include concrete witnesses when the chapter exposes executable
algorithms.  A Python runner verifies that all 35 chapter files exist and
elaborate; CI runs that runner after the normal Lean build.

**Tech Stack:** Lean 4 metaprogramming (`Lean.collectAxioms`), Mathlib command
elaboration and `#guard_msgs`, Python's standard library, Lake, GitHub Actions.

## Acceptance contract

- All 35 canonical fourth-edition chapters have a trust file. Chapter 1 is
  explicitly expository; each theorem-bearing chapter selects one to three
  flagship declarations.
- Every flagship declaration remains reachable through its canonical chapter
  import and has a pinned, CLRS-facing type.
- Its transitive axiom set is a subset of `propext`, `Classical.choice`, and
  `Quot.sound`; `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, and every
  project-local axiom are rejected.
- Each executable flagship band contains at least one small, non-vacuous
  example when such an example is meaningful for the model.
- Every historical MAJOR semantic finding is freshly classified as fixed,
  outside the advertised boundary, or still real. A still-real MAJOR blocks v1
  until the proof is repaired or the public status/scope is downgraded.
- The gate does not claim a line-by-line audit of all 1,609 tracked entries and
  does not reopen pointer/RAM, floating-point, exercise, or chapter-problem
  layers already excluded by `docs/scope.md`.
- This file becomes an immutable audit record after the v1 gate closes. Open
  work remains in GitHub issues rather than in another status ledger.

## File structure

- `CLRSLean/Audit/Axioms.lean`: the reusable Lean command and allowed-axiom
  policy.
- `Tests/Trust/AxiomAudit.lean`: positive and guarded-negative command tests.
- `Tests/Trust/Chapter_01.lean` through `Tests/Trust/Chapter_35.lean`: isolated
  chapter trust surfaces.
- `scripts/check_v1_trust_gate.py`: completeness and narrow-file elaboration
  runner.
- `scripts/test_check_v1_trust_gate.py`: runner unit tests that do not invoke
  Lean.
- `.github/workflows/lean_action_ci.yml`: post-build trust-gate invocation.

## Task 1: Lean axiom assertion command

**Files:**

- Create `Tests/Trust/AxiomAudit.lean`.
- Create `CLRSLean/Audit/Axioms.lean`.

- [x] Add a positive test that imports `CLRSLean.Audit.Axioms` and accepts
  `Nat.add_comm`, `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Run `lake env lean Tests/Trust/AxiomAudit.lean`; confirm RED because the
  audit module or command does not yet exist.
- [x] Implement the minimal command shell so the positive assertions pass.
- [x] Add a `#guard_msgs` negative test for `Lean.ofReduceBool`; confirm RED
  because the command shell fails to emit the expected error.
- [x] Use `Lean.collectAxioms`, filter the fixed allowed set, sort unexpected
  names for deterministic diagnostics, and throw a command elaboration error
  when the result is nonempty.
- [x] Run `lake env lean Tests/Trust/AxiomAudit.lean`; expect exit 0 with the
  guarded negative error consumed by `#guard_msgs`.
- [x] Commit as `feat(audit): add native axiom trust gate`.

## Task 2: Chapter 1--6 pilot

**Files:**

- Create `Tests/Trust/Chapter_01.lean` through
  `Tests/Trust/Chapter_06.lean`.

- [x] Add the six files first with canonical imports and intended flagship
  names; run them and confirm any incorrect names or namespaces fail.
- [x] Pin Chapter 2 sorting correctness and all-input merge-sort asymptotics;
  Chapter 3 the shared-threshold Θ interface and standard-function hierarchy;
  Chapter 4 Strassen/continuous-master/Akra--Bazzi results; Chapter 5 uniform
  randomization and probabilistic-analysis results; and Chapter 6 in-place
  heapsort correctness plus logarithmic/linear/n-log-n cost results.
- [x] Add small executable examples for insertion sort, merge sort, hiring, and
  heapsort without using `native_decide`.
- [x] Run each file independently with `lake env lean` and then run
  `uv run python scripts/check_repository.py`.
- [x] Commit as `test(audit): register chapter 1 through 6 flagships`.

## Task 3: Trust runner and CI contract

**Files:**

- Create `scripts/test_check_v1_trust_gate.py`.
- Create `scripts/check_v1_trust_gate.py`.
- Modify `.github/workflows/lean_action_ci.yml`.

- [x] Write runner unit tests for missing chapter files, an unexpected chapter
  filename, deterministic chapter order, and propagation of Lean failures.
- [x] Run `uv run python scripts/test_check_v1_trust_gate.py`; confirm RED
  because the runner does not yet exist.
- [x] Implement the runner with `--chapters LOW-HIGH` for staged local checks
  and a default exact `1-35` completeness gate.
- [x] Run the runner tests and the `1-6` pilot; expect both to pass.
- [x] Add `python3 scripts/check_v1_trust_gate.py` after
  `leanprover/lean-action` in the Lean CI workflow, but only after all 35 trust
  files exist.
- [x] Commit as `ci(audit): enforce the v1 flagship trust gate`.

## Task 4: Remaining chapter bands

Create and verify chapter files in these independently committable bands:

- [x] Chapters 7--12: randomized quicksort, sorting lower bounds, selection,
  elementary structures, hashing, and BST correctness.
- [x] Chapters 13--18: red-black invariants, augmented trees, dynamic
  programming, greedy optimality, amortized analysis, and B-tree operations.
- [x] Chapters 19--24: disjoint sets, graph algorithms, MST, shortest paths,
  matching, and maximum flow.
- [x] Chapters 25--30: matching refinements, parallel algorithms, online
  algorithms, matrix computations, linear programming, and FFT.
- [x] Chapters 31--35: number theory, string matching, machine learning,
  NP-completeness, and approximation algorithms.

For each band, first add the files and observe failures for incorrect public
names or unexpected axiom dependencies, then repair only the declaration
surface needed by the accepted flagship theorem. Run the band through
`scripts/check_v1_trust_gate.py --chapters LOW-HIGH` and create one commit.

## Task 5: MAJOR semantic-fidelity closure

- [x] Re-run the Chapter 2, 5, and 6 audit claims against current source and
  exact fourth-edition theorem statements.
- [x] Close findings already repaired, with theorem and test evidence.
- [x] For a real finding inside the advertised boundary, add a failing public
  interface test before changing the proof or model.
- [x] Repair the proof through the chapter main-content gate, or downgrade the
  progress row and public status before v1.
- [x] Run the full trust runner, repository checks, changed interface tests,
  `lake build CLRSLean`, and `git diff --check`.
- [x] Freeze this audit record with the verified commit hash and zero
  unexplained MAJOR findings.

The third item required no new failing Lean test: the only live in-bound defect
was a textbook-reference label in documentation, not a theorem statement,
proof, or executable model.  It was reproduced by searching the live source
for `Lemma 5.5`, then repaired as `Lemma 5.4` in the section guide, theorem
documentation, and canonical progress row.  The theorem itself remains pinned
by `Tests/Trust/Chapter_05.lean`.

### Fresh MAJOR closure record (2026-08-26)

The dated semantic-fidelity reports remain unchanged snapshots.  The following
table is the fresh v1 classification against `docs/scope.md` and the current
canonical chapter guides.

| Historical finding | V1 classification | Current evidence |
|---|---|---|
| Chapter 2 M1/M3: line-cost table and exact instruction sum | Outside advertised boundary | `docs/scope.md` excludes line-by-line pseudocode and word-RAM behavior; Chapter 2 advertises comparison bounds, correctness, and recurrence results. |
| Chapter 2 M2/M4: from-scratch MERGE and implementation-derived linear cost | Outside advertised boundary | The canonical §2.3 guide explicitly delegates to verified `List.mergeSort` and records local MERGE as a future strengthening; executable-performance matching is not claimed. |
| Chapter 5 M1: RANDOMIZE-IN-PLACE mislabeled as Lemma 5.5 | Fixed | Every live reference now says Lemma 5.4; `randomizeInPlace_uniform` is axiom-audited in `Tests/Trust/Chapter_05.lean`. |
| Chapter 6 M1: array-level MAX-HEAP-INSERT absent | Outside advertised boundary | The represented functional interface includes proved `heapInsert`; the §6.5 guide explicitly selects array-level maximum, increase-key, extract-max, and delete state theorems rather than every pseudocode operation. |
| Chapter 6 M2: functional increase/delete rebuild the heap | Outside advertised boundary | The functions are documented as a compact mathematical scaffold, and `docs/scope.md` excludes executable-performance equivalence. The selected array-level increase/delete state theorems are now bundled into the native Chapter 6 trust audit. |
| Chapter 6 M3: functional arrays rather than mutation | Outside advertised boundary | Mutation, allocation, and imperative RAM behavior are explicit project-wide exclusions; the §6.4 guide states the functional-array boundary. |

Result: all eight historical MAJOR findings are explained—one fixed and seven
outside the advertised v1 boundary.  There is no still-real MAJOR inside that
boundary.

### Verification record

Verified source commit: `14af3b885b7eb240c9903002812ff8e23ad2568f`
(2026-08-26, Asia/Shanghai).

The following commands completed successfully at that commit:

```text
python3 scripts/check_v1_trust_gate.py
lake env lean Tests/Chapter_05_Interface.lean
lake env lean Tests/Chapter_06_Interface.lean
python3 scripts/check_repository.py
lake build CLRSLean
git diff --check
```

The full build completed all 10,580 jobs.  The native gate elaborated the
command audit and every `Tests/Trust/Chapter_01.lean` through
`Tests/Trust/Chapter_35.lean`; every selected declaration's transitive axiom
set stayed within `propext`, `Classical.choice`, and `Quot.sound`.  The final
semantic closure count is one fixed historical MAJOR, seven findings outside
the explicit v1 boundary, and zero unexplained or still-real MAJOR findings
inside that boundary.

## Failure policy

- Missing or renamed flagship: fail the chapter file; either restore a
  compatible wrapper or deliberately revise the accepted interface.
- Unexpected axiom: fail with the full deterministic name list; do not add it
  to the allowlist merely to make CI green.
- Vacuous statement or model mismatch: treat as a semantic failure even when
  Lean compiles; repair it or downgrade the advertised boundary.
- Expensive chapter: keep it isolated so other chapter trust files still
  elaborate incrementally; never merge all checks into one giant Lean file.
