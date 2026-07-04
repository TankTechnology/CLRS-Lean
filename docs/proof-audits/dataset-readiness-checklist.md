# Dataset Readiness Checklist

This document prepares CLRS-Lean to be used as a benchmark dataset for
agent-based Lean 4 theorem proving.

A *task* in the dataset is: given a theorem statement plus its surrounding
definitions and imports, produce a proof that Lean accepts.

---

## 1. Dataset Unit Definition

Each task should contain:

| Field | Description |
|---|---|
| `task_id` | Stable identifier, e.g. `ch13.inTree_insert_iff` |
| `chapter` | CLRS chapter number |
| `section` | CLRS section number |
| `difficulty` | `easy` / `medium` / `hard` / `extreme` |
| `theorem_name` | Fully qualified Lean name |
| `statement` | The theorem statement as Lean source |
| `imports` | Exact imports needed to elaborate the statement |
| `context_defs` | Supporting definitions/lemmas that must be visible |
| `gold_proof` | The checked-in proof body |
| `dependencies` | List of `task_id`s whose proofs are reused here |
| `tags` | E.g. `induction`, `simp`, `automation`, `graph`, `sorting` |

---

## 2. Required Artifacts

- [ ] A task extractor script that parses `.lean` files and emits one task per public theorem.
- [ ] A gold-proof corpus with all `sorry`/`admit` removed.
- [ ] A per-task prompt template for agents.
- [ ] A hidden-test stub for each task: the same theorem with `:= by` erased and a placeholder.
- [ ] A `metadata.jsonl` with chapter/section/difficulty/dependencies/tags.
- [ ] A dependency graph file so the benchmark can enforce prerequisite order.

---

## 3. Quality Criteria

### 3.1 Compilable

- [ ] Every task can be elaborated in a clean Lean environment with the given imports.
- [ ] The gold proof closes the goal and produces no warnings.
- [ ] The hidden-test stub fails before a proof is supplied and passes after.

### 3.2 No Information Leakage

- [ ] Agent prompts do not include the gold proof.
- [ ] Agent prompts do not include tactic-state traces from the gold proof.
- [ ] Hold-out test set is separated from training set by chapter or section, not randomly.

### 3.3 Difficulty Annotation

| Difficulty | Signal |
|---|---|
| `easy` | One-step `simp`/`omega`/`linarith` proof, < 10 lines. |
| `medium` | Induction or case analysis, 10–40 lines, few helper lemmas. |
| `hard` | Requires multiple helper lemmas, complex invariant, or non-trivial automation. |
| `extreme` | Randomized analysis, large state-machine invariants, pointer semantics, or open research-level gaps. |

- [ ] Each theorem is tagged with one difficulty.
- [ ] Difficulty is reviewed by a human after a first-pass annotation.

### 3.4 Determinism

- [ ] A fixed Lean toolchain (`lean-toolchain`) is pinned.
- [ ] `lake-manifest.json` is committed and version-locked.
- [ ] Re-running the extractor on the same commit produces identical task IDs and content.

---

## 4. Evaluation Metrics

Primary metrics:

- **Pass rate**: percentage of tasks whose proof is accepted by `lake build`.
- **Partial credit** (optional): whether the agent produced a proof outline with all `sorry` removed.
- **Token/time budget**: average tokens and wall-clock per task.
- **Proof length**: lines of generated proof compared to gold proof.
- **Dependency violations**: number of tasks solved without solving their declared prerequisites.

Secondary metrics:

- **Style drift**: excessive use of `all_goals`/`try`/unexplained `simp`.
- **Axiom leakage**: `#print axioms` check on generated proofs.

---

## 5. Infrastructure Needed

| Tool | Purpose |
|---|---|
| `scripts/extract_tasks.py` | Parse Lean files into task JSON and hidden-test stubs. |
| `scripts/run_agent_harness.py` | Feed prompts to an agent and collect proof attempts. |
| `scripts/evaluate_proofs.py` | Replace stub bodies, run `lake build`, report pass/fail. |
| `scripts/equivalence_check.py` | Verify that a generated proof proves the same statement as the gold proof (Lean handles this via elaboration). |

---

## 6. Anti-Cheating Checklist

- [ ] Gold proofs are stored in a separate directory or branch, not included in agent prompts.
- [ ] The hidden-test stub uses the exact same theorem statement as the gold task.
- [ ] Evaluation is done in a fresh environment without tactic-state caches.
- [ ] Agents are not allowed to read `docs/proof-audits/` or other documents containing proof strategy hints unless the benchmark intentionally allows it.

---

## 7. First Concrete Step

The lowest-friction pilot is to extract one chapter (e.g., Chapter 2) into the
full pipeline:

1. Run `scripts/extract_tasks.py` on `CLRSLean/Chapter_02`.
2. Produce `metadata.jsonl` and hidden-test stubs.
3. Run one baseline agent (e.g., this same codebase without gold proofs) against the stubs.
4. Report pass rate and iterate on prompt/template design.

Once Chapter 2 is stable, scale to Chapter 13 (red-black trees) and then the rest.
