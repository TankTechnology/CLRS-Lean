# Complexity Reduction Closure Skill Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add and validate a repository-local skill that identifies and closes the exact missing proof layer in Lean polynomial-time reductions, then use its contract to produce the VERTEX-COVER kickoff ledger for CLRS §34.5.

**Architecture:** Keep the trigger and orchestration loop in a concise `SKILL.md`, move stage-specific proof contracts into six focused references, and store three repository-grounded evaluation prompts plus inline dry runs under `evals/`. A deterministic Python test validates the package shape, routing links, closure statuses, and evaluation schema. The existing chapter-scale skill receives only a short routing note.

**Tech Stack:** Markdown Codex skills, JSON evaluation fixtures, Python `unittest`, CLRS-Lean repository policy checks, Git checkpoint commits.

---

### Task 1: Add a failing package-contract test

**Files:**
- Create: `scripts/test_complexity_reduction_closure_skill.py`
- Test: `scripts/test_complexity_reduction_closure_skill.py`

- [ ] **Step 1: Write the failing structural test**

Create a `unittest.TestCase` that resolves
`.codex/skills/complexity-reduction-closure`, requires `SKILL.md`, the six
approved reference files, `evals/evals.json`, and three dry-run Markdown files.
It must also assert that:

```python
required_statuses = {
    "semantic-only",
    "size-certified",
    "machine-certified",
    "reduction-complete",
    "np-complete",
}
required_eval_ids = {
    "clique-to-vertex-cover",
    "ham-cycle-gadget",
    "subset-sum-numeric",
}
```

The test parses `evals/evals.json`, checks exactly those IDs, requires a
nonempty prompt and expected output for every case, verifies every Markdown
link of the form `references/<name>.md` points to an existing file, and checks
that each dry run contains the headings `Closure ledger`, `First missing
bridge`, and `Narrow verification`.

- [ ] **Step 2: Run the test and observe the expected failure**

Run:

```bash
python3 scripts/test_complexity_reduction_closure_skill.py
```

Expected: FAIL because
`.codex/skills/complexity-reduction-closure/SKILL.md` does not exist.

### Task 2: Implement the core skill and stage references

**Files:**
- Create: `.codex/skills/complexity-reduction-closure/SKILL.md`
- Create: `.codex/skills/complexity-reduction-closure/references/reduction-contract.md`
- Create: `.codex/skills/complexity-reduction-closure/references/np-membership-contract.md`
- Create: `.codex/skills/complexity-reduction-closure/references/semantic-to-machine.md`
- Create: `.codex/skills/complexity-reduction-closure/references/encoding-and-malformed-input.md`
- Create: `.codex/skills/complexity-reduction-closure/references/polynomial-bound-composition.md`
- Create: `.codex/skills/complexity-reduction-closure/references/ch34-case-study.md`
- Test: `scripts/test_complexity_reduction_closure_skill.py`

- [ ] **Step 1: Write `SKILL.md` frontmatter and trigger description**

Use this frontmatter:

```yaml
---
name: complexity-reduction-closure
description: Use for Lean formalization of polynomial-time many-one reductions, NP membership, NP-hardness, or NP-completeness, especially when bridging typed semantics to serialized raw languages, certificate checkers, concrete machines, and polynomial runtime bounds. Trigger for SAT, CLIQUE, VERTEX-COVER, HAM-CYCLE, TSP decision, SUBSET-SUM, PolyTimeReducible, ClassNP, NPHard, or when a reduction is semantically proved but not yet honestly closed.
---
```

- [ ] **Step 2: Add the orchestration loop**

The core skill must require this order:

```text
inspect local interfaces
  -> emit closure ledger
  -> select exactly one first missing bridge
  -> stabilize typed semantic iff
  -> totalize raw encoding
  -> prove raw membership iff
  -> prove serialized size
  -> compute the exact same map with a fixed machine
  -> lift runtime to original input length
  -> package reduction / NP membership / hardness
  -> verify public surface and status honesty
```

It must route to the six references only when their proof stage applies and
must explicitly forbid equating polynomial output length with polynomial-time
computability.

- [ ] **Step 3: Write the six focused references**

Use these responsibilities:

- `reduction-contract.md`: closure ledger template, status vocabulary, exact
  `iff` truth-source rule, and reduction packaging checklist.
- `np-membership-contract.md`: checker semantics, certificate encoding/length,
  fixed-machine runtime, and `PolyTimeVerifiable` packaging.
- `semantic-to-machine.md`: phase contracts, exact-map identity, script-cost
  caveat, small-file decomposition, and composition order.
- `encoding-and-malformed-input.md`: round trips, well-formedness separation,
  canonical no-instances, total raw maps, and all-input language equivalence.
- `polynomial-bound-composition.md`: structural count versus serialized length,
  unary versus binary numeric bounds, and local-to-global runtime lifting.
- `ch34-case-study.md`: concise evidence from Cook--Levin,
  GeneralCircuitSAT-to-SAT, and general CLIQUE, including rejected shortcuts.

- [ ] **Step 4: Run the structural test**

Run:

```bash
python3 scripts/test_complexity_reduction_closure_skill.py
```

Expected: still FAIL because evaluations and dry runs do not yet exist, while
the core skill and references satisfy their own checks.

### Task 3: Add evaluation prompts and inline dry runs

**Files:**
- Create: `.codex/skills/complexity-reduction-closure/evals/evals.json`
- Create: `.codex/skills/complexity-reduction-closure/evals/clique-to-vertex-cover-dry-run.md`
- Create: `.codex/skills/complexity-reduction-closure/evals/ham-cycle-gadget-dry-run.md`
- Create: `.codex/skills/complexity-reduction-closure/evals/subset-sum-numeric-dry-run.md`
- Test: `scripts/test_complexity_reduction_closure_skill.py`

- [ ] **Step 1: Record the three approved evaluations**

Use this JSON shape for every entry:

```json
{
  "id": "stable-kebab-case-id",
  "prompt": "A realistic repository-grounded Lean task",
  "expected_output": "The required proof-layer diagnosis and first bridge",
  "files": []
}
```

The VERTEX-COVER prompt must exercise graph reuse, complement semantics,
parameter subtraction, raw totality, certificate verification, and a concrete
reduction.  The HAM-CYCLE prompt must put local gadget semantics before machine
work.  The SUBSET-SUM prompt must distinguish value bounds from bit-length and
arithmetic runtime.

- [ ] **Step 2: Produce three dry runs using the draft skill**

Each dry run uses this common report surface:

```markdown
## Closure ledger

| Layer | Current evidence | Status |
| --- | --- | --- |

## First missing bridge

One exact theorem or representation decision.

## File decomposition

Focused modules in dependency order.

## Narrow verification

One command that verifies the first milestone.
```

The VERTEX-COVER dry run becomes the kickoff ledger for the subsequent §34.5
design; the other two demonstrate that the skill generalizes beyond one graph
complement reduction.

- [ ] **Step 3: Run the package test and skill-creator validator**

Run:

```bash
python3 scripts/test_complexity_reduction_closure_skill.py
python3 /home/ubuntu/.codex/skills/skill-creator/scripts/quick_validate.py \
  .codex/skills/complexity-reduction-closure
```

Expected: both commands PASS.

- [ ] **Step 4: Commit the validated skill package**

```bash
git add .codex/skills/complexity-reduction-closure \
  scripts/test_complexity_reduction_closure_skill.py
git commit -m "feat(skills): add complexity reduction closure workflow"
```

### Task 4: Route chapter-scale complexity work to the new skill

**Files:**
- Modify: `.codex/skills/clrs-chapter-formalization/SKILL.md`
- Modify: `scripts/test_complexity_reduction_closure_skill.py`
- Test: `scripts/test_complexity_reduction_closure_skill.py`

- [ ] **Step 1: Strengthen the test before changing the existing skill**

Add an assertion that `.codex/skills/clrs-chapter-formalization/SKILL.md`
contains the exact skill name `complexity-reduction-closure` and routes
polynomial-time reductions/NP-completeness work to it.

- [ ] **Step 2: Run the test and observe the routing failure**

Run:

```bash
python3 scripts/test_complexity_reduction_closure_skill.py
```

Expected: FAIL because the existing chapter skill does not yet name the new
skill.

- [ ] **Step 3: Add one concise Chapter Pattern routing paragraph**

Add a small paragraph, not the full reduction contract.  It should state that
complexity-reduction chapters use `complexity-reduction-closure` to distinguish
semantic equivalence, output size, exact polynomial-time computation, NP
membership, and hardness packaging.

- [ ] **Step 4: Rerun the package test**

Run:

```bash
python3 scripts/test_complexity_reduction_closure_skill.py
```

Expected: PASS.

- [ ] **Step 5: Commit the routing integration**

```bash
git add .codex/skills/clrs-chapter-formalization/SKILL.md \
  scripts/test_complexity_reduction_closure_skill.py
git commit -m "docs(skills): route complexity reductions to closure skill"
```

### Task 5: Verify the skill and hand its VERTEX-COVER ledger to §34.5

**Files:**
- Create: `docs/proof-audits/2026-08-24-complexity-reduction-skill.md`
- Read: `.codex/skills/complexity-reduction-closure/evals/clique-to-vertex-cover-dry-run.md`
- Test: repository verification commands below

- [ ] **Step 1: Re-read the approved design and check every acceptance item**

Record evidence for trigger scope, reference routing, status distinctions,
three evaluations, VERTEX-COVER dry run, repository checks, and absence of
global configuration changes.

- [ ] **Step 2: Run fresh final verification**

Run:

```bash
python3 scripts/test_complexity_reduction_closure_skill.py
python3 /home/ubuntu/.codex/skills/skill-creator/scripts/quick_validate.py \
  .codex/skills/complexity-reduction-closure
python3 scripts/check_repository.py
git diff --check origin/main...HEAD
git status --short --branch
```

Expected: all tests and checks pass; the worktree contains only the audit file
before its final commit.

- [ ] **Step 3: Write and commit the acceptance audit**

The audit records exact commands, commit IDs, evaluation coverage, and the
VERTEX-COVER first missing bridge.  Then run `python3 scripts/check_repository.py`
and `git diff --check` once more before committing:

```bash
git add docs/proof-audits/2026-08-24-complexity-reduction-skill.md
git commit -m "docs(skills): audit complexity reduction closure skill"
```

- [ ] **Step 4: Begin the separate VERTEX-COVER design cycle**

Use the accepted skill and its dry-run ledger to inspect exact existing
`CliqueInstance`, `CliqueSym`, verifier, and PolyBuilder interfaces.  Produce a
focused VERTEX-COVER design specification before adding Lean source.  That
specification must decide whether the target reuses `CliqueSym` with a distinct
language or introduces an explicit `VertexCoverSym`, and must justify the
choice in terms of unambiguous public encodings and machine reuse.
