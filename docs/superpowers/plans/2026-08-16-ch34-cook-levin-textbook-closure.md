# Chapter 34 Textbook Cook--Levin Circuitization Implementation Plan

> **For Codex:** REQUIRED SUB-SKILL: Use `superpowers:executing-plans` to implement this plan task by task.

**Goal:** Close and name the textbook circuitization core of Cook--Levin with an explicit circuit map, exact membership equivalence, and a polynomial output-length certificate, while leaving standard NP-hardness visibly dependent on polynomial-time computability of that map.

**Architecture:** Add a small theorem-layer module above the existing verified `cookLevinMap`.  A `PolynomialOutputReduction` records the explicit map, semantic equivalence, and output-length polynomial without pretending that those fields imply `PolyTimeReducible`.  A bridge theorem turns this certificate into `PolyTimeReducible` exactly when a `PolyTimeComputable` proof for the map is supplied.  No custom predicate is named NP-hard or NP-complete.

**Tech Stack:** Lean 4, Mathlib polynomial library, CLRS-Lean TM2 complexity interfaces, Lake.

---

### Task 1: Freeze the public theorem interface with a failing test

**Files:**

- Create: `Tests/Chapter_34_CookLevin_Textbook.lean`

**Step 1: Write the failing interface test**

Import the new `CookLevin.Textbook` module and check the certificate type, the Cook--Levin constructor, its semantic and size projections, and the machine-level bridge.

**Step 2: Run the test and confirm the expected failure**

Run `lake env lean Tests/Chapter_34_CookLevin_Textbook.lean`; the missing module or declarations must fail before implementation.

### Task 2: Implement the honest textbook circuitization layer

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Textbook.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin.lean`

**Step 1: Define the reduction certificate**

Define `PolynomialOutputReduction` with an explicit map, a polynomial length bound, exact source/target membership equivalence, and the length inequality.

**Step 2: Prove the machine-level bridge**

Prove `PolynomialOutputReduction.toPolyTimeReducible`, taking the missing `PolyTimeComputable` proof as an explicit premise.

**Step 3: Package the existing Cook--Levin construction**

Build `cookLevinPolynomialOutputReduction` from `cookLevinMap_mem_generalCircuitSAT_iff` and `cookLevinMap_length_le`, then lift it from `VerifierWitness` to every `PolyTimeVerifiable` language.

**Step 4: Package the universal circuitization statement**

Prove `cookLevin_textbookCircuitization` for every `PolyTimeVerifiable` language.  Do not introduce weaker predicates named NP-hard or NP-complete.

**Step 5: Run the focused test**

Run `lake env lean Tests/Chapter_34_CookLevin_Textbook.lean` and require it to pass.

### Task 3: Integrate the theorem into chapter-facing surfaces

**Files:**

- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_34.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/index.md`
- Modify: `literate.toml`
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/clrs-fourth-edition-map.csv`

**Step 1: Export the new module**

Add it to the Cook--Levin facade and documentation module listings.

**Step 2: Update status claims without overstating the result**

Record the textbook circuitization milestone and keep the concrete map-generating TM2 plus standard `NPHard` / `NPComplete` theorems explicitly open.

**Step 3: Regenerate derived progress artifacts**

Run `python3 scripts/check_progress_csv.py --write-dashboard` and do not hand-edit generated progress modules.

### Task 4: Verify, review, and checkpoint

**Files:**

- Verify all files changed above.

**Step 1: Run focused and public builds**

Run the focused test, `lake build CLRSLean.Chapter_34`, and the repository contract's `lake build CLRSLean`.

**Step 2: Audit theorem assumptions and repository policy**

Run the test's `#print axioms`, the repository placeholder policy, the progress checker, and the site/config checks required by `scripts/check_repository.py`.

**Step 3: Request an independent proof review**

Ask a review agent to inspect the theorem strength, namespace/API surface, and whether documentation distinguishes textbook and machine-level closure.

**Step 4: Commit and push the auditable checkpoint**

Commit only after fresh verification passes, then push `codex/ch34-textbook-closure`.
