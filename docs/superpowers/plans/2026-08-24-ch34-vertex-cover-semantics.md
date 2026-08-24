# Chapter 34 VERTEX-COVER Semantics Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the typed CLIQUE-to-VERTEX-COVER complement theorem over the existing honest graph-plus-`k` representation and wire this semantic milestone as partial §34.5 progress.

**Architecture:** Reuse `CliqueInstance` directly. Define the at-most-target cover predicate in one module, the deterministic row-major graph complement in a second module, and the two semantic directions plus final `iff` in a third. Keep raw encoding, certificate machines, and reduction machines out of this milestone.

**Tech Stack:** Lean 4.32, Mathlib `Finset`/`List`, CLRS-Lean `CliqueInstance`, focused interface tests, repository status ledgers.

---

### Task 1: Add the failing public semantic interface

**Files:**
- Create: `Tests/Chapter_34_VertexCover_Semantics.lean`
- Test: `Tests/Chapter_34_VertexCover_Semantics.lean`

- [ ] **Step 1: Write the intended interface before source implementation**

Create:

```lean
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementSemantics

#check CLRS.Chapter34.CliqueInstance.IsVertexCover
#check CLRS.Chapter34.CliqueInstance.HasVertexCover
#check CLRS.Chapter34.CliqueInstance.complementForVertexCover
#check CLRS.Chapter34.CliqueInstance.complementForVertexCover_wellFormed
#check CLRS.Chapter34.CliqueInstance.hasClique_iff_complement_hasVertexCover
```

- [ ] **Step 2: Run the test and observe the expected RED failure**

Run:

```bash
lake env lean Tests/Chapter_34_VertexCover_Semantics.lean
```

Expected: FAIL because the imported module does not exist.

### Task 2: Define typed VERTEX-COVER semantics

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover/Instance.lean`
- Test: `Tests/Chapter_34_VertexCover_Semantics.lean`

- [ ] **Step 1: Add problem-facing representation aliases**

Import general CLIQUE encoding and define:

```lean
abbrev VertexCoverInstance := CliqueInstance
abbrev VertexCoverSym := CliqueSym
abbrev encodeVertexCoverInstance := encodeCliqueInstance
abbrev decodeVertexCoverInstance := decodeCliqueInstance
abbrev encodeVertexCoverCertificate := encodeCliqueCertificate
abbrev decodeVertexCoverCertificate := decodeCliqueCertificate
```

- [ ] **Step 2: Define the finite-set cover truth source**

Inside `namespace CliqueInstance`, add:

```lean
def IsVertexCover (I : CliqueInstance) (vertices : Finset Nat) : Prop :=
  (∀ v ∈ vertices, v < I.vertexCount) ∧
    ∀ e ∈ I.edges, e.1 ∈ vertices ∨ e.2 ∈ vertices

def HasVertexCover (I : CliqueInstance) : Prop :=
  ∃ vertices : Finset Nat,
    vertices.card ≤ I.targetSize ∧ I.IsVertexCover vertices
```

Add direct projection lemmas for bounds and edge coverage only if the semantic
proof uses them repeatedly.

- [ ] **Step 3: Compile the new source module**

Run:

```bash
lake build +CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Instance
```

Expected: PASS.  The public interface test remains RED because the complement
module is still absent.

### Task 3: Define the deterministic normalized complement

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover/Complement.lean`
- Test: `Tests/Chapter_34_VertexCover_Semantics.lean`

- [ ] **Step 1: Define deterministic pair enumeration**

Use row-major `List.range` enumeration:

```lean
def normalizedPairRow (n u : Nat) : List (Nat × Nat) :=
  (List.range (n - u - 1)).map fun offset => (u, u + offset + 1)

def normalizedPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (normalizedPairRow n)
```

- [ ] **Step 2: Prove the exact pair membership theorem**

Prove:

```lean
theorem mem_normalizedPairs_iff {n u v : Nat} :
    (u, v) ∈ normalizedPairs n ↔ u < v ∧ v < n
```

First prove the corresponding row membership lemma.  Isolate all `Nat`
subtraction arithmetic in a short `omega` block rather than mixing it into the
later graph proof.

- [ ] **Step 3: Define and characterize complement edges**

```lean
def complementEdges (I : CliqueInstance) : List (Nat × Nat) :=
  (normalizedPairs I.vertexCount).filter fun edge => edge ∉ I.edges

theorem mem_complementEdges_iff {I : CliqueInstance} {u v : Nat} :
    (u, v) ∈ complementEdges I ↔
      u < v ∧ v < I.vertexCount ∧ (u, v) ∉ I.edges
```

- [ ] **Step 4: Define the reduction instance and well-formedness theorem**

```lean
def complementForVertexCover (I : CliqueInstance) : CliqueInstance where
  vertexCount := I.vertexCount
  targetSize := I.vertexCount - I.targetSize
  edges := complementEdges I

theorem complementForVertexCover_wellFormed
    {I : CliqueInstance} (hI : I.WellFormed) :
    I.complementForVertexCover.WellFormed
```

The target-bound conclusion uses `Nat.sub_le`; edge normalization and range use
`mem_complementEdges_iff`.

- [ ] **Step 5: Compile the complement module**

Run:

```bash
lake build +CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement
```

Expected: PASS.

### Task 4: Prove clique-to-cover soundness

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover/ComplementSoundness.lean`
- Test: `Tests/Chapter_34_VertexCover_Semantics.lean`

- [ ] **Step 1: Prove the in-range complement cardinality helper**

For `vertices ⊆ Finset.range n`, expose:

```lean
theorem card_range_sdiff_of_subset
    {n : Nat} {vertices : Finset Nat}
    (hvertices : vertices ⊆ Finset.range n) :
    (Finset.range n \ vertices).card = n - vertices.card
```

Use `Finset.card_sdiff_of_subset` and `Finset.card_range`.

- [ ] **Step 2: Prove soundness**

```lean
theorem hasVertexCover_complement_of_hasClique
    {I : CliqueInstance} (hI : I.WellFormed) (hclique : I.HasClique) :
    I.complementForVertexCover.HasVertexCover
```

Given clique `S`, use `Finset.range I.vertexCount \ S`.  Show its cardinality
is exactly `vertexCount - targetSize`.  For a complement edge `(u,v)`, if
neither endpoint lies in the cover then both lie in `S`; clique adjacency and
`adj_iff_of_lt` contradict source-edge nonmembership.

- [ ] **Step 3: Compile soundness**

Run:

```bash
lake build +CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementSoundness
```

Expected: PASS.

### Task 5: Prove cover-to-clique completeness and final `iff`

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover/ComplementCompleteness.lean`
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover/ComplementSemantics.lean`
- Test: `Tests/Chapter_34_VertexCover_Semantics.lean`

- [ ] **Step 1: Prove the independent-set size inequality**

For a cover `C` with `C.card ≤ n - k`, `k ≤ n`, and `C ⊆ range n`, prove:

```lean
k ≤ (Finset.range n \ C).card
```

Rewrite with `Finset.card_sdiff_of_subset`; keep the remaining natural-number
subtraction fact in one `omega` block.

- [ ] **Step 2: Select an exact-size candidate**

Apply:

```lean
Finset.exists_subset_card_eq
```

to obtain `S ⊆ Finset.range n \ C` with `S.card = k`.

- [ ] **Step 3: Prove candidate adjacency**

For distinct `u,v ∈ S`, split on `u < v` or `v < u`.  If the normalized pair
were absent from the source edge list, `mem_complementEdges_iff` would make it a
target complement edge.  The cover condition would put one endpoint in `C`,
contradicting membership in the set difference.  Use `adj_comm` for the reversed
orientation.

- [ ] **Step 4: Prove completeness and final theorem**

```lean
theorem hasClique_of_hasVertexCover_complement
    {I : CliqueInstance} (hI : I.WellFormed)
    (hcover : I.complementForVertexCover.HasVertexCover) :
    I.HasClique

theorem hasClique_iff_complement_hasVertexCover
    (I : CliqueInstance) (hI : I.WellFormed) :
    I.HasClique ↔ I.complementForVertexCover.HasVertexCover
```

`ComplementSemantics.lean` should be a thin assembly module importing the two
directions and exporting the final `iff`.

- [ ] **Step 5: Run the public interface test**

Run:

```bash
lake env lean Tests/Chapter_34_VertexCover_Semantics.lean
```

Expected: PASS.

- [ ] **Step 6: Audit headline axioms and unfinished markers**

Add temporary `#print axioms` commands to the focused interface test or use a
small audit file for:

```text
CliqueInstance.complementForVertexCover_wellFormed
CliqueInstance.hasClique_iff_complement_hasVertexCover
```

Expected: only standard Lean/Mathlib foundations and no `sorryAx`.  Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' \
  CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover \
  Tests/Chapter_34_VertexCover_Semantics.lean
```

Expected: no proof placeholders.

- [ ] **Step 7: Commit the typed semantic checkpoint**

```bash
git add \
  CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover \
  Tests/Chapter_34_VertexCover_Semantics.lean
git commit -m "proof(ch34): prove clique vertex-cover complement semantics"
```

### Task 6: Wire the partial §34.5 semantic milestone honestly

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover.lean`
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_34.lean`
- Modify: `literate.toml`
- Modify: `docs/clrs-fourth-edition-map.csv`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/proof-map.md`
- Modify: `docs/proof-status-board.md`
- Modify: `CLRSLean/Status.lean`
- Modify: `docs/index.md`
- Regenerate: `CLRSLean/Progress.lean`

- [ ] **Step 1: Add focused aggregators and Chapter import**

The aggregators import `ComplementSemantics` and document the exact open
boundary: raw language, concrete reduction, verifier, and NP-completeness.

- [ ] **Step 2: Register source navigation**

Add all new modules to `literate.toml` with explicit human titles and include
the new source paths in `docs/index.md`.

- [ ] **Step 3: Update status ledgers**

Promote §34.5 from `not-started` to `partial`.  Add the typed complement theorem
as one tracked Chapter 34 theorem, changing Chapter 34 from 37/37 to 38/38 while
retaining one edition gap unit until the selected §34.5 chain is complete.

State explicitly that VERTEX-COVER is only `semantic-only`; no raw decision
language or NP-completeness theorem is claimed yet.

- [ ] **Step 4: Regenerate the progress dashboard**

Run:

```bash
python3 scripts/check_progress_csv.py --write-dashboard
```

- [ ] **Step 5: Run milestone verification**

Run:

```bash
lake env lean Tests/Chapter_34_VertexCover_Semantics.lean
lake build CLRSLean.Chapter_34
python3 scripts/check_repository.py
git diff --check
```

Expected: all commands PASS.

- [ ] **Step 6: Commit wiring and status**

```bash
git add CLRSLean/Chapter_34.lean CLRSLean/FourthEdition/Chapter_34.lean \
  CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems.lean \
  CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/VertexCover.lean \
  CLRSLean/Status.lean CLRSLean/Progress.lean literate.toml docs
git commit -m "docs(ch34): record vertex-cover semantic milestone"
```

### Task 7: Record the next closure boundary

**Files:**
- Create: `docs/proof-audits/2026-08-24-ch34-vertex-cover-semantics.md`

- [ ] **Step 1: Record exact accepted evidence**

The audit names typed definitions, complement construction, soundness,
completeness, final `iff`, focused test, Chapter build, placeholder scan, and
axiom results.

- [ ] **Step 2: Record the next missing bridge**

The next ledger row is the honest raw `GeneralVERTEXCOVER` language and total
`cliqueToVertexCoverMap` membership theorem.  Do not describe the semantic
checkpoint as `PolyTimeReducible` or NP-complete.

- [ ] **Step 3: Run fresh verification and commit**

Run:

```bash
lake env lean Tests/Chapter_34_VertexCover_Semantics.lean
lake build CLRSLean.Chapter_34
python3 scripts/check_repository.py
git diff --check
```

Then commit:

```bash
git add docs/proof-audits/2026-08-24-ch34-vertex-cover-semantics.md
git commit -m "docs(ch34): audit vertex-cover complement semantics"
```
