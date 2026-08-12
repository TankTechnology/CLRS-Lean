# CLRS and TCS Formalization Execution Plan

This document lays out a phased execution plan. The core goal is to first use human researchers and off-the-shelf large-model agents
to advance proofs of the classic CLRS algorithms, and then gradually extend to the CLRS proof map and formalization of TCS papers.

Current phase: Synthesis.

In other words, we already have the Huffman V2 and MST cut-property starting points, but we are not yet at the stage of “formalizing
the whole of CLRS” or “training a dedicated Lean model”. The most important thing right now is to establish a steady execution cadence,
proof assets, and an auditable record of failures.

## 1. Overall principles

The main line is not model training, but building formalized proof assets.

Short- and medium-term priorities:

1. Use humans + off-the-shelf large-model agents to complete proofs of the classic CLRS algorithms;
2. Build the CLRS proof map, gradually covering the important theorems of the major chapters;
3. Once the CLRS assets are stable, pick suitable TCS papers for formalization pilots;
4. Model training is not an early goal for now; only keep data recording and an optional future interface.

This means we will not self-train Qwen-7B early on, and will not treat RL as a prerequisite for advancing CLRS. We will try to use
already-trained large models as much as possible, improving proof efficiency through better theorem interfaces, a proof-pattern catalog, task
decomposition, and a verification workflow.

## 2. Current assets

Core assets already completed or started:

```text
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
docs/clrs-lean-research-plan.md
docs/proof-map.md
docs/huffman-optimality-v2.md
docs/proof-patterns-catalog.md
```

Current representative theorems:

```lean
HuffmanV2.optimum_huffman_freqs
CLRS.MST.safe_edge_of_lightest_crossing
CLRS.MST.mst_exchange_step
```

They represent two important proof patterns respectively:

- Huffman: exchange argument / local tree transformation;
- MST: cut property / safe edge / exchange step.

This is already enough as a starting point for the CLRS formalization roadmap, but not enough to support a strong narrative of “whole-book proofs” or “TCS paper
formalization”. The next step is to expand the sample of algorithms and, in parallel, organize the proof patterns.

## 3. Phase one: core proofs of classic algorithms

Goal: first complete a batch of CLRS algorithms that best represent different proof patterns.

Suggested priority list:

1. Huffman coding;
2. MST/Kruskal;
3. Dijkstra;
4. LCS or edit distance;
5. Bellman-Ford or BFS shortest path;
6. Matrix-chain multiplication or amortized analysis samples.

Each algorithm should produce four things:

- a mathematical specification;
- an algorithm definition or abstract algorithm interface;
- a correctness / optimality theorem;
- a proof-pattern note.

### 3.1 Huffman

Status: a complete V2 proof in a single file already exists.

Short-term strategy:

- Freeze the main proof structure;
- Do not sacrifice readability to minimize line counts;
- Organize the theorem chain, key lemmas, and proof patterns;
- Make Huffman the flagship case study for greedy exchange.

### 3.2 MST/Kruskal

Status: the cut property / safe edge proof core already exists.

Current files:

```text
CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
```

Next steps:

1. Define finite graphs, edge weights, spanning trees, connectivity, or an equivalent spanning-tree spec;
2. Instantiate `CutCertificate` on concrete finite graphs;
3. Prove the graph-theoretic certificate for the cut property;
4. Advance the mathematical-version optimality of Kruskal;
5. Defer the union-find performance implementation for now.

Acceptance criteria:

```lean
theorem kruskal_optimal :
  IsMST (kruskal G)
```

Early on we can prove the mathematical-version Kruskal without requiring a proof of the high-performance disjoint-set-union implementation.

### 3.3 Dijkstra

Proof pattern: loop invariant / settled set / relaxation.

It is suggested to first do the mathematical state version, rather than a priority-queue implementation version.

Core objects:

- nonnegative-weight graph;
- source;
- distance map;
- settled set;
- relaxation invariant;
- shortest-path specification.

Acceptance criteria:

```lean
theorem dijkstra_correct :
  ShortestPathDistances G source (dijkstra G source)
```

Fallback plan:

- If the Dijkstra state machine is too heavy, do Bellman-Ford first;
- If the weighted graph is too heavy, do BFS shortest path first;
- Keep the Dijkstra theorem interface and the invariant drafts.

### 3.4 DP samples

Proof pattern: optimal substructure / recurrence correctness.

LCS or edit distance is suggested as a priority.

Reasons:

- the specification is clear;
- strong connection to the textbook;
- fills in proof patterns beyond greedy / graph.

Acceptance criteria:

```lean
theorem lcs_correct :
  IsLongestCommonSubsequence xs ys (lcs xs ys)
```

If time is short, existing small DP exercises can serve as proof-pattern evidence first, but ideally we eventually complete a
textbook-level DP sample.

## 4. Phase two: CLRS proof map

Goal: expand from “a few classic algorithm proofs” to “the main CLRS proof map”.

This does not require proving the whole book, nor does it promise that every theorem will be solved. The key is to divide the book's main proofs into buckets
with clear statuses.

Suggested status classification:

| Status | Meaning |
|------|------|
| `proved` | a sorry-free Lean theorem already exists in the main library |
| `statement` | the theorem interface is written, but the proof is not complete |
| `partial` | key lemmas or partial proofs exist, but the main theorem is not complete |
| `blocked-mathlib` | stuck on a Mathlib gap or missing foundational library |
| `blocked-design` | stuck on the representation-layer design, e.g. graphs, paths, arrays, probability models |
| `out-of-scope` | not done in the current phase, e.g. complex implementation details or low-yield chapters |

The main build path must remain `sorry-free`. Unfinished theorems should not be mixed into the main library as `axiom`s.

Recommended organization:

```text
docs/proof-map.md
docs/chapters/
docs/status/
CLRSLean/
  Chapter_16/
  Chapter_23/
  Blueprint/
```

Where:

- `CLRSLean/Chapter_*/*` holds only buildable, maintainable formal proofs;
- `CLRSLean/Blueprint/` can later hold theorem statements or exploratory interfaces, but by default does not count as complete;
- Unresolved problems are recorded in docs first, rather than being disguised as complete via unreliable axioms.

The success criterion for phase two is not “prove the whole book”, but rather:

- the major chapters have proof maps;
- every important theorem has a status;
- unresolved items have clear reasons;
- completed theorems pass `lake build`;
- the proof-pattern catalog can explain recurring proof routines.

## 5. Phase three: TCS paper formalization pilot

TCS paper formalization should not be fully expanded too early.

Prerequisites for starting:

- at least three case studies among Huffman, MST, Dijkstra, DP are stable;
- basic proof infrastructure for graphs, paths, weights, optimality, recurrences, etc., exists;
- the proof map shows we are not working on isolated examples;
- the agent workflow can already reliably assist with Lean proofs.

Paper types to prioritize:

- graph algorithm papers adjacent to the CLRS assets;
- papers related to greedy, exchange arguments, cut property;
- dynamic programming or approximation algorithms;
- amortized analysis;
- foundational parts of randomized algorithms.

Not recommended to pick at the start:

- papers depending on heavy background in probability theory;
- papers requiring complex algebra, category, or measure-theoretic foundations;
- modern TCS papers whose definitional apparatus is heavy but which have no obvious reuse of CLRS assets;
- papers requiring proofs of correctness for large-scale engineering-system implementations.

The first goal of phase three is not “formalizing a complete TCS paper”, but doing a narrow pilot:

- pick one core theorem from a paper;
- write out the Lean statement;
- prove the core lemma or give a blocked reason;
- record which CLRS proof infrastructure it reuses;
- assess whether it is worth extending into a full paper formalization project.

## 6. Model and agent strategy

We will not self-train models early on.

Reasons:

- training Qwen-7B or doing RL is only weakly coupled to the current main line of CLRS proofs;
- datasets, reward, environments, compute, and evaluation each require separate engineering investment;
- training when proof assets are insufficient tends to yield models that can only do local tactics;
- using existing strong models can advance the algorithm proofs themselves more quickly.

Current strategy:

1. Use off-the-shelf large-model agents to complete proof tasks that humans can review;
2. Break tasks into theorem statements, lemmas, proof patterns, and verification commands;
3. Record a blocked reason for every failure, rather than keeping only successful proofs;
4. Turn proof attempts into benchmark data usable in the future.

Data that can be recorded:

- theorem statement;
- imports;
- proof state;
- failed attempts;
- final proofs;
- build commands;
- human intervention points;
- proof-pattern labels.

If we train models in the future, the suggested order is:

1. First build an eval benchmark;
2. Then do supervised fine-tuning;
3. Consider RL only at the very end;
4. Use whether the Lean compilation passes as the reward initially, and do not design complex process rewards first.

In other words, model training is a long-term enhancement, not an early dependency.

## 7. Division of labor between humans and agents

Humans are mainly responsible for:

- choosing proof targets;
- judging whether a theorem statement has mathematical meaning;
- deciding the representation-layer design;
- reviewing whether a proof matches the textbook narrative;
- judging whether a blocked reason is genuine.

Agents are mainly responsible for:

- searching for existing lemmas;
- drafting Lean definitions;
- decomposing proof obligations;
- completing partial proofs;
- running `lake env lean` and `lake build`;
- maintaining proof-pattern notes and the proof map.

For complex algorithms, a recommended working loop:

1. Human and agent first agree on the theorem interface;
2. The agent writes minimal definitions and interface checks;
3. The human confirms the statement does not change the goal;
4. The agent proves local lemmas;
5. Run a build after each layer is completed;
6. Update the proof-pattern catalog in sync;
7. When stuck, record a blocked reason rather than forcing in axioms.

## 8. Near-term milestones

### Milestone A: MST core closed loop

Goal:

- Advance from the current `safe_edge_of_lightest_crossing` to mathematical-version Kruskal optimality.

Deliverables:

- finite graph specification;
- spanning tree specification;
- cut exchange certificate;
- Kruskal theorem statement;
- Kruskal optimality proof or an explicit blocked reason.

### Milestone B: Dijkstra theorem interface

Goal:

- Do not rush to prove the full implementation; first freeze the statement and invariants.

Deliverables:

- nonnegative weighted graph;
- path weight;
- shortest distance;
- Dijkstra state;
- settled-set invariant;
- `dijkstra_correct` statement.

### Milestone C: first version of the CLRS proof map

Goal:

- List and classify the important proofs of the major CLRS chapters.

Deliverables:

- `docs/proof-map.md`;
- a status classification table;
- 3-10 candidate theorems per chapter;
- status / priority / blocked reason for each theorem.

### Milestone D: proof-pattern catalog upgrade

Goal:

- Upgrade from Codeforces proof patterns to CLRS proof patterns.

New patterns:

- exchange argument;
- cut property;
- loop invariant;
- relaxation invariant;
- optimal substructure;
- recurrence completeness;
- amortized potential.

## 9. Publication and output paths

Short-term outputs:

- Huffman V2 technical note;
- MST/Kruskal proof note;
- CLRS proof map;
- proof-pattern catalog;
- technical blog or workshop note.

Medium-term outputs:

- formalized CLRS classic algorithm proof artifacts;
- proof-pattern methodology paper;
- Lean proof-agent benchmark;
- ITP/CPP-style paper or artifact paper.

Long-term outputs:

- continued expansion of the main CLRS proofs;
- TCS paper formalization pilots;
- proof-agent datasets and evaluation;
- optional model fine-tuning or RL experiments.

Short-term commitments not recommended:

- fully formalizing the entire CLRS book;
- self-trained models surpassing existing large models;
- formalizing the full set of difficult TCS papers;
- using agents to fully automatically complete complex algorithm proofs.

## 10. Next steps

The most direct next step is to continue with MST.

Suggested execution order:

1. In `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`,
   continue filling in the concrete finite-graph proof of cut exchange;
2. Prove that the current `CutCertificate` can be constructed from a concrete cut exchange;
3. In `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`, continue strengthening
   `kruskal_optimal`: the sorted-order external assumption has already been removed and complete-scan
   spanning has been proved; next, remove the forest-preservation external assumption;
4. If the full Kruskal is too heavy, first complete the mathematical-version safe-edge induction;
5. Keep `docs/proof-map.md` maintained in sync, recording the status of MST, Dijkstra, and DP.

This roadmap keeps early work focused: no need to train a model first, no need to formalize the whole book immediately, but rather step by step
turn CLRS's key proofs into buildable, reusable, publishable Lean artifacts.
