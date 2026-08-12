# Research Plan for Formalizing CLRS Algorithm Proofs in Lean

This document lays out a research plan spanning roughly three months. The goal is
not to formalize all of CLRS, but rather, around a representative set of algorithm
proofs, to establish reusable Lean proof patterns and produce a publishable
artifact and a methodological narrative.

Current phase: Synthesis.

That is, we already have some usable material, especially the Huffman V2
optimality proof, but we cannot yet move directly into the submission-packaging
phase. The most important next step is to pin down the research questions, the
algorithm samples, the acceptance criteria, and the failure/downgrade paths.

## 1. Core assessment

Proving only a batch of basic greedy toy problems is not enough to support a
strong submission.

A more reasonable goal is:

> Prove the correctness of a set of nontrivial CLRS-style algorithms, and distill
> from them reusable Lean proof patterns.

The value of this direction lies not in "a few more algorithm theorems in Lean,"
but in answering:

- Whether the proof recipes in classical algorithm textbooks can be organized
  into stable formalization patterns;
- Which proof patterns are reusable, and where Lean's data structures and
  invariants force new design;
- What transferable engineering and proof experience there is for the future
  large-scale formalization of algorithm textbooks.

## 2. Current baseline

Flagship sample already in hand:

```text
CfProofs/Greedy/HuffmanV2/Optimality.lean
```

Current features of Huffman V2:

- Isolated from the legacy `CfProofs.Greedy.Huffman.*` paths;
- Contains the complete Huffman optimality proof in one file;
- The main proof line is split-leaf / exchange;
- Currently about 2971 lines;
- Exposes a final theorem at the frequency-table level:

```lean
HuffmanV2.optimum_huffman_freqs
```

Huffman V2 can serve as the first core case study in the paper, because it
contains a genuine optimality exchange argument, rather than merely verifying the
return value of a program.

## 3. Candidate research questions

The questions below are stratified by altitude. In the end, we recommend not
leading with all of them at once; instead, choose one headline question and pair
it with 1-2 supporting questions.

### Q1. Can CLRS-style algorithm proofs be organized into reusable proof patterns in Lean?

Altitude: structural question.

This question is suitable as the main question. It sits above any single
algorithm, yet can be answered with 3-5 algorithm samples.

The main risk is: if every algorithm is a one-off proof, lacking shared interfaces
and pattern summaries, this question degenerates into a case-study collection.

### Q2. Can the exchange / cut / local transformation proofs of greedy algorithms be unified?

Altitude: mechanism question.

This question is suitable as a supporting question. Huffman uses split-leaf /
exchange, MST uses the cut property, and activity selection or interval problems
use an exchange argument. They share a common local-replacement flavor, but
whether they can share the same abstraction in Lean must be tested by actually
formalizing them.

### Q3. In Lean, should loop-invariant algorithms be proved by program execution, or by mathematical state relations?

Altitude: mechanism question.

This question is suitable for covering algorithms such as Dijkstra, BFS, and
Bellman-Ford. The key is not code execution itself, but how state invariants such
as the settled set, the distance map, and the relaxation invariant are expressed.

### Q4. Can DP optimal-substructure proofs form a stable template?

Altitude: mechanism question.

This question is suitable for extension via LCS, edit distance, matrix-chain
multiplication, or the existing CutRibbon/Boredom experience. The difficulty in DP
is usually bridging the recurrence, reachability, and optimal lower bound with the
array/list implementation.

### Q5. Which stages suit single-file proofs and modular proofs respectively?

Altitude: engineering question.

Huffman V2 shows that single-file proofs are easier to read and better for
showcasing a submission artifact; but when advancing on multiple algorithms, fully
single-file proofs reduce reusability. This question fits in the lessons-learned
summary, not as a main question.

### Q6. When formalizing textbook algorithms, is the real bottleneck the mathematical proof, or the representation-layer design?

Altitude: structural question.

This question is valuable but easily becomes too broad. It can serve as a
cross-cutting finding in the discussion section: much of the difficulty lies not
in the algorithmic idea itself, but in the choice of Lean representations for
objects such as frequency tables, graphs, paths, forests, and invariants.

### Q7. Can a small proof-pattern catalog lower the cost of subsequent algorithm proofs?

Altitude: methodology question.

This question can become an artifact contribution: each case study outputs a
theorem interface, a proof skeleton, the key lemma types, and reuse records.

### Q8. Where are the gaps in current Mathlib support for textbook algorithm proofs?

Altitude: ecosystem question.

This question is suitable as a supplementary contribution. Do not make it the main
question, because within three months it is hard to systematically evaluate all of
Mathlib; we can only infer local gaps from samples.

## 4. Self-review conclusions

The most suitable main question:

> Can CLRS-style correctness proofs of nontrivial algorithms be organized in Lean
> into reusable proof patterns, rather than one-off formalizations isolated from
> one another?

Supporting questions:

1. How should exchange / cut / local transformation in greedy optimality be
   formalized?
2. How should loop invariants and DP optimal substructure be turned into a stable
   theorem interface?

Questions we do not recommend leading with:

- "Formalize all of CLRS": unrealistic in three months and easy to appear
  over-committed;
- "Break through hard mathematical problems": disconnected from the current repo
  assets, too risky in the short term;
- "Prove many basic algorithms": high in quantity but shallow in depth, easily
  viewed as teaching exercises at submission time;
- "Do only Huffman": good depth, but a single sample, hard to support a
  methodological contribution.

## 5. Target algorithm portfolio

We recommend completing, or nearly completing, the following four kinds of core
samples within three months.

### A. Huffman coding

Proof pattern: exchange argument / local tree transformation.

Current status: V2 is already the core baseline.

Goals:

- Keep the single-file proof readable;
- Continue to compress local redundancy without sacrificing the main-line
  structure;
- Write a proof roadmap and a LOC / lemma distribution record for the paper.

### B. MST: Kruskal or Prim

Proof pattern: cut property / safe edge.

Recommend prioritizing Kruskal.

Rationale:

- Strong CLRS representativeness;
- The cut property and Huffman's exchange can form a contrast;
- The union-find implementation can first be abstracted into a relation /
  component spec, without having to prove a high-performance union-find from the
  start.

Minimum acceptance:

```lean
theorem kruskal_optimal :
  IsMST (kruskal G)
```

One can first prove a mathematical version of Kruskal, then gradually connect it
to an executable implementation.

### C. Dijkstra shortest paths

Proof pattern: loop invariant / settled set / relaxation.

Rationale:

- More substantial than the basic greedy toy problems;
- Like MST, it is a graph algorithm, but with a different proof structure;
- Can showcase the expressive power of state invariants in Lean.

Minimum acceptance:

```lean
theorem dijkstra_correct :
  ShortestPathDistances G source (dijkstra G source)
```

One can start with nonnegative weights, finitely many nodes, and a simple map
representation, avoiding getting stuck in a heap implementation from the start.

### D. One DP algorithm

Proof pattern: optimal substructure / recurrence completeness.

Candidates:

- LCS;
- edit distance;
- matrix-chain multiplication.

Recommend prioritizing LCS or edit distance, because the specification is more
intuitive and connects well with the textbook narrative.

Minimum acceptance:

```lean
theorem lcs_correct :
  IsLongestCommonSubsequence xs ys (lcs xs ys)
```

If time is short, the existing CutRibbon/Boredom can be used as a pilot
experiment, and then a more textbook-like DP sample can be completed.

## 6. What we will not do

To keep the paper's goals clear, we recommend explicitly stating the following
non-goals:

- Do not attempt to formalize all of CLRS within three months;
- Do not make high-performance data-structure implementation the first goal;
- Do not treat the number of Codeforces toy problems as a primary contribution;
- Do not pursue executable-first for every algorithm;
- Do not commit to proving complexity bounds unless the main correctness proofs
  are already stable.

Complexity proofs can be a bonus, but should not block the main line.

## 7. Three-month milestones

### Weeks 1-2: Research questions and interface freeze

Deliverables:

- Pin down the headline question in this document;
- Set up a `docs/clrs-proof-patterns/` or equivalent directory;
- Write a one-page theorem interface draft for each of Huffman, MST, Dijkstra, and
  DP;
- Record Huffman V2's theorem chain, LOC, and core lemma classification.

Acceptance criteria:

- Every target algorithm has an explicit spec;
- Every spec can clearly state what is proved and what is not proved;
- "Prove many algorithms" is no longer used as a goal description.

### Weeks 3-5: MST/Kruskal

Deliverables:

- Mathematical definitions of graphs, edge weights, spanning trees, cuts, and safe
  edges;
- The cut property;
- An optimality proof for the mathematical version of Kruskal;
- Record which lemmas can be reused in other greedy proofs.

Acceptance criteria:

- `lake build` passes;
- There is a public theorem expressing MST optimality;
- The documentation can explain the commonalities and differences between the
  Kruskal and Huffman exchange proofs.

### Weeks 6-8: Dijkstra

Deliverables:

- A specification for nonnegatively weighted graphs and distances;
- The relaxation invariant;
- The settled-nodes invariant;
- The main Dijkstra correctness theorem.

Acceptance criteria:

- The algorithm state, the mathematical shortest-path definition, and the loop
  invariants can be clearly distinguished;
- No dependence on a specific high-performance priority-queue implementation;
- The invariant proof pattern is documented.

### Weeks 9-10: DP sample

Deliverables:

- A specification for LCS or edit distance;
- Recurrence correctness;
- An optimality theorem for the algorithm's return value;
- A comparison against the existing DP toy-problem proofs.

Acceptance criteria:

- There is a textbook-level DP theorem;
- A DP optimal-substructure pattern is added to the proof pattern catalog.

### Week 11: Cross-cutting consolidation

Deliverables:

- A proof-pattern taxonomy;
- A theorem interface table for each algorithm;
- Records of LOC, lemma counts, reuse points, and failed attempts;
- A record of Mathlib / Lean representation-layer gaps.

Acceptance criteria:

- Can answer the reviewer question "these are not four isolated proofs but one
  methodology";
- Can answer the reviewer question "why are these algorithms representative enough
  of CLRS proof patterns".

### Week 12: First draft of submission materials

Deliverables:

- Paper outline;
- Artifact README;
- Case study table;
- Reproducibility commands;
- The intro's problem statement and contribution list.

Acceptance criteria:

- Form an ITP/CPP-style submission skeleton;
- If the results are stronger, also consider CAV-style framing;
- If the number of algorithms is insufficient, downgrading to a workshop / artifact
  / technical report still holds.

## 8. File structure suggestions

In the short term, the CLRS direction has already been split from `CfProofs` into
the standalone `CLRS-Lean` repository. Huffman V2 has become the formal chapter
file for Section 16.3:

```text
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
```

When adding new CLRS directions, organize them by CLRS chapter and section rather
than by algorithmic topic:

```text
CLRSLean/
  Chapter_16/
    Section_16_3_Huffman_Codes.lean
  Chapter_23/
    Section_23_1_Growing_Minimum_Spanning_Trees.lean
    Section_23_2_Kruskal_And_Prim.lean
  Blueprint/
```

Note: do not over-abstract `Patterns/` from the start. The safer approach is to
first complete two case studies, then extract the recurring structures.

## 9. Shape of the paper's contribution

Recommended contribution list:

1. A Lean 4 artifact covering Huffman, MST, Dijkstra, and one DP algorithm;
2. A CLRS proof-pattern taxonomy;
3. Theorem interfaces and proof skeletons for each kind of proof pattern;
4. Lessons learned on Lean/Mathlib representation-layer choices;
5. A reproducible experiment table: LOC, key lemmas, reuse points, and build
   commands for each algorithm.

Do not frame the contribution as:

- "We proved many algorithms";
- "Lean can prove algorithm correctness";
- "Formalizing CLRS is feasible".

These claims are too broad or too weak. A better statement is:

> We identify and mechanize reusable proof patterns for textbook algorithm
> correctness in Lean, using representative CLRS algorithms as case studies.

## 10. Risks and downgrade paths

### Risk 1: The Dijkstra proof drags on too long

Downgrade:

- Keep the specification and invariant drafts for Dijkstra;
- Replace it with a mathematical version of BFS shortest path or Bellman-Ford;
- In the paper, present Dijkstra as an ongoing extension rather than a core result.

### Risk 2: MST gets bogged down in the graph representation and union-find implementation

Downgrade:

- First prove the mathematical version of Kruskal;
- Treat union-find only as a future executable refinement;
- Focus the main contribution on the cut property and safe edges.

### Risk 3: The DP sample cannot be completed in time

Downgrade:

- Use the existing CutRibbon/Boredom as evidence for a DP pattern;
- Keep the LCS spec and partial lemmas;
- Do not put DP first among the core contributions.

### Risk 4: The proof-pattern abstraction is not unified enough

Downgrade:

- Do not force a generic framework;
- Reframe the contribution as "design study + reusable interfaces";
- Use tables to show which parts are reusable and which are not.

## 11. Acceptance criteria

After three months, a strong version should satisfy:

- Huffman V2 stays complete, buildable, and explainable;
- MST and Dijkstra each have at least one main correctness theorem;
- DP has at least one textbook-level sample or clear substitute evidence;
- Every algorithm has a documented theorem interface;
- There is a proof-pattern catalog rather than just a pile of Lean files;
- `lake build` is the basic reproducibility entry point for the artifact.

An acceptable downgraded version should satisfy:

- Huffman V2 + MST complete;
- At least one of Dijkstra or DP complete;
- The other has a spec, a partial proof, and clear risk records;
- The paper's goal is downgraded to an ITP/CPP workshop, artifact paper, or
  technical report.

## 12. Next steps

Three things are recommended immediately:

1. Freeze Huffman V2, and stop breaking the readability of the main line for the
   sake of extreme line-count compression;
2. Create a new isolated CLRS directory, and first write the MST/Kruskal
   specification and theorem statements;
3. Maintain a `proof-patterns` table in sync, recording for each completed lemma
   whether it belongs to exchange, cut, loop invariant, or optimal substructure.

For the first genuinely new proof, we recommend starting with Kruskal's cut
property. Like Huffman, it has the flavor of greedy optimality, but with a
different proof shape, and it can most quickly move the project from "one strong
Huffman proof" toward "a set of CLRS proof patterns".
