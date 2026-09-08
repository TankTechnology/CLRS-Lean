# Fourth-Edition Chapter Review · 2026-09-08

This report compares the current Lean definitions, public theorems, selected
proof dependencies, and chapter-completion claims. The review found issues that
prevented the previous whole-book completion wording from remaining accurate.
A successful build, absence of proof placeholders, and acceptable axiom
dependencies do not by themselves establish that an algorithm definition is
correct, its premises are satisfiable, or its runtime theorem measures the
actual execution.

## Baseline and limits

- Scope: fourth-edition Chapters 1–35 and 137 mapped section entries; Chapter 1
  is expository.
- Baseline commit: `c8b074e961fb204ab50b9ea123b864260dafde38`, plus the website
  and documentation cleanup already present in this task.
- Lean snapshot: 2,164 files. SHA-256 over sorted `path + NUL + contents + NUL`:
  `e9d903b1080a3b0da09f24210a021bf96a5aae6332fb6fdee96f43cc0023a022`.
- `check_book_coverage.py --report` passed. The ledger's 1,689/1,689 entries and
  34 `main-proof-complete` chapters were claims under review, not conclusions.
- The audit itself did not modify Lean definitions, proofs, or chapter status.

**NOT-INDEPENDENTLY-VERIFIED:** the audit did not compare every claim against the
textbook text independently. The [publisher's fourth-edition page](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/)
confirms edition metadata only. Deterministic findings below follow from source
definitions, inconsistent interfaces, and kernel-checked counterexamples. A
statement that no issue was found applies only to the inspected public surface
and selected proof dependencies.

## Reproduced blocking findings

### Chapter 27: the caching algorithm interface is uninhabited on its target domain

`Algorithm.step_size` bounds every cache by `k`, while `step_hit` preserves the
cache on a hit; neither premise restricts the initial cache to a legal state. For
`Page = Fin (k + 1)` and `C = univ`, the interface derives `k + 1 ≤ k`. Competitive
and lower-bound theorems over this interface therefore had empty premises. The
repair needed a legal-state domain, preservation, sufficient history for LRU-like
algorithms, and a nonempty implementation.

### Chapter 13: pointer rotations disconnect reachable keys

`rotateLeftP` and `rotateRightP` changed local nodes without updating
`RBStore.root` or the former parent's child link. A two-node example changed the
reachable keys from `[1, 2]` to `[1]`. `StoreRepr` also allowed a sentinel address
to represent a nonempty tree. The functional red-black-tree proofs remained
valid, but the pointer refinement required root/parent rewiring and stronger
sentinel, ownership, and parent-child invariants.

### Chapter 14: recursive LCS execution did not support the tabular runtime claim

Public `lcsLength` evaluated both recursive branches on unequal inputs without a
table or memo cache, while the fourth-edition guide described it as a tabulated
Theta(mn) algorithm. `lcsTableCells` counted a separate size expression. Equal-
length disjoint inputs of length 5 produced 503 recursive calls versus 36 table
cells; length 8 produced 25,739 versus 81. These executions motivated an actual
tabulated implementation with refinement and attached cost.

### Chapter 17: interval insertion lost distinct intervals with equal low endpoints

Inserting `(0, 10)` into a valid one-node `(0, 1)` tree left the tree unchanged;
a later query for `(5, 5)` returned `none`. The comparator used only the low
endpoint, so distinct intervals became the same key without a uniqueness premise.
The static search theorem remained valid, but update membership, BST preservation,
and search-after-update needed a total interval order or explicit overwrite rule.

All four examples are in the [reproducible Lean appendix](counterexamples.md).

## Chapter verdicts

Each distribution is ordered MATCH / MINOR / MAJOR / CRITICAL / UNCERTAIN.

| Ch. | Topic | Distribution | Review conclusion | Evidence |
| ---: | --- | --- | --- | --- |
| 1 | The Role of Algorithms | 1/1/0/0/0 | Expository; correct legacy navigation and failure-API conventions. | [detail](chapters-01-13.md) |
| 2 | Getting Started | 2/0/0/0/1 | MERGE was present; the insertion-sort worst-case count bridge needed proof. | [detail](chapters-01-13.md) |
| 3 | Characterizing Running Times | 3/0/0/0/0 | No core defect found in the inspected asymptotic interfaces. | [detail](chapters-01-13.md) |
| 4 | Divide-and-Conquer | 3/0/0/0/4 | Matrix correctness held; costs and recurrence theorems needed public execution bridges and precise scope. | [detail](chapters-01-13.md) |
| 5 | Probabilistic Analysis and Randomized Algorithms | 4/0/0/0/0 | No core defect found; existing longest-streak results were missing from the guide. | [detail](chapters-01-13.md) |
| 6 | Heapsort | 5/0/0/0/0 | Core heap results held; documentation overstated the heapify repair region. | [detail](chapters-01-13.md) |
| 7 | Quicksort | 4/0/0/0/0 | No core defect found in the inspected execution and expectation bridge. | [detail](chapters-01-13.md) |
| 8 | Sorting in Linear Time | 0/0/3/0/1 | Distribution executions repeatedly scanned input and the decision-tree lower bound used unreachable depth. | [detail](chapters-01-13.md) |
| 9 | Medians and Order Statistics | 3/0/0/0/0 | No core defect found within the stated partition-work model. | [detail](chapters-01-13.md) |
| 10 | Elementary Data Structures | 1/2/0/0/0 | Array legality, list query contracts, and fourth-edition numbering needed clarification. | [detail](chapters-01-13.md) |
| 11 | Hash Tables | 4/0/1/0/0 | Perfect-hash injectivity quantified over too large a domain; construction cost was detached. | [detail](chapters-01-13.md) |
| 12 | Binary Search Trees | 2/1/0/0/0 | Set semantics and the supplementary expected-height scope needed explicit documentation. | [detail](chapters-01-13.md) |
| 13 | Red-Black Trees | 1/0/3/0/0 | Pointer rotations and representation invariants were unsound; update cost was independent. | [detail](chapters-01-13.md) |
| 14 | Dynamic Programming | 0/1/4/0/0 | LCS, matrix-chain, and optimal-BST evaluators did not match tabular execution claims. | [detail](chapters-14-27.md) |
| 15 | Greedy Algorithms | 3/1/0/0/0 | Core proofs held; arbitrary-capacity offline caching excluded an empty initial cache. | [detail](chapters-14-27.md) |
| 16 | Amortized Analysis | 3/1/0/0/0 | MULTIPOP had a single-call bound rather than a mixed-trace amortized theorem. | [detail](chapters-14-27.md) |
| 17 | Augmenting Data Structures | 0/0/2/0/1 | Equal-low interval insertion, update/search composition, and actual maintenance costs needed repair. | [detail](chapters-14-27.md) |
| 18 | B-Trees | 2/1/0/0/0 | Correctness held; page-access wording exceeded the recursive-descent counter. | [detail](chapters-14-27.md) |
| 19 | Data Structures for Disjoint Sets | 3/1/0/0/0 | Forest results held; weighted-list union lacked a constructed total rewrite count. | [detail](chapters-14-27.md) |
| 20 | Elementary Graph Algorithms | 4/1/0/0/0 | BFS/DFS held; topological sort and SCC omitted finish-time sorting from their costs. | [detail](chapters-14-27.md) |
| 21 | Minimum Spanning Trees | 1/0/1/0/0 | Prim execution did not yet construct the final spanning-tree certificate or attach queue costs. | [detail](chapters-14-27.md) |
| 22 | Single-Source Shortest Paths | 2/1/1/0/1 | Tight predecessor edges did not guarantee a source-rooted tree; negative-cycle scope needed clarification. | [detail](chapters-14-27.md) |
| 23 | All-Pairs Shortest Paths | 0/0/3/0/0 | Negative-cycle completeness and actual construction costs were overstated. | [detail](chapters-14-27.md) |
| 24 | Maximum Flow | 3/0/2/0/0 | Edmonds-Karp used a dense augmentation bound; relabel-to-front lacked a complete scheduler. | [detail](chapters-14-27.md) |
| 25 | Bipartite Matching | 1/2/0/0/0 | Core flow, stable-matching, and Hungarian chains held; one direction note and stale gaps needed correction. | [detail](chapters-14-27.md) |
| 26 | Parallel Algorithms | 2/1/0/0/0 | Results held within their stated dimension and scheduler models. | [detail](chapters-14-27.md) |
| 27 | Online Algorithms | 0/1/1/1/0 | The caching interface was uninhabited; deterministic lower-bound quantifiers were too weak. | [detail](chapters-14-27.md) |
| 28 | Matrix Operations | 3/0/0/0/0 | LUP execution and cost held; legacy asymptotic wording required alignment. | [detail](chapters-28-35.md) |
| 29 | Linear Programming | 3/0/0/0/0 | Public contracts held; the guide overstated the imported solver's executable scope. | [detail](chapters-28-35.md) |
| 30 | Polynomials and the FFT | 2/1/0/0/0 | Correctness held; exact counts needed root-preparation and sharing assumptions. | [detail](chapters-28-35.md) |
| 31 | Number-Theoretic Algorithms | 6/1/1/0/0 | Miller-Rabin result and count came from different computations; repeated-trial probability lacked composition. | [detail](chapters-28-35.md) |
| 32 | String Matching | 2/1/2/0/0 | DFA table size was used as construction work and Rabin-Karp omitted power-update cost. | [detail](chapters-28-35.md) |
| 33 | Machine-Learning Algorithms | 3/0/0/0/0 | No core defect found within the one-step and finite-step claims. | [detail](chapters-28-35.md) |
| 34 | NP-Completeness | 5/0/0/0/0 | Sampled semantic, serialization, machine-time, NP-membership, and hardness chains held. | [detail](chapters-28-35.md) |
| 35 | Approximation Algorithms | 2/3/0/0/0 | Existing guarantees depended on caller-supplied MST/LP witnesses and needed composed public outputs. | [detail](chapters-28-35.md) |

The totals are **83 / 21 / 24 / 1 / 8 = 137**. This is a section-level
classification rather than an error count. A section can retain valid
mathematical theorems while receiving a MAJOR verdict for its execution or cost
claim. Ten online-supplement entries with `chapter_no=0` are outside this
denominator. See [sections.csv](sections.csv) for section IDs and source modules.

## Cross-review

| Range | MATCH rows challenged independently | Final sections | Record |
| --- | ---: | ---: | --- |
| Chapters 1–13 | 43 | 50 | [review and corrections](cross-review-01-13.md) |
| Chapters 14–27 | 35 | 52 | [review and corrections](cross-review-14-27.md) |
| Chapters 28–35 | 38 | 35 | [review and corrections](cross-review-28-35.md) |

Independent reviewers did not overturn functional-correctness MATCH verdicts
within their stated scope. They corrected the direction of the Chapter 25
woman-pessimal note and clarified the boundaries of the legacy bucket-sort model,
Rabin-Karp abstract steps, and shared FFT arithmetic.

## Resolution

Issues [#345](https://github.com/TankTechnology/CLRS-Lean/issues/345) through
[#375](https://github.com/TankTechnology/CLRS-Lean/issues/375) tracked every
actionable chapter finding. The repairs, focused regressions, model boundaries,
and unified verification are recorded in the
[chapter-repair index](../../plans/2026-09-08-chapter-repairs/index.md). The
current release wording refers to the selected proof inventory and completed
repair scope rather than every theorem, exercise, or low-level implementation in
the textbook.

## Verification record

- Structural coverage passed, with exactly one first-pass and cross-reviewed
  primary verdict for every one of the 137 canonical section IDs.
- All four counterexample or execution-evidence groups passed `lake env lean`.
- The final 2,164-file Lean snapshot fingerprint matched the baseline.
- Markdown links, generated README content, and fast repository checks passed at
  archival time.
- The audit delivered evidence and repair acceptance criteria; the subsequent
  repair commits and unified verification record establish their resolution.
