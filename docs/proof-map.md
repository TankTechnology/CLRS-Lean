# CLRS-lean Proof Map

This ledger records what is proved, what is partial, and what is currently
deferred.  It is intended to become the website's main navigation table.

## Chapter 1 - The Role of Algorithms

- Lean source: `CLRSLean/Chapter_01.lean`
- Status: `expository`
- Main theorem: none
- Current gap: none; theorem-bearing work starts in later chapters

This page explains the project contract: translate each selected textbook claim
into a Lean-friendly model, expose a public theorem interface, prove it, and
record the status honestly.

## Chapter 2 - Getting Started

### Section 2.1 - Insertion sort

- Lean source: `CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.insertionSort_sorted`
  - `CLRS.Chapter02.insertionSort_perm`
- Proof pattern: induction, sortedness preservation, permutation preservation
- Current gap: none for the current functional-list theorem statement

The section proves functional correctness for insertion sort over lists of
natural numbers.  The proof mirrors the textbook loop invariant by separating
orderedness from element preservation.

### Section 2.2 - Analyzing algorithms

- Lean source: `CLRSLean/Chapter_02/Section_02_2_Analyzing_Algorithms.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.insertionSortWorstComparisons_quadratic`
  - `CLRS.Chapter02.insertionSortWorstComparisons_eventually_quadratic`
- Proof pattern: triangular sum, natural-number inequalities, asymptotic wrapper
- Current gap: full RAM semantics and exact line-by-line pseudocode cost are
  future strengthening targets

The section proves that the standard insertion-sort worst-case comparison count
is bounded by a quadratic function.

### Section 2.3 - Designing algorithms

- Lean source: `CLRSLean/Chapter_02/Section_02_3_Designing_Algorithms.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter02.mergeSort_sortedLE`
  - `CLRS.Chapter02.mergeSort_perm`
  - `CLRS.Chapter02.mergeSortRecurrenceOnPowersOfTwo_closedForm`
- Proof pattern: divide and conquer, sortedness, permutation preservation,
  recurrence solving
- Current gap: arbitrary-size floor/ceiling recurrence and full RAM execution
  cost are future strengthening targets

The section proves functional correctness for merge sort using Lean's verified
`List.mergeSort` implementation.  It also proves the exact closed form of the
standard recurrence on input sizes `2^k`.

## Chapter 3 - Growth of Functions

### Section 3.1 - Asymptotic notation

- Lean source: `CLRSLean/Chapter_03/Section_03_1_Asymptotic_Notation.lean`
- Status: `proved`
- Main theorems:
  - `CLRS.Chapter03.isBigO_iff`
  - `CLRS.Chapter03.isLittleO_iff`
  - `CLRS.Chapter03.isBigOmega_iff`
  - `CLRS.Chapter03.isLittleOmega_iff`
  - `CLRS.Chapter03.isBigTheta_trans`
- Proof pattern: bridge CLRS discrete witnesses to Mathlib filters
- Current gap: none for the wrapper interface

The section gives CLRS-facing names for O, Ω, Θ, o, and ω over functions
`ℕ → ℝ`, proves the textbook-style witness forms, and collects basic algebraic
rules.

### Section 3.2 - Standard functions

- Lean source: `CLRSLean/Chapter_03/Section_03_2_Standard_Functions.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter03.isLittleO_pow_pow`
  - `CLRS.Chapter03.isBigO_pow_pow`
  - `CLRS.Chapter03.isBigTheta_nat_floor_coerce`
  - `CLRS.Chapter03.isBigTheta_nat_ceil_coerce`
  - `CLRS.Chapter03.factorial_upper_bound`
  - `CLRS.Chapter03.isLittleO_exp_vs_factorial`
- Proof pattern: reuse Mathlib asymptotic and factorial facts through the CLRS
  wrappers
- Current gap: logarithm-vs-polynomial, polynomial-vs-exponential, and a more
  complete CLRS standard-function table remain future strengthening targets.

This section is the safe part of the `chapter-1-exploration` branch merged into
the main site.  It compiles, but it is not yet the whole Chapter 3 growth
library.

## Chapter 4 - Divide and Conquer

### Section 4.5 - The master method

- Lean source: not imported on `main`
- Status: `blocked-design`
- Exploration source: `worktree-chapter-1-exploration`
- Current gap: the exploration branch contains a useful design for the exact
  power case and the general-n extension, but the Lean file currently has
  syntax errors and unsolved goals.  It should be repaired before being added
  to the build.

## Chapter 5 - Probabilistic Analysis and Randomized Algorithms

### Section 5.1 - The hiring problem

- Lean source: not imported on `main`
- Status: `blocked-mathlib`
- Exploration source: `worktree-chapter-1-exploration`
- Current gap: the exploration branch sketches the harmonic-number expectation
  route, but the Lean file currently fails to compile.  A clean import will
  likely need a smaller deterministic harmonic-number layer before the
  probability interface.

## Chapter 10 - Elementary Data Structures

### Section 10.1 - Stacks and queues

- Lean source: `CLRSLean/Chapter_10/Section_10_1_Stacks_And_Queues.lean`
- Status: `proved` for the functional-list model
- Main theorems:
  - `CLRS.Chapter10.pop_push`
  - `CLRS.Chapter10.dequeue_enqueue_empty`
  - `CLRS.Chapter10.dequeue_enqueue_nonempty`
  - `CLRS.Chapter10.length_enqueue`
- Proof pattern: definitional equations over list-backed stacks and queues
- Current gap: array overflow/underflow, circular buffers, and RAM costs are
  deferred to a future execution model

The section proves the algebraic behavior of stacks and queues using lists:
stack top is list head, and queue front is list head with enqueue at the back.

### Section 10.2 - Linked lists

- Lean source: `CLRSLean/Chapter_10/Section_10_2_Linked_Lists.lean`
- Status: `proved` for the functional-list model
- Main theorems:
  - `CLRS.Chapter10.listSearch_sound`
  - `CLRS.Chapter10.mem_listInsert_self`
  - `CLRS.Chapter10.mem_listInsert_of_mem`
  - `CLRS.Chapter10.mem_listDeleteAll_iff`
- Proof pattern: list recursion, membership preservation, filter membership
- Current gap: predecessor/successor pointer updates and free-list allocation
  require an imperative memory model

## Chapter 11 - Hash Tables

### Section 11.1 - Direct-address tables

- Lean source: `CLRSLean/Chapter_11/Section_11_1_Direct_Address_Tables.lean`
- Status: `proved` for the functional table model
- Main theorems:
  - `CLRS.Chapter11.search_insert_same`
  - `CLRS.Chapter11.search_insert_other`
  - `CLRS.Chapter11.search_delete_same`
  - `CLRS.Chapter11.search_delete_other`
- Proof pattern: total functions, point update by `if`
- Current gap: bounded arrays and RAM costs are deferred

### Section 11.2 - Chained hash tables

- Lean source: `CLRSLean/Chapter_11/Section_11_2_Chained_Hash_Tables.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter11.bucket_hashInsert_same`
  - `CLRS.Chapter11.bucket_hashInsert_other`
  - `CLRS.Chapter11.hashSearch_hashInsert_self`
- Proof pattern: deterministic bucket update for a fixed hash function
- Current gap: expected search time under simple uniform hashing requires a
  probability model over keys or hash functions

## Chapter 12 - Binary Search Trees

### Section 12.1 - Binary search trees

- Lean source: `CLRSLean/Chapter_12/Section_12_1_Binary_Search_Trees.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter12.BSTree.inTree_insert_iff`
  - `CLRS.Chapter12.BSTree.inTree_insert_self`
  - `CLRS.Chapter12.BSTree.insert_ordered`
- Proof pattern: inductive tree membership, bound predicates, ordered invariant
- Current gap: search, minimum/maximum, successor/predecessor, and deletion
  remain future section targets

This section proves the core insertion invariant: insertion adds exactly one key
to the membership relation and preserves the BST ordering invariant.

## Chapter 13 - Red-Black Trees

### Section 13.1 - Red-black trees

- Lean source: `CLRSLean/Chapter_13/Section_13_1_Red_Black_Trees.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`
  - `CLRS.Chapter13.RBTree.inTree_rotateRight_iff`
  - `CLRS.Chapter13.RBTree.red_node_children_black`
  - `CLRS.Chapter13.RBTree.noRedRed_repaint_black`
  - `CLRS.Chapter13.RBTree.balancedBlackHeight_repaintRoot`
- Proof pattern: local colored-tree invariants, rotations, root recoloring
- Current gap: full `RB-INSERT`, `RB-INSERT-FIXUP`, `RB-DELETE`, and
  `RB-DELETE-FIXUP` are not mechanized

The section builds the local invariant library needed before mechanizing the
full balancing algorithms.

## Chapter 16 - Greedy Algorithms

### Section 16.1 - Activity selection

- Lean source: `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean`
- Status: `partial`
- Main proved theorems:
  - `CLRS.ActivitySelection.earliest_finish_minFinish`
  - `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`
- Proof pattern: earliest-finish greedy choice, finite-list feasibility,
  certificate-based exchange argument
- Current gap: derive the `GreedyChoiceCertificate` automatically from a
  finish-time-sorted input interface and prove the full recursive
  `greedySelect` maximum-cardinality theorem without an external certificate.

The section proves the core finite-list model and the Lean-friendly
greedy-choice theorem for CLRS activity selection.  It deliberately exposes the
exchange certificate as an explicit hypothesis, making the remaining automation
target precise rather than hidden inside an incomplete theorem statement.

### Section 16.3 - Huffman codes

- Lean source: `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean`
- Status: `proved`
- Main theorem: `HuffmanV2.optimum_huffman_freqs`
- Proof pattern: greedy exchange argument, split-leaf transformation
- Current gap: none for the current theorem statement

The section proves that Huffman coding produces an optimal prefix tree for a
nonempty frequency table with distinct symbols and positive frequencies.

## Chapter 23 - Minimum Spanning Trees

### Section 23.1 - Growing a minimum spanning tree

- Lean source:
  `CLRSLean/Chapter_23/Section_23_1_Growing_Minimum_Spanning_Trees.lean`
- Status: `partial`
- Main proved theorem: `CLRS.MST.safe_edge_of_lightest_crossing`
- Supporting theorem: `CLRS.MST.mst_exchange_step`
- Proof pattern: cut property, safe edge, exchange argument
- Current gap: the concrete path/cycle lemma that constructs the exchange edge
  from a finite graph spanning tree is still an explicit certificate.

This section contains the mathematical core of the CLRS MST proof.  It proves
that a light edge crossing a cut is safe once the graph-specific exchange
certificate is supplied.

### Section 23.2 - Kruskal and Prim

- Lean source: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`
- Status: `partial`
- Main proved theorem: `CLRS.MST.kruskal_optimal`
- Supporting theorem: `CLRS.MST.FiniteGraph.kruskal_optimal`
- Proof pattern: safe-edge induction over an edge list
- Deferred implementation: union-find correctness
- Current gaps:
  - derive lightness automatically from a sorted edge order;
  - prove the final selected edge set is a spanning tree from connectedness and
    complete edge scan;
  - add Prim's algorithm theorem interface.

The section currently proves a mathematical Kruskal skeleton: if accepted edges
come with safe-edge certificates and the final selected set is a spanning tree,
then the result is optimal.

## Deferred And Blocked Items

| Item | Status | Reason |
| --- | --- | --- |
| Union-find implementation correctness | `deferred-implementation` | Not needed for the mathematical MST correctness theorem. |
| Activity-selection sorted-order exchange certificate | `partial` | Needs a sorted-by-finish interface that derives the current certificate automatically. |
| Sorted-order lightness for Kruskal | `partial` | Needs a list-order invariant over processed edges. |
| Chapter 4 Master Theorem exploration | `blocked-design` | Useful design exists in `chapter-1-exploration`, but the Lean file is not compiler-clean. |
| Chapter 5 hiring problem exploration | `blocked-mathlib` | Harmonic-number route exists in `chapter-1-exploration`, but the current file fails to compile. |
| Hash-table expected-time analysis | `blocked-design` | Needs a probability model for simple uniform hashing. |
| Pointer-level linked lists and free lists | `future-work` | Requires an imperative memory model. |
| BST deletion/transplant | `future-work` | Needs either a functional deletion theorem or pointer-transplant semantics. |
| Full red-black insertion/deletion | `blocked-design` | Needs a balancing representation and invariant-preservation proof across fixup cases. |
| Concrete MST exchange edge from paths | `blocked-design` | Needs a stable finite path/walk representation. |
| Prim's algorithm | `statement` | Section file exists only through the Chapter 23.2 target; theorem interface has not been added yet. |
| CLRS exercises | `future-work` | Keep the first pass focused on main textbook claims; add exercises after section interfaces stabilize. |
| Chapter-end problems | `future-work` | Treat as a second track with explicit priority and difficulty labels. |
| Full RAM semantics | `future-work` | Requires an imperative machine/cost semantics rather than only mathematical functions and recurrences. |
| General merge-sort recurrence | `future-work` | Needs floor/ceiling arithmetic and an asymptotic theorem for all input sizes. |

## Publication Value

The proof map is intentionally honest.  Completed sections show theorem names
that compile.  Partial sections expose the exact missing mathematical or
representation layer.  This lets future contributors pick a section without
reverse-engineering the project state.
