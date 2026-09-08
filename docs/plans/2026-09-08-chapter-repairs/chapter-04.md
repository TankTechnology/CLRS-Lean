# Chapter 4 repair plan — issue #348

Keep the existing value functions and recurrence interfaces. Add a shared scalar-operation execution layer: recursively visit all scalar entries for matrix addition/subtraction, count each scalar ring operation once, run eight or seven recursive products, and charge actual preparation/reassembly calls. Prove result erasure, same-run recurrence, and comparison with the existing asymptotic budgets. The domain remains depth-indexed 2^k squares; padOne is a one-level block embedding, not an arbitrary-dimension API.

- [x] Add missing public-contract tests for costed matrix execution.
- [x] Implement MatrixExecution/Basic.lean, Algorithms.lean and Bounds.lean with result and scalar work from the same recursion. Verify 2x2 arithmetic and exact counts, prove semantic erasure and public bounds.
- [x] Derive Master case 3 from eventual forcing regularity in §4.5, without an assumed solution upper bound; focused tests owned by the Master proof subtask.
- [x] Extend Akra–Bazzi to the missing 0<q-p<1 regime using a discrete power-sum bound; investigate p=0 using integral-only induction potential.
- [x] Connect actual rounded integer-tree costs to asymptotic results, not just recurrence predicates.
- [x] Update chapter scope, CSV evidence, interface/trust checks and repair record. Maintain explicit remaining obligations; no completion label merely from successful compilation.
- [x] Independent specification and code review; changed-module build and matrix semantic test.
- [x] Finish trust/compatibility tests and batch full-library/repository verification.

No source ownership overlap: root owns MatrixExecution, integer-tree integration, chapter metadata; Master subtask owns §4.5 and its focused test. Akra analysis initially read-only. Existing shared checkout changes and audit snapshots remain intact.

Implementation review found no actionable issues in the new matrix, Master, rounded-tree, or generalized Akra–Bazzi proofs. Broader forcing/perturbations and arbitrary-dimension matrix padding are explicitly outside these statements.
