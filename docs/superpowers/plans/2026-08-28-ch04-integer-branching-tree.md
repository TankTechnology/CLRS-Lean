# Chapter 4 Integer Branching-Tree Implementation Plan

> **For agentic workers:** Use `superpowers:executing-plans` and compile one
> proof layer at a time.  Do not rebuild all of Chapter 4 between local edits.

**Goal:** Construct unequal-depth integer recursion trees and prove exact
agreement with floor/ceiling recurrences for both detailed CLRS examples.

**Architecture:** A finite branching specification contains decreasing child
sizes.  Well-founded recursion builds the tree; strong induction proves its
total cost equals any independently stated recurrence solution.  Small
example modules discharge the rounding arithmetic and connect the concrete
tree costs to the existing all-input asymptotic interfaces.

**Tech stack:** Lean 4, Mathlib well-founded recursion and finite sums, the
existing Chapter 4 master-theorem and Akra--Bazzi APIs.

---

### Task 1: Freeze the public contract

**Files:**
- Create: `Tests/Chapter_04/IntegerBranchingTree.lean`

- [x] Add failing imports and `#check` declarations for the generic exact
  bridge, the two example bridges, the unequal-depth witness, and the
  all-input recurrence connection.
- [x] Run only this test and record the expected missing-module failure.
- [x] Commit the contract test.

### Task 2: Tree model

**Files:**
- Create: `.../Branching/IntegerTree/Model.lean`

- [x] Define `IntegerBranchingTree`, `rootSize`, `rootWork`, `totalCost`, and
  `height`.
- [x] Add native examples that distinguish equal and unequal child heights.
- [x] Compile the model module.

### Task 3: Well-founded execution and exact semantics

**Files:**
- Create: `.../Branching/IntegerTree/Execution.lean`

- [x] Define `IntegerBranchingSpec` and its independent `Satisfies` predicate.
- [x] Define `build` by well-founded recursion on input size.
- [x] Prove root-size, leaf-cutoff, and internal-node invariants.
- [x] Prove `build_totalCost_eq` by strong induction.
- [x] Compile and commit the generic layer.

### Task 4: Balanced floor-division instance

**Files:**
- Create: `.../Branching/IntegerTree/Balanced.lean`

- [x] Prove `n / 4 < n` above the cutoff and instantiate three branches.
- [x] State the textbook `3T(n/4)+cn^2` recurrence and prove the exact tree
  equality.
- [x] Define the generated tree cost and prove its
  `FloorDivideRecurrence 3 4` bridge plus the above-cutoff forcing equation.
- [x] Add native shape/total checks and compile the module.

### Task 5: Unbalanced floor/ceiling instance

**Files:**
- Create: `.../Branching/IntegerTree/Unbalanced.lean`

- [x] Prove both `n/3` and `ceil(2n/3)` strictly decrease for `n > 2`.
- [x] State the textbook recurrence and prove the exact tree equality.
- [x] Prove a concrete unequal-depth child witness.
- [x] Prove the floor/ceiling one-unit sandwich and publish the existing
  Akra--Bazzi `p = 1` root as the asymptotic connection.
- [x] Add native checks and compile the module.

### Task 6: Facade, trust audit, and chapter integration

**Files:**
- Create: `.../Branching/IntegerTree.lean`
- Modify: `.../Section_04_4_Recursion_Tree_Method.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_04.lean`
- Modify: `Tests/Trust/Chapter_04.lean`
- Modify: progress/audit documentation

- [x] Publish the small facade and update §4.4's status text.
- [x] Run the focused interface/native tests and Chapter 4 trust audit.
- [x] Run one Chapter 4 aggregate build as the checkpoint.
- [x] Update the proof ledger and issue #336 with exact verification evidence.
- [x] Commit and push the closure.
