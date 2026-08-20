# Chapter 34 Cook--Levin Final Machine Closure Plan

**Goal:** Prove the unconditional machine-level Cook--Levin reduction from every
polynomially verifiable language to `GeneralCircuitSAT`, and derive the standard
`NPHard` and `NPComplete` theorems without oracle premises.

**Architecture:** Keep the established semantic circuit and polynomial-size
proofs unchanged.  Close only the remaining raw-input compiler boundary.  The
critical terminal-stack path is split into small reusable unary-frame machines:
fixed suffix deletion, one push/pop packet rewrite, finite action folding, and
the complete true-arm source.  Those outputs are then connected to the existing
transition, verifier-body, prefix, and reduction wrappers.

**Verification policy:** Every new public interface is added to a focused Lean
test before implementation, observed failing because the declaration is
missing, then made green.  Each completed stage is checked for `sorry`/`admit`,
committed, and pushed before the next stage.

---

### Task 1: Fixed-suffix unary-row machine

**Files:**

- Create `Tests/Chapter_34_PolyBuilder_UnaryFrameFixedSuffixDrop.lean`.
- Create `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/UnaryFrameFixedSuffixDrop.lean`.

Prove exact semantics for deleting the last verifier-fixed number of values
from every `frameEnd`-terminated unary row.  Implement it as reverse, a finite
state pass over reversed rows, and reverse again.  Export an unconditional
`TM2ComputableInPolyTime` theorem.

### Task 2: Primitive structured stack rewrites

**Files:**

- Create focused push and pop packet modules under `CookLevin/Circuitization/`.
- Extend the transition input-compiler test with their public contracts.

Use the existing two-boundary structured source.  Combine fixed-prefix drop,
Task 1 suffix drop, and verifier-fixed affine inserted operands to compute one
selected push or pop exactly, preserving the height/cell boundary.

### Task 3: Finite selected-action fold

**Files:**

- Create `GeneratorTransitionStatementStackRouteActionMachine.lean`.
- Create a focused action-fold test.

Fold the verifier-fixed selected action list using the primitive packet
rewrites.  Prove byte equality with
`transitionStmtSelectedStackActionValues_eval` and lift it over every transition
seed, terminal label, and machine stack.

### Task 4: Complete transition true-arm compiler

**Files:**

- Create a terminal-stack frame compiler and a unified true-arm compiler.
- Update `GeneratorTransitionInputCompiler.lean` and its focused test.

Merge the already concrete branch arm, terminal prefix, and Task 3 stack suffix
in canonical label order.  Close the unconditional polynomial-time theorem for
the complete transition script family.

### Task 5: Whole verifier-body and map compiler

**Files:**

- Add the unconditional body compiler theorem to `GeneratorBody.lean` through a
  small source-assembly module.
- Create the full circuit-map machine module and focused interface test.

Connect header/input/pool, validity rows, transition rows, and the existing
boundary/tail stream into one fixed machine computing `cookLevinMap W` from the
raw input.  Transport the TM2 witness to `PolyTimeComputable`.

### Task 6: Textbook headline theorems

**Files:**

- Extend `CookLevin/Textbook.lean`.
- Extend `GeneralCircuit/NP.lean` or add a small completeness wrapper.
- Update Chapter 34 interface tests and status documentation.

Export unconditional `PolyTimeReducible L GeneralCircuitSAT` for every
`PolyTimeVerifiable L`, then prove `NPHard GeneralCircuitSAT` and
`NPComplete GeneralCircuitSAT`.  Run focused tests, `lake build
CLRSLean.Chapter_34`, and an axiom audit before the final staged commit and push.
