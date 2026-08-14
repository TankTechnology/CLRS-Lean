# Ch34 Stack-Family Semantics Plan

**Goal:** Lift the completed primitive stack-cell streams to exact whole-cell
and whole-stack semantic gate streams before implementing the uniform family
iterator.

## Tasks

- [x] Add the cell-block decomposition interface test.
- [x] Prove `cellValidityGateTrace` is the ordered flattening of all six-gate blocks.
- [x] Instantiate the decomposition at arithmetic row wires.
- [x] Close one stack's mask-plus-cell semantic gate stream.
- [x] Lift the exact blocks through the fixed machine-stack enumeration.
- [x] Audit, regress, document, and commit.
