# Ch34 Non-Halting Family-Loop Plan

**Goal:** Turn the completed validity serializers into one concrete bounded
builder that can execute consecutive cell and stack blocks without halting
between them.

## Acceptance boundary

- [x] Identify the final conjunction's exact source-wire list and serialized
      trace, so the single-row target has no opaque suffix left.
- [x] Define an unambiguous delimiter-bearing runtime frame and an exact
      three-field loader that preserves the unconsumed tail, output, and both
      work stacks while loading primitive-local unary registers.
- [x] Add continuation-preserving `NOT -> BoolEq` execution for one complete
      six-gate cell, with exact output, exact steps, and a quadratic bound.
- [x] Embed the frame loader and cell continuation in one fixed family
      controller, retaining the remaining frame between cells.
- [x] Lift the cell block across the runtime-height loop for one stack.
- [x] Prepend one stack's suffix-OR mask and execute its complete runtime-height
      cell family without an intermediate halt.
- [x] Lift the complete stack block across the fixed machine-stack family.
- [x] Match the linked output byte-for-byte with
      `arithmeticStackFamilyGateStream` and prove a polynomial step bound.
- [x] Run focused module/interface checks and `#print axioms` for the completed
      runtime-height cell-family cut; repeat the placeholder scan and
      `git diff --check` before each commit.

## Known failed routes retained

- Independently halting primitive runs cannot be concatenated: after the first
  `halt`, the builder semantics has no transition to the next primitive.
- Replacing the concrete run by equality of semantic gate lists proves no TM2
  computability statement.
- Embedding a runtime cell, row, or gate index in a control label violates the
  fixed finite-machine requirement.
- A linker that merely changes `.halt` to `.jump` is not semantics preserving:
  `.halt` also clears both symbol buffers and the test bit.  The accepted
  linker must reproduce that normalization before entering its continuation.
- Linking the current public `runFrom` theorems is still insufficient even if
  halt normalization is reproduced: successful exit deliberately erases all
  three unary registers and requires both work stacks to be empty, so the next
  cell loses its runtime gate/source indices.  The accepted family controller
  therefore needs a delimiter-bearing persistent frame and
  continuation-preserving primitive exits.
- Adding every cell-controller phase as another flat constructor to the main
  label type exceeds Lean's derived-`Fintype` nested-sum synthesis depth.  Cell
  phases therefore live in the separate finite `SequentialCellLabel` type
  beneath one grouped `.cell` constructor.
- Reusing the ordinary unary-field separator as the end of a complete stack
  frame is ambiguous: zero-valued fields already produce consecutive bare
  separators.  The accepted encoding adds a dedicated `frameEnd` symbol;
  treating an arbitrary separator run as the outer boundary is rejected.
