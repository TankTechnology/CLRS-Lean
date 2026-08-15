# Ch34 Non-Halting Family-Loop Plan

**Goal:** Turn the completed validity serializers into one concrete bounded
builder that can execute consecutive cell and stack blocks without halting
between them.

## Acceptance boundary

- [x] Identify the final conjunction's exact source-wire list and serialized
      trace, so the single-row target has no opaque suffix left.
- [ ] Add a delimiter-bearing runtime frame for gate/source indices; keep it
      on symbol work stacks while primitive-local unary registers are reused.
- [ ] Add continuation-preserving `NOT -> BoolEq` execution over that frame.
- [ ] Lift the cell block across the runtime-height loop and then the fixed
      machine-stack family.
- [ ] Match the linked output byte-for-byte with
      `arithmeticStackFamilyGateStream` and prove a polynomial step bound.
- [ ] Run focused module/interface checks, `#print axioms`, placeholder scan,
      and `git diff --check` before each commit.

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
