# Ch34 Validity Halted-Match Boundary Plan

**Goal:** Instantiate the verified contextual Boolean-equality serializer at
the real halted/none-label wires of an arithmetic tableau row and advance the
completed row-validity boundary past those five gates.

## Tasks

- [x] Add a RED public-interface test.
- [x] Give the raw one-hot gate count and halted-match indices closed formulas.
- [x] Identify the semantic halted-match stream with `affineBoolEqGateStream`.
- [x] Split the post-one-hot suffix exactly after halted match.
- [x] Instantiate the concrete run and its polynomial bound.
- [x] Run focused regressions, audit axioms, document, and commit.
