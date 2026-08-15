# Ch34 Whole Validity Row Plan

**Goal:** Link the completed raw one-hot family, halted/none-label equality,
stack-validity family, and final conjunction into one exact fixed-program run
for a canonical arithmetic tableau row.

## Acceptance boundary

- [x] Reuse the exactly-one family program's embedded sequential kernel for a
      contextual Boolean equality and stop at its public family boundary.
- [x] Define one delimiter-bearing runtime frame containing the raw family,
      halted-equality triple, and completed validity tail.
- [x] Add one fixed controller with checked boundary cleanup and a persistent
      three-field loader between the phases.
- [x] Prove one continuous exact run and byte-for-byte agreement with the
      concatenated row stream.
- [x] Prove a uniform quadratic runtime bound in the exact encoded row frame.
- [x] Instantiate the controller at the arithmetic Cook--Levin indices and
      prove exact output `validityRowGateStreamAt`.
- [x] Add focused interface/axiom tests and register both modules in the public
      chapter and site surfaces.

## Known failed or rejected routes

- Concatenating the existing standalone one-hot, BoolEq, and tail run theorems
  is invalid because their successful runs execute a halt before the next
  phase can start.
- Entering BoolEq immediately after the one-hot boundary without a loader
  loses its runtime gate/source indices; those values cannot be embedded in
  finite control.
- Treating the separator left in buffer one as harmless breaks the exact entry
  configuration of the next component.  Every bridge now clears the buffered
  outer delimiter with an empty-work-stack check.
- Sharing one undistinguished family phase for raw one-hot and BoolEq makes the
  `.finish` continuation ambiguous.  The accepted controller uses disjoint
  `oneHot` and `boolEq` control tags even though both reuse the same component
  program.
- Semantic list concatenation alone is not an executable reduction.  The
  accepted result includes an exact `EvalsToInTime` theorem for the combined
  fixed program and a bound over its concrete runtime encoding.

## Next link

Lift the completed arithmetic row controller across all public tableau rows in
row-major order.  That family theorem must emit exactly
`verifierValidityGateStream` and expose a redirectable boundary for the
transition serializer.
