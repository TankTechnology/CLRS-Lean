# Ch34 Contextual Boolean-Equality Serializer Plan

**Goal:** Prove a concrete contextual builder run for the five-gate
`boolEqGateTrace start left right`, with arbitrary unary parameters and output
suffix.

**Architecture:** Extend the already verified three-counter exactly-one
program with a finite Boolean-equality control path.  Reuse its public
counter-preserving encoders and register cleanup.  Keep `start`, `left`, and
`right` in the three unary counters; finite control contains only the fixed
five-phase algorithm.  After the first three gates, clear the operand counters,
copy `start`, construct `start+1`, and increment to `start+2/start+3` for the
last two gates.

## Tasks

- [x] Add a RED interface test for stream, body configuration, exact steps,
  contextual run, and quadratic bound.
- [x] Extend the existing finite control without changing the original main
  path or any old transition.
- [x] Prove operand clearing and start-copy/restoration exactly.
- [x] Prove all five encoded gates and final cleanup compose to the semantic
  `boolEqGateTrace` stream.
- [x] Prove a quadratic bound, audit axioms, and run old exactly-one plus new
  Boolean-equality regressions.
- [x] Integrate documentation and commit the independently accepted slice.
