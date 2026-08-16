# First validity-row halted-frame compiler

## Goal

Close one concrete part of the remaining Cook--Levin source-to-script gap:
from the raw verifier input, a fixed TM2 must emit the three unary operands
used by the halted/none-label equality phase of the first actual validity row.

## Proof checkpoints

1. Define an exact natural polynomial for `arithmeticRawOneHotGateCount` and
   prove its evaluation theorem.
2. Define the three verifier-input polynomials for the first row's
   `haltedStart`, `haltedLeft`, and `haltedRight` fields.
3. Instantiate `exactPolynomialUnaryFrames_computableInPolyTime` to obtain a
   concrete fixed TM2 from the raw source word.
4. Prove byte-for-byte agreement with the corresponding fields of
   `arithmeticValidityRowFrame`, and prove that this byte stream occurs in the
   actual encoded first-row frame at the controller boundary.
5. Add a focused compile/axiom-surface test, expose the module through Chapter
   34 imports and documentation metadata, then commit and push this checkpoint.

## Verification

- Focused production module and test compile.
- Chapter 34 root compiles.
- Axiom audit shows no unexpected axioms.
- Placeholder, status-claim, progress-table, whitespace, and site-consistency
  checks introduce no new failure attributable to this module.
