# Ch34 Row-Validity One-Hot Integration Plan

**Goal:** Connect every arithmetic row one-hot group to the contextual affine
exactly-one serializer, then expose the family order needed by the concrete
row-validity generator.

**Architecture:** Keep machine execution in `PolyBuilder.ExactlyOne.AffineRun`
and add a Cook--Levin-facing bridge beside `GeneratorValidity`.  First prove a
single case-complete theorem giving the consecutive wire base and count of
label, state, stack-height, and stack-cell groups.  Then describe the explicit
finite group order and show its semantic gate family is the concatenation of
those affine traces.  A later driver can consume exactly these closed
parameters without runtime-dependent data in finite control.

## Task 1: Arithmetic group parameters

- [x] Add a RED interface test for group base, group count, wire equality, and
  the affine stream bridge.
- [x] Define `arithmeticCfgOneHotGroupWireBase` and
  `arithmeticCfgOneHotGroupWireCount` by the four group constructors.
- [x] Prove `arithmeticCfgOneHotGroupWires_eq_affine` for every group.
- [x] Prove `arithmeticCfgOneHotGroupGateStream_eq_affine` against the
  canonical semantic `exactlyOneGateTrace`.

## Task 2: Ordered raw one-hot family

- [x] Define an explicit per-index affine specification using
  `cfgOneHotGroupEquivFin`.
- [x] Prove the accumulated gate start equals the semantic family prefix
  length.
- [x] Prove the raw one-hot gate stream is the ordered concatenation of affine
  group streams.

## Task 3: Acceptance

- [x] Check theorem axioms and the four constructor-complete group proof.
- [x] Run the new interface test plus existing affine and validity tests.
- [x] Run repository policy and `git diff --check`, then commit the slice.
