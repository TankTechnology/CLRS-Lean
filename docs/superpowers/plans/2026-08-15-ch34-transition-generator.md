# Ch34 Transition Generator Plan

**Goal:** Execute the exact dimension-only transition suffix emitted after
canonical validity, using one fixed finite controller and an explicit
polynomial runtime bound.

## Acceptance boundary

- [x] Freeze `transitionGateStreamAt tm H T` as the literal semantic-builder
      suffix after validity.
- [x] Prove exact append agreement with `arithmeticTransitionsAt` and exact
      gate count `T * transitionCircuitGateCost tm H`.
- [x] Expose verifier-by-length and complete transition-prefix interfaces.
- [ ] Decompose one local transition stream into widening, finite-label
      dispatch, narrowing, complete-row equality, and final AND.
- [ ] Give each runtime-sized phase an exact fixed-controller execution theorem.
- [ ] Iterate the local controller over all `T` adjacent row pairs.
- [ ] Prove byte-for-byte equality with `transitionGateStreamAt`, plus a
      polynomial bound in the exact runtime encoding.
- [ ] Add focused interface/axiom tests and update the failure ledger.

## Known failed or rejected routes

- Extracting a suffix with `List.drop` defines the correct target but is not a
  machine implementation. No execution claim is allowed until an
  `EvalsToInTime` theorem emits exactly that stream.
- Carrying `arithmeticTransitionsAt tm H T` or its gate list in a control label
  is not a fixed `FinTM2`; both dimensions and the resulting gates are runtime
  data.
- Gate-count equality alone cannot replace ordered gate-stream equality: two
  builders may have the same cost and different wire arguments.
- Reusing independently halting subphase runs recreates the composition gap.
  Every phase must expose a tail-preserving redirectable exit.
