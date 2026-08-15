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
- [x] Decompose one local transition stream into widening, finite-label
      dispatch, narrowing, complete-row equality, and final AND.
- [ ] Give each runtime-sized phase an exact fixed-controller execution theorem.
      The complete-row equality and multiplexer subphases are now closed by
      `affineEqFinCanonical_run` and `affineMuxFinCanonical_run`; narrowing is
      closed by `affineNarrowCfg_run`. All statement primitives, including the
      height-sensitive `pop` merge, now have exact fixed-controller runs; the
      recursive compiler now lowers to a tagged five-kind runtime phase script
      whose interpreted bytes equal `compileStmtGateTrace`, with a uniform
      linear aggregate component budget. `affineStmtRevProgram` is now the one
      fixed controller embedding both primitive machines and redirecting clean
      OR/mux boundaries by tag; dispatch, empty script, and four empty-family
      redirects execute exactly. Pure-data step simulation now lifts every one
      of the five phase kinds to an exact final-phase run, including nonempty
      OR/pair-map/mux inputs. The remaining gap is preserving a nonempty tagged
      suffix while redirecting into the next phase.
- [ ] Iterate the local controller over all `T` adjacent row pairs.
- [ ] Prove byte-for-byte equality with `transitionGateStreamAt`, plus a
      polynomial bound in the exact runtime encoding.  The semantic target is
      now explicit: `transitionGateListAt_eq_trace` removes `List.drop` from
      the acceptance surface; concrete controller execution remains.
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
- The affine interval suffix-OR controller cannot serialize sparse finite
  truth-table fibers. The accepted arbitrary-list controller carries each
  ordered source/carry pair in its runtime frame.
- Active-mask OR order is `.or carry wire`, but general disjunction order is
  `.or wire carry`; semantic commutativity is not an encoding proof.
- Reusing independently halting subphase runs recreates the composition gap.
  Every phase must expose a tail-preserving redirectable exit.
- Redirecting the embedded AND exit without clearing its incremented carry
  register corrupts the next runtime load. The shared controller must execute
  an explicit cleanup loop before returning to its public finish boundary.
- Semantic commutativity of AND does not permit operand swapping here: exact
  encoding equality distinguishes `.and previous matched` from
  `.and matched previous`.
- Reusing the public one-element suffix-OR runner for the final mux arm emits
  an extra false seed; use the contextual seed-free one-gate OR interface.
- The controller label cannot compute the runtime wire `falseArm + 1`; encode
  that shifted value in the third unary loader field.
- Pushing the OR-loop tick directly at loader exit preserves the loader's
  separator buffer. Normalize the buffer first, then seed the tick in a
  dedicated finite-control phase.
- A separately halting OR run followed by a separately halting NOT run is not
  one narrowing computation. The accepted controller reserves `.tick` as the
  phase boundary and redirects into the NOT loader without halting.
- The OR kernel clears its counters, so reconstructing the final disjunction
  wire after the phase boundary is invalid. The exact NOT source is supplied
  as a runtime unary field.
- A consumed phase marker remains in `buffer₁`; entering the NOT loader before
  clearing it does not match the loader theorem's initial configuration.
- The public false-seeded arbitrary-OR runner cannot implement a positive-height
  `pop`: it would emit an extra `.const false` gate. The accepted seed-free
  entry begins at the shared OR check state and emits exactly the height merge.
- Splitting `pop` into separately selected programs for `H = 0` and `H > 0`
  would make the machine depend on a runtime dimension. The accepted controller
  handles the empty and singleton frame lists with the same fixed program.
- Concatenating untagged unary component frames is ambiguous because the same
  three delimiter symbols have phase-local meanings. The accepted statement
  input uses five finite phase tags and embeds only unary operand frames.
- Feeding the controller a pre-serialized target gate list would make execution
  tautological. `compileStmtScript` stores wire operands and phase boundaries;
  `compileStmtScript_gateStream_eq_trace` separately proves that interpreting
  those operands yields the semantic trace.
- The tagged boundary operation is not globally equal to a structural relabel
  of the source component: it deliberately handles phase tags differently.
  The valid lifting theorem is restricted to pure `.data` configurations and
  stops at the source component's clean finish label.
