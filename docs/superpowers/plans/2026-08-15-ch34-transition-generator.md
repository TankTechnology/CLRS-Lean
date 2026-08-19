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
- [x] Give each runtime-sized phase an exact fixed-controller execution theorem.
      The complete-row equality and multiplexer subphases are now closed by
      `affineEqFinCanonical_run` and `affineMuxFinCanonical_run`; narrowing is
      closed by `affineNarrowCfg_run`. All statement primitives, including the
      height-sensitive `pop` merge, now have exact fixed-controller runs; the
      recursive compiler now lowers to a tagged five-kind runtime phase script
      whose interpreted bytes equal `compileStmtGateTrace`, with a uniform
      linear aggregate component budget. `affineStmtRevProgram` is now the one
      fixed controller embedding both primitive machines. A three-symbol unary
      phase prefix makes the remainder an ordinary suffix that the components
      preserve. `affineStmt_phase_next_run`, `affineStmt_entry_run`, and
      `affineStmt_run` now execute nonempty multi-phase scripts with no
      intermediate halt; `compileStmtScript_run` emits exactly the structural
      `compileStmtGateTrace`. The concrete runtime is linear:
      `affineStmtScriptRunSteps ≤ 200 * input.length + 4`.
- [x] Compose the five phases of one local transition under one fixed program.
      `compileTransitionScript_run` now executes the concrete operand script,
      halts with the byte-for-byte encoding of `transitionCircuitGateTrace`,
      and `affineTransition_steps_le` bounds the exact run linearly in the
      complete delimiter-bearing script.
- [ ] Iterate the local controller over all `T` adjacent row pairs.
- [ ] Prove byte-for-byte equality with `transitionGateStreamAt`, plus a
      polynomial bound in the exact runtime encoding.  The semantic target is
      now explicit: `transitionGateListAt_eq_trace` removes `List.drop` from
      the acceptance surface; concrete controller execution remains.
- [x] Add focused local interface/axiom tests and update the failure ledger.
      This closes the one-pair controller checkpoint, not the whole transition
      family.

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
- Appending high-level sum-type tags directly after a unary component payload
  does not match the component's suffix-preservation contract. The accepted
  controller encodes each phase tag as a fixed three-symbol unary prefix; the
  first `tick` is the common boundary and the next two symbols select one of
  five phase kinds. Simulation explicitly excludes only the boundary state,
  then the statement controller takes over for four parser/clear steps.
- Treating the statement controller's reserved three-symbol exit code as a
  three-step clean exit is false. The tag parser leaves the final symbol in
  `buffer₁`; the accepted controller adds a fourth `clearFinish` step before
  exposing its redirectable finish state.
- Consuming the narrowing-to-equality or equality-to-AND `tick` and entering
  the next component immediately is false for the same machine-state reason:
  `popInput` retains the consumed marker in `buffer₁`. The accepted outer
  controller uses explicit `narrowClear` and `eqClear` states, so each boundary
  takes two steps and the lifted component begins from its proved clean entry.
- A structural simulation theorem parameterized by an arbitrary statement
  label embedding is false: the target configuration is specifically tagged
  by `.stmt`. The proved theorem fixes that embedding and does not advertise a
  stronger parametric interface.
