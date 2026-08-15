# Ch34 Local Transition Controller Checkpoint

## Scope

This checkpoint closes one complete Cook--Levin local-transition serializer.
It does **not** yet iterate the serializer over every adjacent tableau-row pair
and does not by itself complete the whole verifier-circuit generator.

## Closed interfaces

- `compileDispatchScript_run` executes the recursively compiled finite-label
  dispatch script under the fixed statement controller.
- `compileTransitionScript_gateStream_eq_trace` proves that the concrete
  operand script denotes exactly `transitionCircuitGateTrace`.
- `affineTransition_run` executes all five phases continuously: Boolean
  constants, statement dispatch, narrowing, complete-row equality, and the
  final conjunction.
- `compileTransitionScript_run` specializes the execution theorem to the
  semantic Cook--Levin builder and proves exact encoded output followed by
  halt.
- `affineTransition_steps_le` gives the explicit bound
  `steps ≤ 500 * encodedInput.length + 20`.

## Rejected routes discovered during composition

1. Independently halting component runs cannot be concatenated into one
   generator. Every inner phase needs a suffix-preserving redirectable exit.
2. The statement controller cannot expose a clean exit after only the three
   reserved tag symbols. Its parser leaves the last symbol in `buffer₁`; a
   fourth clear step is required.
3. A phase-boundary `popInput` does not establish the next component's clean
   initial configuration. It consumes the marker but retains it in `buffer₁`;
   `narrowClear` and `eqClear` are therefore required before entering equality
   and final AND.
4. The equality component is structurally simulated only away from the exact
   boundary symbols that the outer controller deliberately intercepts. A
   global relabeling theorem would be false.
5. Statement relabeling is valid for the concrete `.stmt` embedding, not for
   an arbitrary label map whose target configurations need not match.

## Focused verification

The following checks passed without a full-repository build:

```text
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionController
lake env lean Tests/Chapter_34_PolyBuilder_TransitionController.lean
lake env lean Tests/Chapter_34_PolyBuilder_DispatchController.lean
lake env lean Tests/Chapter_34_PolyBuilder_TransitionScript.lean
lake env lean Tests/Chapter_34_PolyBuilder_StatementController.lean
lake env lean Tests/Chapter_34_PolyBuilder_Narrowing.lean
lake env lean Tests/Chapter_34_PolyBuilder_EqFin.lean
lake env lean CLRSLean/Chapter_34.lean
git diff --check
```

The headline execution and bound theorems report only the standard Lean
dependencies `[propext, Classical.choice, Quot.sound]`; no project axiom or
`sorryAx` appears.

## Next acceptance boundary

The next generator checkpoint must encode and execute a runtime-length family
of adjacent-row transition scripts, prove byte-for-byte equality with
`transitionGateStreamAt`, and give a polynomial bound in the family's exact
runtime encoding. Only after that family is joined with header, validity,
boundary, and final-output phases can the concrete `verifierCircuit` generator
be claimed complete.
