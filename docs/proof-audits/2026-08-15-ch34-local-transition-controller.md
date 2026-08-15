# Ch34 Local Transition Controller Checkpoint

## Scope

This checkpoint closes one complete Cook--Levin local-transition serializer
and the fixed controller that iterates any runtime-length family of such
serializers.  It does **not** yet construct that family from every adjacent
tableau-row pair and does not by itself complete the whole verifier-circuit
generator.

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
- `affineTransition_runToFinishWithTail` proves that one local serializer
  preserves an arbitrary unary-encoded family suffix and returns through a
  redirectable finish state.
- `affineTransitionFamily_run` executes a runtime-length list of local scripts
  under one fixed program and emits their exact concatenated gate stream.
- `affineTransitionFamily_steps_le` gives the family-level bound
  `steps ≤ 500 * encodedFamily.length + 2`.
- `compileTransitionFamilyScripts` mirrors the semantic prefix recursion and
  extracts exactly one operand script per adjacent tableau-row pair.
- `compileTransitionFamilyScriptsAt_gateStream_eq` identifies its complete
  byte stream with the frozen `transitionGateStreamAt` target.
- `compileTransitionFamilyScriptsAt_run` is the end-to-end executable theorem
  for the canonical dimension-only transition family.
- `verifierInitialBoundary_gates_eq` freezes the exact complete-row equality
  trace immediately following transitions.
- `compileVerifierInitialBoundaryFrames_run` executes its canonical `EqFin`
  frames and emits exactly the symbolic initial-boundary byte stream.
- `affineOptionalEqFin_run` executes both branches of a total boundary under
  one fixed program: marker-led complete equality or empty zero-gate output.
- `verifierAcceptingBoundary_gates_eq` and
  `compileVerifierAcceptingBoundaryFrames_run` freeze and execute the exact
  accepting-row branch chosen by the semantic constructor.
- `verifierCircuit_gates_eq_finalConjunction` freezes the last gate family of
  the complete verifier circuit, and `verifierFinalConjunctionFrame_run`
  executes its canonical tail-first conjunction frame.
- `buildSeparatorNots_gates_eq`, `buildInputArms_gates_eq`, and
  `verifierInputShapeCircuit_gates_eq` expose the three literal input-shape
  phases. `verifierInputBoundary_gates_eq` specializes their exact trace to
  the assembled verifier.
- `affineNotFamily_run` executes any runtime list of NOT operands under one
  fixed controller, with the linear bound
  `steps ≤ 20 * encodedSources.length + 2`.
- `affineOptionalConjunctionFamily_run` executes a runtime family whose entries
  either append one full conjunction or exactly zero gates, with a quadratic
  bound in its exact marker-bearing input.
- `compileInputArmFrames_gateStream_eq_trace` proves that the optional family
  reproduces all certificate-length arms, including nonfitting zero-gate
  branches.
- `compileVerifierInputShapeScript_gateStream_eq_trace` and
  `verifierInputBoundaryScript_gateStream_eq` package separator NOTs, optional
  arms, and the final OR into one canonical operand script whose combined byte
  stream is the complete semantic input-boundary trace.
- `affineInputShape_run` joins separator NOTs, optional arms, and the final OR
  under one fixed controller, without an intermediate halt, and emits their
  exact combined stream. `affineInputShapeRev_steps_le` supplies the uniform
  quadratic envelope in the exact runtime encoding length.
- `verifierInputBoundary_run` specializes that continuous execution to the
  assembled verifier boundary; `verifierInputBoundary_steps_le` carries the
  same explicit bound to the frozen semantic target.

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
6. Concatenating local unary payloads without an outer marker is ambiguous:
   the local final `frameEnd` terminates a payload but cannot also announce
   whether another payload follows.  The family protocol therefore uses a
   leading `frameEnd` before every local payload; the empty suffix has no
   leading marker.
7. Treating the unrepresentable accepting target as equality over an empty
   coordinate family is byte-incorrect: empty `EqFin` emits its true seed,
   whereas `falseBoundaryCircuit` emits no gate and reuses the shared false
   wire.  The optional controller therefore has a genuine zero-output branch.
8. A zero-gate input arm cannot be encoded by an empty conjunction frame:
   empty conjunction still emits its true seed.  Optional arm entries therefore
   use a distinct `separator` marker for zero gates and a `tick` marker for a
   real conjunction.
9. Reusing `frameEnd` both for a zero-gate entry and for end-of-family is
   ambiguous, especially for consecutive nonfitting arms.  The optional arm
   protocol reserves `frameEnd` solely as the final family terminator.

## Focused verification

The following checks passed without a full-repository build:

```text
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionController
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionFamilyController
lake env lean Tests/Chapter_34_PolyBuilder_TransitionController.lean
lake env lean Tests/Chapter_34_PolyBuilder_TransitionFamilyController.lean
lake env lean Tests/Chapter_34_PolyBuilder_TransitionFamilyScript.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorInitialBoundary.lean
lake env lean Tests/Chapter_34_PolyBuilder_OptionalEqFin.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorAcceptingBoundary.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorConjunction.lean
lake env lean Tests/Chapter_34_CookLevin_VerifierInputTraces.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorInputBoundary.lean
lake env lean Tests/Chapter_34_PolyBuilder_NotFamily.lean
lake env lean Tests/Chapter_34_PolyBuilder_OptionalConjunctionFamily.lean
lake env lean Tests/Chapter_34_PolyBuilder_InputShapeController.lean
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

The next generator checkpoint must join the now-continuous input phase with
header, validity, transition, initial/accepting boundaries, conjunction, and
final-output phases. A dimension-level bound on the canonical runtime inputs
must then connect the component bounds to the verifier polynomials. Only after
that composition can the concrete `verifierCircuit` generator be claimed
complete.
