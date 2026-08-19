# Ch34 Affine Conjunction Controller Design

## Objective

Close the concrete-execution gap for the final conjunction of one canonical
Cook--Levin validity row.  The milestone must produce the already-identified
`arithmeticValidityFinalConjunctionGateStream` with one fixed finite TM2
controller, an exact run theorem, and an explicit polynomial step bound.

This is route A: build and verify a reusable conjunction controller first,
then instantiate it at the arithmetic row-validity indices.  Linking it to the
preceding stack-family controller is a later, separate milestone.

## Accepted architecture

Add a focused `PolyBuilder/Conjunction.lean` module.  Its public runtime data is
an `AffineConjunctionFrame` containing:

- `start`, the fresh wire of the initial true seed; and
- `wires`, the ordered source wires of the semantic conjunction.

The encoded frame contains one unary `start` block, followed by the source
wires in reverse order, followed by the dedicated `UnaryFrameSym.frameEnd`.
Reversal is part of the representation because
`CircuitBuilder.conjunctionGateTrace` is tail-first: it emits the true seed,
then folds sources from the last list element back to the first.

The controller has fixed finite phases independent of `start`, wire values,
and wire count:

1. load `start` into the persistent accumulator counter;
2. emit `const true`;
3. load one unary source wire into a temporary counter;
4. emit `.and source accumulator` with the shared counter-preserving numeral
   encoder;
5. increment the accumulator, clear the temporary wire, and repeat;
6. consume `frameEnd`, normalize scratch state, and reach a redirectable
   `finish` label;
7. execute the standalone halt only in the public standalone interface.

The shared numeral encoder may be extended with the smallest conjunction-only
continuation labels required by this kernel.  Runtime indices must never occur
in the controller label type.

## Encoding and boundary rules

The intended encoding is equivalent to:

```lean
encodeUnaryFrame [frame.start] ++
  (frame.wires.reverse.flatMap encodeUnaryFrameBlock) ++
  [.frameEnd]
```

Every number, including zero, ends in `separator`.  Only `frameEnd` terminates
the variable-length wire family.  The controller rejects `frameEnd` inside the
initial `start` field and treats malformed symbols inside a partially loaded
wire as invalid.  Correctness theorems target well-formed encodings; malformed
behavior remains deterministic but is not promoted into the main semantic
statement.

## Public proof surface

The reusable layer must expose these public names:

```lean
AffineConjunctionFrame
encodeAffineConjunctionFrame
affineConjunctionGateStream
affineConjunctionRevProgram
affineConjunctionLoopCfg
affineConjunctionFinishCfg
affineConjunctionRevSteps
affineConjunction_runToFinish
affineConjunction_run
encodeAffineConjunctionFrame_length
affineConjunctionRev_steps_le
```

`affineConjunctionGateStream frame` must be exactly:

```lean
(CircuitBuilder.conjunctionGateTrace frame.start frame.wires).gates.flatMap
  encodeCircuitGate
```

The contextual theorem stops at a clean `finish` label while preserving an
arbitrary input tail.  The standalone theorem adds only the final halt.  This
split is mandatory so the next row-validity linker does not need to reopen the
conjunction proof.

The exact step function may be recursive over `frame.wires.reverse`.  Its
public complexity theorem must bound the standalone run by
`1000 * (encodeAffineConjunctionFrame frame).length ^ 2 + 2`.  Tight constants
are not a goal; the fixed envelope is intentionally conservative.

## Arithmetic instantiation

Extend `GeneratorValidityStack.lean` with an arithmetic frame whose fields are:

```lean
start := arithmeticValidityFinalStart tm H start
wires := arithmeticValidityConstraintWires tm H start rowBase
```

The arithmetic layer must prove:

- the generic frame stream is byte-for-byte
  `arithmeticValidityFinalConjunctionGateStream`;
- the fixed controller executes that exact stream from arbitrary prior output;
- the arithmetic invocation inherits the generic quadratic bound.

The semantic theorem
`arithmeticValidityFinalConjunctionGateStream_eq_semantic` remains the bridge
to `CircuitBuilder.conjunctionGateTrace`; list equality alone is not accepted
as evidence of TM2 execution.

## Rejected routes

- Proving only equality of generated lists does not establish concrete TM2
  computability.
- Placing a source wire or wire position in a control label violates the fixed
  finite-machine requirement.
- Processing `wires` in forward order produces a different trace from the
  tail-first semantic conjunction.
- Using ordinary separators to terminate the wire family is ambiguous in the
  presence of zero-valued wires; `frameEnd` is required.
- Proving only a standalone halting theorem recreates the previously observed
  composition gap.  A redirectable finish theorem is required now.
- Folding conjunction directly into `affineStackRevProgram` is rejected for
  this milestone because it couples two independently reusable controllers
  and enlarges the proof surface before the conjunction kernel is stable.

## Verification and acceptance

No full-repository build is required.  Acceptance consists of:

1. dependency-scoped builds for the shared encoder, `Conjunction.lean`, and
   `GeneratorValidityStack.lean`;
2. a new `Tests/Chapter_34_PolyBuilder_Conjunction.lean` sentinel checking the
   frame, exact stream, contextual run, standalone run, length, and bound;
3. arithmetic conjunction checks and `#print axioms` entries in
   `Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean`;
4. axiom output containing only the repository-standard logical axioms;
5. no proof placeholders, project axioms, or unfinished-work markers in changed
   proof and test files;
6. `git diff --check` passing before each commit.

## Non-goals

This milestone does not yet connect raw one-hot, halted equality, the stack
family, and the final conjunction into one complete row controller.  It also
does not iterate row validity over the tableau horizon or package the full
Cook--Levin reduction.  Those integrations consume the redirectable interface
delivered here.
