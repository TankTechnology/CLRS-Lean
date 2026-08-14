# Chapter 34 Cook--Levin Generator Attack

Date: 2026-08-14

## Exact Remaining Theorem Boundary

The semantic Cook--Levin construction and the target-language verifier are
closed. The remaining main-theorem boundary is the concrete machine-level
implementation of

```lean
fun x => encodeCircuit (Turing.CookLevin.verifierCircuit W x)
```

followed by the existing semantic bridge to `GeneralCircuitSAT`. Completion
requires all of the following public declarations, with no placeholder or
project axiom:

- `Turing.CookLevin.verifierCircuitProgram`;
- `Turing.CookLevin.verifierCircuitProgram_outputs`;
- `Turing.CookLevin.verifierCircuitTime`;
- `Turing.CookLevin.verifierCircuitSteps_le`;
- `Turing.CookLevin.verifierCircuitComputableInPolyTime`;
- `Turing.CookLevin.polyTimeVerifiable_reducible_to_generalCircuitSAT`;
- `generalCircuitSAT_npHard` and `generalCircuitSAT_npComplete`.

The interface was run in RED before implementation. The failures were exactly
these missing generator/reduction declarations; the already completed
Cook--Levin semantics and `GeneralCircuitSAT ∈ NP` declarations remained green.

## Foundation Closed in This Attack

The bounded-builder foundation now supplies the missing clock, output
orientation, and gate-index layers:

- `unitClock_computableInPolyTime` implements the linear clock;
- `squareUnitClock_computableInPolyTime` implements one concrete quadratic
  expansion;
- `iteratedSquareClock_computableInPolyTime d` composes these machines and
  produces exactly `n ^ (2 ^ d)` unit tokens;
- `polynomial_eval_le_polynomialClock_length` proves that the clock derived
  from any fixed `Polynomial Nat` dominates its value on nonempty inputs;
- `polynomialClock_computableInPolyTime` packages that dominating clock as a
  concrete polynomial-time TM2.
- `sentinelInput_computableInPolyTime` appends one unique sentinel using a
  concrete builder with an exact `3n + 4` run;
- `tuplePower_computableInPolyTime d` enumerates all width-`2 ^ d` perfect
  tuples using verified ordered-pair loops;
- `tuplePrefixMatches_count` proves that the prefix/sentinel filter selects
  exactly `n ^ k` tuples, including `n ^ 0 = 1` when the input is empty;
- `exactMonomialClock_computableInPolyTime k` produces exactly `n ^ k`
  tokens;
- `exactPolynomialClock_length` and
  `exactPolynomialClock_computableInPolyTime` provide the formerly missing
  concrete TM2 whose output length is exactly `p.eval n` for every input;
- `VerifierWitness.alphabetFintype` recovers source-alphabet finiteness from
  the finite pair-encoding alphabet already carried by the verifier machine;
- the certificate, verifier-input, horizon, height, gate-bound, and
  encoding-bound clock wrappers instantiate the exact clock without adding a
  typeclass premise to the universal reduction;
- `cfgBitPolynomial_eval` derives an exact affine polynomial for one semantic
  tableau-row width, and `verifierTableauInputPolynomial_eval` composes it with
  the exact verifier height and horizon;
- `verifierCircuitHeader_computableInPolyTime` emits exactly
  `encNat (verifierCircuit W x).inputCount`, closing the serialized circuit
  header rather than merely encoding its published upper bound;
- `reverse_computableInPolyTime` gives a verified linear-time finalization
  pass for the builder language's prepend-only output stack;
- `unaryIndexRev_outputs` proves the exact reversed stream contract for all
  unary indices `0, ..., n - 1`;
- `unaryIndexRev_polyBound` bounds that concrete streamer quadratically;
- `unaryIndexStream_computableInPolyTime` composes it with reversal and thus
  computes the forward Boolean wire-reference stream;
- `lengthEncoding_computableInPolyTime` directly serializes an arbitrary
  finite input length as the canonical `encNat` block;
- `circuitIndexStream_computableInPolyTime` maps the verified Boolean index
  stream into the actual `CircuitSym` alphabet and proves equality with
  `encNat 0 ++ ... ++ encNat (n - 1)`.
- `inputGateStream_computableInPolyTime` emits the complete serialized family
  `.input 0, ..., .input (n - 1)` with a concrete quadratic-time TM2;
- `allocateCfgInputs_gates_eq` and `allocateTableauRows_gates_eq` expose the
  exact semantic gate order of the proof-carrying allocators;
- `verifierInputGateStream_eq` proves that the concrete input-gate streamer is
  byte-for-byte the encoding of `(verifierRows W x).builder.gates`.
- `circuitInputPrefix_computableInPolyTime` parks and restores its unit clock
  while producing `encNat n ++ inputGateStream n` in one concrete quadratic
  run;
- `verifierCircuitInputPrefix_isPrefix` proves that the instantiated stream is
  a literal list prefix of `encodeCircuit (verifierCircuit W x)`, while
  `verifierCircuitInputPrefix_computableInPolyTime` supplies its concrete TM2.
- `appendBoolPool_computableInPolyTime` appends the canonical false/true tags
  to any existing circuit prefix with a concrete linear-time machine;
- `allocateBoolWirePool_gates_eq` fixes the semantic gate order, and
  `verifierCircuitPoolPrefix_isPrefix` advances the verified literal encoding
  prefix through the shared constant-pool allocation.
- `CircuitBuilder.input_gates`, `not_gates`, `and_gates`, and `or_gates`
  expose the exact primitive gate appended by each proof-carrying constructor;
- `boolEqGateTrace`, `eq_gates_eq`, and `eq_wire_eq_trace` fix all five XNOR
  gates and their predecessor indices;
- `conjunctionGateTrace`, `conjunction_gates_eq`, and
  `conjunction_wire_eq_trace` fix the true seed and tail-first conjunction
  gates used to collect constraint outputs;
- `exactlyOneGateTrace`, `exactlyOne_gates_eq`, and
  `exactlyOne_wire_eq_trace` fix the complete tail-first `3n+4` gate sequence
  used by every one-hot validity constraint;
- `suffixOrGateTrace`, `activeMask_gates_eq`, and
  `activeMask_output_eq_trace` fix the active-stack-cell mask gate order and
  every position-aligned output wire.
- `cellValidityGateTrace` and `buildCellValidity_gates_eq` compose one
  negation with the five-gate XNOR trace, fixing all `6H` per-stack cell gates
  and their outputs;
- `exactlyOneFamilyGateTrace` lifts the single-group trace to an arbitrary
  ordered finite family, and `rawOneHotGateTrace` identifies that family with
  every label, state, height, and cell-symbol one-hot group in a row;
- `buildRawOneHot_gates_eq` and `buildRawOneHot_output_eq_trace` close the
  complete raw-decodability gate suffix and its group outputs;
- `stackValidityFamilyGateTrace`, `buildStackValidityFamily_gates_eq`, and
  `buildStackValidityFamily_output_eq_trace` compose each ordered stack's
  suffix-OR active mask with all `6H` cell-validity gates, fixing the complete
  stack-validity family suffix and every cell constraint output;
- `canonicalValidityGateTrace`, `validCfgCircuit_gates_eq`, and
  `validCfgCircuit_wire_eq_trace` close the complete single-row validity
  suffix: raw one-hot, halted/none-label XNOR, every stack constraint, and the
  final tail-first conjunction.  `canonicalValidityGateTrace_length` also
  recovers the existing exact affine cost from the literal trace;
- `validCfgCircuitFamilyGateTrace`, `validCfgCircuitFamily_gates_eq`, and
  `validCfgCircuitFamily_output_eq_trace` lift that exact suffix across every
  public tableau row in finite-index order, with total length equal to the row
  count times `validCfgGateCost`.

The exact clock handles empty inputs and nonzero constant terms uniformly.
The older domination lemma still retains its explicit nonempty-input premise,
but the generator no longer needs a separate finite-control branch merely to
recover exact polynomial dimensions.

## Accepted Construction Route

The generator will be a streaming TM2 whose finite control embeds only data
from the fixed verifier `W`. Runtime-sized values remain unary counters or
bounded stack data. The implementation phases are:

1. preserve and scan the public input while constructing polynomial clocks for
   the certificate, horizon, height, and gate-index envelopes;
2. stream tableau-input gates, the shared Boolean pool, row-validity gates,
   transition gates, and the three boundary families in the same order as the
   existing `CircuitBuilder` construction;
3. maintain the current gate index in unary and serialize every predecessor
   reference directly in the established `CircuitSym` wire format;
4. stream the final conjunction and output marker;
5. prove one output theorem per phase and compose them into exact equality with
   `encodeCircuit (verifierCircuit W x)`;
6. package the polynomial runtime, universal reduction, NP-hardness, and
   NP-completeness wrappers.

The exact polynomial-value clock, circuit header, initial tableau input-gate
family, their combined serialization prefix, and the two-gate shared Boolean
pool are now closed.  The validity phase now has exact gate traces for its
three repeated primitives: equality, exactly-one, and suffix-OR active masks.
The six-gate per-cell family and the complete raw one-hot family are now also
closed, as is the ordered family that combines every stack's active mask and
cell constraints.  The complete row-validity suffix is now closed as well.
Its finite family across all tableau rows is now closed too.  The next cut
connects this literal family to a polynomial-time validity-stream serializer,
advancing the already verified input-and-pool prefix through the complete
validity phase. Output orientation, natural-number serialization, input
parking/restoration, fixed-suffix appending, and exact agreement with the
semantic allocators are already closed independently.

## Known Failed or Rejected Routes

1. **Deriving computation from output length.** A polynomial output-size
   theorem does not imply polynomial-time computability, or even computability
   for an arbitrary function.
2. **A membership-selected constant circuit.** Selecting `true` or `false`
   from `x ∈ L` is noncomputable and is not the Cook--Levin construction.
3. **Putting the generator into `VerifierWitness`.** This merely assumes the
   theorem that Cook--Levin must prove and makes the reduction circular.
4. **Weakening `PolyTimeReducible`.** Replacing its concrete TM2 obligation by
   a size bound changes the project's complexity model and invalidates the
   theorem statement.
5. **Unbounded input in finite control.** A label carrying `x`, a tableau row,
   or a runtime gate position cannot inhabit the finite control of `FinTM2`.
   Such data must live on bounded stacks or unary counters.
6. **Using only the existing quadratic macro.** A verifier witness may carry
   a polynomial of any fixed degree. One nested loop cannot justify the
   universal theorem. `PolyBuilder.Clock` closes this specific gap.
7. **Treating the clock as the circuit generator.** A long enough unit stream
   proves only that sufficient iterations exist; it does not compute gate tags,
   input-dependent boundary symbols, or unary predecessor indices.
8. **Relying on Lean/native evaluation as the machine.** Executability of the
   meta-level definition does not furnish the concrete `FinTM2.outputsFun`
   witness required by `TM2ComputableInPolyTime`.
9. **Treating a dominating clock as an exact dimension.** The current
   `polynomialClock p x` has length
   `coefficient * |x| ^ (2 ^ natDegree p)`, which only bounds `p(|x|)` on
   nonempty inputs.  Substituting that value for the exact horizon, height, or
   gate indices changes the generated circuit and cannot prove equality with
   `encodeCircuit (verifierCircuit W x)`.  This route remains rejected;
   `exactPolynomialClock` is the accepted replacement.
10. **Encoding `verifierCircuitInputBound` as the circuit header.** That
    polynomial is only an upper bound on the semantic tableau input count.
    Writing it as `Circuit.inputCount` would change the encoded circuit even
    though every allocated input gate still fits.  The accepted route uses
    `verifierTableauInputPolynomial`, whose evaluation is proved exactly equal
    to `tableauInputCount`.
11. **Concatenating independently generated streams after consuming the
    input.** Ordinary TM composition gives the second phase only the first
    phase's output, not the original clock.  It therefore cannot justify
    `header ++ gates` by simply composing the already separate machines.  The
    accepted route scans the clock into a work stack, emits the header, restores
    the clock exactly, and then enters a relabeled copy of the verified gate
    streamer.

## Focused Acceptance Mechanism

During generator development, use only dependency-scoped checks:

```text
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Clock
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryIndex
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.NatEncoding
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputGate
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.CircuitPrefix
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPool
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader
lake env lean Tests/Chapter_34_PolyBuilder_Clock.lean
lake env lean Tests/Chapter_34_PolyBuilder_ExactPolynomialClock.lean
lake env lean Tests/Chapter_34_PolyBuilder_Reverse.lean
lake env lean Tests/Chapter_34_PolyBuilder_UnaryIndex.lean
lake env lean Tests/Chapter_34_PolyBuilder_NatEncoding.lean
lake env lean Tests/Chapter_34_PolyBuilder_InputGate.lean
lake env lean Tests/Chapter_34_PolyBuilder_CircuitPrefix.lean
lake env lean Tests/Chapter_34_PolyBuilder_BoolPool.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorClock.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorHeader.lean
lake env lean Tests/Chapter_34_CookLevin_ExactlyOneGateTrace.lean
lake env lean Tests/Chapter_34_CookLevin_ValidityGateTrace.lean
lake env lean Tests/Chapter_34_CookLevin_Interface.lean
python3 scripts/check_repository.py
git diff --check
```

The Cook--Levin interface is green only after all generator and
NP-completeness names above resolve. The final trust gate also prints axioms
for the generator computation theorem, the universal reduction, and
`generalCircuitSAT_npComplete`, and rejects `sorryAx` or project axioms. No
full-repository build belongs to this attack checkpoint.
