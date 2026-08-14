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
- `cfgSlotEquivFin_halted_val` through `cfgSlotEquivFin_stackCell_val` replace
  the runtime-height-dependent choice of row-coordinate order with explicit
  halted/label/state/stack offsets;
- `cfgOneHotGroupEquivFin_label_val` through
  `cfgOneHotGroupEquivFin_stackCell_val` similarly fix the exact one-hot group
  order used by both the pure trace and proof-carrying validity builder;
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
  count times `validCfgGateCost`;
- `verifierValidityGateStream_eq` flattens that literal trace into the public
  circuit wire format and proves exact equality with the semantic validity
  builder suffix;
- `verifierRowWire_eq` and its halted/label/state/stack specializations give
  closed global wire indices of the form `row * rowWidth + localOffset`;
- `validCfgGatePolynomial_eval`, `verifierValidityRowCostClock`, and
  `verifierValidityGateCountClock` provide concrete exact-polynomial TM2
  clocks for the single-row and all-row validity loop bounds;
- `validCfgCircuitFamilyGateTrace_gates_eq_flatMap`,
  `verifierPoolGateCount_eq`, and `verifierValidityGateStream_rows_eq` replace
  the recursive all-row trace by an exact row-major flattening whose row `r`
  begins at `tableauInputCount + 2 + r * validCfgGateCost`;
- `validityGateStreamAt` and `verifierValidityGateStream_eq_byLength` prove
  that this entire phase is source-symbol independent and factors through the
  input length, leaving the future concrete serializer with unary input only;
- `arithmeticCfgWires`, `allocateTableauRows_rows_eq_arithmetic`, and
  `validityGateStreamAt_rows_eq` erase the proof-carrying allocator from that
  unary serializer contract: every row is now expressed solely by its closed
  gate start, wire base, and explicit local coordinate arithmetic;
- `verifierCircuitValidityPrefix_eq` and
  `verifierCircuitValidityPrefix_isPrefix` advance the verified serialized
  circuit prefix through the complete canonical row-validity phase.
- `sequentialExactlyOneGateStream` is the first concrete validity serializer:
  on a unary clock of length `n` it emits byte-for-byte the encoding of
  `exactlyOneGateTrace 0 (List.range n)`;
- `sequentialExactlyOneRev_run` proves the exact run of the concrete
  three-counter prepend machine, including its final halted configuration and
  output, rather than inferring computation from an output-size theorem;
- `sequentialExactlyOneRev_computableInPolyTime` and
  `sequentialExactlyOneGateStream_computableInPolyTime` package the reversed
  machine and its verified final reversal as genuine quadratic-time TM2s.
- `affineSequentialExactlyOneGateList_eq_trace` lifts the pure arithmetic
  trace to arbitrary runtime gate and source-wire bases;
- `affineSequentialExactlyOneRev_runFrom` proves the same concrete machine can
  run inside an existing output context, preserve its suffix, clear every
  unary register, and emit exactly the canonical affine semantic trace;
- `affineSequentialExactlyOneRev_steps_le` bounds that contextual run by
  `200 * (start + rowBase + count + 1)^2`.
- `arithmeticCfgOneHotGroupWires_eq_affine` gives closed consecutive source
  intervals for all label, state, stack-height, and stack-cell groups;
- `arithmeticCfgOneHotGroupRev_runFrom` instantiates the concrete runner for
  any such semantic group, while
  `arithmeticRawOneHotGateStream_eq_affineFamily` proves their canonical raw
  row trace is exactly the ordered concatenation of affine streams.
- `validityRowGateStreamAt_eq_rawOneHot_append_post` freezes the exact
  acceptance boundary after that completed phase: the remaining row suffix is
  now explicitly limited to halted/label equality, stack canonicality, and the
  final conjunction.
- `affineBoolEqRev_runFrom` closes the next reusable validity primitive: for
  arbitrary gate/source indices and an arbitrary existing output suffix, the
  concrete three-counter program emits exactly
  `CircuitBuilder.boolEqGateTrace`, clears all scratch, and halts;
- `affineBoolEqRevSteps` gives its exact cost
  `27 * start + 11 * left + 11 * right + 85`, while
  `affineBoolEqRev_steps_le` supplies a uniform quadratic envelope.
- `arithmeticHaltedMatchGateStream_eq_semantic` instantiates that serializer
  at the real arithmetic row wires after a closed raw-one-hot gate count;
- `arithmeticValidityPostOneHot_eq_haltedMatch_append_post` advances the exact
  completed boundary by five gates, leaving only stack canonicality and the
  final conjunction in the row-local suffix.
- `suffixOrGateTrace_output_eq`, `cellValidityGateTrace_output_eq`, and
  `stackValidityFamilyGateTrace_output_eq` remove the remaining recursive
  output lookups from stack canonicality: every active mask and cell
  constraint now has a closed affine wire index.

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
pool are now closed.  The validity phase now has exact gate traces for every
primitive, cell, stack, row, and finite row family.  Its flattened wire-format
stream is proved to agree exactly with the semantic builder, and the resulting
list is a literal prefix of the final verifier encoding through the complete
validity phase.  The first real serializer inside that phase is also closed:
the zero-based sequential exactly-one primitive has an exact-output theorem,
an exact-run theorem, and a quadratic TM2 bound.  Its affine-base lift is now
also closed for arbitrary runtime `start`, `rowBase`, `count`, and pre-existing
output suffix.  This does **not** yet close the whole single-row validity
serializer.  The next cut instantiates the contextual theorem for the label,
state, height, and stack-cell one-hot groups and composes those runs.  Output
orientation, natural-number serialization, input parking/restoration,
fixed-suffix appending, and exact agreement with the semantic allocators are
already closed independently.

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
12. **Using `Fintype.equivFin` on a runtime-height-dependent type.** A fresh
    classical enumeration of `CfgSlot tm H` or `CfgOneHotGroup tm H` for each
    runtime `H` is a semantic numbering, not a uniform algorithm available to
    one fixed TM2.  The accepted replacement uses explicit sum/product
    coordinates and keeps only the fixed verifier's finite stack enumeration
    in finite control.
13. **Treating phase zero as an ordinary later scan phase.** The first
    exactly-one update uses the two false seeds and has a different three-gate
    chunk from every later phase.  Generalizing the later-loop lemma to
    `phase = 0` silently asks for the wrong semantic stream.  The accepted
    internal interface carries `0 < phase`, while the public positive run
    enters it at phase one after proving the special first block separately.
14. **Flattening every Boolean-equality phase into the already large main
    label enumeration.** The automatically derived `Fintype` instance then
    exceeds the elaborator's nested-sum synthesis depth.  The accepted route
    keeps one main `boolEq` constructor whose argument is a separate finite
    phase type; this changes only the representation of finite control, not
    the program's runtime data or transition semantics.

The row-validity attack has now also closed the arithmetic stack ordinal,
per-stack block start, suffix-OR output, blank-symbol row wire, leading-not
output, and five-gate XNOR start for every fixed stack/cell coordinate.
`arithmeticStackCellBoolEqRev_runFrom` executes that exact XNOR stream with a
quadratic counter bound.  This deliberately does not claim that the suffix-OR
or leading-not streams are generated yet; those two iterators remain explicit
acceptance gaps before the whole stack family can be called executable.

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
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolEq
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader
lake build +CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidity
lake env lean Tests/Chapter_34_PolyBuilder_Clock.lean
lake env lean Tests/Chapter_34_PolyBuilder_ExactPolynomialClock.lean
lake env lean Tests/Chapter_34_PolyBuilder_Reverse.lean
lake env lean Tests/Chapter_34_PolyBuilder_UnaryIndex.lean
lake env lean Tests/Chapter_34_PolyBuilder_NatEncoding.lean
lake env lean Tests/Chapter_34_PolyBuilder_InputGate.lean
lake env lean Tests/Chapter_34_PolyBuilder_CircuitPrefix.lean
lake env lean Tests/Chapter_34_PolyBuilder_BoolPool.lean
lake env lean Tests/Chapter_34_CookLevin_ExactlyOneSerializer.lean
lake env lean Tests/Chapter_34_CookLevin_AffineExactlyOne.lean
lake env lean Tests/Chapter_34_CookLevin_AffineBoolEq.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorValidityOneHot.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorValidityBoolEq.lean
lake env lean Tests/Chapter_34_CookLevin_ValidityIndices.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorClock.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorHeader.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorValidity.lean
lake env lean Tests/Chapter_34_CookLevin_ExplicitCfgSlotEncoding.lean
lake env lean Tests/Chapter_34_CookLevin_ExplicitOneHotGroupEncoding.lean
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
