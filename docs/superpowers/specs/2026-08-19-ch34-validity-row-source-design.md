# Chapter 34 Validity-Row Source Design

Date: 2026-08-19

## Goal

Close the first remaining machine-level boundary in the Cook--Levin proof:
construct a fixed polynomial-time TM2 which maps the original verifier input
`x` to the exact canonical runtime input consumed by the complete validity-row
controller, and then compose that source with the existing controller to obtain
a polynomial-time machine for `verifierValidityGateStream W`.

The milestone ends with these public declarations:

```lean
noncomputable def verifierValidityRowTailOperandFrames_computableInPolyTime

def verifierValidityRowFamilyInput

theorem verifierValidityRowFamilyInput_eq_canonical

noncomputable def verifierValidityRowFamilyInput_computableInPolyTime

noncomputable def verifierValidityRowFrames_computableInPolyTime

noncomputable def verifierValidityGateStream_computableInPolyTime
```

Every equality is byte-for-byte and order-sensitive.  A length equality,
permutation statement, or multiset statement is not an acceptable substitute.

## Scope

This milestone includes only the raw-input compiler for all validity rows and
its composition with the established validity-row gate controller.  It does
not include transition-family script compilation, post-transition verifier-tail
script compilation, the complete `cookLevinMap` TM2, `NPHard` or `NPComplete`
for `GeneralCircuitSAT`, general graph-plus-`k` `CLIQUE`, or Section 34.5.

## Existing foundation to reuse

The implementation must reuse the following established layers rather than
reprove their gate semantics:

- `verifierValidityRowSeedFrames_computableInPolyTime` for the raw-input,
  row-major `(height, start, rowBase)` seed stream;
- the structured one-hot row source and compact-frame expander underlying
  `verifierValidityRowOneHotOperands_computableInPolyTime`;
- the affine halted-triple formulas and exact row-major theorem in
  `GeneratorValidityRowHaltedOperands`;
- the runtime-height stack and cell sources in
  `AffineValidityTailRowFamilySource` and
  `AffineValidityTailStackFamilySource`;
- `arithmeticFinalConjunctionWires_eq_semantic` and the one-hot output-family
  source in `GeneratorValidityRowTailOperands`;
- `affineValidityRowFamilyGateStream_computableInPolyTime` for the downstream
  gate serialization.

Reuse means embedding, relabeling, or composing the existing concrete machines
and transporting their exact-run and runtime theorems.  Merely reusing a
mathematical target definition while replacing the machine with an oracle
premise does not satisfy this design.

## Architecture

The approved data flow is:

```text
original x
  -> canonical validity-row seed compiler
  -> delimiter-preserving, row-at-a-time operand source
  -> encodeAffineValidityRowFamilyInput
  -> existing validity-row family gate controller
  -> verifierValidityGateStream
```

The source consumes one canonical `ValidityRowSeed` at a time.  For each seed
it emits the exact stream owned by `encodeAffineValidityRowFrame`:

```text
tick
  ++ encodeAffineExactlyOneFamily frame.oneHotFrames
  ++ frameEnd
  ++ encodeUnaryFrame [frame.haltedStart, frame.haltedLeft, frame.haltedRight]
  ++ frameEnd
  ++ encodeAffineValidityTailFrame frame.tailFrame
```

After the final row it emits the outer `frameEnd` required by
`encodeAffineValidityRowFamilyInput`.

The implementation must remain row-at-a-time.  It must not concatenate three
independently flattened whole-family outputs and call the result an interleave:
the one-hot, halted, and tail fragments have different row-boundary structures,
and `comp_scratch` supplies sequential composition rather than a three-way zip.

All input-dependent quantities, including height, row count, gate starts,
tableau bases, and wire indices, remain unary tape data.  Only verifier-fixed
stack tags, alphabet widths, and control phases may occur in finite control.

## Components

### 1. Final-conjunction source linker

Complete the missing continuous source for one validity-row final conjunction.
It emits, in this exact order:

1. outputs of the row's raw one-hot groups;
2. the halted/none-label equality output;
3. the reverse-ordered outputs of every fixed stack and runtime cell block;
4. `arithmeticValidityFinalStart`;
5. the conjunction terminator.

The semantic target is the ordered list identified by
`arithmeticFinalConjunctionWires_eq_semantic`.  The implementation shall reuse
the existing output-family and runtime-stack source controllers and expose an
exact `EvalsToInTime` theorem plus a polynomial bound in its encoded invocation
length.

### 2. Complete validity-tail operand source

Connect the fixed-stack/runtime-cell source to the final-conjunction linker
without an intermediate halt.  Lift the exact one-row theorem to the canonical
row-seed family and expose
`verifierValidityRowTailOperandFrames_computableInPolyTime` from the original
input `x`.

The output must equal:

```lean
(verifierValidityRowFramesByLength W x.length).flatMap
  (fun frame => encodeAffineValidityTailFrame frame.tailFrame)
```

with both the stack-family boundary and final-conjunction boundary preserved.

### 3. Delimiter-preserving row source

Build one finite controller that consumes the canonical seed stream and emits
complete rows in order.  It reuses redirectable one-row components for one-hot,
halted, stack/cell, and conjunction operands, inserts the two internal
`frameEnd` bytes and the leading row `tick`, clears all persistent counters at
row boundaries, and emits the final outer `frameEnd`.

The public semantic function is the output of this concrete source pipeline:

```lean
def verifierValidityRowFamilyInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List UnaryFrameSym
```

It must not be defined as the canonical target followed by an unrelated
computability proof.  Its principal correctness theorem is:

```lean
theorem verifierValidityRowFamilyInput_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    verifierValidityRowFamilyInput W x =
      encodeAffineValidityRowFamilyInput
        (verifierValidityRowFramesByLength W x.length)
```

The byte-level `verifierValidityRowFamilyInput_computableInPolyTime` object is
obtained only from the raw seed compiler, the concrete row source, and standard
composition/reversal combinators.  The same concrete machine is also packaged
under the structured interface:

```lean
noncomputable def verifierValidityRowFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Turing.TM2ComputableInPolyTime id
      encodeAffineValidityRowFamilyInput
      (fun x => verifierValidityRowFramesByLength W x.length)
```

This view is required for type-correct composition with the existing
validity-row controller; it does not introduce a second implementation.

### 4. Downstream gate-stream composition

Compose `verifierValidityRowFrames_computableInPolyTime` with
`affineValidityRowFamilyGateStream_computableInPolyTime`, rewrite using
`verifierValidityRowFamilyInput_eq_canonical` and the existing validity-row
semantic theorem, and expose:

```lean
noncomputable def verifierValidityGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Turing.TM2ComputableInPolyTime id id
      (verifierValidityGateStream W)
```

No oracle premise may remain in this declaration.

## Correctness invariants

The proof is organized around the following invariants:

- the unconsumed source is exactly the encoding of the remaining row seeds;
- the output accumulator is the reverse of the completed canonical row prefix;
- all three unary counters are empty at every public row boundary;
- component exits retain the exact tail expected by the next component;
- row order agrees with `verifierValidityRowFramesByLength`;
- one-hot group order agrees with `cfgOneHotGroupEquivFin`;
- stack order agrees with the verifier's fixed `FinTM2.K` enumeration;
- conjunction sources agree in list order, not merely extensionally.

The zero-row, zero-height, and empty fixed-stack-family cases use the same
public run theorem as the nonempty cases.

## Malformed source behavior

The source machine is total.  Unexpected separators, missing `frameEnd`
markers, truncated unary fields, and extra symbols enter an explicit invalid
phase and halt.  The headline `outputsFun` theorem is required only for the
canonical seed stream produced from `x`, but malformed inputs must not create
nonterminating control paths.

## Runtime argument

Each component first receives an exact step-count theorem.  The combined
source count is the sum of:

- seed loading and row-boundary overhead;
- one-hot structured-row generation and frame expansion;
- halted-triple generation;
- runtime-height stack/cell generation;
- final-conjunction source generation;
- counter clearing and final halt.

The component bounds are weakened to one explicit polynomial in the canonical
seed/source encoding length.  Composition with the existing exact-polynomial
seed compiler then yields a polynomial in `x.length`.  The proof must not infer
polynomial time solely from the already established polynomial output length.

## Verification and commit boundaries

The work is delivered in four independently auditable commits:

1. `feat(ch34): link validity final conjunction source`
2. `feat(ch34): compile validity row tail operands`
3. `feat(ch34): compile complete validity row input`
4. `feat(ch34): compute verifier validity gate stream`

Every commit must pass its focused interface tests, direct source compilation,
axiom audit, unfinished-declaration scan, `git diff --check`, and
`lake build CLRSLean.Chapter_34`.  The final commit must additionally pass
`lake build CLRSLean` and `python3 scripts/check_repository.py`.

The audited public theorems may depend only on the repository's standard
`propext`, `Classical.choice`, and `Quot.sound` axiom surface.
