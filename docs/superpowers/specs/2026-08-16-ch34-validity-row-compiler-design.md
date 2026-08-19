# Chapter 34 Cook--Levin Validity-Row Compiler Design

## Goal

Close the next concrete Cook--Levin generator gap: for every verifier witness
`W`, construct one fixed polynomial-time TM2 that maps the raw source word `x`
to the exact delimiter-bearing input consumed by the complete validity-row
controller:

```lean
encodeAffineValidityRowFamilyInput
  (verifierValidityRowFramesByLength W x.length)
```

This milestone is an input compiler theorem.  The already proved semantic row
controller and its quadratic script-time bound are dependencies, not substitutes
for the raw-input theorem.

## Accepted Route

Use the row-first route.  Reuse the existing polynomial-time source compilers
for row ordinals, tableau bases, validity-gate starts, and halted operand
triples.  Add only the missing fixed-parameter field families and a fixed
row-major assembler that converts those synchronized streams into the canonical
`AffineValidityRowFrame` encoding.

The alternatives are deferred:

- compiling the verifier tail first leaves the larger validity family gap
  untouched;
- compiling transition scripts first introduces the most heterogeneous family
  before the simpler row assembler has established the composition pattern;
- proving only a polynomial bound on the mathematical encoding does not provide
  the concrete TM2 required by the standard reduction theorem.

## Architecture

The compiler has two layers.

1. **Field-source layer.**  Fixed polynomial/unary source machines generate
   every runtime-dependent field family from `x`.  Existing machines supply:
   row ordinals, `haltedLeft`, validity-row gate starts, and the three halted
   operands.  New field sources cover the remaining entries of
   `AffineValidityRowFrame`, using constant families or affine polynomial
   progressions as dictated by the frame formula.
2. **Row assembler layer.**  One finite controller consumes the synchronized
   delimiter-bearing field streams and emits, for each row, the leading
   `.tick`, the exact `encodeAffineValidityRowFrame` payload, and finally the
   outer `.frameEnd`.  Runtime row counts and numbers remain data on the tapes;
   none are embedded in finite control.

The public semantic equality identifies the assembler output byte-for-byte
with the canonical family encoding.  Generic TM2 composition then packages the
field sources and assembler into the raw-input
`TM2ComputableInPolyTime` theorem.

## Public Interface

The milestone exposes two reader-facing declarations with names following the
existing generator family:

```lean
theorem verifierValidityRowFamilyInput_eq_canonical ...

noncomputable def
    verifierValidityRowFamilyInput_computableInPolyTime ... :
  Turing.TM2ComputableInPolyTime id id
    (fun x => encodeAffineValidityRowFamilyInput
      (verifierValidityRowFramesByLength W x.length))
```

Helper definitions and exact field equalities remain local to focused
`GeneratorValidityRow...` modules unless they form a reusable source-compiler
surface for later transition compilation.

## Data and Correctness Flow

For a raw word `x`:

```text
x
  -> polynomial unary field streams
  -> fixed synchronized row assembler
  -> encodeAffineValidityRowFamilyInput
       (verifierValidityRowFramesByLength W x.length)
  -> affineValidityRowFamilyRevProgram
  -> verifierValidityGateStream W x
```

Correctness is split into exact field-family equalities, exact row-major
assembly, and the final raw-input polynomial-time composition theorem.  Empty
or zero-sized finite subfamilies must still produce the canonical delimiters;
malformed intermediate streams may halt without a semantic guarantee, because
the composed source machines only supply canonical streams.

## Verification and Commit Boundary

The work follows the repository proof-surface TDD loop:

1. add unresolved `#check` declarations for the two public names and observe
   the focused Lean interface test fail for the missing declarations;
2. implement the smallest exact field sources and assembler needed to satisfy
   those checks;
3. prove byte equality and `TM2ComputableInPolyTime` from raw `x`;
4. run the focused source build and Chapter 34 interface test;
5. audit the new headline theorem with `#print axioms`, scan the touched Cook--
   Levin files for `sorry`, `admit`, and project axioms, and run
   `git diff --check`;
6. create one independently reviewable Chapter 34 feature commit.

This checkpoint does not claim the complete Cook--Levin reduction.  After it
passes, transition-script compilation and tail-script compilation remain before
`compileVerifierBodyScript` can be supplied by a raw-input polynomial-time TM2.
