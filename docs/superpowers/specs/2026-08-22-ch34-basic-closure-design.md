# Chapter 34 Basic Closure Design

## Goal

Use the two-day time box to close the largest remaining textbook discontinuity
after Cook--Levin: connect the honest serialized `GeneralCircuitSAT` language to
the existing SAT language.  The work must leave Chapter 34 in a truthful,
buildable state even if the concrete reduction machine or SAT NP-membership
wrapper does not fit in the time box.

This design narrows the broader Chapter 34 closure design from 2026-08-15.  It
does not replace that full design; it defines the accepted stopping point for
the present basic-closure pass.

## Chosen Approach

Translate `GeneralCircuit` directly to a Boolean formula.  Give every declared
input variable index `i` the formula variable `i`, and give gate `j` the formula
variable `c.inputCount + j`.  The formula asserts the selected output variable
and conjoins one consistency equation for every gate:

```text
input i       : gate(j) <-> input(i)
constant b    : gate(j) <-> b
not source    : gate(j) <-> not gate(source)
and left right: gate(j) <-> gate(left) and gate(right)
or left right : gate(j) <-> gate(left) or gate(right)
```

The translation is preferable to converting through the legacy `Gate` model.
That model only connects each gate to the immediately preceding wires, whereas
`GeneralCircuit` permits arbitrary earlier dependencies.  A routing conversion
would obscure the textbook argument and add unnecessary proof surface.

## Module Boundaries

The new proof is split into small files:

- `GeneralCircuit/ToSAT/Semantics.lean` defines the formula translation and
  proves satisfiability equivalence for well-formed general circuits.
- `GeneralCircuit/ToSAT/Encoding.lean` defines the total serialized map,
  handles malformed circuit strings as SAT no-instances, proves exact language
  semantics, and proves a polynomial output-length bound.
- `GeneralCircuit/ToSAT/Machine.lean` is reserved for the fixed TM2 computing
  the serialized map.  It is imported only when its exact output and runtime
  proofs compile.
- `GeneralCircuit/ToSAT.lean` is the stable public facade.
- `Tests/Chapter_34_GeneralCircuit_ToSAT.lean` fixes the intended public theorem
  surface and audits headline declarations.

The existing `CircuitSAT.lean` formula syntax, evaluator, prefix encoding, and
decoder remain canonical.  The new modules reuse them rather than introducing
a second SAT representation.

## Acceptance Levels

### Required basic closure

The pass is useful and may be committed when all of the following compile:

- a direct `generalCircuitToFormula` definition;
- `generalCircuitSatisfiable_iff_satisfiable_generalCircuitToFormula`;
- a total raw-input map from `List CircuitSym` to `List FormulaSym`;
- exact membership equivalence for canonical and malformed encodings;
- a fixed polynomial output-length bound;
- public interface tests, no unfinished proof markers, and accurate status
  documentation.

This level is a semantic-and-size textbook bridge.  It must not be described as
`PolyTimeReducible`, NP-hardness of SAT, or SAT NP-completeness.

### Preferred machine closure

If the fixed transducer and its runtime proof fit in the time box, expose:

```lean
generalCircuitSAT_reducible_to_SAT :
  PolyTimeReducible GeneralCircuitSAT SAT

sat_npHard : NPHard SAT
```

The NP-hardness wrapper follows from `generalCircuitSAT_npHard` and the new
reduction; it contains no additional reduction construction.

### Stretch closure

Only after the preferred level is green, add a concrete polynomial-time SAT
assignment verifier and expose:

```lean
sat_polyTimeVerifiable : PolyTimeVerifiable SAT
sat_npComplete : NPComplete SAT
```

No status document may advertise the stretch result unless both the verifier
machine and the public theorem compile.

## Malformed Inputs

`GeneralCircuitSAT` rejects every string for which `decodeCircuit` returns
`none`.  The total reduction therefore maps malformed circuit strings to the
canonical encoding of `Formula.const false`.  Successfully decoded circuits
map to the encoding of `generalCircuitToFormula c`.  A decoded but ill-formed
circuit also maps to false, matching `GeneralCircuitSatisfiable`.

This makes the language equivalence total and avoids placing decoder or
well-formedness premises on the public reduction statement.

## Verification

Development follows a red-green interface loop.  Each public theorem name is
first added to `Tests/Chapter_34_GeneralCircuit_ToSAT.lean` and observed failing
because the declaration is absent.  After every proof slice, run the focused
module build and interface test.  Before committing a claimed acceptance level,
run the repository policy check, Chapter 34 build, focused tests, unfinished
marker scan, `git diff --check`, and the full `CLRSLean` build.

## Explicitly Deferred Scope

The present pass does not implement general graph-plus-`k` CLIQUE,
VERTEX-COVER, HAM-CYCLE, TSP, or SUBSET-SUM.  It records those items as the
remaining Section 34.5/full-closure boundary.  Chapter 34 remains `partial`
unless later work closes those named problems; the basic closure may instead be
described as completing Cook--Levin and the semantic GeneralCircuitSAT-to-SAT
textbook bridge.
