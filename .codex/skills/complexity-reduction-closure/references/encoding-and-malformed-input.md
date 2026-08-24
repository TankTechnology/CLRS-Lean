# Encoding and Malformed Input

Use this reference when lifting typed decision problems to languages of raw
finite strings.

## Canonical Encoding Contract

Separate these concerns:

- `encodeInstance` gives one public representation;
- `decodeInstance` consumes the complete raw string;
- round trip proves `decodeInstance (encodeInstance I) = some I`;
- `WellFormed I` enforces graph, arithmetic, or record invariants;
- language membership requires both successful decoding and well-formed
  semantic acceptance.

Do not make parser success silently imply all semantic well-formedness unless
that fact is explicitly proved.

## Total Raw Maps

A many-one reduction map is total.  Define both branches:

```lean
def rawMap (input : List SourceSym) : List TargetSym :=
  match decodeSource input with
  | some source => encodeTarget (typedMap source)
  | none => encodeTarget canonicalNoInstance
```

If decoded-but-ill-formed source instances are not source-language members,
either map them to the same no-instance or prove that the typed transformation
also rejects them.

## Canonical No-Instance

Choose a small target instance that is:

- well formed;
- provably outside the target language;
- easy to serialize;
- cheap for the concrete machine to emit.

Prove these facts once and reuse them in parser-rejection branches.

## Raw Membership Proof

Case split on decoding and well-formedness.  Reduce the valid branch to the
typed semantic `iff`; reduce invalid branches to the canonical no-instance
lemma.  If the raw proof repeats parser internals, add a membership
characterization theorem before continuing.
