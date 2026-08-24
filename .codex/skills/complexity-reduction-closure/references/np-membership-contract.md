# NP Membership Contract

Use this reference when proving that an honestly serialized target language is
in NP.

## Certificate Triad

### Exact checker semantics

Define a total Boolean checker on raw strings and prove an exact theorem:

```lean
checker certificate input = true ↔
  ∃ decodedInstance decodedCertificate,
    decodeInstance input = some decodedInstance ∧
    decodeCertificate certificate = some decodedCertificate ∧
    ValidCertificate decodedInstance decodedCertificate
```

Include malformed instances and malformed certificates in the theorem.  They
must evaluate to rejection without extra hypotheses.

### Polynomial certificate length

Prove both directions needed by the repository verifier interface:

- an accepted certificate implies target membership;
- target membership supplies an encoded accepted certificate whose raw length
  is bounded by an explicit polynomial in input length.

Bound the encoded certificate, not only the number of mathematical witness
elements.

### Fixed polynomial-time checker

Construct a fixed machine computing the same Boolean `checker`.  Prove its
exact result and a runtime polynomial in the combined raw input size required
by the local `PolyTimeVerifiable` interface.

## Packaging

Only after the triad is closed, build:

```lean
target_polyTimeVerifiable : PolyTimeVerifiable TargetLanguage
target_mem_ClassNP : TargetLanguage ∈ ClassNP TargetSym
```

An executable Lean `decide`, a native function, or a semantic existential
alone is not a concrete NP verifier in a machine-based complexity model.
