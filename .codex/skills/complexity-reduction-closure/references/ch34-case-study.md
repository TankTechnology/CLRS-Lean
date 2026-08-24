# Chapter 34 Case Study

This reference records reusable lessons from the closed §34.4 chain.

## Cook--Levin

The tableau circuit first established:

- circuit well-formedness;
- semantic satisfiability equivalence;
- gate, input, and serialized encoding bounds.

Those facts produced a size-certified semantic reduction, not yet a repository
`PolyTimeReducible`.  The missing bridge was a fixed polynomial-time machine
computing the exact complete circuit encoding from the original verifier input.
Once that bridge existed, a thin public theorem packaged Cook--Levin,
GeneralCircuitSAT NP-hardness, and GeneralCircuitSAT NP-completeness.

## GeneralCircuitSAT to SAT

The semantic formula construction and cubic output bound were closed before
the concrete machine.  Malformed and decoded-but-ill-formed circuits mapped to
a canonical false formula, so the raw theorem covered every source string.
The later exact machine reused the same raw map and upgraded the bridge to a
genuine polynomial-time reduction.

## General CLIQUE

The public problem uses an honest graph-plus-target-size encoding rather than
the specialized occurrence graph.  Its layers were separated into instance
semantics, unique encoding, certificate semantics, verifier machine, occurrence
reduction semantics, raw reduction encoding, reduction machine, NP packaging,
and the final textbook-facing alias.

## Rejected Shortcuts

- Polynomial output length is not polynomial-time computability.
- A clock is not a serializer.
- Native Lean evaluation is not a fixed machine witness.
- A specialized occurrence language is not general CLIQUE.
- A semantic existential alone is not an NP verifier.
- A theorem restricted to hidden well-formed raw inputs is not a total
  language reduction.

## Reusable Public Spine

For later §34.5 problems, reuse:

```text
CLIQUE_npComplete
  -> concrete CLIQUE-to-target reduction
  -> NPHard.of_reducible
  -> independently proved target PolyTimeVerifiable
  -> target NPComplete
```

Do not replay Cook--Levin for each target problem.
