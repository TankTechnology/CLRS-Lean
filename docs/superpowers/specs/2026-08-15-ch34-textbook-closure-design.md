# Chapter 34 Textbook Closure Design

## Goal

Complete the main theorem chain advertised for CLRS Chapter 34 without
formalizing open complexity-theory questions.  The completion boundary is a
concrete Cook--Levin many-one reduction, honest general graph-plus-`k` CLIQUE,
and the selected Section 34.5 decision-problem chain.  Every reduction counted
as complete must have semantic correctness and a concrete polynomial-time TM2.

## Accepted Route

The work continues the previously approved Route A: finish the Cook--Levin
generator vertically before broadening the problem catalog.  The order is:

1. lift the verified zero-based exactly-one serializer to runtime affine gate
   and source-wire bases;
2. compose that kernel across raw one-hot groups, one validity row, and every
   tableau row;
3. serialize transition, boundary, final-conjunction, and output phases;
4. prove exact equality with `encodeCircuit (verifierCircuit W x)`, package the
   concrete polynomial-time generator, and derive `GeneralCircuitSAT`
   NP-hardness and NP-completeness;
5. define honest graph-plus-`k` CLIQUE and bridge the existing occurrence graph
   reduction;
6. formalize the selected Section 34.5 chain: VERTEX-COVER, HAM-CYCLE and TSP
   decision, and SUBSET-SUM, each with NP membership and a concrete machine
   reduction before it is counted as complete.

Small independent Section 34.1 closure lemmas may be added between these
milestones, but they do not replace the generator critical path.

## Architecture

Generator work is split into streaming kernels.  A kernel owns a finite-control
program, an exact independent-semantics run, an exact output theorem, and a
polynomial bound.  Parent phases enter kernels with runtime-sized values stored
only in unary counters or bounded stacks.  No runtime gate index, tableau row,
or source string is embedded in finite control.

The first affine kernel is contextual: it starts with unary counters holding
`start`, `start + 2`, and `rowBase + count`, plus a `count` loop stack.  It emits
the reverse encoding of

```text
exactlyOneGateTrace start
  ((List.range count).map (fun wire => rowBase + wire))
```

onto an arbitrary existing output suffix.  This is the interface the future
row serializer actually needs.  A standalone structured-input wrapper is not
required until composition needs an external TM2 boundary.

## Acceptance Rules

For every generator slice:

- add an unresolved public `#check` first and observe the focused test fail;
- prove the exact emitted symbol stream, not only its length;
- prove the exact or explicitly bounded run of the concrete program;
- reject `sorry`, `admit`, project axioms, and noncomputable membership-selected
  circuits;
- audit headline declarations with `#print axioms`;
- use focused Lake/Lean checks during proof development and do not run a full
  repository build unless the user explicitly requests it.

## Known Rejected Routes

- Polynomial output length is not polynomial-time computability.
- A clock is not a serializer.
- Native evaluation is not a TM2 witness.
- A specialized occurrence-graph language is not general CLIQUE.
- A semantic predicate or NP-membership theorem alone is not an NP-completeness
  result.
- Embedding runtime indices or rows in finite control violates the fixed-machine
  requirement.

## Completion Accounting

Chapter 34 remains `partial` until the concrete Cook--Levin generator and
general CLIQUE bridge are complete.  Section 34.5 is reported problem by
problem and is not promoted from `not-started` merely because one target
language has been defined.
