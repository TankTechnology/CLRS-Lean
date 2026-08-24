# Dry run: HAM-CYCLE gadget

## Closure ledger

| Layer | Current evidence | Status |
| --- | --- | --- |
| Typed gadget construction | Vertex and clause gadget definitions exist | closed |
| Local traversal semantics | Entry/exit choices and forced traversal of one variable gadget are not characterized exactly | open |
| Global soundness | A Hamiltonian cycle has not yet been decoded into a consistent assignment | open |
| Global completeness | A satisfying assignment has not yet been assembled into a Hamiltonian cycle | open |
| Encoding and malformed input | No stable target instance theorem is available to serialize | open |
| Output size | Gadget counts may be estimated, but their final encoding is not stable | open |
| Exact machine and runtime | Premature while typed semantics is open | open |
| NP membership and hardness | Downstream of the semantic and representation layers | open |

Current status: the construction is below `semantic-only` because its typed
truth-source `iff` is not closed.

## First missing bridge

Prove one local variable-gadget traversal theorem: every Hamiltonian traversal
entering through a designated endpoint must leave through the matching endpoint
and chooses exactly one of the two truth tracks.  State the converse constructor
in a separate lemma.

This local correspondence is used by both global directions.  Do not start the
serializer or concrete machine yet; doing so would freeze a gadget interface
whose semantics are still changing.

## File decomposition

```text
HamiltonianCycle/
├── Gadget.lean
├── VariableTraversalSoundness.lean
├── VariableTraversalCompleteness.lean
├── ClauseAttachment.lean
├── ReductionSoundness.lean
├── ReductionCompleteness.lean
└── Semantics.lean
```

Only after `Semantics.lean` exports the typed `iff` should separate encoding,
certificate, machine, runtime, and completeness modules be planned.

## Narrow verification

```bash
lake env lean Tests/Chapter_34_HamiltonianCycle_Gadget.lean
```

The first RED test should `#check` the local forced-traversal theorem, not the
final NP-completeness wrapper.
