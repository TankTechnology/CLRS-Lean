# Dry run: numeric SUBSET-SUM reduction

## Closure ledger

| Layer | Current evidence | Status |
| --- | --- | --- |
| Typed semantics | The generated natural-number instance has a solution iff the source 3-CNF is satisfiable | closed |
| Number count | Polynomially many output numbers are generated | closed |
| Numeric representation | No honest raw grammar and canonical parser/encoder are fixed | open |
| Encoded field size | No bound on the binary digit length of every generated number and target | open |
| Total raw map | Malformed source encodings have no canonical target no-instance | open |
| Raw membership iff | Depends on the numeric encoding and malformed-input policy | open |
| Exact computation | Native arithmetic construction is not yet computed by a fixed machine | open |
| Runtime | Number count alone does not bound carries, digit emission, or arithmetic cost | open |
| Public reduction | `PolyTimeReducible` cannot yet be packaged | open |

Current status: typed `semantic-only`; the serialized reduction is not yet
`size-certified`.

## First missing bridge

Choose the raw numeric representation and prove a serialization theorem that
bounds the total encoded length, including the bit length of every generated
number and the target, by a polynomial in the original raw formula length.

The theorem must distinguish:

```text
number of records
number magnitude
binary bit length
total serialized symbol count
```

A polynomial record count alone is insufficient.

## File decomposition

```text
SubsetSum/
├── Instance.lean
├── Encoding.lean
├── EncodingLength.lean
├── ReductionSemantics.lean
├── RawMap.lean
├── ArithmeticMachine.lean
├── PolynomialRuntime.lean
├── Certificate.lean
└── Completeness.lean
```

Keep digit/carry lemmas separate from the semantic subset-selection proof.

## Narrow verification

```bash
lake env lean Tests/Chapter_34_SubsetSum_Encoding.lean
```

The first test should check the encoder/parser round trip and total serialized
length theorem; exact machine computation comes afterward.
