# Polynomial Bound Composition

Use this reference for output-size and runtime bounds.

## Separate the Quantities

Do not conflate:

- number of generated vertices, gates, clauses, or records;
- magnitude of numeric fields;
- number of symbols in each encoded field;
- machine steps used to generate those symbols.

Prove structural counts first, then lift them through the encoder.

## Unary and Binary Encodings

For unary numbers, an endpoint value `v` may contribute `v` symbols.  A bound
on the number of edges is therefore insufficient without a bound on endpoint
magnitudes.

For binary numbers, prove a bit-length bound such as
`Nat.size value ≤ polynomial input.length`.  A polynomial bound on the numeric
value is stronger than necessary in some settings and unavailable in others;
state the serialization-relevant fact.

## Local-to-Global Output Bounds

For each phase prove:

```text
emittedLength phase input ≤ localPolynomial(inputMeasures)
```

Then bound every auxiliary measure by the original raw input length and combine
the inequalities into one named output polynomial.

## Runtime Lifting

When a phase runtime depends on generated data, prove in order:

1. the data's length bound from raw input;
2. monotonicity of the phase runtime expression;
3. substitution of the length bound;
4. closure under addition and composition with earlier phases.

Keep arithmetic in small helper lemmas.  Use the repository's established
polynomial composition APIs instead of rebuilding closure algebra at each
reduction.
