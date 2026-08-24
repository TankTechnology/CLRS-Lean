# Chapter 34 Raw Graph Well-Formedness Pipeline Plan

**Goal:** Connect the completed syntax normalizer to the completed graph
well-formedness guard, yielding one fixed polynomial-time TM2 from an ordinary
raw graph string to the exact well-formedness verdict of its syntax-normalized
typed value.

**Encoding bridge:** The guard consumes `pairEncoding [] input`, while the
normalizer emits `input`.  The identity

```text
pairEncoding [] input = reverse (OptionPairLeft.format (reverse input))
```

allows the bridge to reuse the existing reverse, option-tagging/separator, and
reverse machines.

## Task 1: Graph-pair formatter

- [ ] Define the empty-certificate graph-pair format and prove the reverse /
  `OptionPairLeft` identity.
- [ ] Compose the three existing fixed polynomial-time machines.

## Task 2: Raw well-formedness pipeline

- [ ] Repackage the formatter over canonical typed graph encodings.
- [ ] Compose syntax normalization, graph-pair formatting, and the completed
  Boolean guard.
- [ ] Prove the resulting Boolean equals `decide
  (normalizedInstanceValue input).WellFormed` on every raw input.

## Task 3: Verification and checkpoint

- [ ] Add focused interface/axiom tests, build Chapter 34, run repository
  checks, and commit proof/documentation checkpoints separately.
