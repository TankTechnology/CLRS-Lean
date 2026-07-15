# Chapter 4 - Divide and Conquer

The represented chapter contains the maximum-subarray algorithm, recursive
Strassen multiplication, substitution and recursion-tree templates, and the
exact-power/all-input Master-theorem stack.  This note records the execution
boundary of Section 4.1; theorem-level status remains canonical in
`docs/proof-map.md`.

## Section 4.1 Completed

- Exhaustive specification:
  - `CLRS.Chapter04.mem_nonemptySubarrays_iff`
  - `CLRS.Chapter04.maxSubarray_correct`
- Linear crossing scans:
  - `CLRS.Chapter04.maxPrefixLinear_result_correct`
  - `CLRS.Chapter04.maxSuffixLinear_result_correct`
  - `CLRS.Chapter04.maxCrossingSubarrayLinear_result_correct`
- Executable midpoint recursion:
  - `CLRS.Chapter04.midpointSplitTree_unitLeaves`
  - `CLRS.Chapter04.maxSubarrayDivide_result_correct`
  - `CLRS.Chapter04.maxSubarrayDivideCosted_result`
  - `CLRS.Chapter04.maxSubarrayDivideCosted_correct`
- Execution-attached cost:
  - `CLRS.Chapter04.maxPrefixLinearScoredWithCost_cost`
  - `CLRS.Chapter04.maxSuffixLinearScoredWithCost_cost`
  - `CLRS.Chapter04.maxCrossingSubarrayLinearScoredWithCost_cost`
  - `CLRS.Chapter04.maxSubarrayDivideCosted_cost_eq`
  - `CLRS.Chapter04.maxSubarrayDivideCost_unfold`
  - `CLRS.Chapter04.maxSubarrayDivideCost_monotone`
  - `CLRS.Chapter04.maxSubarrayDivideCost_power_sandwich`
  - `CLRS.Chapter04.maxSubarrayDivideCost_pow_two`
  - `CLRS.Chapter04.maxSubarrayDivideCost_isBigTheta_nlogn`

The measured run has base cost `C(0) = C(1) = 1`.  For `2 ≤ n`, its exact
length-indexed recurrence is

```text
C(n) = C(n / 2) + C(n - n / 2)
     + 3(n / 2) + 2(n - n / 2) + 5.
```

Thus odd inputs retain distinct floor and ceiling branches, and the asymmetric
linear term is the proved count of the reverse/prefix scans rather than a
detached recurrence weight.  On powers of two,
`2 C(2^k) + 10 = (5k + 12)2^k`; monotonicity and adjacent-power sandwiching
lift the balanced bound to all positive lengths, yielding `Theta(n log n)`.

## Open Refinements

The cost is an abstract control-step metric.  It charges recursive frames,
linear scan transitions, and constant-size candidate choices.  It does not
charge construction of the explicit split tree, integer arithmetic, Lean
`List` allocation/copying, garbage collection, or machine-level memory
operations.  A direct-recursion or imperative array/RAM refinement that
accounts for those operations remains open; it does not reopen the proved
algorithm-level runtime theorem.
