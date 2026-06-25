# Chapter 17 - Amortized Analysis

- Status: `partial`
- Lean entry: `CLRSLean/Chapter_17.lean`
- Interface test: `Tests/Chapter_17_Interface.lean`

## Proved First-Pass Surface

- `CLRS.Chapter17.aggregate_bound_of_prefix_bound`
- `CLRS.Chapter17.accounting_totalCost_eq_totalCharge_sub_delta`
- `CLRS.Chapter17.accounting_totalCost_le_totalCharge`
- `CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta`
- `CLRS.Chapter17.potential_totalCost_le_totalAmortized`
- `CLRS.Chapter17.multiPop_totalCost_le`
- `CLRS.Chapter17.binaryCounter_increment_potential_le_two`
- `CLRS.Chapter17.binaryCounter_trace_potential_le`
- `CLRS.Chapter17.binaryCounter_trace_totalFlips_le`
- `CLRS.Chapter17.binaryCounter_totalFlips_le`
- `CLRS.Chapter17.dynamicPotential_nonneg`
- `CLRS.Chapter17.dynamicTableInsertSize_fits`
- `CLRS.Chapter17.dynamicTableInsertSize_ge_size`
- `CLRS.Chapter17.dynamicTableInsert_valid`
- `CLRS.Chapter17.dynamicTableInsert_num`
- `CLRS.Chapter17.dynamicTableInsert_amortizedBound`
- `CLRS.Chapter17.dynamicTableDeleteSize_fits`
- `CLRS.Chapter17.dynamicTableDeleteSize_le_size`
- `CLRS.Chapter17.dynamicTableDelete_valid`
- `CLRS.Chapter17.dynamicTableDelete_num`
- `CLRS.Chapter17.dynamicTableDelete_amortizedBound`
- `CLRS.Chapter17.dynamicTable_amortizedBound`

## Remaining Work

The current chapter is a mathematical first pass.  It now includes the exact
one-step and multi-step binary-counter flip/potential proofs, while deferring
mutable-array copying, allocation, RAM-cost constants, and sharper load-factor
potential refinements for dynamic tables.  The dynamic-table layer currently
exposes a nonnegative potential and checks that the chosen post-operation
capacity can hold the resulting element count while moving in the expected
direction for insertion and deletion, but it is still a size-level model rather
than an array-copying model.
