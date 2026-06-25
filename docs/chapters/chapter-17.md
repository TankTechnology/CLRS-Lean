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
- `CLRS.Chapter17.binaryCounter_totalFlips_le`
- `CLRS.Chapter17.dynamicTableInsert_valid`
- `CLRS.Chapter17.dynamicTableInsert_num`
- `CLRS.Chapter17.dynamicTableInsert_amortizedBound`
- `CLRS.Chapter17.dynamicTable_amortizedBound`

## Remaining Work

The current chapter is a mathematical first pass.  It now includes the exact
one-step binary-counter flip/potential proof, while deferring the executable
multi-step counter trace theorem, dynamic-table contraction transition,
allocation, and RAM-cost constants.
