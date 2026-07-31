# Chapter 17 - Amortized Analysis

- Status: `selected-section-complete`
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
- `CLRS.Chapter17.dynamicTableInsert_potential_nonneg`
- `CLRS.Chapter17.dynamicTableDelete_potential_nonneg`
- `CLRS.Chapter17.dynamicTableInsertCost_pos`
- `CLRS.Chapter17.dynamicTableInsertCost_le_num_succ`
- `CLRS.Chapter17.dynamicTableInsertCost_of_fits`
- `CLRS.Chapter17.dynamicTableInsertCost_of_expand`
- `CLRS.Chapter17.dynamicTableInsertSize_of_fits`
- `CLRS.Chapter17.dynamicTableInsertSize_of_expand`
- `CLRS.Chapter17.dynamicTableInsertSize_fits`
- `CLRS.Chapter17.dynamicTableInsertSize_ge_size`
- `CLRS.Chapter17.dynamicTableInsertSize_ge_double_of_expand`
- `CLRS.Chapter17.dynamicTableInsert_valid`
- `CLRS.Chapter17.dynamicTableInsert_num`
- `CLRS.Chapter17.dynamicTableInsert_size`
- `CLRS.Chapter17.dynamicTableInsert_size_of_fits`
- `CLRS.Chapter17.dynamicTableInsert_size_of_expand`
- `CLRS.Chapter17.dynamicTableInsert_num_pos`
- `CLRS.Chapter17.dynamicTableInsert_num_gt`
- `CLRS.Chapter17.dynamicTableInsert_num_ge`
- `CLRS.Chapter17.dynamicTableInsert_capacity_fits`
- `CLRS.Chapter17.dynamicTableInsert_capacity_pos`
- `CLRS.Chapter17.dynamicTableInsert_capacity_ge_size`
- `CLRS.Chapter17.dynamicTableInsert_capacity_ge_double_of_expand`
- `CLRS.Chapter17.dynamicTableInsert_amortizedCost_eq`
- `CLRS.Chapter17.dynamicTableInsert_amortizedBound`
- `CLRS.Chapter17.dynamicTableDeleteCost_pos_of_nonempty`
- `CLRS.Chapter17.dynamicTableDeleteCost_pos_iff_nonempty`
- `CLRS.Chapter17.dynamicTableDeleteCost_zero_iff_empty`
- `CLRS.Chapter17.dynamicTableDeleteCost_le_num`
- `CLRS.Chapter17.dynamicTableDeleteCost_empty`
- `CLRS.Chapter17.dynamicTableDeleteCost_of_contract`
- `CLRS.Chapter17.dynamicTableDeleteCost_of_no_contract`
- `CLRS.Chapter17.dynamicTableDeleteCost_eq_num_of_contract`
- `CLRS.Chapter17.dynamicTableDeleteCost_eq_one_of_no_contract`
- `CLRS.Chapter17.dynamicTableDeleteSize_of_contract`
- `CLRS.Chapter17.dynamicTableDeleteSize_of_no_contract`
- `CLRS.Chapter17.dynamicTableDeleteSize_fits`
- `CLRS.Chapter17.dynamicTableDeleteSize_le_size`
- `CLRS.Chapter17.dynamicTableDeleteSize_le_half_of_contract`
- `CLRS.Chapter17.dynamicTableDelete_valid`
- `CLRS.Chapter17.dynamicTableDelete_num`
- `CLRS.Chapter17.dynamicTableDelete_size`
- `CLRS.Chapter17.dynamicTableDelete_size_of_contract`
- `CLRS.Chapter17.dynamicTableDelete_size_of_no_contract`
- `CLRS.Chapter17.dynamicTableDelete_num_le`
- `CLRS.Chapter17.dynamicTableDelete_num_empty`
- `CLRS.Chapter17.dynamicTableDelete_num_pos_of_one_lt`
- `CLRS.Chapter17.dynamicTableDelete_num_lt_of_nonempty`
- `CLRS.Chapter17.dynamicTableDelete_capacity_fits`
- `CLRS.Chapter17.dynamicTableDelete_capacity_pos_of_one_lt`
- `CLRS.Chapter17.dynamicTableDelete_capacity_le_size`
- `CLRS.Chapter17.dynamicTableDelete_capacity_le_half_of_contract`
- `CLRS.Chapter17.dynamicTableDelete_amortizedCost_eq`
- `CLRS.Chapter17.dynamicTableDelete_amortizedBound`
- `CLRS.Chapter17.dynamicTable_amortizedBound`
- `CLRS.Chapter17.growTo_toList`
- `CLRS.Chapter17.growTo_size`
- `CLRS.Chapter17.arrayTable_toState_insert`
- `CLRS.Chapter17.arrayTable_insertCost_eq`
- `CLRS.Chapter17.insert_copy_cost`
- `CLRS.Chapter17.dynamicTableCopyCount_eq_growCopyCost`
- `CLRS.Chapter17.sharpPotentialZ_nonneg`
- `CLRS.Chapter17.sharpPotential_nonneg`
- `CLRS.Chapter17.sharpInsert_amortized_le_three`
- `CLRS.Chapter17.sharpDelete_amortized_le_three`
- `CLRS.Chapter17.sharpDelete_loadFactor_eq_half_of_contract`
- `CLRS.Chapter17.sharpDelete_loadFactor_ge_half_of_contract`

## Optional Refinements

The represented aggregate, accounting, potential, stack/counter, and dynamic-
table analyses are complete.  The dynamic-table surface includes a physical
array-copy model and its connection to the abstract copying cost, plus the CLRS
load-factor potential with constant amortized bounds for insertion and deletion.
General allocator semantics, lower-level RAM constants, and broader interleaved
operation-trace packaging remain optional refinements.
