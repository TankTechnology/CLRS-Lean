import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework
import CLRSLean.Chapter_17.Section_17_2_Stack_And_Counter
import CLRSLean.Chapter_17.Section_17_4_Dynamic_Tables

/-!
# Chapter 17 - Amortized Analysis

Chapter 17 develops reusable finite-prefix arithmetic for amortized analysis
and instantiates it on compact stack, counter, and dynamic-table examples.  The
current first pass contains the aggregate, accounting, and potential-method
framework theorems, a {lit}`MULTIPOP` stack cost bound, an executable
binary-counter one-step potential proof plus a multi-step executable trace
bound, and size-level dynamic-table insertion/deletion capacity and transition
wrappers with capacity-direction and actual-cost lower/upper-bound facts plus an
explicit nonnegative potential fact, actual-cost and capacity-choice case
specifications, direct post-state field equations and allocation-size case
wrappers, direct post-state stored-count and capacity corollaries including
positive insertion/deletion count/capacity wrappers, and direct
resize-branch capacity wrappers plus premise-light deletion-cost branch wrappers,
post-transition potential nonnegativity, and concrete amortized-cost unfolding
wrappers, including exact zero/positive deletion cost specifications.

## Sections

* 17.1-17.3 Amortized analysis framework: {lit}`proved` for finite-prefix
  aggregate, accounting, and potential telescoping facts.
  Main results:
  {lit}`CLRS.Chapter17.aggregate_bound_of_prefix_bound`,
  {lit}`CLRS.Chapter17.accounting_totalCost_eq_totalCharge_sub_delta`,
  {lit}`CLRS.Chapter17.accounting_totalCost_le_totalCharge`,
  {lit}`CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta`, and
  {lit}`CLRS.Chapter17.potential_totalCost_le_totalAmortized`.
* 17.2 Stack and counter examples: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter17.multiPop_totalCost_le`,
  {lit}`CLRS.Chapter17.binaryCounter_increment_potential_le_two`,
  {lit}`CLRS.Chapter17.binaryCounter_trace_potential_le`,
  {lit}`CLRS.Chapter17.binaryCounter_trace_totalFlips_le`, and
  {lit}`CLRS.Chapter17.binaryCounter_totalFlips_le`.
* 17.4 Dynamic tables: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter17.dynamicPotential_nonneg`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_potential_nonneg`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_potential_nonneg`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_pos`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_le_num_succ`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_of_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsertCost_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_of_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_ge_size`,
  {lit}`CLRS.Chapter17.dynamicTableInsertSize_ge_double_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_valid`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_size`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_size_of_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_size_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num_pos`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num_gt`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num_ge`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_fits`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_pos`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_ge_size`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_capacity_ge_double_of_expand`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_amortizedCost_eq`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_amortizedBound`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_pos_of_nonempty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_pos_iff_nonempty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_zero_iff_empty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_le_num`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_empty`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_eq_num_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteCost_eq_one_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_fits`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_le_size`,
  {lit}`CLRS.Chapter17.dynamicTableDeleteSize_le_half_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_valid`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_size`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_size_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_size_of_no_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_le`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_empty`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_pos_of_one_lt`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num_lt_of_nonempty`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_fits`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_pos_of_one_lt`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_le_size`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_capacity_le_half_of_contract`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_amortizedCost_eq`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_amortizedBound`, and
  {lit}`CLRS.Chapter17.dynamicTable_amortizedBound`.

## Current Gaps

Allocator semantics, mutable-array copying, and RAM constants remain
strengthening targets.
-/

namespace CLRS
namespace Chapter17
end Chapter17
end CLRS
