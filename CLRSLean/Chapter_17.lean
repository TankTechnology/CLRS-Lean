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
bound, and size-level dynamic-table insertion/deletion wrappers.

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
  {lit}`CLRS.Chapter17.dynamicTableInsert_valid`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_num`,
  {lit}`CLRS.Chapter17.dynamicTableInsert_amortizedBound`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_valid`,
  {lit}`CLRS.Chapter17.dynamicTableDelete_num`,
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
