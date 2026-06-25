import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework

/-!
# Chapter 17 - Amortized Analysis

Chapter 17 develops reusable finite-prefix arithmetic for amortized analysis.
The current first pass contains the aggregate, accounting, and potential-method
framework theorems.  Concrete {lit}`MULTIPOP`, binary-counter, dynamic-table, and
later Fibonacci-heap instantiations build on this layer.

## Sections

* 17.1-17.3 Amortized analysis framework: {lit}`proved` for finite-prefix
  aggregate, accounting, and potential telescoping facts.
  Main results:
  {lit}`CLRS.Chapter17.aggregate_bound_of_prefix_bound`,
  {lit}`CLRS.Chapter17.accounting_totalCost_eq_totalCharge_sub_delta`,
  {lit}`CLRS.Chapter17.accounting_totalCost_le_totalCharge`,
  {lit}`CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta`, and
  {lit}`CLRS.Chapter17.potential_totalCost_le_totalAmortized`.

## Current Gaps

The concrete {lit}`MULTIPOP`, binary-counter, and dynamic-table examples are not yet
represented in Lean.
-/

namespace CLRS
namespace Chapter17
end Chapter17
end CLRS
