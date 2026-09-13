import CLRSLean.FourthEdition.Chapter_16.Section_16_1_Amortized_Framework

/-!
# 16.3. The Potential Method

This fourth-edition reader facade presents the potential method independently
from the aggregate and accounting methods.

## Main results

* {name}`CLRS.Chapter17.amortizedCost` adds the change in potential to an
  operation's actual cost.
* {name}`CLRS.Chapter17.potential_totalCost_eq_totalAmortized_sub_delta` proves
  the exact telescoping identity for a finite trace.
* {name}`CLRS.Chapter17.potential_totalCost_le_totalAmortized` derives the
  standard upper bound when the endpoint potential does not decrease.

Status: `proved` for the finite-trace potential framework.
-/
