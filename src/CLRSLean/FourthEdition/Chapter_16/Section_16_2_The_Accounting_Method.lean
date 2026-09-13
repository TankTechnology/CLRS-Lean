import CLRSLean.FourthEdition.Chapter_16.Section_16_1_Amortized_Framework
import CLRSLean.FourthEdition.Chapter_16.Section_16_1_Amortized_Framework.Section_16_2_Stack_And_Counter
import CLRSLean.FourthEdition.Chapter_16.Section_16_1_Amortized_Framework.Section_16_2_Stack_And_Counter.StackExecution

/-!
# 16.2. The Accounting Method

This fourth-edition reader facade presents the accounting method and its
executable stack and binary-counter examples.

## Main results

* {name}`CLRS.Chapter17.accounting_totalCost_eq_totalCharge_sub_delta` proves
  the exact telescoping credit identity.
* {name}`CLRS.Chapter17.accounting_totalCost_le_totalCharge` derives the usual
  upper bound from nonnegative final credit.
* {name}`CLRS.Chapter17.multiPop_totalCost_le` bounds the work of MULTIPOP.
* {name}`CLRS.Chapter17.binaryCounter_trace_totalFlips_le` proves that
  {lit}`n` increments from the empty counter flip at most {lit}`2n` bits.

The mixed stack executor also proves exact cell conservation and a linear
whole-trace bound.  Status: `proved` for the accounting framework and these
examples.

## Implementation details

* [Stack and counter examples](CLRSLean/FourthEdition/Chapter_16/Section_16_1_Amortized_Framework/Section_16_2_Stack_And_Counter/)
* [Stack execution and linear work](CLRSLean/FourthEdition/Chapter_16/Section_16_1_Amortized_Framework/Section_16_2_Stack_And_Counter/StackExecution/)
-/
