import CLRSLean.Probability.FiniteExpectation

/-!
# Finite probability toolkit

This namespace collects the reusable finite-probability infrastructure shared by
the randomized-analysis chapters (5, 7, 8, 9, and 11).  The modules stay
independent of any single algorithm so that a chapter can borrow the expectation
algebra without importing its neighbours.

Current modules:

* {lit}`FiniteExpectation`: uniform average over a finite index type, linearity,
  and the indicator/expectation bridge used by the Chapter 7 comparison
  probability argument.

## Implementation details

The reusable probability support page remains available outside the main sidebar:

* [Finite Expectation Toolkit](CLRSLean/Probability/FiniteExpectation/)
-/
