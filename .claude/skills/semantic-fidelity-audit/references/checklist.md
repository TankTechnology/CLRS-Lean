# Ten-Dimensional Semantic Checklist

For every theorem, definition, and algorithm in a section, record the textbook
item, Lean location, verdict, and a one-sentence difference. Avoid vague judgments.

1. **Data representation:** indices, mutability, sentinels, and array/list/tree/
   graph/hash representations match the stated model.
2. **Initialization and preconditions:** entry state matches the algorithm and
   premises are complete without being stronger than the source assumptions.
3. **Invariant and termination:** control flow, invariants, and termination
   assumptions match the source.
4. **Output specification:** return value, ordering, multiset semantics, and side
   effects match.
5. **Complexity claim:** asymptotic bounds use the correct unit, such as
   comparisons, primitive operations, or amortized work.
6. **Quantifiers and free variables:** quantifier order and variable meaning do
   not silently strengthen or weaken the theorem.
7. **Boundary cases:** empty, singleton, degenerate, and negative-weight inputs
   are handled or explicitly excluded where the source discusses them.
8. **Pseudocode correspondence:** implementation control flow maps to the source;
   merged or expanded steps are documented.
9. **Theorem correspondence:** numbered textbook theorems map one-to-one to Lean
   declarations, with omissions and additions recorded.
10. **Declared simplifications:** facade, partial, legacy, and out-of-scope choices
    agree with the edition map; undisclosed simplifications are defects.
