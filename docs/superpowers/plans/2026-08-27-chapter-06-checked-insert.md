# Chapter 6 Checked Heap Insert Plan

1. Add a failing focused interface test for the checked and costed APIs.
2. Move the existing full-prefix implementation into `Insert/Basic.lean` and
   keep `Insert.lean` as a facade.
3. Prove prefix/tail transport lemmas and the total `arrayHeapInsert?` guard,
   state, length, heap-size, and permutation contracts.
4. Instrument upward bubbling and prove erasure plus its logarithmic
   control-frame bound.
5. Connect the costed checked wrapper to the uncosted API and package state
   correctness with the logarithmic bound.
6. Export the interface, add native axiom-audit checks, and update the chapter
   map, progress ledger, audit, and reader navigation.
7. Run focused and repository verification, commit, fast-forward to `main`,
   verify again, push, and close #320 with exact evidence.
