import CLRSLean.ProofPatterns.Boundary
import CLRSLean.ProofPatterns.Exchange
import CLRSLean.ProofPatterns.Fiber
import CLRSLean.ProofPatterns.Interval

/-!
# Reusable CLRS proof patterns

This namespace contains small, proof-oriented abstractions that occur across
several CLRS chapters.  The modules are intentionally light: they name recurring
proof geometry without forcing chapter-specific algorithms into one interface.

Current modules:

* {lit}`Boundary`: one-step boundary-shift induction for prefix/suffix and scan
  invariants.
* {lit}`Exchange`: the certificate shape for greedy exchange arguments.
* {lit}`Fiber`: key-fiber decomposition for buckets, digit classes, and chains.
* {lit}`Interval`: strict before/nested interval relations for DFS and recursive
  decompositions.
-/
