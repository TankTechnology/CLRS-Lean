import CLRSLean.Chapter_04.Section_04_3_Substitution_Method
import CLRSLean.Chapter_04.Section_04_4_Recursion_Tree_Method
import CLRSLean.Chapter_04.Section_04_5_Master_Theorem

/-!
# Chapter 4. Divide-and-Conquer

Chapter 4 has several good Lean targets.  The current first pass starts with
the recurrence layer because it reuses the Chapter 3 asymptotic interface and
supports later divide-and-conquer analyses.  Sections 4.3 and 4.4 now provide
the proof-method infrastructure used by the Master-method file and by future
divide-and-conquer runtime proofs.

* Section 4.1 - The maximum-subarray problem: `future-work`.
  A good Lean target is correctness of a divide-and-conquer maximum-subarray
  algorithm over arrays or lists, with a bridge from subarray intervals to sums.
* Section 4.2 - Strassen's algorithm for matrix multiplication: `future-work`.
  This is formalizable as block-matrix algebra plus a proof that the seven
  products reconstruct ordinary matrix multiplication.
* Section 4.3 - The substitution method: `proved` for one-step recurrence
  bounds.
  The file proves upper-bound, lower-bound, sandwich, linear, and geometric
  substitution templates.
* Section 4.4 - The recursion-tree method: `proved` for additive finite level
  expansions.
  The file proves exact unrolling into level-cost sums and envelope bounds for
  the resulting finite sums.
* Section 4.5 - The master method: `proved` for exact-power recurrences.
  The file proves the normalized recurrence expansion and three Master-style
  exact-power criteria for bounded, constant, and tail-dominated normalized
  forcing.
* Section 4.6 - Proof of the master theorem: `future-work`.
  The exact-power proof is the current compiler-clean core.  The full textbook
  theorem for all natural input sizes still needs monotone recurrence models,
  floor/ceiling sandwiching, and a cleaner statement of regularity hypotheses.
-/

namespace CLRS
namespace Chapter04
end Chapter04
end CLRS
