import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S1_CostModel

/-!
# CLRS Chapter 27.3 — Binary Lower-Bound Definitions

This module defines the sequential lower-bound search used by P-MERGE.  The
search works over half-open index ranges and records one unit of work and span
for every inspected element.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMerge
namespace Internal

/-- Internal half-open-range lower-bound search.

{lit}`loop xs pivot lo hi` searches the range {lit}`[lo, hi)`.  It is intentionally
namespaced, rather than Lean-private, so that the correctness module can state
and prove its range invariant without adding the helper to Chapter 27's public
surface.
-/
def loop [LinearOrder α] (xs : List α) (pivot : α) (lo hi : ℕ) : Costed ℕ :=
  if lo < hi then
    let mid := (lo + hi) / 2
    match xs[mid]? with
    | none => Costed.charge 1 1 lo
    | some x =>
        Costed.seq (Costed.charge 1 1 ()) fun _ =>
          if x < pivot then
            loop xs pivot (mid + 1) hi
          else
            loop xs pivot lo mid
  else
    Costed.pure lo
termination_by hi - lo
decreasing_by
  all_goals omega

end Internal
end ParallelMerge

/-- Return the first position at which {name}`pivot` can be inserted into {name}`xs`.

Correctness is established in the following module under the usual sortedness
hypothesis.  The executable definition remains total on arbitrary lists.
-/
def binaryLowerBound [LinearOrder α] (xs : List α) (pivot : α) : Costed ℕ :=
  ParallelMerge.Internal.loop xs pivot 0 xs.length

end Chapter27
end CLRS
