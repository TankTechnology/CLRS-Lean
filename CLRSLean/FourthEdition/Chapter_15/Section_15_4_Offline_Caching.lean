import Mathlib
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S1_Cache_Model
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S2_Farthest_In_Future
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S3_Optimality
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.EmptyStart

/-!
# 15.4. Offline caching

This section formalizes the offline caching problem of CLRS §15.4 and the
farthest-in-future (Belady) eviction policy: the cache model with policies,
hits and misses, the next-use function, the farthest-in-future selection, and
the finite-trace exchange proof that the policy is optimal.

Main results:

- `Policy` / `Policy.step` / `misses`: the caching model (CLRS §15.4)
- `nextUse`: the next request position of a page at or after a position
- `Farther`: the "at least as far in the future" order
- `farthestInFuture cache σ i`: the resident page whose next use is farthest
- `fifoPolicy σ`: the farthest-in-future eviction policy
- `fifo_step_of_mem` / `fifo_step_fault`: the policy's cache transitions
- `LegalTrace`: a policy-independent certificate for a legal cache execution
- `fifo_optimal`: optimality for every nonempty eviction-phase cache
- `fifo_optimal_from_empty`: optimality from the literal empty cache, including
  the compulsory first miss (CLRS Theorem 15.5)
- `fifo_optimal_after_compulsory_fill`: the capacity-independent bridge from a
  common compulsory-fill phase to the verified eviction phase

Completion boundary:

- The mathematical offline-caching optimality theorem is complete for finite
  request lists.  Both a nonempty eviction-phase cache and the literal empty
  start of the core transition semantics are covered; arbitrary-capacity fill
  phases use the explicit policy-independent `compulsoryFillCost` bridge.
  Pointer-level cache mutation, RAM costs, and hardware caching behavior are
  separate implementation refinements and are not claimed here.

Notation conventions used in this section:

- `C` : cache (a `Finset Page` of resident pages)
- `σ` : request sequence
- `i` : position of the fault
- `π` : eviction policy

## Implementation details

The section is split into the following sub-modules:

* [Cache Model](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S1_Cache_Model/)
* [Farthest-In-Future Eviction](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S2_Farthest_In_Future/)
* [Optimality](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/S3_Optimality/)
* [Optimality proof overview](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/)
* [Trace-coupling proof](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/)
* [Legal cache traces](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A1_LegalTrace/)
* [Exact one-page cache difference](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A2_OnePageDiff/)
* [Recursive coupling core](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A3_CouplingCore/)
* [Coupling correctness](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A4_CouplingCorrect/)
* [One-step FIF exchange](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A5_Exchange/)
* [Finite exchange iteration](CLRSLean/FourthEdition/Chapter_15/Section_15_4_Offline_Caching/Optimality/Trace/A6_Iteration/)
-/
