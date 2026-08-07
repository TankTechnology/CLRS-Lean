import Mathlib
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S1_Cache_Model
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S2_Farthest_In_Future
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S3_Optimality

/-!
# 15.4. Offline caching

This section formalizes the offline caching problem of CLRS §15.4 and the
farthest-in-future (Belady) eviction policy: the cache model with policies,
hits and misses, the next-use function, the farthest-in-future selection, and
basic sanity lemmas for the policy.

Main results:

- `Policy` / `Policy.step` / `misses`: the caching model (CLRS §15.4)
- `nextUse`: the next request position of a page at or after a position
- `Farther`: the "at least as far in the future" order
- `farthestInFuture cache σ i`: the resident page whose next use is farthest
- `fifoPolicy σ`: the farthest-in-future eviction policy
- `fifo_step_of_mem` / `fifo_step_fault`: the policy's cache transitions

Current gaps:

- The optimality theorem (`fifo_optimal`: no eviction policy has fewer
  misses than the farthest-in-future policy, CLRS Theorem 15.5) remains to
  be formalized; the classical exchange argument over request suffixes is
  deferred.

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
-/
