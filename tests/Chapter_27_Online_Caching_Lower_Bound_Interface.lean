import CLRSLean.FourthEdition.Chapter_27

/-!
# Chapter 27 §27.3 deterministic lower bound interface test

Verifies the online-caching (paging) Sleator-Tarjan lower bound: the
adversarial request construction, the fact that the adversary faults the online
algorithm on every request, the offline phase-based schedule's miss bound, and
the public theorems showing no deterministic online algorithm beats `k`.
-/

namespace CLRS

namespace OnlineCaching

-- The adversary: the fresh-page request and the adversarial sequence/cache.
#check freshPage
#check freshPage_spec
#check advCache
#check advSeq
#check advSeq_length
#check advSeq_misses
#check runGo_advSeq

-- The offline phase-based schedule and its per-phase eviction.
#check offlineStep
#check servePhase
#check servePhaseMisses
#check offCache
#check offMisses
#check servePhaseMisses_le
#check servePhaseMisses_le_one
#check offMisses_bound_from_full
#check offMisses_bound

-- The two public lower-bound theorems.
#check caching_lower_bound
#check caching_no_c_competitive

#print axioms advSeq_misses
#print axioms offMisses_bound
#print axioms caching_lower_bound
#print axioms caching_no_c_competitive

end OnlineCaching

end CLRS
