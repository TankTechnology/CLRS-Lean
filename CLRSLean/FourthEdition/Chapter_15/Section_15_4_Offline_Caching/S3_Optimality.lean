import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S1_Cache_Model
import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.S2_Farthest_In_Future

/-!
# S3. Optimality of the farthest-in-future policy

Basic sanity lemmas for the farthest-in-future (Belady) eviction policy of
CLRS §15.4: it always evicts a resident page and preserves the cache size.

Main results:

- `fifo_evicts_resident`: the FIF policy evicts a resident page
- `fifo_step_size`: a FIF step preserves the cache size

Current gaps:

- The optimality theorem (`fifo_optimal`: no eviction policy — even offline —
  has fewer misses than the farthest-in-future policy, CLRS Theorem 15.5)
  remains to be formalized: the classical exchange argument transforms an
  optimal policy at a fault into one that evicts the farthest-in-future page
  by simulating the two caches between the fault and the evicted page's next
  request.  This requires a suffix-simulation induction over the request
  sequence that is deferred.
-/

namespace CLRS

namespace Caching

open Finset

/-- The farthest-in-future policy always evicts a resident page. -/
lemma fifo_evicts_resident (σ : List Page) (i : ℕ) (C : Finset Page) (p : Page)
    (hp : p ∉ C) (hC : C.Nonempty) :
    (fifoPolicy σ).evict i C p ∈ C :=
  (fifoPolicy σ).evict_mem i C p hp hC

/-- A step of the farthest-in-future policy preserves the cache size. -/
lemma fifo_step_size (σ : List Page) (i : ℕ) (C : Finset Page) (p : Page)
    (hC : C.Nonempty) :
    ((fifoPolicy σ).step i C p).card = C.card :=
  step_card (fifoPolicy σ) i C p hC

end Caching

end CLRS
