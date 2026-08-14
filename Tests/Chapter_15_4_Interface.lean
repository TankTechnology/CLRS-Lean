import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching

open Finset

namespace CLRS.Caching

#check fifo_optimal
#print axioms fifo_optimal
#check exchange_trace
#print axioms exchange_trace

example (T : LegalTrace C₀ σ) (t : ℕ) (ht : t < σ.length)
    (hagree : TraceAgreesWithFIF T t)
    (hdis : T.cache (t + 1) ≠ cacheSeq (fifoPolicy σ) C₀ σ (t + 1)) :
    ∃ T' : LegalTrace C₀ σ,
      TraceAgreesWithFIF T' (t + 1) ∧
      traceMisses T' ≤ traceMisses T := by
  exact exchange_trace T t ht hagree hdis

example (π : Policy) (C₀ : Finset Page) (σ : List Page)
    (hC₀ : C₀.Nonempty) :
    misses (fifoPolicy σ) C₀ σ ≤ misses π C₀ σ := by
  exact fifo_optimal π C₀ σ hC₀

end CLRS.Caching
