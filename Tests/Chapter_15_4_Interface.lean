import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching

open Finset

namespace CLRS.Caching

#check fifo_optimal
#print axioms fifo_optimal

example (π : Policy) (C₀ : Finset Page) (σ : List Page)
    (hC₀ : C₀.Nonempty) :
    misses (fifoPolicy σ) C₀ σ ≤ misses π C₀ σ := by
  exact fifo_optimal π C₀ σ hC₀

end CLRS.Caching
