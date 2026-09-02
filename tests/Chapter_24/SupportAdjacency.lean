import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS.SupportAdjacency

#check CLRS.Chapter26.buildSupportAdjacency
#check CLRS.Chapter26.mem_buildSupportAdjacency
#check CLRS.Chapter26.buildSupportAdjacency_work
#check CLRS.Chapter26.buildSupportAdjacency_storage
#check CLRS.Chapter26.sum_bucket_card_le_storage

namespace CLRS.Chapter26.SupportAdjacencyTest

open Finset

noncomputable def threeArcs : Finset (Fin 4 × Fin 4) :=
  {(0, 1), (0, 2), (2, 3)}

example :
    (buildSupportAdjacency threeArcs).work = 3 := by
  rw [buildSupportAdjacency_work]
  decide

example :
    (buildSupportAdjacency threeArcs).adjacency.storage = 3 := by
  rw [buildSupportAdjacency_storage]
  decide

example :
    (1 : Fin 4) ∈ (buildSupportAdjacency threeArcs).adjacency.bucket 0 := by
  rw [mem_buildSupportAdjacency]
  decide

end CLRS.Chapter26.SupportAdjacencyTest
