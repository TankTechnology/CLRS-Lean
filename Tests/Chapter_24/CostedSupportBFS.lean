import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS.CostedSupportBFS

#check CLRS.Chapter26.costedResidualBFS
#check CLRS.Chapter26.costedResidualBFS_state
#check CLRS.Chapter26.costedResidualBFS_work_le
#check CLRS.Chapter26.costedResidualBFS_scanWork_le
#check CLRS.Chapter26.BFSParentPath.verticesWithCost_vertices
#check CLRS.Chapter26.BFSParentPath.verticesWithCost_work

namespace CLRS.Chapter26.CostedSupportBFSTest

def zeroNetwork : FlowNetwork (Fin 2) where
  c := fun _ _ => 0
  s := 0
  t := 1
  hc_nonneg := by simp
  hc_self := by simp
  hs_ne_t := by decide

def zeroFlow : Flow (Fin 2) zeroNetwork where
  f := fun _ _ => 0
  hcapacity := by simp [zeroNetwork]
  hskew_symm := by simp
  hconservation := by simp

def emptyAdjacency : SupportAdjacency (Fin 2) :=
  SupportAdjacency.empty

theorem emptyAdjacency_covers : SupportsResidual emptyAdjacency zeroFlow := by
  intro u v hres
  simp [Flow.residualEdge, Flow.residualCapacity, zeroFlow, zeroNetwork] at hres

example :
    (costedResidualBFS emptyAdjacency zeroFlow).state = residualBFS zeroFlow :=
  costedResidualBFS_state emptyAdjacency zeroFlow emptyAdjacency_covers

example : (costedResidualBFS emptyAdjacency zeroFlow).work ≤ 2 := by
  simpa [emptyAdjacency, SupportAdjacency.storage, SupportAdjacency.empty] using
    costedResidualBFS_work_le emptyAdjacency zeroFlow emptyAdjacency_covers

end CLRS.Chapter26.CostedSupportBFSTest
