import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Fields

/-!
# Complete TSP instance and certificate parsers
-/

namespace CLRS.Chapter34

/-- Canonical finite encoding of one row-major TSP record. -/
def encodeTSPData (data : TSPData) : List TSPSym :=
  .instanceMark ::
    (encodeTSPFields (data.vertexCount :: data.budget :: data.weights) ++
      [.recordEnd])

/-- Decode one complete TSP instance word. -/
def decodeTSPData : List TSPSym → Option TSPData
  | .instanceMark :: input =>
      match decodeTSPFields input with
      | some (vertexCount :: budget :: weights) =>
          some { vertexCount, budget, weights }
      | _ => none
  | _ => none

/-- Canonical certificate: an ordered list of compact vertex indices. -/
def encodeTSPCertificate (vertices : List Nat) : List TSPSym :=
  .certificateMark :: (encodeTSPFields vertices ++ [.recordEnd])

/-- Decode one complete ordered-tour certificate. -/
def decodeTSPCertificate : List TSPSym → Option (List Nat)
  | .certificateMark :: input => decodeTSPFields input
  | _ => none

end CLRS.Chapter34
