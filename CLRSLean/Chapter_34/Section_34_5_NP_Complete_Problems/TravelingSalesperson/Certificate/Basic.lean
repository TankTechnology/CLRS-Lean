import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Language

/-! # Raw decision-TSP certificate checker -/

namespace CLRS.Chapter34

/-- Total Boolean checker for an ordered decision-TSP tour certificate. -/
def tspVerifier (certificate input : List TSPSym) : Bool :=
  match decodeTSPData input, decodeTSPCertificate certificate with
  | some data, some vertices =>
      decide (data.WellFormed ∧
        data.toInstance.ListRepresentsTour vertices)
  | _, _ => false

end CLRS.Chapter34
