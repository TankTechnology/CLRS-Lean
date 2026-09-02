import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Language
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Basic

/-! # Raw HAM-CYCLE certificate checker -/

namespace CLRS.Chapter34

abbrev encodeHamiltonianCycleCertificate := encodeCliqueCertificate
abbrev decodeHamiltonianCycleCertificate := decodeCliqueCertificate

/-- Total Boolean checker for an ordered Hamiltonian-cycle certificate. -/
def hamiltonianCycleVerifier
    (certificate input : List HamiltonianCycleSym) : Bool :=
  match decodeHamiltonianCycleInstance input,
      decodeHamiltonianCycleCertificate certificate with
  | some I, some vertices =>
      decide (I.WellFormed ∧ I.targetSize = I.vertexCount ∧
        I.ListRepresentsHamiltonianCycle vertices)
  | _, _ => false

end CLRS.Chapter34
