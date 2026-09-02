import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.EncodingBounds

/-!
# Function-level Cook--Levin map

The closed verifier circuit is serialized into the general-circuit language.
This gives the reduction an explicit function-level interface together with
its exact language semantics and output-length polynomial.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- The explicit Cook--Levin map from verifier inputs to circuit encodings. -/
def cookLevinMap {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitSym :=
  encodeCircuit (verifierCircuit W x)

/-- The explicit reduction map preserves and reflects language membership. -/
theorem cookLevinMap_mem_generalCircuitSAT_iff {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (x : List Γ) :
    cookLevinMap W x ∈ GeneralCircuitSAT ↔ x ∈ L := by
  rw [cookLevinMap, encodeCircuit_mem_generalCircuitSAT_iff,
    verifierCircuit_satisfiable_iff]

/-- The explicit reduction map has polynomially bounded output length. -/
theorem cookLevinMap_length_le {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (cookLevinMap W x).length ≤
      (verifierCircuitEncodingBound W).eval x.length := by
  exact verifierCircuit_encoding_length_le W x

end

end CLRS.Chapter34.Turing.CookLevin
