import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.ReductionMap

/-!
# The textbook Cook--Levin circuitization layer

This module packages the already verified Cook--Levin circuit construction at
the circuitization level normally exposed inside a textbook proof: an explicit map,
exact preservation and reflection of membership, and a polynomial bound on the
serialized output length.

The distinction from the repository's stronger machine interface is
intentional.  `PolynomialOutputReduction` does not assert that its map is
computed in polynomial time, so the results in this module are not named
`NPHard` or `NPComplete`.  Polynomial output length alone cannot establish
either standard predicate.  The theorem
`PolynomialOutputReduction.toPolyTimeReducible` records the exact remaining
bridge: a `PolyTimeComputable` proof for the same explicit map.
-/

namespace CLRS.Chapter34

/-- An explicit semantic many-one reduction whose encoded output length has a
polynomial bound.

This is the proof object delivered by the textbook circuit construction.  It
deliberately does not include a concrete machine computing `map`; use
`toPolyTimeReducible` once that additional obligation is available. -/
structure PolynomialOutputReduction {Γ₁ Γ₂ : Type}
    (L₁ : Language Γ₁) (L₂ : Language Γ₂) where
  /-- The explicit instance map. -/
  map : List Γ₁ → List Γ₂
  /-- A polynomial bounding the length of every encoded output. -/
  bound : Polynomial ℕ
  /-- The map preserves and reflects membership. -/
  correct : ∀ x : List Γ₁, x ∈ L₁ ↔ map x ∈ L₂
  /-- The serialized output length is bounded by `bound`. -/
  output_length_le : ∀ x : List Γ₁, (map x).length ≤ bound.eval x.length

namespace PolynomialOutputReduction

/-- A polynomial-output reduction becomes the repository's machine-level
polynomial-time reduction once its explicit map is proved polynomial-time
computable by the TM2 interface. -/
theorem toPolyTimeReducible {Γ₁ Γ₂ : Type} {L₁ : Language Γ₁}
    {L₂ : Language Γ₂} (R : PolynomialOutputReduction L₁ L₂)
    (hmap : PolyTimeComputable (id : List Γ₁ → List Γ₁)
      (id : List Γ₂ → List Γ₂) R.map) :
    PolyTimeReducible L₁ L₂ := by
  exact ⟨R.map, hmap, R.correct⟩

end PolynomialOutputReduction

namespace Turing.CookLevin

noncomputable section

/-- The verified Cook--Levin circuit map packaged with its exact semantic and
polynomial output-length contracts. -/
def cookLevinPolynomialOutputReduction {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) :
    PolynomialOutputReduction L GeneralCircuitSAT where
  map := cookLevinMap W
  bound := verifierCircuitEncodingBound W
  correct := fun x => (cookLevinMap_mem_generalCircuitSAT_iff W x).symm
  output_length_le := cookLevinMap_length_le W

/-- Every polynomially verifiable language supplies the normalized verifier
witness needed by the explicit Cook--Levin circuit map. -/
def cookLevinPolynomialOutputReduction_of_verifiable {Γ : Type}
    {L : Language Γ} (hL : PolyTimeVerifiable L) :
    PolynomialOutputReduction L GeneralCircuitSAT :=
  cookLevinPolynomialOutputReduction
    (VerifierWitness.ofPolyTimeVerifiable hL)

/-- Exact strong-interface boundary for the Cook--Levin construction: proving
the explicit map polynomial-time computable upgrades the circuitization certificate
to `PolyTimeReducible`. -/
theorem cookLevin_polyTimeReducible_of_computable {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L)
    (hmap : PolyTimeComputable (id : List Γ → List Γ)
      (id : List CircuitSym → List CircuitSym) (cookLevinMap W)) :
    PolyTimeReducible L GeneralCircuitSAT := by
  exact (cookLevinPolynomialOutputReduction W).toPolyTimeReducible hmap

/-- **Cook--Levin textbook circuitization.**  Every polynomially verifiable
language has an explicit semantics-correct circuit map to `GeneralCircuitSAT`
whose serialized output length is polynomially bounded.

This is the semantic-and-size core of the textbook construction, not the
standard NP-hardness theorem: the latter additionally requires the map's
`PolyTimeComputable` premise exposed by
`cookLevin_polyTimeReducible_of_computable`. -/
theorem cookLevin_textbookCircuitization {Γ : Type} {L : Language Γ}
    (hL : PolyTimeVerifiable L) :
    Nonempty (PolynomialOutputReduction L GeneralCircuitSAT) :=
  ⟨cookLevinPolynomialOutputReduction_of_verifiable hL⟩

end

end Turing.CookLevin

end CLRS.Chapter34
