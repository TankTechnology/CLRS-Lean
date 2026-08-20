import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteCountSemantics

/-!
# Affine source shift for terminal stack pop routes

Dropping a verifier-fixed number of rows from an affine progression advances
each base by that many strides and saturating-subtracts the shared count.
This is the descriptor-level form needed by pop routes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Descriptor obtained after dropping a fixed prefix of progression rows. -/
def transitionStackRouteDropPrefix (amount : Nat)
    (progression : AffineUnaryTripleProgression) :
    AffineUnaryTripleProgression :=
  { base₁ := progression.base₁ + amount * progression.step₁
    base₂ := progression.base₂ + amount * progression.step₂
    base₃ := progression.base₃ + amount * progression.step₃
    step₁ := progression.step₁
    step₂ := progression.step₂
    step₃ := progression.step₃
    count := progression.count - amount }

/-- Advancing the bases and shortening the count denotes exactly `List.drop`
on the original affine row stream. -/
theorem transitionStackRouteDropPrefix_rows
    (amount : Nat) (progression : AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionRows
        (transitionStackRouteDropPrefix amount progression) =
      (affineUnaryTripleProgressionRows progression).drop amount := by
  rw [affineUnaryTripleProgressionRows_eq_ofFn,
    affineUnaryTripleProgressionRows_eq_ofFn]
  apply List.ext_get
  · simp [transitionStackRouteDropPrefix]
  · intro index hleft hright
    simp [transitionStackRouteDropPrefix]
    constructor
    · ring
    · constructor <;> ring

end CLRS.Chapter34.Turing.CookLevin
