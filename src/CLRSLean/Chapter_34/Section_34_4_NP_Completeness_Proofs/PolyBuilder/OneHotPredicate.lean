import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.FiniteLookup

/-!
# Concrete serialization of Boolean queries over one-hot families

A static predicate selects one sparse source-wire fiber.  The arbitrary-list
OR controller serializes that fiber exactly, including the all-false predicate
whose operand list is empty.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

def affineOneHotPredicateCanonicalFrames {n : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) :
    List AffineOrFinPairFrame :=
  affineOrFinCanonicalFrames start (oneHotPredicateWires source f)

theorem affineOneHotPredicateGateStream_eq_trace {n : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) :
    affineOrFinGateStream
        (affineOneHotPredicateCanonicalFrames start source f) =
      (CircuitBuilder.disjunctionGateTrace start
        (oneHotPredicateWires source f)).gates.flatMap
          encodeCircuitGate :=
  affineOrFinCanonicalGateStream_eq_trace start _

/-- Execute the exact semantic suffix of a one-hot predicate query. -/
def affineOneHotPredicate_run {n : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg
        (encodeAffineOrFinFrames
          (affineOneHotPredicateCanonicalFrames start source f)) output)
      (some (haltCfg affineOrFinRevProgram
        (((CircuitBuilder.disjunctionGateTrace start
          (oneHotPredicateWires source f)).gates.flatMap
            encodeCircuitGate).reverse ++ output)))
      (affineOrFinRevSteps
        (affineOneHotPredicateCanonicalFrames start source f)) := by
  simpa [affineOneHotPredicateCanonicalFrames] using
    affineOrFinCanonical_run start (oneHotPredicateWires source f) output

theorem affineOneHotPredicate_steps_le {n : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) :
    affineOrFinRevSteps
        (affineOneHotPredicateCanonicalFrames start source f) ≤
      100 * (encodeAffineOrFinFrames
        (affineOneHotPredicateCanonicalFrames start source f)).length + 3 :=
  affineOrFinRev_steps_le _

end CLRS.Chapter34.Turing.PolyBuilder
