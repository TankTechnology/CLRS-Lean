import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.FiniteLookup

/-!
# Concrete serialization of binary one-hot maps

The fixed controller first materializes the Cartesian-product conjunctions,
then switches without halting to target-major sparse disjunction fibers.  The
combined byte stream is exactly the semantic `oneHotPairMapGateTrace`.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

def affineOneHotPairMapAndFrames {n p : Nat}
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire) :
    List AffineAndFinPairFrame :=
  affineAndFinCanonicalFrames (oneHotPairOperands left right)

def affineOneHotPairMapOrGroups {n p m : Nat} (start : Nat)
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m) : List AffineOrFinGroup :=
  affineAndThenOrCanonicalGroups start (oneHotPairOperands left right)
    (oneHotPairMapFamilies start left right f)

def affineOneHotPairMapInput {n p m : Nat} (start : Nat)
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m) : List UnaryFrameSym :=
  encodeAffineAndThenOrInput (affineOneHotPairMapAndFrames left right)
    (affineOneHotPairMapOrGroups start left right f)

theorem affineOneHotPairMapGateStream_eq_trace {n p m : Nat} (start : Nat)
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m) :
    affineAndThenOrGateStream (affineOneHotPairMapAndFrames left right)
        (affineOneHotPairMapOrGroups start left right f) =
      (oneHotPairMapGateTrace start left right f).gates.flatMap
        encodeCircuitGate := by
  rw [affineOneHotPairMapAndFrames, affineOneHotPairMapOrGroups,
    affineAndThenOrCanonicalGateStream_eq_trace,
    oneHotPairMapGateTrace_gates_eq_phases]

/-- Execute the complete binary lookup with one fixed controller and no
intermediate halt between pair materialization and target disjunctions. -/
def affineOneHotPairMap_run {n p m : Nat} (start : Nat)
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineAndFinLoopCfg (affineOneHotPairMapInput start left right f) output)
      (some (haltCfg affineOrFinRevProgram
        (((oneHotPairMapGateTrace start left right f).gates.flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineAndThenOrRevSteps (affineOneHotPairMapAndFrames left right)
        (affineOneHotPairMapOrGroups start left right f)) := by
  simpa [affineOneHotPairMapInput, affineOneHotPairMapAndFrames,
    affineOneHotPairMapOrGroups,
    oneHotPairMapGateTrace_gates_eq_phases] using
      affineAndThenOrCanonical_run start (oneHotPairOperands left right)
        (oneHotPairMapFamilies start left right f) output

theorem affineOneHotPairMap_steps_le {n p m : Nat} (start : Nat)
    (left : Fin n → CircuitBuilder.Wire)
    (right : Fin p → CircuitBuilder.Wire)
    (f : Fin n → Fin p → Fin m) :
    affineAndThenOrRevSteps (affineOneHotPairMapAndFrames left right)
        (affineOneHotPairMapOrGroups start left right f) ≤
      100 * (affineOneHotPairMapInput start left right f).length + 2 := by
  exact affineAndThenOrRev_steps_le _ _

end CLRS.Chapter34.Turing.PolyBuilder
