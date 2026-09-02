import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.FiniteLookup

/-!
# Concrete serialization of finite one-hot maps

The semantic finite lookup builds one false-seeded disjunction per target
coordinate.  This module supplies the bridge to one fixed runtime controller:
the encoded target fibers execute to the exact `oneHotMapGateTrace`, including
empty fibers, with a linear machine-step bound.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Canonical runtime groups for every target fiber of a finite one-hot map. -/
def affineOneHotMapCanonicalGroups {n m : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m) :
    List AffineOrFinGroup :=
  affineOrFinCanonicalGroupsFrom start (oneHotMapFibers source f)

/-- The controller's forward symbol stream is the exact encoded semantic
one-hot-map trace. -/
theorem affineOneHotMapGateStream_eq_trace {n m : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m) :
    affineOrFinFamilyGateStream
        (affineOneHotMapCanonicalGroups start source f) =
      (oneHotMapGateTrace start source f).gates.flatMap
        encodeCircuitGate := by
  rw [affineOneHotMapCanonicalGroups,
    affineOrFinCanonicalFamilyGateStream_eq_trace,
    oneHotMapGateTrace_gates_eq_family]

/-- The fixed family controller executes a complete one-hot-map suffix and
halts with the exact semantic gate trace. -/
def affineOneHotMap_run {n m : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg
        (encodeAffineOrFinGroups
          (affineOneHotMapCanonicalGroups start source f)) output)
      (some (haltCfg affineOrFinRevProgram
        (((oneHotMapGateTrace start source f).gates.flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineOrFinFamilyRevSteps
        (affineOneHotMapCanonicalGroups start source f)) := by
  simpa [affineOneHotMapCanonicalGroups,
    oneHotMapGateTrace_gates_eq_family] using
      affineOrFinFamilyCanonical_run start
        (oneHotMapFibers source f) output

/-- The concrete one-hot-map execution has a linear bound in its runtime
fiber encoding. -/
theorem affineOneHotMap_steps_le {n m : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Fin m) :
    affineOrFinFamilyRevSteps
        (affineOneHotMapCanonicalGroups start source f) ≤
      100 * (encodeAffineOrFinGroups
        (affineOneHotMapCanonicalGroups start source f)).length + 2 :=
  affineOrFinFamilyRev_steps_le _

/-- The semantic builder itself appends exactly the family trace consumed by
the concrete controller. -/
theorem oneHotMap_gates_eq_disjunctionFamily (base : CircuitBuilder)
    {n m : Nat} (source : Fin n → CircuitBuilder.Wire)
    (f : Fin n → Fin m)
    (hsource : ∀ i, base.WireValid (source i)) :
    (oneHotMap base source f hsource).builder.gates =
      base.gates ++ CircuitBuilder.disjunctionFamilyGateTrace
        base.gates.length (oneHotMapFibers source f) := by
  rw [oneHotMap_gates_eq, oneHotMapGateTrace_gates_eq_family]

end CLRS.Chapter34.Turing.PolyBuilder
