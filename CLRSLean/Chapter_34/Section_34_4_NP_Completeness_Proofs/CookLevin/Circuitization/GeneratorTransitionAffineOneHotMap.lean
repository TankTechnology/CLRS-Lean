import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineCanonicalOrGroups
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotMap

/-!
# Canonical affine one-hot-map sources

For a fixed finite lookup table, the target-major preimage partition is
static.  This module lifts that partition from concrete wire numbers to
symbolic affine forms, proves that evaluation preserves its exact order, and
instantiates the canonical OR-family compiler with the resulting fibers.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Target-major source-form fibers for the first `k` targets. -/
def transitionOneHotBodyFiberForms {n m : Nat}
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m) :
    (k : Nat) → (hk : k ≤ m) → List (List AffineUnaryTripleForm)
  | 0, _ => []
  | k + 1, hk =>
      let hkPrevious : k ≤ m := by omega
      let target : Fin m := Fin.castLE hk (Fin.last k)
      transitionOneHotBodyFiberForms source f k hkPrevious ++
        [(oneHotPreimage f target).toList.map source]

/-- Complete target-major affine source-form fibers. -/
def transitionOneHotFiberForms {n m : Nat}
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m) :
    List (List AffineUnaryTripleForm) :=
  transitionOneHotBodyFiberForms source f m (Nat.le_refl m)

private theorem transitionOneHotBodyFiberForms_eval {n m : Nat}
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (seed : AffineUnaryTripleSeed) : ∀ (k : Nat) (hk : k ≤ m),
    (transitionOneHotBodyFiberForms source f k hk).map
        (fun wires => wires.map fun wire =>
          affineUnaryTripleFormValue wire seed) =
      oneHotMapBodyFibers
        (fun i => affineUnaryTripleFormValue (source i) seed) f k hk := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      simp only [transitionOneHotBodyFiberForms, oneHotMapBodyFibers,
        List.map_append, List.map_cons, List.map_nil]
      rw [ih]
      congr 2
      simp [oneHotPreimageWires, List.map_map, Function.comp_def]

/-- Evaluation of affine target fibers is the literal concrete fiber family
used by `oneHotMap`. -/
theorem transitionOneHotFiberForms_eval {n m : Nat}
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (seed : AffineUnaryTripleSeed) :
    (transitionOneHotFiberForms source f).map
        (fun wires => wires.map fun wire =>
          affineUnaryTripleFormValue wire seed) =
      oneHotMapFibers
        (fun i => affineUnaryTripleFormValue (source i) seed) f := by
  exact transitionOneHotBodyFiberForms_eval source f seed m (Nat.le_refl m)

theorem transitionOneHotFiberForms_nonempty {n m : Nat}
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (hm : 0 < m) : transitionOneHotFiberForms source f ≠ [] := by
  cases m with
  | zero => omega
  | succ m => simp [transitionOneHotFiberForms,
      transitionOneHotBodyFiberForms]

/-- Symbolic canonical OR groups for one complete finite one-hot map. -/
def transitionAffineOneHotCanonicalGroups {n m : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m) :
    List TransitionAffineOrGroupForm :=
  transitionAffineOrCanonicalGroupFormsFrom start
    (transitionOneHotFiberForms source f)

/-- Evaluating the symbolic one-hot groups gives exactly the canonical
runtime groups already verified against the semantic lookup circuit. -/
theorem transitionAffineOneHotCanonicalGroups_eval {n m : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (seed : AffineUnaryTripleSeed) :
    (transitionAffineOneHotCanonicalGroups start source f).map
        (fun group => group.map fun frame => frame.eval seed) =
      affineOneHotMapCanonicalGroups
        (affineUnaryTripleFormValue start seed)
        (fun i => affineUnaryTripleFormValue (source i) seed) f := by
  unfold transitionAffineOneHotCanonicalGroups
    affineOneHotMapCanonicalGroups
  rw [transitionAffineOrCanonicalGroupFormsFrom_eval]
  rw [transitionOneHotFiberForms_eval]

/-- Raw-input canonical payload for one fixed affine one-hot map per
transition row seed. -/
noncomputable def verifierTransitionAffineOneHotMap
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n m : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (hm : 0 < m) (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineCanonicalOrGroups W start
    (transitionOneHotFiberForms source f)
    (transitionOneHotFiberForms_nonempty source f hm) input

/-- Exact canonical one-hot payload semantics of the raw-input compiler. -/
theorem verifierTransitionAffineOneHotMap_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n m : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (hm : 0 < m) (input : List Γ) :
    verifierTransitionAffineOneHotMap W start source f hm input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineOrFinGroups
          (affineOneHotMapCanonicalGroups
            (affineUnaryTripleFormValue start
              (transitionTailAffineSeed seed))
            (fun i => affineUnaryTripleFormValue (source i)
              (transitionTailAffineSeed seed)) f) := by
  unfold verifierTransitionAffineOneHotMap
  rw [verifierTransitionAffineCanonicalOrGroups_eq_rows]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionOneHotFiberForms_eval]
  rfl

/-- One fixed polynomial-time TM2 emits the canonical affine one-hot-map
payload directly from the original verifier input. -/
noncomputable def verifierTransitionAffineOneHotMap_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n m : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (hm : 0 < m) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineOneHotMap W start source f hm) :=
  verifierTransitionAffineCanonicalOrGroups_computableInPolyTime W start
    (transitionOneHotFiberForms source f)
    (transitionOneHotFiberForms_nonempty source f hm)

end CLRS.Chapter34.Turing.CookLevin
