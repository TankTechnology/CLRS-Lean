import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineOneHotPhase
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPredicate

/-!
# Complete affine one-hot-predicate statement phases

A Boolean query over one-hot state wires is a single canonical disjunction of
the verifier-fixed true fiber.  This module constructs that fiber and its OR
frames symbolically, proves that affine evaluation recovers the existing
semantic phase, and emits the phase tag and payload together from the original
verifier input.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Affine source forms selected by the true fiber of a fixed predicate. -/
def transitionOneHotPredicateWireForms {n : Nat}
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool) :
    List AffineUnaryTripleForm :=
  (oneHotTruePreimage f).toList.map source

/-- Evaluation of the symbolic true fiber is the literal operand list used by
the semantic one-hot-predicate circuit. -/
theorem transitionOneHotPredicateWireForms_eval {n : Nat}
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool)
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionOneHotPredicateWireForms source f) seed =
      oneHotPredicateWires
        (fun i => affineUnaryTripleFormValue (source i) seed) f := by
  simp [transitionOneHotPredicateWireForms, oneHotPredicateWires,
    affineUnaryTripleMap, List.map_map, Function.comp_def]

/-- Symbolic canonical OR frames for one fixed one-hot predicate. -/
def transitionAffineOneHotPredicateCanonicalFrames {n : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool) :
    List TransitionAffineOrPairForm :=
  transitionAffineOrCanonicalFrameForms start
    (transitionOneHotPredicateWireForms source f)

/-- Evaluating the symbolic frames gives the established canonical predicate
phase, including the all-false empty-fiber case. -/
theorem transitionAffineOneHotPredicateCanonicalFrames_eval {n : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool)
    (seed : AffineUnaryTripleSeed) :
    (transitionAffineOneHotPredicateCanonicalFrames start source f).map
        (fun frame => frame.eval seed) =
      affineOneHotPredicateCanonicalFrames
        (affineUnaryTripleFormValue start seed)
        (fun i => affineUnaryTripleFormValue (source i) seed) f := by
  unfold transitionAffineOneHotPredicateCanonicalFrames
    affineOneHotPredicateCanonicalFrames
  rw [transitionAffineOrCanonicalFrameForms_eval]
  congr 1
  exact transitionOneHotPredicateWireForms_eval source f seed

/-- Affine fields for a complete tagged predicate phase. -/
def transitionAffineOneHotPredicatePhaseFieldForms {n : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool) :
    List AffineUnaryTripleForm :=
  [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
    transitionAffineOrFieldForms
      (transitionAffineOneHotPredicateCanonicalFrames start source f)

/-- Fixed delimiter table for a complete tagged predicate phase. -/
def transitionAffineOneHotPredicatePhaseDelimiters {n : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool) :
    List UnaryFrameSym :=
  [.tick, .tick, .frameEnd] ++
    transitionAffineOrDelimiters
      (transitionAffineOneHotPredicateCanonicalFrames start source f)

theorem transitionAffineOneHotPredicatePhase_lengths {n : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool) :
    (transitionAffineOneHotPredicatePhaseFieldForms start source f).length =
      (transitionAffineOneHotPredicatePhaseDelimiters start source f).length := by
  simp [transitionAffineOneHotPredicatePhaseFieldForms,
    transitionAffineOneHotPredicatePhaseDelimiters]

theorem transitionAffineOneHotPredicatePhaseDelimiters_nonempty {n : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool) :
    0 <
      (transitionAffineOneHotPredicatePhaseDelimiters start source f).length := by
  simp [transitionAffineOneHotPredicatePhaseDelimiters]

/-- Fixed-delimiter evaluation is exactly the official complete predicate
controller phase, tag included. -/
theorem transitionAffineOneHotPredicatePhase_fixed_encoding {n : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineOneHotPredicatePhaseFieldForms start source f)
          seed)
        (transitionAffineOneHotPredicatePhaseDelimiters start source f) =
      encodeAffineStmtControllerPhase
        (.oneHotPredicate
          ((transitionAffineOneHotPredicateCanonicalFrames start source f).map
            fun frame => frame.eval seed)) := by
  rw [show transitionAffineOneHotPredicatePhaseFieldForms start source f =
      [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
        transitionAffineOrFieldForms
          (transitionAffineOneHotPredicateCanonicalFrames start source f) by
        rfl]
  rw [affineUnaryTripleMap, List.map_append]
  rw [show transitionAffineOneHotPredicatePhaseDelimiters start source f =
      [.tick, .tick, .frameEnd] ++
        transitionAffineOrDelimiters
          (transitionAffineOneHotPredicateCanonicalFrames start source f) by
        rfl]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change _ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        (transitionAffineOrFieldForms
          (transitionAffineOneHotPredicateCanonicalFrames start source f))
        seed)
      (transitionAffineOrDelimiters
        (transitionAffineOneHotPredicateCanonicalFrames start source f)) = _
  rw [transitionAffineOr_fixed_encoding]
  simp [encodeAffineStmtControllerPhase, affineStmtPhaseTagCode,
    affineStmtPhasePayload, transitionZeroForm,
    affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]

/-- One transition seed's complete predicate phase agrees with the canonical
semantic predicate phase. -/
theorem transitionAffineOneHotPredicatePhaseRow_eq_encoding {n : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool)
    (seed : TransitionRowSeed) :
    transitionAffineDelimitedMapRow
        (transitionAffineOneHotPredicatePhaseFieldForms start source f)
        (transitionAffineOneHotPredicatePhaseDelimiters start source f) seed =
      encodeAffineStmtControllerPhase
        (.oneHotPredicate
          (affineOneHotPredicateCanonicalFrames
            (affineUnaryTripleFormValue start
              (transitionTailAffineSeed seed))
            (fun i => affineUnaryTripleFormValue (source i)
              (transitionTailAffineSeed seed)) f)) := by
  unfold transitionAffineDelimitedMapRow
  rw [transitionAffineOneHotPredicatePhase_fixed_encoding]
  rw [transitionAffineOneHotPredicateCanonicalFrames_eval]

/-- Raw-input target containing one complete tagged predicate phase per
transition row. -/
noncomputable def verifierTransitionAffineOneHotPredicatePhase
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineDelimitedMapFrames W
    (transitionAffineOneHotPredicatePhaseFieldForms start source f)
    (transitionAffineOneHotPredicatePhaseDelimiters start source f)
    (transitionAffineOneHotPredicatePhaseDelimiters_nonempty start source f)
    input

/-- Exact row-major semantics of the complete predicate-phase compiler. -/
theorem verifierTransitionAffineOneHotPredicatePhase_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool)
    (input : List Γ) :
    verifierTransitionAffineOneHotPredicatePhase W start source f input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineStmtControllerPhase
          (.oneHotPredicate
            (affineOneHotPredicateCanonicalFrames
              (affineUnaryTripleFormValue start
                (transitionTailAffineSeed seed))
              (fun i => affineUnaryTripleFormValue (source i)
                (transitionTailAffineSeed seed)) f)) := by
  unfold verifierTransitionAffineOneHotPredicatePhase
  rw [verifierTransitionAffineDelimitedMapFrames_eq_rows W
    (transitionAffineOneHotPredicatePhaseFieldForms start source f)
    (transitionAffineOneHotPredicatePhaseDelimiters start source f)
    (transitionAffineOneHotPredicatePhaseDelimiters_nonempty start source f)
    (transitionAffineOneHotPredicatePhase_lengths start source f)]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionAffineOneHotPredicatePhaseRow_eq_encoding start source f seed

/-- One fixed polynomial-time TM2 emits the complete tagged predicate phase
directly from the original verifier input. -/
noncomputable def
    verifierTransitionAffineOneHotPredicatePhase_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineOneHotPredicatePhase W start source f) :=
  verifierTransitionAffineDelimitedMapFrames_computableInPolyTime W
    (transitionAffineOneHotPredicatePhaseFieldForms start source f)
    (transitionAffineOneHotPredicatePhaseDelimiters start source f)
    (transitionAffineOneHotPredicatePhaseDelimiters_nonempty start source f)

end CLRS.Chapter34.Turing.CookLevin
