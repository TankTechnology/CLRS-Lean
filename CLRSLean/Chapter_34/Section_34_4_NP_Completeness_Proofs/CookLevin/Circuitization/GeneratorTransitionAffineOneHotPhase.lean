import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineOneHotMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Statement

/-!
# Complete affine one-hot-map statement phases

The one-hot-map payload compiler and the static phase-tag compiler are useful
separately, but the continuous statement controller consumes them interleaved:
each three-symbol tag is immediately followed by its operand payload.  This
module represents the tag by three zero affine fields with literal `tick`
delimiters, appends the canonical one-hot payload table, and compiles that
whole phase as one fixed-delimiter row from every raw-input transition seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Affine fields for one complete one-hot-map controller phase.  The first
three zero fields materialize its literal three-`tick` tag. -/
def transitionAffineOneHotPhaseFieldForms {n m : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m) :
    List AffineUnaryTripleForm :=
  [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
    transitionAffineOrGroupFamilyFieldForms
      (transitionAffineOneHotCanonicalGroups start source f)

/-- Fixed delimiter table matching one complete one-hot-map phase. -/
def transitionAffineOneHotPhaseDelimiters {n m : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m) :
    List UnaryFrameSym :=
  [.tick, .tick, .tick] ++
    transitionAffineOrGroupFamilyDelimiters
      (transitionAffineOneHotCanonicalGroups start source f)

theorem transitionAffineOneHotPhase_lengths {n m : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m) :
    (transitionAffineOneHotPhaseFieldForms start source f).length =
      (transitionAffineOneHotPhaseDelimiters start source f).length := by
  simp [transitionAffineOneHotPhaseFieldForms,
    transitionAffineOneHotPhaseDelimiters,
    transitionAffineOrGroupFamily_lengths]

theorem transitionAffineOneHotPhaseDelimiters_nonempty {n m : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m) :
    0 < (transitionAffineOneHotPhaseDelimiters start source f).length := by
  simp [transitionAffineOneHotPhaseDelimiters]

/-- Evaluating and serializing the symbolic phase gives exactly the official
continuous statement-controller encoding, tag included. -/
theorem transitionAffineOneHotPhase_fixed_encoding {n m : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineOneHotPhaseFieldForms start source f) seed)
        (transitionAffineOneHotPhaseDelimiters start source f) =
      encodeAffineStmtControllerPhase
        (.oneHotMap
          ((transitionAffineOneHotCanonicalGroups start source f).map
            fun group => group.map fun frame => frame.eval seed)) := by
  rw [show transitionAffineOneHotPhaseFieldForms start source f =
      [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
        transitionAffineOrGroupFamilyFieldForms
          (transitionAffineOneHotCanonicalGroups start source f) by rfl]
  rw [affineUnaryTripleMap, List.map_append]
  rw [show transitionAffineOneHotPhaseDelimiters start source f =
      [.tick, .tick, .tick] ++
        transitionAffineOrGroupFamilyDelimiters
          (transitionAffineOneHotCanonicalGroups start source f) by rfl]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _
    (by simp)]
  change _ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        (transitionAffineOrGroupFamilyFieldForms
          (transitionAffineOneHotCanonicalGroups start source f)) seed)
      (transitionAffineOrGroupFamilyDelimiters
        (transitionAffineOneHotCanonicalGroups start source f)) = _
  rw [transitionAffineOrGroupFamily_fixed_encoding]
  simp [encodeAffineStmtControllerPhase, affineStmtPhaseTagCode,
    affineStmtPhasePayload, transitionZeroForm,
    affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]

/-- One transition row's complete affine one-hot phase is byte-for-byte the
controller phase built from that row's seed. -/
theorem transitionAffineOneHotPhaseRow_eq_encoding {n m : Nat}
    (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (seed : TransitionRowSeed) :
    transitionAffineDelimitedMapRow
        (transitionAffineOneHotPhaseFieldForms start source f)
        (transitionAffineOneHotPhaseDelimiters start source f) seed =
      encodeAffineStmtControllerPhase
        (.oneHotMap
          ((transitionAffineOneHotCanonicalGroups start source f).map
            fun group => group.map fun frame =>
              frame.eval (transitionTailAffineSeed seed))) := by
  exact transitionAffineOneHotPhase_fixed_encoding start source f
    (transitionTailAffineSeed seed)

/-- Raw-input target containing one complete tagged one-hot-map phase for
every adjacent tableau-row seed. -/
noncomputable def verifierTransitionAffineOneHotPhase
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n m : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineDelimitedMapFrames W
    (transitionAffineOneHotPhaseFieldForms start source f)
    (transitionAffineOneHotPhaseDelimiters start source f)
    (transitionAffineOneHotPhaseDelimiters_nonempty start source f) input

/-- Exact row-major semantics of the complete phase compiler. -/
theorem verifierTransitionAffineOneHotPhase_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n m : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m)
    (input : List Γ) :
    verifierTransitionAffineOneHotPhase W start source f input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineStmtControllerPhase
          (.oneHotMap
            ((transitionAffineOneHotCanonicalGroups start source f).map
              fun group => group.map fun frame =>
                frame.eval (transitionTailAffineSeed seed))) := by
  unfold verifierTransitionAffineOneHotPhase
  rw [verifierTransitionAffineDelimitedMapFrames_eq_rows W
    (transitionAffineOneHotPhaseFieldForms start source f)
    (transitionAffineOneHotPhaseDelimiters start source f)
    (transitionAffineOneHotPhaseDelimiters_nonempty start source f)
    (transitionAffineOneHotPhase_lengths start source f)]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionAffineOneHotPhaseRow_eq_encoding start source f seed

/-- One fixed polynomial-time TM2 emits the complete tagged one-hot-map phase
directly from the original verifier input. -/
noncomputable def verifierTransitionAffineOneHotPhase_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n m : Nat} (start : AffineUnaryTripleForm)
    (source : Fin n → AffineUnaryTripleForm) (f : Fin n → Fin m) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineOneHotPhase W start source f) :=
  verifierTransitionAffineDelimitedMapFrames_computableInPolyTime W
    (transitionAffineOneHotPhaseFieldForms start source f)
    (transitionAffineOneHotPhaseDelimiters start source f)
    (transitionAffineOneHotPhaseDelimiters_nonempty start source f)

end CLRS.Chapter34.Turing.CookLevin
