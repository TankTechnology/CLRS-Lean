import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineOneHotPredicatePhase
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionOneHotPairMapCoordinates
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPairMap

/-!
# Complete affine one-hot pair-map statement phases

Binary one-hot lookup first materializes every pair-major conjunction and then
runs a target-major family of disjunctions over those fresh pair wires.  This
module gives both subphases fixed affine form tables, joins them through the
controller's literal separator, prefixes the statement tag, and obtains one
raw-input polynomial-time generator for the complete phase.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Symbolic operands of one pair-major AND frame. -/
structure TransitionAffineAndPairForm where
  left : AffineUnaryTripleForm
  right : AffineUnaryTripleForm
deriving DecidableEq, Repr

/-- Evaluate one symbolic AND frame. -/
def TransitionAffineAndPairForm.eval
    (frame : TransitionAffineAndPairForm)
    (seed : AffineUnaryTripleSeed) : AffineAndFinPairFrame :=
  { left := affineUnaryTripleFormValue frame.left seed
    right := affineUnaryTripleFormValue frame.right seed }

/-- Pair-major symbolic AND frames for the first `k` flattened pairs. -/
def transitionOneHotPairBodyAndForms {n p : Nat}
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm) :
    (k : Nat) → (hk : k ≤ n * p) → List TransitionAffineAndPairForm
  | 0, _ => []
  | k + 1, hk =>
      let hkPrevious : k ≤ n * p := by omega
      let q : Fin (n * p) := Fin.castLE hk (Fin.last k)
      let pair := finProdFinEquiv.symm q
      transitionOneHotPairBodyAndForms left right k hkPrevious ++
        [{ left := left pair.1, right := right pair.2 }]

/-- Complete pair-major symbolic AND-frame family. -/
def transitionOneHotPairAndForms {n p : Nat}
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm) :
    List TransitionAffineAndPairForm :=
  transitionOneHotPairBodyAndForms left right (n * p) (Nat.le_refl _)

private theorem transitionOneHotPairBodyAndForms_eval {n p : Nat}
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) : ∀ (k : Nat) (hk : k ≤ n * p),
    (transitionOneHotPairBodyAndForms left right k hk).map
        (fun frame => frame.eval seed) =
      affineAndFinCanonicalFrames
        (oneHotPairBodyOperands
          (fun i => affineUnaryTripleFormValue (left i) seed)
          (fun j => affineUnaryTripleFormValue (right j) seed) k hk) := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      simp only [transitionOneHotPairBodyAndForms, oneHotPairBodyOperands,
        List.map_append, List.map_cons, List.map_nil,
        affineAndFinCanonicalFrames]
      rw [ih]
      simp [affineAndFinCanonicalFrames,
        TransitionAffineAndPairForm.eval]

/-- Evaluation of symbolic pair frames gives exactly the established
pair-major AND phase. -/
theorem transitionAffineOneHotPairAndFrames_eval {n p : Nat}
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) :
    (transitionOneHotPairAndForms left right).map
        (fun frame => frame.eval seed) =
      affineOneHotPairMapAndFrames
        (fun i => affineUnaryTripleFormValue (left i) seed)
        (fun j => affineUnaryTripleFormValue (right j) seed) := by
  exact transitionOneHotPairBodyAndForms_eval left right seed
    (n * p) (Nat.le_refl _)

/-- Affine coordinate of freshly materialized pair wire `q`. -/
def transitionOneHotPairWireForm {n p : Nat}
    (start : AffineUnaryTripleForm) (q : Fin (n * p)) :
    AffineUnaryTripleForm :=
  transitionAffineFormAddConst start q.val

theorem transitionOneHotPairWireForm_value {n p : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (q : Fin (n * p)) (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleFormValue (transitionOneHotPairWireForm start q) seed =
      (oneHotPairAndGateTrace
        (affineUnaryTripleFormValue start seed)
        (fun i => affineUnaryTripleFormValue (left i) seed)
        (fun j => affineUnaryTripleFormValue (right j) seed)).wires q := by
  rw [transitionOneHotPairWireForm,
    transitionAffineFormAddConst_value,
    oneHotPairAndGateTrace_wire_eq_start_add_val]

/-- Symbolic canonical OR groups following pair materialization. -/
def transitionAffineOneHotPairCanonicalGroups {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) : List TransitionAffineOrGroupForm :=
  transitionAffineOrCanonicalGroupFormsFrom
    (transitionAffineFormAddConst start (n * p))
    (transitionOneHotFiberForms
      (transitionOneHotPairWireForm start) (oneHotPairFunction f))

/-- Evaluation of the symbolic post-AND groups gives the exact established
pair-map OR family. -/
theorem transitionAffineOneHotPairOrGroups_eval {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) (seed : AffineUnaryTripleSeed) :
    (transitionAffineOneHotPairCanonicalGroups start f).map
        (fun group => group.map fun frame => frame.eval seed) =
      affineOneHotPairMapOrGroups
        (affineUnaryTripleFormValue start seed)
        (fun i => affineUnaryTripleFormValue (left i) seed)
        (fun j => affineUnaryTripleFormValue (right j) seed) f := by
  unfold transitionAffineOneHotPairCanonicalGroups
    affineOneHotPairMapOrGroups affineAndThenOrCanonicalGroups
  rw [transitionAffineOrCanonicalGroupFormsFrom_eval]
  rw [transitionOneHotFiberForms_eval]
  rw [transitionAffineFormAddConst_value]
  rw [oneHotPairOperands_length]
  unfold oneHotPairMapFamilies
  rw [oneHotPairAndGateTrace_wires_eq_start_add_val]
  simp [transitionOneHotPairWireForm]

/-! ## Fixed-delimiter serialization of pair-major AND frames -/

/-- Five fields whose fixed-delimiter encoding is one AND frame. -/
def transitionAffineAndPairFieldForms
    (frame : TransitionAffineAndPairForm) : List AffineUnaryTripleForm :=
  [transitionZeroForm, frame.right, transitionZeroForm, frame.left,
    transitionZeroForm]

/-- Fixed delimiter layout of one AND frame. -/
def transitionAffineAndPairDelimiterTable : List UnaryFrameSym :=
  [.tick, .separator, .separator, .separator, .frameEnd]

/-- Flattened affine fields for a fixed AND-frame family. -/
def transitionAffineAndFieldForms
    (frames : List TransitionAffineAndPairForm) :
    List AffineUnaryTripleForm :=
  frames.flatMap transitionAffineAndPairFieldForms

/-- Matching flattened delimiters for a fixed AND-frame family. -/
def transitionAffineAndDelimiters
    (frames : List TransitionAffineAndPairForm) : List UnaryFrameSym :=
  frames.flatMap fun _ => transitionAffineAndPairDelimiterTable

@[simp] theorem transitionAffineAndFieldForms_length
    (frames : List TransitionAffineAndPairForm) :
    (transitionAffineAndFieldForms frames).length = 5 * frames.length := by
  simp [transitionAffineAndFieldForms, transitionAffineAndPairFieldForms]
  omega

@[simp] theorem transitionAffineAndDelimiters_length
    (frames : List TransitionAffineAndPairForm) :
    (transitionAffineAndDelimiters frames).length = 5 * frames.length := by
  simp [transitionAffineAndDelimiters, transitionAffineAndPairDelimiterTable]
  omega

/-- Fixed-delimiter evaluation of symbolic AND frames is their official
controller encoding. -/
theorem transitionAffineAnd_fixed_encoding
    (frames : List TransitionAffineAndPairForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap (transitionAffineAndFieldForms frames) seed)
        (transitionAffineAndDelimiters frames) =
      encodeAffineAndFinFrames (frames.map fun frame => frame.eval seed) := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      rw [show transitionAffineAndFieldForms (frame :: frames) =
          transitionAffineAndPairFieldForms frame ++
            transitionAffineAndFieldForms frames by rfl]
      rw [affineUnaryTripleMap, List.map_append]
      rw [show transitionAffineAndDelimiters (frame :: frames) =
          transitionAffineAndPairDelimiterTable ++
            transitionAffineAndDelimiters frames by rfl]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _
        (by simp [transitionAffineAndPairFieldForms,
          transitionAffineAndPairDelimiterTable])]
      change _ ++ encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap (transitionAffineAndFieldForms frames) seed)
          (transitionAffineAndDelimiters frames) = _
      rw [ih]
      simp [transitionAffineAndPairFieldForms,
        transitionAffineAndPairDelimiterTable,
        TransitionAffineAndPairForm.eval, transitionZeroForm,
        affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters,
        encodeAffineAndFinFrames, encodeAffineAndFinPairFrame,
        encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]

/-! ## Joined AND-then-OR payload and complete statement phase -/

/-- Complete affine field table of the pair-map payload. -/
def transitionAffineOneHotPairPayloadFieldForms {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) : List AffineUnaryTripleForm :=
  transitionAffineAndFieldForms (transitionOneHotPairAndForms left right) ++
    [transitionZeroForm] ++
      transitionAffineOrGroupFamilyFieldForms
        (transitionAffineOneHotPairCanonicalGroups start f)

/-- Delimiters of the pair-map payload, including the AND-to-OR switch. -/
def transitionAffineOneHotPairPayloadDelimiters {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) : List UnaryFrameSym :=
  transitionAffineAndDelimiters (transitionOneHotPairAndForms left right) ++
    [.separator] ++
      transitionAffineOrGroupFamilyDelimiters
        (transitionAffineOneHotPairCanonicalGroups start f)

theorem transitionAffineOneHotPairPayload_lengths {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) :
    (transitionAffineOneHotPairPayloadFieldForms start left right f).length =
      (transitionAffineOneHotPairPayloadDelimiters start left right f).length := by
  simp [transitionAffineOneHotPairPayloadFieldForms,
    transitionAffineOneHotPairPayloadDelimiters,
    transitionAffineOrGroupFamily_lengths]

theorem transitionAffineOneHotPairPayload_fixed_encoding {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineOneHotPairPayloadFieldForms start left right f)
          seed)
        (transitionAffineOneHotPairPayloadDelimiters start left right f) =
      encodeAffineAndThenOrInput
        ((transitionOneHotPairAndForms left right).map
          fun frame => frame.eval seed)
        ((transitionAffineOneHotPairCanonicalGroups start f).map
          fun group => group.map fun frame => frame.eval seed) := by
  rw [show transitionAffineOneHotPairPayloadFieldForms start left right f =
      transitionAffineAndFieldForms
          (transitionOneHotPairAndForms left right) ++
        ([transitionZeroForm] ++
          transitionAffineOrGroupFamilyFieldForms
            (transitionAffineOneHotPairCanonicalGroups start f)) by
      simp [transitionAffineOneHotPairPayloadFieldForms,
        List.append_assoc]]
  rw [affineUnaryTripleMap, List.map_append]
  rw [show transitionAffineOneHotPairPayloadDelimiters start left right f =
      transitionAffineAndDelimiters
          (transitionOneHotPairAndForms left right) ++
        ([.separator] ++
          transitionAffineOrGroupFamilyDelimiters
            (transitionAffineOneHotPairCanonicalGroups start f)) by
      simp [transitionAffineOneHotPairPayloadDelimiters,
        List.append_assoc]]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        (transitionAffineAndFieldForms
          (transitionOneHotPairAndForms left right)) seed)
      (transitionAffineAndDelimiters
        (transitionOneHotPairAndForms left right)) ++ _ = _
  rw [transitionAffineAnd_fixed_encoding]
  change _ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        ([transitionZeroForm] ++
        transitionAffineOrGroupFamilyFieldForms
          (transitionAffineOneHotPairCanonicalGroups start f)) seed)
      ([.separator] ++
        transitionAffineOrGroupFamilyDelimiters
          (transitionAffineOneHotPairCanonicalGroups start f)) = _
  rw [affineUnaryTripleMap, List.map_append]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change _ ++ (_ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        (transitionAffineOrGroupFamilyFieldForms
          (transitionAffineOneHotPairCanonicalGroups start f)) seed)
      (transitionAffineOrGroupFamilyDelimiters
        (transitionAffineOneHotPairCanonicalGroups start f))) = _
  rw [transitionAffineOrGroupFamily_fixed_encoding]
  simp [encodeAffineAndThenOrInput, transitionZeroForm,
    affineUnaryTripleFormValue,
    encodeUnaryFrameWithFixedDelimiters]

/-- Fields of the complete tagged pair-map phase. -/
def transitionAffineOneHotPairPhaseFieldForms {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) : List AffineUnaryTripleForm :=
  [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
    transitionAffineOneHotPairPayloadFieldForms start left right f

/-- Delimiters of the complete tagged pair-map phase. -/
def transitionAffineOneHotPairPhaseDelimiters {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) : List UnaryFrameSym :=
  [.tick, .tick, .separator] ++
    transitionAffineOneHotPairPayloadDelimiters start left right f

theorem transitionAffineOneHotPairPhase_lengths {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) :
    (transitionAffineOneHotPairPhaseFieldForms start left right f).length =
      (transitionAffineOneHotPairPhaseDelimiters start left right f).length := by
  simp [transitionAffineOneHotPairPhaseFieldForms,
    transitionAffineOneHotPairPhaseDelimiters,
    transitionAffineOneHotPairPayload_lengths]

theorem transitionAffineOneHotPairPhaseDelimiters_nonempty {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) :
    0 < (transitionAffineOneHotPairPhaseDelimiters
      start left right f).length := by
  simp [transitionAffineOneHotPairPhaseDelimiters]

/-- Fixed-delimiter evaluation is the official complete pair-map phase. -/
theorem transitionAffineOneHotPairPhase_fixed_encoding {n p m : Nat}
    (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineOneHotPairPhaseFieldForms start left right f) seed)
        (transitionAffineOneHotPairPhaseDelimiters start left right f) =
      encodeAffineStmtControllerPhase
        (.oneHotPairMap
          ((transitionOneHotPairAndForms left right).map
            fun frame => frame.eval seed)
          ((transitionAffineOneHotPairCanonicalGroups start f).map
            fun group => group.map fun frame => frame.eval seed)) := by
  rw [show transitionAffineOneHotPairPhaseFieldForms start left right f =
      [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
        transitionAffineOneHotPairPayloadFieldForms start left right f by rfl]
  rw [affineUnaryTripleMap, List.map_append]
  rw [show transitionAffineOneHotPairPhaseDelimiters start left right f =
      [.tick, .tick, .separator] ++
        transitionAffineOneHotPairPayloadDelimiters start left right f by rfl]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change _ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        (transitionAffineOneHotPairPayloadFieldForms start left right f) seed)
      (transitionAffineOneHotPairPayloadDelimiters start left right f) = _
  rw [transitionAffineOneHotPairPayload_fixed_encoding]
  simp [encodeAffineStmtControllerPhase, affineStmtPhaseTagCode,
    affineStmtPhasePayload, transitionZeroForm,
    affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]

/-- Raw-input target containing one complete tagged pair-map phase per
transition row. -/
noncomputable def verifierTransitionAffineOneHotPairPhase
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n p m : Nat} (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineDelimitedMapFrames W
    (transitionAffineOneHotPairPhaseFieldForms start left right f)
    (transitionAffineOneHotPairPhaseDelimiters start left right f)
    (transitionAffineOneHotPairPhaseDelimiters_nonempty start left right f)
    input

/-- Exact row-major semantics of the complete pair-map phase compiler. -/
theorem verifierTransitionAffineOneHotPairPhase_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n p m : Nat} (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) (input : List Γ) :
    verifierTransitionAffineOneHotPairPhase W start left right f input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineStmtControllerPhase
          (.oneHotPairMap
            (affineOneHotPairMapAndFrames
              (fun i => affineUnaryTripleFormValue (left i)
                (transitionTailAffineSeed seed))
              (fun j => affineUnaryTripleFormValue (right j)
                (transitionTailAffineSeed seed)))
            (affineOneHotPairMapOrGroups
              (affineUnaryTripleFormValue start
                (transitionTailAffineSeed seed))
              (fun i => affineUnaryTripleFormValue (left i)
                (transitionTailAffineSeed seed))
              (fun j => affineUnaryTripleFormValue (right j)
                (transitionTailAffineSeed seed)) f)) := by
  unfold verifierTransitionAffineOneHotPairPhase
  rw [verifierTransitionAffineDelimitedMapFrames_eq_rows W
    (transitionAffineOneHotPairPhaseFieldForms start left right f)
    (transitionAffineOneHotPairPhaseDelimiters start left right f)
    (transitionAffineOneHotPairPhaseDelimiters_nonempty start left right f)
    (transitionAffineOneHotPairPhase_lengths start left right f)]
  apply List.flatMap_congr
  intro seed hseed
  unfold transitionAffineDelimitedMapRow
  rw [transitionAffineOneHotPairPhase_fixed_encoding]
  rw [transitionAffineOneHotPairAndFrames_eval,
    transitionAffineOneHotPairOrGroups_eval]

/-- One fixed polynomial-time TM2 emits the complete tagged pair-map phase
directly from the original verifier input. -/
noncomputable def verifierTransitionAffineOneHotPairPhase_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {n p m : Nat} (start : AffineUnaryTripleForm)
    (left : Fin n → AffineUnaryTripleForm)
    (right : Fin p → AffineUnaryTripleForm)
    (f : Fin n → Fin p → Fin m) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineOneHotPairPhase W start left right f) :=
  verifierTransitionAffineDelimitedMapFrames_computableInPolyTime W
    (transitionAffineOneHotPairPhaseFieldForms start left right f)
    (transitionAffineOneHotPairPhaseDelimiters start left right f)
    (transitionAffineOneHotPairPhaseDelimiters_nonempty start left right f)

end CLRS.Chapter34.Turing.CookLevin
