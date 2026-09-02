import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineOrFrames

/-!
# Affine OR-group transition sources

One-hot maps serialize one false-seeded disjunction for every target, with a
pair of separators around each (possibly empty) fiber.  This module lifts the
affine OR-frame compiler through that group protocol and retains the literal
target-major byte order required by the statement controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Symbolic affine form of one target fiber. -/
abbrev TransitionAffineOrGroupForm := List TransitionAffineOrPairForm

/-- Affine fields for a group, including zero-valued fields that materialize
its two literal separators. -/
def transitionAffineOrGroupFieldForms
    (group : TransitionAffineOrGroupForm) : List AffineUnaryTripleForm :=
  transitionZeroForm :: transitionAffineOrFieldForms group ++
    [transitionZeroForm]

/-- Fixed delimiter layout for one target fiber. -/
def transitionAffineOrGroupDelimiters
    (group : TransitionAffineOrGroupForm) : List UnaryFrameSym :=
  .separator :: transitionAffineOrDelimiters group ++ [.separator]

@[simp] theorem transitionAffineOrGroupFieldForms_length
    (group : TransitionAffineOrGroupForm) :
    (transitionAffineOrGroupFieldForms group).length = 5 * group.length + 2 := by
  simp [transitionAffineOrGroupFieldForms]

@[simp] theorem transitionAffineOrGroupDelimiters_length
    (group : TransitionAffineOrGroupForm) :
    (transitionAffineOrGroupDelimiters group).length = 5 * group.length + 2 := by
  simp [transitionAffineOrGroupDelimiters]

/-- Flattened affine fields for a fixed target-major group family. -/
def transitionAffineOrGroupFamilyFieldForms
    (groups : List TransitionAffineOrGroupForm) :
    List AffineUnaryTripleForm :=
  groups.flatMap transitionAffineOrGroupFieldForms

/-- Matching fixed delimiter table for the group family. -/
def transitionAffineOrGroupFamilyDelimiters
    (groups : List TransitionAffineOrGroupForm) : List UnaryFrameSym :=
  groups.flatMap transitionAffineOrGroupDelimiters

theorem transitionAffineOrGroupFamily_lengths
    (groups : List TransitionAffineOrGroupForm) :
    (transitionAffineOrGroupFamilyFieldForms groups).length =
      (transitionAffineOrGroupFamilyDelimiters groups).length := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      simp [transitionAffineOrGroupFamilyFieldForms,
        transitionAffineOrGroupFamilyDelimiters]

theorem transitionAffineOrGroupFamilyDelimiters_nonempty
    {groups : List TransitionAffineOrGroupForm} (hnonempty : groups ≠ []) :
    0 < (transitionAffineOrGroupFamilyDelimiters groups).length := by
  cases groups with
  | nil => exact (hnonempty rfl).elim
  | cons group groups =>
      simp [transitionAffineOrGroupFamilyDelimiters]

private theorem transitionAffineOrGroup_fixed_encoding
    (group : TransitionAffineOrGroupForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineOrGroupFieldForms group) seed)
        (transitionAffineOrGroupDelimiters group) =
      encodeAffineOrFinGroup (group.map fun frame => frame.eval seed) := by
  unfold transitionAffineOrGroupFieldForms
    transitionAffineOrGroupDelimiters
  simp only [affineUnaryTripleMap, List.map_cons, List.map_append,
    List.map_nil, transitionZeroForm, affineUnaryTripleFormValue,
    List.cons_append]
  simp only [Nat.zero_add, Nat.zero_mul]
  change encodeUnaryFrameWithFixedDelimiters
      ([0] ++ affineUnaryTripleMap (transitionAffineOrFieldForms group) seed ++
        [0])
      ([.separator] ++ transitionAffineOrDelimiters group ++
        [.separator]) = _
  rw [List.append_assoc [0]
    (affineUnaryTripleMap (transitionAffineOrFieldForms group) seed) [0]]
  rw [List.append_assoc [.separator]
    (transitionAffineOrDelimiters group) [.separator]]
  change encodeUnaryFrameWithFixedDelimiters
      (0 :: (affineUnaryTripleMap
        (transitionAffineOrFieldForms group) seed ++ [0]))
      (.separator :: (transitionAffineOrDelimiters group ++ [.separator])) = _
  simp only [encodeUnaryFrameWithFixedDelimiters, List.replicate_zero,
    List.nil_append]
  rw [encodeUnaryFrameWithFixedDelimiters_append
    (affineUnaryTripleMap (transitionAffineOrFieldForms group) seed) [0]
    (transitionAffineOrDelimiters group) [.separator]
    (by simp [affineUnaryTripleMap])]
  rw [transitionAffineOr_fixed_encoding]
  simp [encodeUnaryFrameWithFixedDelimiters, encodeAffineOrFinGroup]

/-- Fixed-delimiter evaluation commutes with the complete group family. -/
theorem transitionAffineOrGroupFamily_fixed_encoding
    (groups : List TransitionAffineOrGroupForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineOrGroupFamilyFieldForms groups) seed)
        (transitionAffineOrGroupFamilyDelimiters groups) =
      encodeAffineOrFinGroups
        (groups.map fun group => group.map fun frame => frame.eval seed) := by
  induction groups with
  | nil => rfl
  | cons group groups ih =>
      rw [show transitionAffineOrGroupFamilyFieldForms (group :: groups) =
          transitionAffineOrGroupFieldForms group ++
            transitionAffineOrGroupFamilyFieldForms groups by rfl]
      rw [affineUnaryTripleMap, List.map_append]
      rw [show transitionAffineOrGroupFamilyDelimiters (group :: groups) =
          transitionAffineOrGroupDelimiters group ++
            transitionAffineOrGroupFamilyDelimiters groups by rfl]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
      change _ ++ encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap
            (transitionAffineOrGroupFamilyFieldForms groups) seed)
          (transitionAffineOrGroupFamilyDelimiters groups) = _
      change encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap
            (transitionAffineOrGroupFieldForms group) seed)
          (transitionAffineOrGroupDelimiters group) ++ _ = _
      rw [transitionAffineOrGroup_fixed_encoding, ih]
      simp [encodeAffineOrFinGroups]

/-- One row's symbolic group family is byte-for-byte the canonical target. -/
theorem transitionAffineOrGroupRow_eq_encoding
    (groups : List TransitionAffineOrGroupForm)
    (seed : TransitionRowSeed) :
    transitionAffineDelimitedMapRow
        (transitionAffineOrGroupFamilyFieldForms groups)
        (transitionAffineOrGroupFamilyDelimiters groups) seed =
      encodeAffineOrFinGroups
        (groups.map fun group => group.map fun frame =>
          frame.eval (transitionTailAffineSeed seed)) := by
  exact transitionAffineOrGroupFamily_fixed_encoding groups
    (transitionTailAffineSeed seed)

/-- Raw-input target containing one fixed affine group family per transition
row seed. -/
noncomputable def verifierTransitionAffineOrGroups
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (groups : List TransitionAffineOrGroupForm) (hnonempty : groups ≠ [])
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineDelimitedMapFrames W
    (transitionAffineOrGroupFamilyFieldForms groups)
    (transitionAffineOrGroupFamilyDelimiters groups)
    (transitionAffineOrGroupFamilyDelimiters_nonempty hnonempty) input

/-- Exact target-major group semantics of the raw-input compiler. -/
theorem verifierTransitionAffineOrGroups_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (groups : List TransitionAffineOrGroupForm) (hnonempty : groups ≠ [])
    (input : List Γ) :
    verifierTransitionAffineOrGroups W groups hnonempty input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineOrFinGroups
          (groups.map fun group => group.map fun frame =>
            frame.eval (transitionTailAffineSeed seed)) := by
  unfold verifierTransitionAffineOrGroups
  rw [verifierTransitionAffineDelimitedMapFrames_eq_rows W
    (transitionAffineOrGroupFamilyFieldForms groups)
    (transitionAffineOrGroupFamilyDelimiters groups)
    (transitionAffineOrGroupFamilyDelimiters_nonempty hnonempty)
    (transitionAffineOrGroupFamily_lengths groups)]
  apply List.flatMap_congr
  intro seed hseed
  exact transitionAffineOrGroupRow_eq_encoding groups seed

/-- One fixed polynomial-time TM2 emits the complete target-major affine OR
group family from the original verifier input. -/
noncomputable def verifierTransitionAffineOrGroups_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (groups : List TransitionAffineOrGroupForm) (hnonempty : groups ≠ []) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineOrGroups W groups hnonempty) :=
  verifierTransitionAffineDelimitedMapFrames_computableInPolyTime W
    (transitionAffineOrGroupFamilyFieldForms groups)
    (transitionAffineOrGroupFamilyDelimiters groups)
    (transitionAffineOrGroupFamilyDelimiters_nonempty hnonempty)

end CLRS.Chapter34.Turing.CookLevin
