import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineMuxPhase
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineOneHotPairPhase

/-!
# Complete fixed affine statement scripts

The individual phase generators become useful to the Cook--Levin main
compiler only after their rows can be concatenated without intermediate
machines or halts.  This module packages all five symbolic phase shapes in one
type, flattens a fixed script to one affine form/delimiter table, and proves
that a single polynomial-time TM2 emits the complete interleaved tagged script
for every transition row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The five statement phase shapes with every runtime wire replaced by an
affine transition-seed form. -/
inductive TransitionAffineStmtPhaseForm
  | oneHotMap (groups : List TransitionAffineOrGroupForm)
  | oneHotPredicate (frames : List TransitionAffineOrPairForm)
  | oneHotPairMap (andFrames : List TransitionAffineAndPairForm)
      (orGroups : List TransitionAffineOrGroupForm)
  | pop (frames : List TransitionAffineOrPairForm)
  | mux (selector : AffineUnaryTripleForm)
      (frames : List TransitionAffineMuxPairForm)
deriving DecidableEq, Repr

/-- Evaluate every operand of one symbolic phase. -/
def TransitionAffineStmtPhaseForm.eval
    (phase : TransitionAffineStmtPhaseForm)
    (seed : AffineUnaryTripleSeed) : AffineStmtPhase :=
  match phase with
  | .oneHotMap groups =>
      .oneHotMap (groups.map fun group =>
        group.map fun frame => frame.eval seed)
  | .oneHotPredicate frames =>
      .oneHotPredicate (frames.map fun frame => frame.eval seed)
  | .oneHotPairMap andFrames orGroups =>
      .oneHotPairMap
        (andFrames.map fun frame => frame.eval seed)
        (orGroups.map fun group => group.map fun frame => frame.eval seed)
  | .pop frames => .pop (frames.map fun frame => frame.eval seed)
  | .mux selector frames =>
      .mux (affineUnaryTripleFormValue selector seed)
        (frames.map fun frame => frame.eval seed)

/-- Affine fields of one complete tagged symbolic phase. -/
def TransitionAffineStmtPhaseForm.fieldForms :
    TransitionAffineStmtPhaseForm → List AffineUnaryTripleForm
  | .oneHotMap groups =>
      [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
        transitionAffineOrGroupFamilyFieldForms groups
  | .oneHotPredicate frames =>
      [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
        transitionAffineOrFieldForms frames
  | .oneHotPairMap andFrames orGroups =>
      [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
        transitionAffineAndFieldForms andFrames ++ [transitionZeroForm] ++
          transitionAffineOrGroupFamilyFieldForms orGroups
  | .pop frames => transitionAffinePopPhaseFieldForms frames
  | .mux selector frames =>
      transitionAffineMuxPhaseFieldForms selector frames

/-- Matching fixed delimiter table of one symbolic phase. -/
def TransitionAffineStmtPhaseForm.delimiters :
    TransitionAffineStmtPhaseForm → List UnaryFrameSym
  | .oneHotMap groups =>
      [.tick, .tick, .tick] ++
        transitionAffineOrGroupFamilyDelimiters groups
  | .oneHotPredicate frames =>
      [.tick, .tick, .frameEnd] ++ transitionAffineOrDelimiters frames
  | .oneHotPairMap andFrames orGroups =>
      [.tick, .tick, .separator] ++
        transitionAffineAndDelimiters andFrames ++ [.separator] ++
          transitionAffineOrGroupFamilyDelimiters orGroups
  | .pop frames => transitionAffinePopPhaseDelimiters frames
  | .mux _ frames => transitionAffineMuxPhaseDelimiters frames

theorem TransitionAffineStmtPhaseForm.lengths
    (phase : TransitionAffineStmtPhaseForm) :
    phase.fieldForms.length = phase.delimiters.length := by
  cases phase with
  | oneHotMap groups =>
      simp [TransitionAffineStmtPhaseForm.fieldForms,
        TransitionAffineStmtPhaseForm.delimiters,
        transitionAffineOrGroupFamily_lengths]
  | oneHotPredicate frames =>
      simp [TransitionAffineStmtPhaseForm.fieldForms,
        TransitionAffineStmtPhaseForm.delimiters]
  | oneHotPairMap andFrames orGroups =>
      simp [TransitionAffineStmtPhaseForm.fieldForms,
        TransitionAffineStmtPhaseForm.delimiters,
        transitionAffineOrGroupFamily_lengths]
  | pop frames => exact transitionAffinePopPhase_lengths frames
  | mux selector frames =>
      exact transitionAffineMuxPhase_lengths selector frames

theorem TransitionAffineStmtPhaseForm.delimiters_nonempty
    (phase : TransitionAffineStmtPhaseForm) :
    0 < phase.delimiters.length := by
  cases phase <;>
    simp [TransitionAffineStmtPhaseForm.delimiters,
      transitionAffinePopPhaseDelimiters,
      transitionAffineMuxPhaseDelimiters]

private theorem transitionAffineGenericPairPayload_fixed_encoding
    (andFrames : List TransitionAffineAndPairForm)
    (orGroups : List TransitionAffineOrGroupForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineAndFieldForms andFrames ++
            [transitionZeroForm] ++
              transitionAffineOrGroupFamilyFieldForms orGroups) seed)
        (transitionAffineAndDelimiters andFrames ++ [.separator] ++
          transitionAffineOrGroupFamilyDelimiters orGroups) =
      encodeAffineAndThenOrInput
        (andFrames.map fun frame => frame.eval seed)
        (orGroups.map fun group =>
          group.map fun frame => frame.eval seed) := by
  rw [show transitionAffineAndFieldForms andFrames ++
        [transitionZeroForm] ++
          transitionAffineOrGroupFamilyFieldForms orGroups =
      transitionAffineAndFieldForms andFrames ++
        ([transitionZeroForm] ++
          transitionAffineOrGroupFamilyFieldForms orGroups) by
      simp [List.append_assoc]]
  rw [affineUnaryTripleMap, List.map_append]
  rw [show transitionAffineAndDelimiters andFrames ++ [.separator] ++
        transitionAffineOrGroupFamilyDelimiters orGroups =
      transitionAffineAndDelimiters andFrames ++
        ([.separator] ++
          transitionAffineOrGroupFamilyDelimiters orGroups) by
      simp [List.append_assoc]]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap (transitionAffineAndFieldForms andFrames) seed)
      (transitionAffineAndDelimiters andFrames) ++ _ = _
  rw [transitionAffineAnd_fixed_encoding]
  change _ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        ([transitionZeroForm] ++
          transitionAffineOrGroupFamilyFieldForms orGroups) seed)
      ([.separator] ++
        transitionAffineOrGroupFamilyDelimiters orGroups) = _
  rw [affineUnaryTripleMap, List.map_append]
  rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
  change _ ++ (_ ++ encodeUnaryFrameWithFixedDelimiters
      (affineUnaryTripleMap
        (transitionAffineOrGroupFamilyFieldForms orGroups) seed)
      (transitionAffineOrGroupFamilyDelimiters orGroups)) = _
  rw [transitionAffineOrGroupFamily_fixed_encoding]
  simp [encodeAffineAndThenOrInput, transitionZeroForm,
    affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]

/-- Every symbolic phase has exactly the official tagged statement-controller
encoding after affine evaluation. -/
theorem transitionAffineStmtPhaseForm_fixed_encoding
    (phase : TransitionAffineStmtPhaseForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap phase.fieldForms seed) phase.delimiters =
      encodeAffineStmtControllerPhase (phase.eval seed) := by
  cases phase with
  | oneHotMap groups =>
      rw [show TransitionAffineStmtPhaseForm.fieldForms (.oneHotMap groups) =
          [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
            transitionAffineOrGroupFamilyFieldForms groups by rfl]
      rw [affineUnaryTripleMap, List.map_append]
      rw [show TransitionAffineStmtPhaseForm.delimiters (.oneHotMap groups) =
          [.tick, .tick, .tick] ++
            transitionAffineOrGroupFamilyDelimiters groups by rfl]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
      change _ ++ encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap
            (transitionAffineOrGroupFamilyFieldForms groups) seed)
          (transitionAffineOrGroupFamilyDelimiters groups) = _
      rw [transitionAffineOrGroupFamily_fixed_encoding]
      simp [TransitionAffineStmtPhaseForm.eval,
        encodeAffineStmtControllerPhase, affineStmtPhaseTagCode,
        affineStmtPhasePayload, transitionZeroForm,
        affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]
  | oneHotPredicate frames =>
      rw [show TransitionAffineStmtPhaseForm.fieldForms
          (.oneHotPredicate frames) =
          [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
            transitionAffineOrFieldForms frames by rfl]
      rw [affineUnaryTripleMap, List.map_append]
      rw [show TransitionAffineStmtPhaseForm.delimiters
          (.oneHotPredicate frames) =
          [.tick, .tick, .frameEnd] ++
            transitionAffineOrDelimiters frames by rfl]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
      change _ ++ encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap (transitionAffineOrFieldForms frames) seed)
          (transitionAffineOrDelimiters frames) = _
      rw [transitionAffineOr_fixed_encoding]
      simp [TransitionAffineStmtPhaseForm.eval,
        encodeAffineStmtControllerPhase, affineStmtPhaseTagCode,
        affineStmtPhasePayload, transitionZeroForm,
        affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]
  | oneHotPairMap andFrames orGroups =>
      rw [show TransitionAffineStmtPhaseForm.fieldForms
          (.oneHotPairMap andFrames orGroups) =
          [transitionZeroForm, transitionZeroForm, transitionZeroForm] ++
            (transitionAffineAndFieldForms andFrames ++
              [transitionZeroForm] ++
                transitionAffineOrGroupFamilyFieldForms orGroups) by
          simp [TransitionAffineStmtPhaseForm.fieldForms,
            List.append_assoc]]
      rw [affineUnaryTripleMap, List.map_append]
      rw [show TransitionAffineStmtPhaseForm.delimiters
          (.oneHotPairMap andFrames orGroups) =
          [.tick, .tick, .separator] ++
            (transitionAffineAndDelimiters andFrames ++ [.separator] ++
              transitionAffineOrGroupFamilyDelimiters orGroups) by
          simp [TransitionAffineStmtPhaseForm.delimiters,
            List.append_assoc]]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _ (by simp)]
      change _ ++ encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap
            (transitionAffineAndFieldForms andFrames ++
              [transitionZeroForm] ++
                transitionAffineOrGroupFamilyFieldForms orGroups) seed)
          (transitionAffineAndDelimiters andFrames ++ [.separator] ++
            transitionAffineOrGroupFamilyDelimiters orGroups) = _
      rw [transitionAffineGenericPairPayload_fixed_encoding]
      simp [TransitionAffineStmtPhaseForm.eval,
        encodeAffineStmtControllerPhase, affineStmtPhaseTagCode,
        affineStmtPhasePayload, transitionZeroForm,
        affineUnaryTripleFormValue, encodeUnaryFrameWithFixedDelimiters]
  | pop frames =>
      exact transitionAffinePopPhase_fixed_encoding frames seed
  | mux selector frames =>
      exact transitionAffineMuxPhase_fixed_encoding selector frames seed

/-- One flat affine form table for a complete fixed symbolic script. -/
def transitionAffineStmtScriptFieldForms
    (script : List TransitionAffineStmtPhaseForm) :
    List AffineUnaryTripleForm :=
  script.flatMap TransitionAffineStmtPhaseForm.fieldForms

/-- One matching delimiter table for a complete fixed symbolic script. -/
def transitionAffineStmtScriptDelimiters
    (script : List TransitionAffineStmtPhaseForm) : List UnaryFrameSym :=
  script.flatMap TransitionAffineStmtPhaseForm.delimiters

theorem transitionAffineStmtScript_lengths
    (script : List TransitionAffineStmtPhaseForm) :
    (transitionAffineStmtScriptFieldForms script).length =
      (transitionAffineStmtScriptDelimiters script).length := by
  induction script with
  | nil => rfl
  | cons phase script ih =>
      simp only [transitionAffineStmtScriptFieldForms,
        transitionAffineStmtScriptDelimiters, List.flatMap_cons,
        List.length_append]
      rw [phase.lengths]
      simpa [transitionAffineStmtScriptFieldForms,
        transitionAffineStmtScriptDelimiters] using
        congrArg (fun n => phase.delimiters.length + n) ih

theorem transitionAffineStmtScriptDelimiters_nonempty
    {script : List TransitionAffineStmtPhaseForm} (hnonempty : script ≠ []) :
    0 < (transitionAffineStmtScriptDelimiters script).length := by
  obtain ⟨phase, rest, rfl⟩ := List.exists_cons_of_ne_nil hnonempty
  simp only [transitionAffineStmtScriptDelimiters, List.flatMap_cons,
    List.length_append]
  have := phase.delimiters_nonempty
  omega

/-- Concatenating symbolic phase rows is byte-for-byte the official complete
statement-controller script encoding. -/
theorem transitionAffineStmtScriptForms_fixed_encoding
    (script : List TransitionAffineStmtPhaseForm)
    (seed : AffineUnaryTripleSeed) :
    encodeUnaryFrameWithFixedDelimiters
        (affineUnaryTripleMap
          (transitionAffineStmtScriptFieldForms script) seed)
        (transitionAffineStmtScriptDelimiters script) =
      encodeAffineStmtControllerScript (script.map fun phase =>
        phase.eval seed) := by
  induction script with
  | nil => rfl
  | cons phase script ih =>
      rw [show transitionAffineStmtScriptFieldForms (phase :: script) =
          phase.fieldForms ++ transitionAffineStmtScriptFieldForms script by
        rfl]
      rw [affineUnaryTripleMap, List.map_append]
      rw [show transitionAffineStmtScriptDelimiters (phase :: script) =
          phase.delimiters ++ transitionAffineStmtScriptDelimiters script by
        rfl]
      rw [encodeUnaryFrameWithFixedDelimiters_append _ _ _ _
        (by simpa [affineUnaryTripleMap] using phase.lengths)]
      change encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap phase.fieldForms seed) phase.delimiters ++
        encodeUnaryFrameWithFixedDelimiters
          (affineUnaryTripleMap
            (transitionAffineStmtScriptFieldForms script) seed)
          (transitionAffineStmtScriptDelimiters script) = _
      rw [transitionAffineStmtPhaseForm_fixed_encoding, ih]
      simp [encodeAffineStmtControllerScript]

/-- Raw-input target containing one complete symbolic statement script per
transition row. -/
noncomputable def verifierTransitionAffineStmtScript
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (script : List TransitionAffineStmtPhaseForm) (hnonempty : script ≠ [])
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineDelimitedMapFrames W
    (transitionAffineStmtScriptFieldForms script)
    (transitionAffineStmtScriptDelimiters script)
    (transitionAffineStmtScriptDelimiters_nonempty hnonempty) input

/-- Exact row-major semantics of the whole-script compiler. -/
theorem verifierTransitionAffineStmtScript_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (script : List TransitionAffineStmtPhaseForm) (hnonempty : script ≠ [])
    (input : List Γ) :
    verifierTransitionAffineStmtScript W script hnonempty input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineStmtControllerScript (script.map fun phase =>
          phase.eval (transitionTailAffineSeed seed)) := by
  unfold verifierTransitionAffineStmtScript
  rw [verifierTransitionAffineDelimitedMapFrames_eq_rows W
    (transitionAffineStmtScriptFieldForms script)
    (transitionAffineStmtScriptDelimiters script)
    (transitionAffineStmtScriptDelimiters_nonempty hnonempty)
    (transitionAffineStmtScript_lengths script)]
  apply List.flatMap_congr
  intro seed hseed
  unfold transitionAffineDelimitedMapRow
  exact transitionAffineStmtScriptForms_fixed_encoding script
    (transitionTailAffineSeed seed)

/-- One fixed polynomial-time TM2 emits the entire interleaved tagged script
directly from the original verifier input. -/
noncomputable def verifierTransitionAffineStmtScript_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (script : List TransitionAffineStmtPhaseForm) (hnonempty : script ≠ []) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineStmtScript W script hnonempty) :=
  verifierTransitionAffineDelimitedMapFrames_computableInPolyTime W
    (transitionAffineStmtScriptFieldForms script)
    (transitionAffineStmtScriptDelimiters script)
    (transitionAffineStmtScriptDelimiters_nonempty hnonempty)

end CLRS.Chapter34.Turing.CookLevin
