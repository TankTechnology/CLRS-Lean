import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgressionFixedGroupsCore

/-!
# Fixed-size groups of affine triple progressions

The controller in the core file is run over an arbitrary descriptor family.
After every `groupLast + 1` descriptors it emits one `frameEnd`, so later
streaming passes can retain the semantic boundary between runtime groups.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Forward triple-row stream starting at an arbitrary finite position in a
fixed-size descriptor group. -/
def affineUnaryTripleProgressionFixedGroupFrameStreamFrom
    (groupLast : Nat) :
    Fin (groupLast + 1) → List AffineUnaryTripleProgression →
      List UnaryFrameSym
  | _, [] => []
  | position, progression :: rest =>
      affineUnaryTripleProgressionFrameStream progression ++
        if hlast : position.val = groupLast then
          .frameEnd :: affineUnaryTripleProgressionFixedGroupFrameStreamFrom
            groupLast ⟨0, by omega⟩ rest
        else
          affineUnaryTripleProgressionFixedGroupFrameStreamFrom groupLast
            ⟨position.val + 1, by omega⟩ rest

/-- Forward stream with one outer marker after every complete fixed-size
descriptor group. -/
def affineUnaryTripleProgressionFixedGroupFrameStream (groupLast : Nat)
    (progressions : List AffineUnaryTripleProgression) :
    List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStreamFrom groupLast
    ⟨0, by omega⟩ progressions

/-- Exact runtime to the fixed-group pre-halt state. -/
def affineUnaryTripleProgressionFixedGroupStepsToFinish :
    List AffineUnaryTripleProgression → Nat
  | [] => 1
  | progression :: rest =>
      4 + affineUnaryTripleProgressionBodySteps progression + 1 +
        affineUnaryTripleProgressionFixedGroupStepsToFinish rest

/-- Fixed-group marking does not change the asymptotic descriptor execution
cost: each descriptor still has the same one-step outer bridge. -/
theorem affineUnaryTripleProgressionFixedGroupStepsToFinish_eq
    (progressions : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFixedGroupStepsToFinish progressions =
      affineUnaryTripleProgressionFamilyStepsToFinish progressions := by
  induction progressions with
  | nil => rfl
  | cons progression rest =>
      simp [affineUnaryTripleProgressionFixedGroupStepsToFinish,
        affineUnaryTripleProgressionFamilyStepsToFinish, *]

/-- Exact continuous execution from any finite group cursor. -/
def affineUnaryTripleProgressionFixedGroup_runToFinish (groupLast : Nat)
    (position : Fin (groupLast + 1))
    (progressions : List AffineUnaryTripleProgression)
    (output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
      (affineUnaryTripleProgressionFixedGroupLoopCfg groupLast position
        (encodeAffineUnaryTripleProgressionFamily progressions) output)
      (some (affineUnaryTripleProgressionFixedGroupFinishCfg groupLast
        ((affineUnaryTripleProgressionFixedGroupFrameStreamFrom groupLast
          position progressions).reverse ++ output)))
      (affineUnaryTripleProgressionFixedGroupStepsToFinish progressions) := by
  induction progressions generalizing position output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons progression rest ih =>
      let restInput := encodeAffineUnaryTripleProgressionFamily rest
      let headOutput :=
        (affineUnaryTripleProgressionFrameStream progression).reverse ++ output
      have hdescriptor :
          encodeAffineUnaryTripleProgression progression ++ restInput ≠ [] := by
        apply List.append_ne_nil_of_left_ne_nil
        exact List.ne_nil_of_length_pos (by
          simp [encodeAffineUnaryTripleProgression])
      have hdispatch :=
        affineUnaryTripleProgressionFixedGroup_dispatch_run groupLast
          position
          (encodeAffineUnaryTripleProgression progression ++ restInput)
          output hdescriptor
      have hbody := affineUnaryTripleProgressionFixedGroup_body_run groupLast
        position progression restInput output
      let bodyDone :=
        affineUnaryTripleProgressionFixedGroupBodyFinishCfg groupLast position
          restInput headOutput
      let h₁ := EvalsToInTime.trans
        (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
        4 _ _ _ _ hdispatch hbody
      by_cases hlast : position.val = groupLast
      · let restPosition : Fin (groupLast + 1) := ⟨0, by omega⟩
        let groupOutput := UnaryFrameSym.frameEnd :: headOutput
        let restStart := affineUnaryTripleProgressionFixedGroupLoopCfg
          groupLast restPosition restInput groupOutput
        have hbridge : EvalsToInTime
            (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
            bodyDone (some restStart) 1 := by
          simpa only [bodyDone, restStart, restPosition, groupOutput] using
            affineUnaryTripleProgressionFixedGroup_lastBridge_run groupLast
              position hlast restInput headOutput
        have hrest := ih restPosition groupOutput
        let h₂ := EvalsToInTime.trans
          (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
          _ 1 _ bodyDone _ h₁ hbridge
        let full := EvalsToInTime.trans
          (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
          _ _ _ restStart _ h₂ hrest
        have hrestPosition : restPosition = ⟨0, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hrestPosition] at full
        convert full using 1
        · simp [encodeAffineUnaryTripleProgressionFamily, restInput]
        · simp [affineUnaryTripleProgressionFixedGroupFrameStreamFrom,
            hlast, groupOutput, headOutput, List.reverse_append,
            List.append_assoc]
        · simp [affineUnaryTripleProgressionFixedGroupStepsToFinish]
          omega
      · let restPosition : Fin (groupLast + 1) :=
          ⟨position.val + 1, by omega⟩
        let restStart := affineUnaryTripleProgressionFixedGroupLoopCfg
          groupLast restPosition restInput headOutput
        have hbridge : EvalsToInTime
            (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
            bodyDone (some restStart) 1 := by
          have hposition : restPosition =
              fixedGroupNextPosition groupLast position hlast := by
            apply Fin.ext
            rfl
          simpa only [bodyDone, restStart, hposition] using
            affineUnaryTripleProgressionFixedGroup_nextBridge_run groupLast
              position hlast restInput headOutput
        have hrest := ih restPosition headOutput
        let h₂ := EvalsToInTime.trans
          (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
          _ 1 _ bodyDone _ h₁ hbridge
        let full := EvalsToInTime.trans
          (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
          _ _ _ restStart _ h₂ hrest
        have hrestPosition : restPosition =
            ⟨position.val + 1, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hrestPosition] at full
        convert full using 1
        · simp [encodeAffineUnaryTripleProgressionFamily, restInput]
        · simp [affineUnaryTripleProgressionFixedGroupFrameStreamFrom,
            hlast, restPosition, headOutput, List.reverse_append,
            List.append_assoc]
        · simp [affineUnaryTripleProgressionFixedGroupStepsToFinish]
          omega

/-- The fixed-group controller inherits the cubic bound of the unchanged
progression-family arithmetic kernel. -/
theorem affineUnaryTripleProgressionFixedGroupStepsToFinish_le
    (progressions : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFixedGroupStepsToFinish progressions ≤
      205 * (encodeAffineUnaryTripleProgressionFamily progressions).length ^ 3 +
        1 := by
  rw [affineUnaryTripleProgressionFixedGroupStepsToFinish_eq]
  exact affineUnaryTripleProgressionFamilyStepsToFinish_le progressions

/-- Full reversed run from the standard initial configuration. -/
def affineUnaryTripleProgressionFixedGroupRev_run (groupLast : Nat)
    (progressions : List AffineUnaryTripleProgression) :
    EvalsToInTime
      (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
      (initialCfg (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
        (encodeAffineUnaryTripleProgressionFamily progressions))
      (some (haltCfg
        (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
        (affineUnaryTripleProgressionFixedGroupFrameStream groupLast
          progressions).reverse))
      (affineUnaryTripleProgressionFixedGroupStepsToFinish progressions + 1) := by
  have body := affineUnaryTripleProgressionFixedGroup_runToFinish groupLast
    ⟨0, by omega⟩ progressions []
  have body' : EvalsToInTime
      (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
      (affineUnaryTripleProgressionFixedGroupLoopCfg groupLast
        ⟨0, by omega⟩
        (encodeAffineUnaryTripleProgressionFamily progressions) [])
      (some (affineUnaryTripleProgressionFixedGroupFinishCfg groupLast
        (affineUnaryTripleProgressionFixedGroupFrameStream groupLast
          progressions).reverse))
      (affineUnaryTripleProgressionFixedGroupStepsToFinish progressions) := by
    simpa [affineUnaryTripleProgressionFixedGroupFrameStream] using body
  have haltStep : EvalsToInTime
      (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
      (affineUnaryTripleProgressionFixedGroupFinishCfg groupLast
        (affineUnaryTripleProgressionFixedGroupFrameStream groupLast
          progressions).reverse)
      (some (haltCfg
        (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
        (affineUnaryTripleProgressionFixedGroupFrameStream groupLast
          progressions).reverse)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
    (affineUnaryTripleProgressionFixedGroupStepsToFinish progressions) 1 _ _ _
      body' haltStep
  simpa only [affineUnaryTripleProgressionFixedGroup_initialCfg_eq_loop,
    Nat.add_comm] using full

/-- Compiled fixed TM2 for the reversed group-marked triple stream. -/
noncomputable def
    affineUnaryTripleProgressionFixedGroupRev_computableInPolyTime
    (groupLast : Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleProgressionFamily id
      (fun progressions =>
        (affineUnaryTripleProgressionFixedGroupFrameStream groupLast
          progressions).reverse) where
  tm := compile (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 205 * Polynomial.X ^ 3 + 2
  outputsFun := fun progressions => by
    have builderRun :=
      affineUnaryTripleProgressionFixedGroupRev_run groupLast progressions
    have compiledRun := compile_evalsToInTime
      (affineUnaryTripleProgressionFixedGroupRevProgram groupLast) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile
          (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)).step
        (_root_.Turing.initList
          (compile
            (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
          (encodeAffineUnaryTripleProgressionFamily progressions))
        (some (_root_.Turing.haltList
          (compile
            (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
          (affineUnaryTripleProgressionFixedGroupFrameStream groupLast
            progressions).reverse))
        (affineUnaryTripleProgressionFixedGroupStepsToFinish progressions +
          1) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime :
        affineUnaryTripleProgressionFixedGroupStepsToFinish progressions + 1 ≤
          (205 * Polynomial.X ^ 3 + 2).eval
            (encodeAffineUnaryTripleProgressionFamily progressions).length := by
      have hbound :=
        affineUnaryTripleProgressionFixedGroupStepsToFinish_le progressions
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile
          (affineUnaryTripleProgressionFixedGroupRevProgram groupLast)).step
        (_root_.Turing.initList
          (compile
            (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
          (encodeAffineUnaryTripleProgressionFamily progressions))
        (some (_root_.Turing.haltList
          (compile
            (affineUnaryTripleProgressionFixedGroupRevProgram groupLast))
          (affineUnaryTripleProgressionFixedGroupFrameStream groupLast
            progressions).reverse))
        ((205 * Polynomial.X ^ 3 + 2).eval
          (encodeAffineUnaryTripleProgressionFamily progressions).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward group-marked triple stream. -/
noncomputable def
    affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime
    (groupLast : Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineUnaryTripleProgressionFamily id
      (affineUnaryTripleProgressionFixedGroupFrameStream groupLast) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineUnaryTripleProgressionFixedGroupRev_computableInPolyTime
        groupLast)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
