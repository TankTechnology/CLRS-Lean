import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionInputCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementHead
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros

/-!
# Static dispatch phase tags from transition-row markers

For a fixed verifier machine, the recursive statement syntax fixes every
statement-controller phase tag.  Only the numeric operand payloads vary with
the input.  This file turns each already compiled transition-row marker into
the complete fixed tag schedule by the verified bounded-loop macro, and proves
that the result is exactly the tag projection of the canonical dispatch
scripts, including tags belonging to nested branches.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Controller tag code indexed by the operand-erased phase kind. -/
def transitionStmtPhaseKindTagCode :
    TransitionStmtPhaseKind → List UnaryFrameSym
  | .oneHotMap => [.tick, .tick, .tick]
  | .oneHotPredicate => [.tick, .tick, .frameEnd]
  | .oneHotPairMap => [.tick, .tick, .separator]
  | .pop => [.tick, .frameEnd, .tick]
  | .mux => [.tick, .frameEnd, .frameEnd]

/-- Erasing a phase's operands preserves its literal three-symbol tag. -/
@[simp] theorem transitionStmtPhaseKindTagCode_kind
    (phase : AffineStmtPhase) :
    transitionStmtPhaseKindTagCode (transitionStmtPhaseKind phase) =
      affineStmtPhaseTagCode phase := by
  cases phase <;> rfl

/-- Complete fixed dispatch tag word for one local transition. -/
def transitionDispatchPhaseTagSchedule
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  (transitionDispatchPhaseKinds tm).flatMap transitionStmtPhaseKindTagCode

/-- Tag-only projection of one concrete local transition dispatch. -/
def transitionScriptDispatchPhaseTagFrames
    (script : AffineTransitionScript) : List UnaryFrameSym :=
  script.dispatch.flatMap affineStmtPhaseTagCode

/-- The tag projection factors through the already verified phase-kind
projection. -/
theorem transitionScriptDispatchPhaseTagFrames_eq_kinds
    (script : AffineTransitionScript) :
    transitionScriptDispatchPhaseTagFrames script =
      (transitionScriptDispatchPhaseKinds script).flatMap
        transitionStmtPhaseKindTagCode := by
  unfold transitionScriptDispatchPhaseTagFrames
    transitionScriptDispatchPhaseKinds
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro phase _
  exact transitionStmtPhaseKindTagCode_kind phase |>.symm

private theorem flatMap_replicate
    {α β : Type} (count : Nat) (value : α) (f : α → List β) :
    (List.replicate count value).flatMap f =
      (List.replicate count (f value)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

/-- The complete canonical transition family repeats one fixed tag schedule
once for every adjacent tableau-row pair. -/
theorem compileTransitionFamilyScriptsAt_dispatchPhaseTagFrames_eq
    (tm : _root_.Turing.FinTM2) (height horizon : Nat) :
    (compileTransitionFamilyScriptsAt tm height horizon).flatMap
        transitionScriptDispatchPhaseTagFrames =
      (List.replicate horizon
        (transitionDispatchPhaseTagSchedule tm)).flatten := by
  let scripts := compileTransitionFamilyScriptsAt tm height horizon
  have hkinds :
      scripts.map transitionScriptDispatchPhaseKinds =
        List.ofFn fun _step : Fin horizon =>
          transitionDispatchPhaseKinds tm := by
    exact compileTransitionFamilyScriptsAt_dispatchPhaseKinds_eq_ofFn
      tm height horizon
  calc
    scripts.flatMap transitionScriptDispatchPhaseTagFrames =
        (scripts.map transitionScriptDispatchPhaseKinds).flatMap
          (fun kinds => kinds.flatMap transitionStmtPhaseKindTagCode) := by
      rw [List.flatMap_map]
      apply List.flatMap_congr
      intro script _
      exact transitionScriptDispatchPhaseTagFrames_eq_kinds script
    _ = (List.replicate horizon (transitionDispatchPhaseKinds tm)).flatMap
          (fun kinds => kinds.flatMap transitionStmtPhaseKindTagCode) := by
      rw [hkinds, List.ofFn_const]
    _ = (List.replicate horizon
          (transitionDispatchPhaseTagSchedule tm)).flatten := by
      exact flatMap_replicate horizon (transitionDispatchPhaseKinds tm)
        (fun kinds => kinds.flatMap transitionStmtPhaseKindTagCode)

/-- One fixed list-valued streaming action: discard ordinary seed bytes and
replace each row marker by the verifier-fixed complete tag schedule. -/
def transitionDispatchPhaseTagExpandBody
    (tm : _root_.Turing.FinTM2) : LoopBody UnaryFrameSym UnaryFrameSym where
  emit symbol :=
    if symbol = .frameEnd then transitionDispatchPhaseTagSchedule tm else []
  cost _ := (transitionDispatchPhaseTagSchedule tm).length
  emit_length_le_cost symbol := by
    by_cases h : symbol = UnaryFrameSym.frameEnd
    · simp [h]
    · simp [h]

/-- Raw-input target emitted by the marker expander. -/
def verifierTransitionDispatchPhaseTagFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (List.replicate (verifierTransitionRowSeeds W input).length
    (transitionDispatchPhaseTagSchedule W.machine.tm)).flatten

private theorem phaseTagExpand_encodeUnaryFrame
    (tm : _root_.Turing.FinTM2) (values : List Nat) :
    (encodeUnaryFrame values).flatMap
        (transitionDispatchPhaseTagExpandBody tm).emit = [] := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change
        (encodeUnaryFrameBlock value ++ encodeUnaryFrame values).flatMap
            (transitionDispatchPhaseTagExpandBody tm).emit = []
      rw [List.flatMap_append, ih]
      simp [encodeUnaryFrameBlock, transitionDispatchPhaseTagExpandBody]

private theorem phaseTagExpand_markedFrame
    (tm : _root_.Turing.FinTM2) (values : List Nat) :
    (encodeUnaryFrame values ++ [UnaryFrameSym.frameEnd]).flatMap
        (transitionDispatchPhaseTagExpandBody tm).emit =
      transitionDispatchPhaseTagSchedule tm := by
  rw [List.flatMap_append, phaseTagExpand_encodeUnaryFrame]
  simp [transitionDispatchPhaseTagExpandBody]

private theorem phaseTagExpand_markedSeedRows
    (tm : _root_.Turing.FinTM2) (seeds : List TransitionRowSeed) :
    (seeds.flatMap fun seed =>
        encodeUnaryFrame [seed.height, seed.start, seed.rowBase] ++
          [.frameEnd]).flatMap
        (transitionDispatchPhaseTagExpandBody tm).emit =
      (List.replicate seeds.length
        (transitionDispatchPhaseTagSchedule tm)).flatten := by
  induction seeds with
  | nil => rfl
  | cons seed seeds ih =>
      simp only [List.flatMap_cons, List.length_cons, List.replicate_succ,
        List.flatten_cons]
      conv_lhs => rw [List.flatMap_append]
      rw [phaseTagExpand_markedFrame, ih]

/-- Applying the verified bounded loop to the concrete marked seed compiler
produces the literal static tag target. -/
theorem verifierTransitionRowMarkedSeedFrames_expandPhaseTags
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionRowMarkedSeedFrames W input).flatMap
        (transitionDispatchPhaseTagExpandBody W.machine.tm).emit =
      verifierTransitionDispatchPhaseTagFrames W input := by
  rw [verifierTransitionRowMarkedSeedFrames_eq_seeds]
  exact phaseTagExpand_markedSeedRows W.machine.tm
    (verifierTransitionRowSeeds W input)

/-- The raw seed family has exactly one row per verifier horizon step. -/
@[simp] theorem verifierTransitionRowSeeds_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionRowSeeds W input).length =
      (verifierHorizon W).eval input.length := by
  unfold verifierTransitionRowSeeds
  rw [verifierTransitionRowSeedTriples_eq_ofFn]
  simp

/-- The generated static stream is not merely a schedule surrogate: it is
byte-for-byte the tag projection of every canonical verifier dispatch. -/
theorem verifierTransitionDispatchPhaseTagFrames_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchPhaseTagFrames W input =
      (verifierTransitionFamilyScripts W input).flatMap
        transitionScriptDispatchPhaseTagFrames := by
  rw [verifierTransitionFamilyScripts_eq_canonical]
  rw [compileTransitionFamilyScriptsAt_dispatchPhaseTagFrames_eq]
  simp [verifierTransitionDispatchPhaseTagFrames]

/-- A concrete fixed polynomial-time TM2 emits every dispatch phase tag,
including nested statement tags, directly from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchPhaseTagFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchPhaseTagFrames W) := by
  let seedCompiler :=
    verifierTransitionRowMarkedSeedFrames_computableInPolyTime W
  let tagExpander := boundedLoop_computableInPolyTime
    (transitionDispatchPhaseTagExpandBody W.machine.tm)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      seedCompiler tagExpander
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionRowMarkedSeedFrames_expandPhaseTags W input]
          using run }

end CLRS.Chapter34.Turing.CookLevin
