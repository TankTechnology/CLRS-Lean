import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeed
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailAffine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqAlignment
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqRowSentinel
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionNarrowNotFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionFinalAndFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryTripleRowMark

/-!
# Canonical complete transition-family input

This file fixes the exact byte target of the remaining transition source
compiler.  The raw-input row seeds, their complete arithmetic expansion, the
runtime family controller input, and the semantic transition gate stream are
connected by literal equalities rather than extensional substitutes.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open StateTransition
open PolyBuilder

/-- Expand a row-major seed family to the complete runtime scripts consumed by
the transition-family controller.  The following public row starts exactly one
configuration width after the current row. -/
def transitionSeedFamilyScripts (tm : _root_.Turing.FinTM2)
    (seeds : List TransitionRowSeed) : List AffineTransitionScript :=
  seeds.map fun seed =>
    transitionScriptFromSeed tm seed
      (seed.rowBase + cfgBitCount tm seed.height)

/-- Exact controller alphabet encoding of a complete seed family. -/
def transitionSeedFamilyInput (tm : _root_.Turing.FinTM2)
    (seeds : List TransitionRowSeed) : List AffineStmtScriptSym :=
  encodeAffineTransitionFamily (transitionSeedFamilyScripts tm seeds)

/-- Pure-unary form of the same family input, before embedding it into the
statement-controller alphabet.  All phase tags of the continuous statement
controller are themselves encoded by fixed unary prefixes. -/
def transitionSeedFamilyUnaryInput (tm : _root_.Turing.FinTM2)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  encodeAffineTransitionFamilyUnary (transitionSeedFamilyScripts tm seeds)

/-- Pure-unary payload of one row seed, including the local controller's
trailing terminator but excluding the outer family's leading marker. -/
def transitionSeedLocalUnaryInput (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) : List UnaryFrameSym :=
  encodeAffineTransitionLocalUnary
    (transitionScriptFromSeed tm seed
      (seed.rowBase + cfgBitCount tm seed.height))

/-- The complete unary target is a literal row-major packet stream.  This is
the interface used by the forthcoming fixed seed-family expander. -/
theorem transitionSeedFamilyUnaryInput_eq_flatMap
    (tm : _root_.Turing.FinTM2) (seeds : List TransitionRowSeed) :
    transitionSeedFamilyUnaryInput tm seeds =
      seeds.flatMap fun seed =>
        .frameEnd :: transitionSeedLocalUnaryInput tm seed := by
  unfold transitionSeedFamilyUnaryInput transitionSeedFamilyScripts
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineTransitionFamilyUnary,
        transitionSeedLocalUnaryInput, ih]

/-- The controller-alphabet target is only the fixed `.data` symbol map over
the pure-unary seed expansion. -/
theorem transitionSeedFamilyInput_eq_map_data
    (tm : _root_.Turing.FinTM2) (seeds : List TransitionRowSeed) :
    transitionSeedFamilyInput tm seeds =
      (transitionSeedFamilyUnaryInput tm seeds).map .data := by
  rfl

/-- Complete transition scripts derived from the verifier's concrete
raw-input seed family. -/
def verifierTransitionFamilyScripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineTransitionScript :=
  transitionSeedFamilyScripts W.machine.tm
    (verifierTransitionRowSeeds W input)

/-- Unique byte-level target for the remaining raw-input transition source
compiler. -/
def verifierTransitionFamilyInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineStmtScriptSym :=
  transitionSeedFamilyInput W.machine.tm
    (verifierTransitionRowSeeds W input)

/-- Raw-verifier specialization of the pure-unary source target. -/
def verifierTransitionFamilyUnaryInputTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  transitionSeedFamilyUnaryInput W.machine.tm
    (verifierTransitionRowSeeds W input)

/-- The exact controller input is the verified fixed symbol map of the unary
source target. -/
theorem verifierTransitionFamilyInputTarget_eq_map_data
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFamilyInputTarget W input =
      (verifierTransitionFamilyUnaryInputTarget W input).map .data := by
  rfl

/-- Raw-input unary target in explicit row-packet order. -/
theorem verifierTransitionFamilyUnaryInputTarget_eq_flatMap
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFamilyUnaryInputTarget W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        .frameEnd :: transitionSeedLocalUnaryInput W.machine.tm seed := by
  exact transitionSeedFamilyUnaryInput_eq_flatMap W.machine.tm
    (verifierTransitionRowSeeds W input)

/-! ## Concrete marked seed source -/

/-- Ordinary value-level triples underlying a transition seed family. -/
def transitionRowSeedTriples (seeds : List TransitionRowSeed) :
    List (Nat × Nat × Nat) :=
  seeds.map fun seed => (seed.height, seed.start, seed.rowBase)

/-- The raw seed source is exactly the ordinary flat triple encoding expected
by the reusable row marker. -/
theorem verifierTransitionRowSeedFrames_eq_triples
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRowSeedFrames W input =
      encodeUnaryTripleRows
        (transitionRowSeedTriples (verifierTransitionRowSeeds W input)) := by
  rw [verifierTransitionRowSeedFrames_eq_seeds]
  simp [encodeUnaryTripleRows, transitionRowSeedTriples,
    List.flatMap_map]

/-- Row-delimited transition seeds produced from the raw verifier word.  The
marker follows each complete three-field seed and is consumed by the local-row
source controller, so it cannot be confused with field separators. -/
def verifierTransitionRowMarkedSeedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  markUnaryTripleRows (verifierTransitionRowSeedFrames W input)

/-- Exact semantic packet order of the marked raw-input seed source. -/
theorem verifierTransitionRowMarkedSeedFrames_eq_seeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRowMarkedSeedFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame [seed.height, seed.start, seed.rowBase] ++
          [.frameEnd] := by
  unfold verifierTransitionRowMarkedSeedFrames
  rw [verifierTransitionRowSeedFrames_eq_triples,
    markUnaryTripleRows_encode]
  simp [encodeUnaryTripleMarkedRows, transitionRowSeedTriples,
    List.flatMap_map]

/-- A concrete fixed polynomial-time TM2 generates the row-delimited seed
packets directly from the raw verifier word. -/
noncomputable def
    verifierTransitionRowMarkedSeedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionRowMarkedSeedFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierTransitionRowSeedFrames_computableInPolyTime W)
      markUnaryTripleRows_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => markUnaryTripleRows
      (verifierTransitionRowSeedFrames W input))
  simpa [Function.comp_def] using Classical.choice composed

/-- Expanding the polynomial-time row seeds recovers the canonical semantic
transition-family script, field for field. -/
theorem verifierTransitionFamilyScripts_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFamilyScripts W input =
      compileTransitionFamilyScriptsAt W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length) := by
  exact verifierTransitionRowSeeds_expand_eq_scripts W input

/-- Consequently the source target is literally the runtime encoding expected
by the already verified transition-family controller. -/
theorem verifierTransitionFamilyInputTarget_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFamilyInputTarget W input =
      encodeAffineTransitionFamily
        (compileTransitionFamilyScriptsAt W.machine.tm
          ((verifierHeight W).eval input.length)
          ((verifierHorizon W).eval input.length)) := by
  change encodeAffineTransitionFamily
      (verifierTransitionFamilyScripts W input) = _
  rw [verifierTransitionFamilyScripts_eq_canonical]

/-- Interpreting the seed-expanded family yields exactly the frozen semantic
transition suffix of the verifier circuit. -/
theorem verifierTransitionFamilyGateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineTransitionFamilyGateStream
        (verifierTransitionFamilyScripts W input) =
      verifierTransitionGateStream W input := by
  rw [verifierTransitionFamilyScripts_eq_canonical]
  simpa [verifierTransitionGateStream,
    verifierTransitionGateStreamByLength] using
    compileTransitionFamilyScriptsAt_gateStream_eq W.machine.tm
      ((verifierHeight W).eval input.length)
      ((verifierHorizon W).eval input.length)

/-- The fixed transition-family controller runs directly on the exact
seed-derived byte target and halts with the semantic transition suffix. -/
def verifierTransitionFamily_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionFamilyRevProgram)
      (affineTransitionFamilyLoopCfg
        (verifierTransitionFamilyInputTarget W input) output)
      (some (haltCfg affineTransitionFamilyRevProgram
        ((verifierTransitionGateStream W input).reverse ++ output)))
      (affineTransitionFamilyTotalSteps
        (verifierTransitionFamilyScripts W input)) := by
  have hrun := affineTransitionFamily_run
    (verifierTransitionFamilyScripts W input) output
  rw [verifierTransitionFamilyGateStream_eq W input] at hrun
  simpa [verifierTransitionFamilyInputTarget,
    transitionSeedFamilyInput,
    verifierTransitionFamilyScripts] using hrun

/-- The verified fixed symbol map lifts any concrete unary source compiler to
the exact controller-alphabet input target. -/
noncomputable def
    verifierTransitionFamilyInputTarget_computableInPolyTime_of_unaryCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (compiler : _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionFamilyUnaryInputTarget W)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionFamilyInputTarget W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch compiler
      (listMap_computableInPolyTime AffineStmtScriptSym.data)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (verifierTransitionFamilyUnaryInputTarget W input).map
        AffineStmtScriptSym.data)
  simpa only [Function.comp_def] using Classical.choice composed

/-- Once a concrete source TM2 emits the exact target fixed above, generic
machine composition produces the verifier transition gate stream.  The
premise is deliberately byte-level, so the remaining source proof cannot hide
an oracle-valued script behind an encoding equivalence. -/
noncomputable def
    verifierTransitionGateStream_computableInPolyTime_of_inputCompiler
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (compiler : _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionFamilyInputTarget W)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionGateStream W) := by
  let typedCompiler : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineTransitionFamily (verifierTransitionFamilyScripts W) :=
    { tm := compiler.tm
      inputAlphabet := compiler.inputAlphabet
      outputAlphabet := compiler.outputAlphabet
      time := compiler.time
      outputsFun := fun input => by
        simpa only [id_eq, verifierTransitionFamilyInputTarget,
          transitionSeedFamilyInput, verifierTransitionFamilyScripts]
          using compiler.outputsFun input }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      typedCompiler affineTransitionFamilyGateStream_computableInPolyTime
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionFamilyGateStream_eq W input] using run }

end CLRS.Chapter34.Turing.CookLevin
