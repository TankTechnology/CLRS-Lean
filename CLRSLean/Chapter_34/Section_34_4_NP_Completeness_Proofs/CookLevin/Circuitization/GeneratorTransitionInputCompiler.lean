import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeed

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
