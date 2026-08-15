import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInitialBoundary
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputShapeController

/-!
# Exact verifier-input boundary target

This module specializes the generic three-phase input-shape trace to the
assembled verifier immediately after the symbolic initial-row boundary.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open StateTransition
open PolyBuilder

namespace VerifierInput

/-- Canonical optional conjunction frames for the first `n` candidate
certificate lengths.  A nonfitting length is represented by `none`, hence by
an explicit runtime branch that emits zero gates. -/
def compileInputArmFrames {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none)))) :
    Nat → List (Option AffineConjunctionFrame)
  | 0 => []
  | n + 1 =>
      let previous := buildInputArms W H x start pool stack hstack
        separatorNots hseparatorNots hseparatorEval n
      compileInputArmFrames W H x start pool stack hstack separatorNots
          hseparatorNots hseparatorEval n ++
        [if hfit : n + 1 + x.length ≤ H then
          some
            { start := previous.builder.gates.length
              wires := inputArmWires W H x stack separatorNots n hfit }
        else none]

/-- Interpreting the canonical optional frame family yields exactly the
recursive input-arm gate trace, including every zero-gate branch. -/
theorem compileInputArmFrames_gateStream_eq_trace
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (n : Nat) :
    affineOptionalConjunctionFamilyGateStream
        (compileInputArmFrames W H x start pool stack hstack separatorNots
          hseparatorNots hseparatorEval n) =
      (inputArmsGateTrace W H x start pool stack hstack separatorNots
        hseparatorNots hseparatorEval n).flatMap encodeCircuitGate := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [compileInputArmFrames, inputArmsGateTrace,
        affineOptionalConjunctionFamilyGateStream, List.flatMap_append,
        List.flatMap_singleton]
      unfold affineOptionalConjunctionFamilyGateStream at ih
      rw [ih]
      by_cases hfit : n + 1 + x.length ≤ H
      · simp [hfit, affineOptionalConjunctionEntryGateStream,
          inputArmGateTrace, affineConjunctionGateStream_eq_trace]
      · simp [hfit, affineOptionalConjunctionEntryGateStream,
          inputArmGateTrace]

end VerifierInput

/-- The verifier specialization uses the generic continuous input-shape
controller's operand-level runtime script without changing its encoding. -/
abbrev AffineVerifierInputShapeScript := AffineInputShapeScript

def affineVerifierInputShapeScriptGateStream
    (script : AffineVerifierInputShapeScript) : List CircuitSym :=
  affineInputShapeGateStream script

def encodeAffineVerifierInputShapeScript
    (script : AffineVerifierInputShapeScript) : List UnaryFrameSym :=
  encodeAffineInputShapeScript script

def affineVerifierInputShapeRevSteps
    (script : AffineVerifierInputShapeScript) : Nat :=
  affineInputShapeRevSteps script

/-- One fixed nonhalting controller executes separator NOTs, optional arms,
and the final OR as a single verifier-input boundary computation. -/
def affineVerifierInputShape_run (script : AffineVerifierInputShapeScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineInputShapeRevProgram)
      (affineInputShapeLoopCfg
        (encodeAffineVerifierInputShapeScript script) output)
      (some (haltCfg affineInputShapeRevProgram
        ((affineVerifierInputShapeScriptGateStream script).reverse ++ output)))
      (affineVerifierInputShapeRevSteps script) := by
  exact affineInputShape_run script output

theorem affineVerifierInputShapeRev_steps_le
    (script : AffineVerifierInputShapeScript) :
    affineVerifierInputShapeRevSteps script ≤
      1200 * (encodeAffineVerifierInputShapeScript script).length ^ 2 + 20 :=
  affineInputShapeRev_steps_le script

/-- Extract the three canonical runtime operand families structurally from
the proof-carrying input-shape builder. -/
def compileVerifierInputShapeScript {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) :
    AffineVerifierInputShapeScript :=
  let separatorNots := VerifierInput.buildSeparatorNots base inputStack
    hinputStack (verifierInputCode W none)
  let pool' := pool.mono separatorNots.extension
  let hstack' := hinputStack.mono separatorNots.extension
  let hseparatorEval := fun inputs cell => by
    rw [separatorNots.eval, separatorNots.extension.evalWire_eq inputs
      (hinputStack.cell cell (verifierInputCode W none))]
  let bound := W.certificateBound.eval x.length
  let arms := VerifierInput.buildInputArms W H x separatorNots.builder pool'
    inputStack hstack' separatorNots.wires separatorNots.valid
      hseparatorEval (bound + 1)
  { separatorSources := VerifierInput.separatorNotSources inputStack
      (verifierInputCode W none)
    armFrames := VerifierInput.compileInputArmFrames W H x
      separatorNots.builder pool' inputStack hstack' separatorNots.wires
      separatorNots.valid hseparatorEval (bound + 1)
    finalOrStart := arms.builder.gates.length
    finalOrWires := List.ofFn arms.wires }

/-- The compiled runtime script denotes exactly the semantic input-shape
trace, byte for byte. -/
theorem compileVerifierInputShapeScript_gateStream_eq_trace
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) :
    affineVerifierInputShapeScriptGateStream
        (compileVerifierInputShapeScript W H x base pool inputStack
          hinputStack) =
      (verifierInputShapeGateTrace W H x base pool inputStack
        hinputStack).flatMap encodeCircuitGate := by
  simp only [compileVerifierInputShapeScript,
    affineVerifierInputShapeScriptGateStream,
    affineInputShapeGateStream, affineInputShapeFinalOrFrames,
    verifierInputShapeGateTrace]
  rw [affineNotFamilyGateStream_eq_trace]
  rw [VerifierInput.separatorNotsGateTrace_eq_sources]
  rw [VerifierInput.compileInputArmFrames_gateStream_eq_trace]
  rw [affineOrFinCanonicalGateStream_eq_trace]
  simp [List.flatMap_append, List.append_assoc]

/-- Canonical runtime operand list for the separator-NOT prefix at the
assembled verifier input stack. -/
def verifierInputSeparatorSources
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List Nat :=
  let rows := verifierRows W x
  let row := rows.rows (verifierFirstRow _)
  VerifierInput.separatorNotSources (row.stack W.machine.tm.k₀)
    (verifierInputCode W none)

/-- The fixed NOT-family controller's canonical operands denote byte-for-byte
the semantic separator-negation prefix. -/
theorem verifierInputSeparatorGateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineNotFamilyGateStream (verifierInputSeparatorSources W x) =
      (VerifierInput.separatorNotsGateTrace
        (((verifierRows W x).rows (verifierFirstRow _)).stack
          W.machine.tm.k₀)
        (verifierInputCode W none)).flatMap encodeCircuitGate := by
  rw [affineNotFamilyGateStream_eq_trace]
  rw [VerifierInput.separatorNotsGateTrace_eq_sources]
  rfl

/-- Exact execution of the first input-boundary phase by one fixed program. -/
def verifierInputSeparator_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineNotFamilyRevProgram)
      (affineNotFamilyLoopCfg
        (encodeAffineNotFamilySources (verifierInputSeparatorSources W x))
        output)
      (some (haltCfg affineNotFamilyRevProgram
        (((VerifierInput.separatorNotsGateTrace
          (((verifierRows W x).rows (verifierFirstRow _)).stack
            W.machine.tm.k₀)
          (verifierInputCode W none)).flatMap encodeCircuitGate).reverse ++
            output)))
      (affineNotFamilyRevSteps (verifierInputSeparatorSources W x)) := by
  simpa [verifierInputSeparatorGateStream_eq] using
    affineNotFamily_run (verifierInputSeparatorSources W x) output

/-- Literal separator-NOT, length-arm, and final-OR trace at the verifier's
actual first-row input stack. -/
def verifierInputBoundaryGateTrace
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitGate :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let extension := pool.extension.trans (validity.extension.trans
    (transitions.extension.trans initial.extension))
  let row := rows.rows (verifierFirstRow _)
  let hrow := (rows.rowValid (verifierFirstRow _)).mono extension
  verifierInputShapeGateTrace W ((verifierHeight W).eval x.length) x
    initial.builder
    (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans initial.extension)))
    (row.stack W.machine.tm.k₀) (hrow.stack _)

/-- Canonical three-phase runtime script at the assembled verifier boundary. -/
def verifierInputBoundaryScript
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : AffineVerifierInputShapeScript :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let extension := pool.extension.trans (validity.extension.trans
    (transitions.extension.trans initial.extension))
  let row := rows.rows (verifierFirstRow _)
  let hrow := (rows.rowValid (verifierFirstRow _)).mono extension
  compileVerifierInputShapeScript W ((verifierHeight W).eval x.length) x
    initial.builder
    (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans initial.extension)))
    (row.stack W.machine.tm.k₀) (hrow.stack _)

/-- The assembled input-boundary builder appends exactly its literal
three-phase trace. -/
theorem verifierInputBoundary_gates_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    (verifierInputBoundary W x).builder.gates =
      (verifierInitialBoundary W x).builder.gates ++
        verifierInputBoundaryGateTrace W x := by
  simpa [verifierInputBoundary, verifierInputBoundaryGateTrace] using
    verifierInputShapeCircuit_gates_eq W
      ((verifierHeight W).eval x.length) x
      (verifierInitialBoundary W x).builder
      ((verifierPool W x).pool.mono
        ((verifierValidity W x).extension.trans
          ((verifierTransitions W x).extension.trans
            (verifierInitialBoundary W x).extension)))
      (((verifierRows W x).rows (verifierFirstRow _)).stack
        W.machine.tm.k₀)
      ((((verifierRows W x).rowValid (verifierFirstRow _)).mono
          ((verifierPool W x).extension.trans
            ((verifierValidity W x).extension.trans
              ((verifierTransitions W x).extension.trans
                (verifierInitialBoundary W x).extension)))).stack
        W.machine.tm.k₀)

/-- Exact encoded byte suffix of the complete input-shape boundary. -/
def verifierInputBoundaryGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitSym :=
  (verifierInputBoundaryGateTrace W x).flatMap encodeCircuitGate

/-- The assembled runtime script denotes the complete frozen input-boundary
byte stream. -/
theorem verifierInputBoundaryScript_gateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineVerifierInputShapeScriptGateStream
        (verifierInputBoundaryScript W x) =
      verifierInputBoundaryGateStream W x := by
  simpa [verifierInputBoundaryScript, verifierInputBoundaryGateStream,
    verifierInputBoundaryGateTrace] using
    compileVerifierInputShapeScript_gateStream_eq_trace W
      ((verifierHeight W).eval x.length) x
      (verifierInitialBoundary W x).builder
      ((verifierPool W x).pool.mono
        ((verifierValidity W x).extension.trans
          ((verifierTransitions W x).extension.trans
            (verifierInitialBoundary W x).extension)))
      (((verifierRows W x).rows (verifierFirstRow _)).stack
        W.machine.tm.k₀)
      ((((verifierRows W x).rowValid (verifierFirstRow _)).mono
          ((verifierPool W x).extension.trans
            ((verifierValidity W x).extension.trans
              ((verifierTransitions W x).extension.trans
                (verifierInitialBoundary W x).extension)))).stack
        W.machine.tm.k₀)

/-- Exact continuous execution of the complete frozen verifier-input
boundary, with no component-level halt between its three phases. -/
def verifierInputBoundary_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineInputShapeRevProgram)
      (affineInputShapeLoopCfg
        (encodeAffineVerifierInputShapeScript
          (verifierInputBoundaryScript W x)) output)
      (some (haltCfg affineInputShapeRevProgram
        ((verifierInputBoundaryGateStream W x).reverse ++ output)))
      (affineVerifierInputShapeRevSteps
        (verifierInputBoundaryScript W x)) := by
  simpa [verifierInputBoundaryScript_gateStream_eq] using
    affineVerifierInputShape_run (verifierInputBoundaryScript W x) output

/-- The specialized verifier-input execution inherits the controller's
uniform quadratic envelope in its explicit runtime operand encoding. -/
theorem verifierInputBoundary_steps_le
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineVerifierInputShapeRevSteps (verifierInputBoundaryScript W x) ≤
      1200 * (encodeAffineVerifierInputShapeScript
        (verifierInputBoundaryScript W x)).length ^ 2 + 20 :=
  affineVerifierInputShapeRev_steps_le (verifierInputBoundaryScript W x)

/-- Exact execution of all optional certificate-length arms. -/
def verifierInputBoundaryArms_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineOptionalConjunctionFamilyRevProgram)
      (affineOptionalConjunctionFamilyLoopCfg
        (encodeAffineOptionalConjunctionFamily
          (verifierInputBoundaryScript W x).armFrames) output)
      (some (haltCfg affineOptionalConjunctionFamilyRevProgram
        ((affineOptionalConjunctionFamilyGateStream
          (verifierInputBoundaryScript W x).armFrames).reverse ++ output)))
      (affineOptionalConjunctionFamilyRevSteps
        (verifierInputBoundaryScript W x).armFrames) :=
  affineOptionalConjunctionFamily_run
    (verifierInputBoundaryScript W x).armFrames output

/-- Exact execution of the final disjunction over all candidate-length arms. -/
def verifierInputBoundaryFinalOr_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg
        (encodeAffineOrFinFrames (affineOrFinCanonicalFrames
          (verifierInputBoundaryScript W x).finalOrStart
          (verifierInputBoundaryScript W x).finalOrWires)) output)
      (some (haltCfg affineOrFinRevProgram
        (((CircuitBuilder.disjunctionGateTrace
          (verifierInputBoundaryScript W x).finalOrStart
          (verifierInputBoundaryScript W x).finalOrWires).gates.flatMap
            encodeCircuitGate).reverse ++ output)))
      (affineOrFinRevSteps (affineOrFinCanonicalFrames
        (verifierInputBoundaryScript W x).finalOrStart
        (verifierInputBoundaryScript W x).finalOrWires)) :=
  affineOrFinCanonical_run
    (verifierInputBoundaryScript W x).finalOrStart
    (verifierInputBoundaryScript W x).finalOrWires output

end

end CLRS.Chapter34.Turing.CookLevin
