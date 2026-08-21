import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConjunctionCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBody
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameSameInputAddPolynomial

/-!
# Complete raw-input compiler for the Cook--Levin verifier body

The final missing field is the selected circuit output wire.  The conjunction
starts at the accepting-boundary endpoint and appends one true seed followed
by one gate per constraint, so its output is the endpoint plus the number of
constraints.  This file generates that exact unary block and closes the
concrete compiler premise required by `GeneratorBody`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact polynomial number of verifier constraints conjoined at the end. -/
def verifierFinalConstraintCountPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) : Polynomial Nat :=
  Polynomial.C 2 * verifierHorizon W + 4

@[simp] theorem verifierFinalConstraintCountPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierFinalConstraintCountPolynomial W).eval n =
      ((verifierHorizon W).eval n + 1) +
        (verifierHorizon W).eval n + 3 := by
  simp [verifierFinalConstraintCountPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul]
  omega

/-- Builder-free arithmetic formula for the selected final output wire. -/
def verifierCircuitOutput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  verifierAcceptingBoundaryEnd W input +
    (verifierFinalConstraintCountPolynomial W).eval input.length

/-- The assembled verifier circuit selects exactly the generated output. -/
theorem verifierCircuit_output_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierCircuit W input).output = verifierCircuitOutput W input := by
  change (verifierConjunction W input).2 = verifierCircuitOutput W input
  unfold verifierConjunction
  rw [CircuitBuilder.conjunction_wire_eq_trace,
    CircuitBuilder.conjunctionGateTrace_wire_eq,
    verifierAcceptingBoundary_gates_length_eq_end,
    verifierConstraintWires_length]
  simp [verifierCircuitOutput]

/-- Unary block containing the selected final circuit-output wire. -/
def verifierCircuitOutputFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  unaryFrameSameInputAddPolynomial
    (verifierAcceptingBoundaryEnd W)
    (verifierFinalConstraintCountPolynomial W) input

@[simp] theorem verifierCircuitOutputFrame_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierCircuitOutputFrame W input =
      encodeUnaryFrameBlock (verifierCircuit W input).output := by
  rw [verifierCircuit_output_eq]
  simp [verifierCircuitOutputFrame, verifierCircuitOutput,
    encodeUnaryFrameBlock]
  unfold encodeUnaryFrame
  simp [encodeUnaryFrameBlock]

/-- A fixed polynomial-time TM2 emits the final output-wire block. -/
noncomputable def verifierCircuitOutputFrame_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierCircuitOutputFrame W) := by
  letI : Fintype Γ := W.alphabetFintype
  let endpointRaw := verifierAcceptingBoundaryEndFrame_computableInPolyTime W
  let endpoint : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeUnaryFrame [verifierAcceptingBoundaryEnd W input]) :=
    { tm := endpointRaw.tm
      inputAlphabet := endpointRaw.inputAlphabet
      outputAlphabet := endpointRaw.outputAlphabet
      time := endpointRaw.time
      outputsFun := fun input => by
        have run := endpointRaw.outputsFun input
        rw [verifierAcceptingBoundaryEndFrame_eq] at run
        simpa only [id_eq] using run }
  change _root_.Turing.TM2ComputableInPolyTime id id
    (unaryFrameSameInputAddPolynomial
      (verifierAcceptingBoundaryEnd W)
      (verifierFinalConstraintCountPolynomial W))
  exact unaryFrameSameInputAddPolynomial_computableInPolyTime
    (verifierAcceptingBoundaryEnd W)
    (verifierFinalConstraintCountPolynomial W) endpoint

/-- Complete unary encoding of the canonical verifier-body script. -/
def verifierCompleteBodyUnaryTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierBodyThroughConjunctionUnaryTarget W input ++
    verifierCircuitOutputFrame W input

theorem verifierCompleteBodyUnaryTarget_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierCompleteBodyUnaryTarget W input =
      encodeAffineVerifierBodyUnary (compileVerifierBodyScript W input) := by
  rw [encodeAffineVerifierBodyUnary_eq_throughConjunction_append]
  simp [verifierCompleteBodyUnaryTarget]

/-- A fixed polynomial-time TM2 emits the full unary verifier-body script. -/
noncomputable def verifierCompleteBodyUnaryTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierCompleteBodyUnaryTarget W) := by
  letI : Fintype Γ := W.alphabetFintype
  let bodyPrefix :=
    verifierBodyThroughConjunctionUnaryTarget_computableInPolyTime W
  let output := verifierCircuitOutputFrame_computableInPolyTime W
  let complete := unaryFrameSameInputConcat_computableInPolyTime
    bodyPrefix output
  exact
    { tm := complete.tm
      inputAlphabet := complete.inputAlphabet
      outputAlphabet := complete.outputAlphabet
      time := complete.time
      outputsFun := fun input => by
        have run := complete.outputsFun input
        simpa only [id_eq, verifierCompleteBodyUnaryTarget] using run }

/-- Complete body-script target in the common controller alphabet. -/
def verifierCompleteBodyTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineStmtScriptSym :=
  (verifierCompleteBodyUnaryTarget W input).map .data

@[simp] theorem verifierCompleteBodyTarget_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierCompleteBodyTarget W input =
      encodeAffineVerifierBodyScript (compileVerifierBodyScript W input) := by
  simp [verifierCompleteBodyTarget, encodeAffineVerifierBodyScript,
    verifierCompleteBodyUnaryTarget_eq]

/-- A fixed polynomial-time TM2 emits the exact common-alphabet body script. -/
noncomputable def verifierCompleteBodyTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierCompleteBodyTarget W) := by
  let unary := verifierCompleteBodyUnaryTarget_computableInPolyTime W
  let mappedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch unary
      (listMap_computableInPolyTime AffineStmtScriptSym.data)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (verifierCompleteBodyUnaryTarget W input).map
        AffineStmtScriptSym.data)
  simpa only [Function.comp_def] using Classical.choice mappedExists

/-- The formerly abstract body-script compiler premise is now discharged by
one concrete fixed TM2 operating on the raw source input. -/
noncomputable def compileVerifierBodyScript_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineVerifierBodyScript (compileVerifierBodyScript W) := by
  let source := verifierCompleteBodyTarget_computableInPolyTime W
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have run := source.outputsFun input
        rw [verifierCompleteBodyTarget_eq] at run
        simpa only [id_eq] using run }

/-- The exact forward verifier-body gate stream is polynomial-time computable
from the original source word by a fixed TM2. -/
noncomputable def verifierCircuitBodyGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierCircuitBodyGateStream W) :=
  verifierCircuitBodyGateStream_computableInPolyTime_of_scriptCompiler W
    (compileVerifierBodyScript_computableInPolyTime W)

end CLRS.Chapter34.Turing.CookLevin
