import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SyntaxSemantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.UnaryBaseInput
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SymmetryCheck
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.BudgetCheck
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr

/-! # Decision-TSP verifier: final Boolean and fixed machine -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.Final

open _root_.Turing

abbrev RawInput := StructuralChecks.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  StructuralChecks.rawEncoding

/-- Conditions that relate the physical certificate and matrix dimensions. -/
def structuralChecks (input : RawInput) : Bool :=
  StructuralChecks.cardinalityCheck input &&
    (StructuralChecks.matrixShapeCheck input &&
      StructuralChecks.minimumVertexCountCheck input)

/-- Certificate range and uniqueness.  The range branch also enforces the
exact unary certificate grammar through the reused CLIQUE syntax checker. -/
def tourShapeChecks (input : RawInput) : Bool :=
  UnaryBaseInput.baseCheck input && UnaryBaseInput.nodupCheck input

/-- Conditions specific to a symmetric weighted complete graph and its
claimed budget. -/
def weightedChecks (input : RawInput) : Bool :=
  SymmetryCheck.symmetryCheck input && BudgetCheck.costCheck input

/-- Complete concrete verifier over a unary tour certificate and a compact
binary TSP instance. -/
def concreteTSPVerifier (input : RawInput) : Bool :=
  Syntax.instanceSyntax input.2 &&
    (structuralChecks input &&
      (tourShapeChecks input && weightedChecks input))

private noncomputable def instanceSyntaxComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => Syntax.instanceSyntax input.2) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    StructuralChecks.instanceProjection Syntax.instanceComputableInPolyTime
  simpa [rawEncoding, Function.comp_def] using Classical.choice composed

noncomputable def structuralChecksComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      structuralChecks := by
  let matrixAndMinimum := TM2AndOr.andOrComputableInPolyTime
    StructuralChecks.matrixShapeCheckComputableInPolyTime
    StructuralChecks.minimumVertexCountCheckComputableInPolyTime Bool.and
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => StructuralChecks.cardinalityCheck input &&
      (StructuralChecks.matrixShapeCheck input &&
        StructuralChecks.minimumVertexCountCheck input))
  exact TM2AndOr.andOrComputableInPolyTime
    StructuralChecks.cardinalityCheckComputableInPolyTime
    matrixAndMinimum Bool.and

noncomputable def tourShapeChecksComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      tourShapeChecks := by
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => UnaryBaseInput.baseCheck input &&
      UnaryBaseInput.nodupCheck input)
  exact TM2AndOr.andOrComputableInPolyTime
    UnaryBaseInput.baseCheckComputableInPolyTime
    UnaryBaseInput.nodupCheckComputableInPolyTime Bool.and

noncomputable def weightedChecksComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      weightedChecks := by
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => SymmetryCheck.symmetryCheck input &&
      BudgetCheck.costCheck input)
  exact TM2AndOr.andOrComputableInPolyTime
    SymmetryCheck.symmetryCheckComputableInPolyTime
    BudgetCheck.costCheckComputableInPolyTime Bool.and

private noncomputable def semanticChecksComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => structuralChecks input &&
        (tourShapeChecks input && weightedChecks input)) := by
  let tourAndWeighted := TM2AndOr.andOrComputableInPolyTime
    tourShapeChecksComputableInPolyTime weightedChecksComputableInPolyTime
    Bool.and
  exact TM2AndOr.andOrComputableInPolyTime
    structuralChecksComputableInPolyTime tourAndWeighted Bool.and

/-- One fixed two-tape machine computes the complete verifier in polynomial
time on every raw certificate/instance pair. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      concreteTSPVerifier := by
  change TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
    (fun input => Syntax.instanceSyntax input.2 &&
      (structuralChecks input &&
        (tourShapeChecks input && weightedChecks input)))
  exact TM2AndOr.andOrComputableInPolyTime
    instanceSyntaxComputableInPolyTime
    semanticChecksComputableInPolyTime Bool.and

end CLRS.Chapter34.Turing.TSPVerifier.Final
