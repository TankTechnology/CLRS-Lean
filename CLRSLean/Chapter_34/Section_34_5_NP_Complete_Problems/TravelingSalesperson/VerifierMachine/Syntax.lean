import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Canonicality
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Decision-TSP verifier: fixed record-syntax checks

The instance and certificate grammars differ only in their opening tag and
minimum field count.  This module implements both checks with one finite
transition table.  In particular, the controller rejects empty binary fields,
noncanonical leading zeroes, missing delimiters, repeated record terminators,
and trailing garbage.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.Syntax

open PolyBuilder

inductive FieldReturn
  | instanceOne
  | instanceMany
  | certificate
deriving DecidableEq, Fintype

inductive Mode
  | instanceStart
  | certificateStart
  | instanceZero
  | instanceOne
  | instanceMany
  | certificateBetween
  | fieldEmpty (returnTo : FieldReturn)
  | fieldSingleZero (returnTo : FieldReturn)
  | fieldPositive (returnTo : FieldReturn)
  | ended
  | invalid
deriving DecidableEq, Fintype

def returned : FieldReturn → Mode
  | .instanceOne => .instanceOne
  | .instanceMany => .instanceMany
  | .certificate => .certificateBetween

def nextMode : Mode → TSPSym → Mode
  | .instanceStart, .instanceMark => .instanceZero
  | .certificateStart, .certificateMark => .certificateBetween
  | .instanceZero, .numberMark => .fieldEmpty .instanceOne
  | .instanceOne, .numberMark => .fieldEmpty .instanceMany
  | .instanceMany, .numberMark => .fieldEmpty .instanceMany
  | .instanceMany, .recordEnd => .ended
  | .certificateBetween, .numberMark => .fieldEmpty .certificate
  | .certificateBetween, .recordEnd => .ended
  | .fieldEmpty returnTo, .bit false => .fieldSingleZero returnTo
  | .fieldEmpty returnTo, .bit true => .fieldPositive returnTo
  | .fieldSingleZero returnTo, .fieldEnd => returned returnTo
  | .fieldPositive returnTo, .bit _ => .fieldPositive returnTo
  | .fieldPositive returnTo, .fieldEnd => returned returnTo
  | _, _ => .invalid

def modeAccepts : Mode → Bool
  | .ended => true
  | _ => false

def spec (initial : Mode) : StatefulFlatMapSpec Mode TSPSym Bool where
  initial := initial
  action mode symbol := ([], nextMode mode symbol)
  finish mode := [modeAccepts mode]

def finalMode (mode : Mode) (input : List TSPSym) : Mode :=
  input.foldl nextMode mode

private theorem rewriteFrom_eq (initial mode : Mode)
    (input : List TSPSym) :
    rewriteStatefulFlatMapFrom (spec initial) mode input =
      [modeAccepts (finalMode mode input)] := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [spec, finalMode] using ih (nextMode mode symbol)

def instanceSyntax (input : List TSPSym) : Bool :=
  (rewriteStatefulFlatMap (spec .instanceStart) input).headD false

def certificateSyntax (input : List TSPSym) : Bool :=
  (rewriteStatefulFlatMap (spec .certificateStart) input).headD false

theorem rewrite_instance_eq (input : List TSPSym) :
    rewriteStatefulFlatMap (spec .instanceStart) input =
      [instanceSyntax input] := by
  unfold instanceSyntax rewriteStatefulFlatMap
  rw [rewriteFrom_eq]
  rfl

theorem rewrite_certificate_eq (input : List TSPSym) :
    rewriteStatefulFlatMap (spec .certificateStart) input =
      [certificateSyntax input] := by
  unfold certificateSyntax rewriteStatefulFlatMap
  rw [rewriteFrom_eq]
  rfl

theorem instanceSyntax_eq (input : List TSPSym) :
    instanceSyntax input = modeAccepts (finalMode .instanceStart input) := by
  unfold instanceSyntax rewriteStatefulFlatMap
  rw [rewriteFrom_eq]
  rfl

theorem certificateSyntax_eq (input : List TSPSym) :
    certificateSyntax input =
      modeAccepts (finalMode .certificateStart input) := by
  unfold certificateSyntax rewriteStatefulFlatMap
  rw [rewriteFrom_eq]
  rfl

private theorem finalMode_append (mode : Mode)
    (xs ys : List TSPSym) :
    finalMode mode (xs ++ ys) =
      finalMode (finalMode mode xs) ys := by
  simp [finalMode, List.foldl_append]

private theorem finalMode_positive (returnTo : FieldReturn)
    (bits : List Bool) :
    finalMode (.fieldPositive returnTo) (bits.map .bit) =
      .fieldPositive returnTo := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.map_cons, finalMode, List.foldl_cons]
      change List.foldl nextMode (.fieldPositive returnTo)
          (bits.map TSPSym.bit) = .fieldPositive returnTo
      simpa [finalMode] using ih

private theorem finalMode_canonicalField (returnTo : FieldReturn)
    (value : Nat) (suffix : List TSPSym) :
    finalMode (.fieldEmpty returnTo)
        ((encodeBinaryNat value).map .bit ++ .fieldEnd :: suffix) =
      finalMode (returned returnTo) suffix := by
  have hcanonical := isCanonicalBinaryNat_encode value
  generalize hbits : encodeBinaryNat value = bits at hcanonical ⊢
  cases bits with
  | nil => simp [isCanonicalBinaryNat] at hcanonical
  | cons first rest =>
      cases first with
      | false =>
          cases rest with
          | nil => simp [finalMode, nextMode]
          | cons next tail => simp [isCanonicalBinaryNat] at hcanonical
      | true =>
          rw [List.map_cons, List.cons_append]
          simp only [finalMode, List.foldl_cons, nextMode,
            List.foldl_append]
          rw [show List.foldl nextMode (.fieldPositive returnTo)
              (rest.map TSPSym.bit) = .fieldPositive returnTo by
            simpa [finalMode] using finalMode_positive returnTo rest]

private theorem finalMode_field_instanceZero (value : Nat) :
    finalMode .instanceZero (encodeTSPField value) = .instanceOne := by
  rw [encodeTSPField]
  change finalMode (.fieldEmpty .instanceOne)
      ((encodeBinaryNat value).map .bit ++ [.fieldEnd]) = .instanceOne
  simpa [finalMode, returned] using
    finalMode_canonicalField .instanceOne value []

private theorem finalMode_field_instanceOne (value : Nat) :
    finalMode .instanceOne (encodeTSPField value) = .instanceMany := by
  rw [encodeTSPField]
  change finalMode (.fieldEmpty .instanceMany)
      ((encodeBinaryNat value).map .bit ++ [.fieldEnd]) = .instanceMany
  simpa [finalMode, returned] using
    finalMode_canonicalField .instanceMany value []

private theorem finalMode_field_instanceMany (value : Nat) :
    finalMode .instanceMany (encodeTSPField value) = .instanceMany := by
  rw [encodeTSPField]
  change finalMode (.fieldEmpty .instanceMany)
      ((encodeBinaryNat value).map .bit ++ [.fieldEnd]) = .instanceMany
  simpa [finalMode, returned] using
    finalMode_canonicalField .instanceMany value []

private theorem finalMode_field_certificate (value : Nat) :
    finalMode .certificateBetween (encodeTSPField value) =
      .certificateBetween := by
  rw [encodeTSPField]
  change finalMode (.fieldEmpty .certificate)
      ((encodeBinaryNat value).map .bit ++ [.fieldEnd]) = .certificateBetween
  simpa [finalMode, returned] using
    finalMode_canonicalField .certificate value []

private theorem finalMode_fields_instanceMany (values : List Nat) :
    finalMode .instanceMany (encodeTSPFields values) = .instanceMany := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [encodeTSPFields, List.flatMap_cons, finalMode_append,
        finalMode_field_instanceMany]
      exact ih

private theorem finalMode_fields_certificate (values : List Nat) :
    finalMode .certificateBetween (encodeTSPFields values) =
      .certificateBetween := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [encodeTSPFields, List.flatMap_cons, finalMode_append,
        finalMode_field_certificate]
      exact ih

private theorem finalMode_instanceHeader (vertexCount budget : Nat)
    (weights : List Nat) :
    finalMode .instanceZero
        (encodeTSPFields (vertexCount :: budget :: weights)) =
      .instanceMany := by
  change finalMode .instanceZero
      (encodeTSPField vertexCount ++
        (encodeTSPField budget ++ encodeTSPFields weights)) = .instanceMany
  rw [finalMode_append, finalMode_field_instanceZero]
  rw [finalMode_append, finalMode_field_instanceOne]
  exact finalMode_fields_instanceMany weights

theorem instanceSyntax_encode (data : TSPData) :
    instanceSyntax (encodeTSPData data) = true := by
  rw [instanceSyntax_eq, encodeTSPData]
  simp only [finalMode, List.foldl_cons, nextMode]
  change modeAccepts
      (finalMode .instanceZero
        (encodeTSPFields (data.vertexCount :: data.budget :: data.weights) ++
          [.recordEnd])) = true
  rw [finalMode_append, finalMode_instanceHeader]
  rfl

theorem certificateSyntax_encode (vertices : List Nat) :
    certificateSyntax (encodeTSPCertificate vertices) = true := by
  rw [certificateSyntax_eq, encodeTSPCertificate]
  simp only [finalMode, List.foldl_cons, nextMode]
  change modeAccepts
      (finalMode .certificateBetween
        (encodeTSPFields vertices ++ [.recordEnd])) = true
  rw [finalMode_append, finalMode_fields_certificate]
  rfl

noncomputable def instanceComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      _root_.Turing.TM2Comp.boolEncoding instanceSyntax := by
  have machine := statefulFlatMap_computableInPolyTime (spec .instanceStart)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [rewrite_instance_eq] at output
        exact output }

noncomputable def certificateComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      _root_.Turing.TM2Comp.boolEncoding certificateSyntax := by
  have machine := statefulFlatMap_computableInPolyTime
    (spec .certificateStart)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [rewrite_certificate_eq] at output
        exact output }

end CLRS.Chapter34.Turing.TSPVerifier.Syntax
