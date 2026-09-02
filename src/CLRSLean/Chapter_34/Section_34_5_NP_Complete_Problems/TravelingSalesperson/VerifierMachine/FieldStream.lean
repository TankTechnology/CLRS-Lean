import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Decision-TSP verifier: field-bit stream

This small fixed transducer forgets the record tags while retaining every bit
and every field boundary.  The resulting `Option Bool` stream is the common
input format of the binary validator, adder, comparator, and list-equality
machines used by the final verifier.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.FieldStream

open PolyBuilder

/-- Pure extraction of binary payloads with `none` as a field separator. -/
def extractSymbol : TSPSym → List (Option Bool)
  | .bit value => [some value]
  | .fieldEnd => [none]
  | _ => []

/-- Extract every bit field from a raw TSP word. -/
def extract (input : List TSPSym) : List (Option Bool) :=
  input.flatMap extractSymbol

private def spec : StatefulFlatMapSpec Unit TSPSym (Option Bool) where
  initial := ()
  action _ symbol := (extractSymbol symbol, ())
  finish _ := []

private theorem rewriteFrom_eq (input : List TSPSym) :
    rewriteStatefulFlatMapFrom spec () input = extract input := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [spec, extract] using congrArg (extractSymbol symbol ++ ·) ih

theorem rewrite_eq (input : List TSPSym) :
    rewriteStatefulFlatMap spec input = extract input := by
  exact rewriteFrom_eq input

private theorem flatMap_bits (bits : List Bool) :
    (bits.map TSPSym.bit).flatMap extractSymbol = bits.map some := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [extractSymbol, ih]

/-- One encoded natural contributes its bits followed by one separator. -/
theorem extract_encodeTSPField (value : Nat) :
    extract (encodeTSPField value) =
      (encodeBinaryNat value).map some ++ [none] := by
  simp [extract, extractSymbol, encodeTSPField, flatMap_bits]

/-- Exact extraction semantics for a sequence of canonical fields. -/
theorem extract_encodeTSPFields (values : List Nat) :
    extract (encodeTSPFields values) =
      values.flatMap (fun value =>
        (encodeBinaryNat value).map some ++ [none]) := by
  induction values with
  | nil => simp [extract, encodeTSPFields]
  | cons value values ih =>
      rw [encodeTSPFields, List.flatMap_cons, extract, List.flatMap_append,
        ← extract, extract_encodeTSPField]
      change _ ++ extract (encodeTSPFields values) = _
      rw [ih]
      simp [List.append_assoc]

theorem extract_encodeTSPData (data : TSPData) :
    extract (encodeTSPData data) =
      (data.vertexCount :: data.budget :: data.weights).flatMap
        (fun value => (encodeBinaryNat value).map some ++ [none]) := by
  rw [encodeTSPData]
  simp only [extract, List.flatMap_cons, extractSymbol, List.nil_append,
    List.flatMap_append]
  rw [← extract, extract_encodeTSPFields]
  simp

theorem extract_encodeTSPCertificate (vertices : List Nat) :
    extract (encodeTSPCertificate vertices) =
      vertices.flatMap (fun value =>
        (encodeBinaryNat value).map some ++ [none]) := by
  rw [encodeTSPCertificate]
  simp only [extract, List.flatMap_cons, extractSymbol, List.nil_append,
    List.flatMap_append]
  rw [← extract, extract_encodeTSPFields]
  simp

/-- The extractor is a genuine fixed linear-time TM2. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id extract := by
  have machine := statefulFlatMap_computableInPolyTime spec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [rewrite_eq] at output
        exact output }

end CLRS.Chapter34.Turing.TSPVerifier.FieldStream
