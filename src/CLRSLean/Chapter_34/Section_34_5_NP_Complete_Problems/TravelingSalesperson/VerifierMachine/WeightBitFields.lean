import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.SelectionFlags
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairSecondProjection

/-!
# Decision-TSP verifier: delimited binary weight fields

A three-mode fixed transducer discards the vertex-count and budget payloads,
then copies every matrix bit and represents each field boundary by `none`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.WeightBitFields

open _root_.Turing
open PolyBuilder

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

inductive Mode
  | vertexCount
  | budget
  | weights
deriving DecidableEq, Fintype

private def nextMode (mode : Mode) (symbol : TSPSym) : Mode :=
  match mode, symbol with
  | .vertexCount, .fieldEnd => .budget
  | .budget, .fieldEnd => .weights
  | _, _ => mode

private def chunk (mode : Mode) (symbol : TSPSym) : List (Option Bool) :=
  match mode, symbol with
  | .weights, .bit value => [some value]
  | .weights, .fieldEnd => [none]
  | _, _ => []

def fieldsFrom : Mode → List TSPSym → List (Option Bool)
  | _, [] => []
  | mode, symbol :: rest =>
      chunk mode symbol ++ fieldsFrom (nextMode mode symbol) rest

def fields (input : List TSPSym) : List (Option Bool) :=
  fieldsFrom .vertexCount input

private def spec : StatefulFlatMapSpec Mode TSPSym (Option Bool) where
  initial := .vertexCount
  action mode symbol := (chunk mode symbol, nextMode mode symbol)
  finish _ := []

private theorem rewriteFrom_eq (mode : Mode) (input : List TSPSym) :
    rewriteStatefulFlatMapFrom spec mode input = fieldsFrom mode input := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [spec, fieldsFrom] using
        congrArg (chunk mode symbol ++ ·) (ih (nextMode mode symbol))

theorem rewrite_eq (input : List TSPSym) :
    rewriteStatefulFlatMap spec input = fields input :=
  rewriteFrom_eq .vertexCount input

private theorem fieldsFrom_bits (bits : List Bool)
    (suffix : List TSPSym) :
    fieldsFrom .weights (bits.map TSPSym.bit ++ suffix) =
      bits.map some ++ fieldsFrom .weights suffix := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.map_cons, List.cons_append, fieldsFrom, chunk, nextMode]
      rw [ih]
      rfl

private theorem fieldsFrom_field (value : Nat) (suffix : List TSPSym) :
    fieldsFrom .weights (encodeTSPField value ++ suffix) =
      (encodeBinaryNat value).map some ++ none ::
        fieldsFrom .weights suffix := by
  rw [encodeTSPField]
  simp only [List.append_assoc, List.singleton_append]
  change fieldsFrom .weights
      (.numberMark :: ((encodeBinaryNat value).map .bit ++
        (.fieldEnd :: suffix))) = _
  rw [fieldsFrom]
  change fieldsFrom .weights
      ((encodeBinaryNat value).map .bit ++ .fieldEnd :: suffix) = _
  rw [fieldsFrom_bits]
  rfl

private theorem fieldsFrom_values (values : List Nat)
    (suffix : List TSPSym) :
    fieldsFrom .weights (encodeTSPFields values ++ suffix) =
      values.flatMap (fun value =>
        (encodeBinaryNat value).map some ++ [none]) ++
          fieldsFrom .weights suffix := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [show encodeTSPFields (value :: values) =
        encodeTSPField value ++ encodeTSPFields values by rfl]
      rw [List.append_assoc]
      rw [fieldsFrom_field, ih]
      simp [List.append_assoc]

private theorem fieldsFrom_vertexField (value : Nat)
    (suffix : List TSPSym) :
    fieldsFrom .vertexCount (encodeTSPField value ++ suffix) =
      fieldsFrom .budget suffix := by
  unfold encodeTSPField
  simp only [List.append_assoc, List.singleton_append]
  rw [fieldsFrom.eq_def]
  change fieldsFrom .vertexCount
      ((encodeBinaryNat value).map .bit ++ .fieldEnd :: suffix) = _
  induction encodeBinaryNat value with
  | nil => rfl
  | cons bit bits ih =>
      rw [List.map_cons, List.cons_append, fieldsFrom]
      exact ih

private theorem fieldsFrom_budgetField (value : Nat)
    (suffix : List TSPSym) :
    fieldsFrom .budget (encodeTSPField value ++ suffix) =
      fieldsFrom .weights suffix := by
  unfold encodeTSPField
  simp only [List.append_assoc, List.singleton_append]
  rw [fieldsFrom.eq_def]
  change fieldsFrom .budget
      ((encodeBinaryNat value).map .bit ++ .fieldEnd :: suffix) = _
  induction encodeBinaryNat value with
  | nil => rfl
  | cons bit bits ih =>
      rw [List.map_cons, List.cons_append, fieldsFrom]
      exact ih

@[simp] theorem fields_encode (data : TSPData) :
    fields (encodeTSPData data) =
      data.weights.flatMap (fun value =>
        (encodeBinaryNat value).map some ++ [none]) := by
  unfold fields encodeTSPData
  rw [fieldsFrom.eq_def]
  change fieldsFrom .vertexCount
      (encodeTSPFields
        (data.vertexCount :: data.budget :: data.weights) ++
          [.recordEnd]) = _
  rw [show encodeTSPFields
      (data.vertexCount :: data.budget :: data.weights) =
    encodeTSPField data.vertexCount ++
      encodeTSPField data.budget ++ encodeTSPFields data.weights by
        simp [encodeTSPFields, List.append_assoc]]
  simp only [List.append_assoc]
  rw [fieldsFrom_vertexField, fieldsFrom_budgetField,
    fieldsFrom_values]
  simp [fieldsFrom, chunk]

noncomputable def fieldsComputableFromInstanceInPolyTime :
    TM2ComputableInPolyTime id id fields := by
  let machine := statefulFlatMap_computableInPolyTime spec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [rewrite_eq] at output
        exact output }

private noncomputable def instanceProjection :
    TM2ComputableInPolyTime rawEncoding id Prod.snd := by
  let machine := PairSecondProjection.computableInPolyTime TSPSym
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        simpa [rawEncoding, UnaryBaseInput.rawEncoding,
          StructuralChecks.rawEncoding] using machine.outputsFun input }

noncomputable def fieldsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id
      (fun input => fields input.2) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    instanceProjection fieldsComputableFromInstanceInPolyTime
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.TSPVerifier.WeightBitFields
