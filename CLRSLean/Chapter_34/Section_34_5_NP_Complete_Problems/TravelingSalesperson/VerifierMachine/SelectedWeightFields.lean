import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.WeightBitFields
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SelectDelimitedFields
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Decision-TSP verifier: selected weight fields

The independently computed matrix-selection flags and delimited weight fields
are packed into the literal input expected by the reusable fixed selector.  A
second fixed-machine composition then emits exactly the selected binary fields.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.SelectedWeightFields

open _root_.Turing
open PolyBuilder

abbrev RawInput := UnaryBaseInput.RawInput

def rawEncoding : RawInput → List (Option TSPSym) :=
  UnaryBaseInput.rawEncoding

def filterInput (input : RawInput) :
    List Bool × List (Option Bool) :=
  (SelectionFlags.selectionFlags input, WeightBitFields.fields input.2)

def selectedFields (input : RawInput) : List (Option Bool) :=
  SelectDelimitedFields.selectFields (filterInput input).1 (filterInput input).2

private def leftPart (input : RawInput) :
    List (Option SelectDelimitedFields.InputSym) :=
  (SelectionFlags.selectionFlags input).map fun flag =>
    some (.flag flag)

private def rightPart (input : RawInput) :
    List (Option SelectDelimitedFields.InputSym) :=
  none :: (WeightBitFields.fields input.2).map fun field =>
    some (.field field)

private noncomputable def leftPartComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id leftPart := by
  let mapped := listMap_computableInPolyTime
    (fun flag : Bool => some (SelectDelimitedFields.InputSym.flag flag))
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    SelectionFlags.selectionFlagsComputableInPolyTime mapped
  change TM2ComputableInPolyTime SelectionFlags.rawEncoding id
    (fun input => (SelectionFlags.selectionFlags input).map fun flag =>
      some (SelectDelimitedFields.InputSym.flag flag))
  simpa only [Function.comp_def] using Classical.choice composed

private def rightSpec : StatefulFlatMapSpec Bool (Option Bool)
    (Option SelectDelimitedFields.InputSym) where
  initial := false
  action started field :=
    if started then ([some (.field field)], true)
    else ([none, some (.field field)], true)
  finish started := if started then [] else [none]

private theorem rightStarted (fields : List (Option Bool)) :
    rewriteStatefulFlatMapFrom rightSpec true fields =
      fields.map fun field => some (.field field) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [rightSpec] using
        congrArg (fun tail => some (SelectDelimitedFields.InputSym.field field) ::
          tail) ih

private theorem rightRewrite (fields : List (Option Bool)) :
    rewriteStatefulFlatMap rightSpec fields =
      none :: fields.map fun field => some (.field field) := by
  cases fields with
  | nil => rfl
  | cons field fields =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom.eq_def]
      simpa [rightSpec] using
        congrArg (fun tail => none ::
          some (SelectDelimitedFields.InputSym.field field) :: tail)
          (rightStarted fields)

private noncomputable def rightFormatterComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun fields : List (Option Bool) =>
        none :: fields.map fun field =>
          some (SelectDelimitedFields.InputSym.field field)) := by
  let machine := statefulFlatMap_computableInPolyTime rightSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun fields => by
        have output := machine.outputsFun fields
        rw [rightRewrite] at output
        exact output }

private noncomputable def rightPartComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id rightPart := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    WeightBitFields.fieldsComputableInPolyTime rightFormatterComputableInPolyTime
  change TM2ComputableInPolyTime WeightBitFields.rawEncoding id
    (fun input => none :: (WeightBitFields.fields input.2).map fun field =>
      some (SelectDelimitedFields.InputSym.field field))
  simpa only [Function.comp_def] using Classical.choice composed

private def encodeInputSymbol :
    Option SelectDelimitedFields.InputSym → UnaryFrameSym × UnaryFrameSym
  | none => (.tick, .tick)
  | some (.flag false) => (.tick, .separator)
  | some (.flag true) => (.tick, .frameEnd)
  | some (.field none) => (.separator, .tick)
  | some (.field (some false)) => (.separator, .separator)
  | some (.field (some true)) => (.separator, .frameEnd)

private def decodeInputSymbol : UnaryFrameSym → UnaryFrameSym →
    Option SelectDelimitedFields.InputSym
  | .tick, .tick => none
  | .tick, .separator => some (.flag false)
  | .tick, .frameEnd => some (.flag true)
  | .separator, .tick => some (.field none)
  | .separator, .separator => some (.field (some false))
  | .separator, .frameEnd => some (.field (some true))
  | _, _ => none

private theorem decode_encodeInputSymbol
    (symbol : Option SelectDelimitedFields.InputSym) :
    decodeInputSymbol (encodeInputSymbol symbol).1
      (encodeInputSymbol symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some symbol =>
      cases symbol with
      | flag flag => cases flag <;> rfl
      | field field =>
          cases field with
          | none => rfl
          | some bit => cases bit <;> rfl

/-- The literal flag/field pair expected by the selector is generated by one
fixed polynomial-time machine from the raw certificate/instance pair. -/
noncomputable def filterInputComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      SelectDelimitedFields.inputEncoding filterInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeInputSymbol decodeInputSymbol decode_encodeInputSymbol
    leftPartComputableInPolyTime rightPartComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        simpa [filterInput, SelectDelimitedFields.inputEncoding, leftPart,
          rightPart, Function.comp_def] using output }

/-- Fixed polynomial-time extraction of exactly the matrix weight fields marked
by the cycle-selection stream. -/
noncomputable def selectedFieldsComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id selectedFields := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    filterInputComputableInPolyTime
    SelectDelimitedFields.computableInPolyTime
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => SelectDelimitedFields.selectFields
      (filterInput input).1 (filterInput input).2)
  simpa only [selectedFields, Function.comp_def] using Classical.choice composed

@[simp] theorem selectedFields_encode (vertices : List Nat) (data : TSPData) :
    selectedFields
        (UnaryCertificate.encode vertices, encodeTSPData data) =
      SelectDelimitedFields.selectFields
        (List.replicate vertices.length false ++
          ((vertexCoverNormalizedPairs vertices.length).map fun edge =>
            decide (edge ∈
              (HamiltonianCycle.VerifierMachine.CyclePairs.cyclePairs vertices).map
                GeneralCliqueVerifier.QueryNormalizer.normalizeQuery)).flatMap
                  fun flag => [flag, flag])
        (data.weights.flatMap fun value =>
          (encodeBinaryNat value).map some ++ [none]) := by
  simp [selectedFields, filterInput]

end CLRS.Chapter34.Turing.TSPVerifier.SelectedWeightFields
