import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.FieldStream
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Decision-TSP verifier: compact header projections

After the shared field extractor, two tiny fixed automata select the first and
second fields.  On canonical instances these are exactly `vertexCount` and
`budget`; malformed layout is handled independently by the syntax branch.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.HeaderBits

open PolyBuilder

inductive FirstMode | copy | done
deriving DecidableEq, Fintype

private def firstSpec :
    StatefulFlatMapSpec FirstMode (Option Bool) Bool where
  initial := .copy
  action mode symbol :=
    match mode, symbol with
    | .copy, some bit => ([bit], .copy)
    | .copy, none => ([], .done)
    | .done, _ => ([], .done)
  finish _ := []

def firstFieldBits (input : List (Option Bool)) : List Bool :=
  rewriteStatefulFlatMap firstSpec input

private theorem firstDone (input : List (Option Bool)) :
    rewriteStatefulFlatMapFrom firstSpec .done input = [] := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [firstSpec] using ih

private theorem firstCopy (bits : List Bool)
    (suffix : List (Option Bool)) :
    rewriteStatefulFlatMapFrom firstSpec .copy
        (bits.map some ++ none :: suffix) = bits := by
  induction bits with
  | nil =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      exact firstDone suffix
  | cons bit bits ih =>
      rw [List.map_cons, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      simpa [firstSpec] using congrArg (bit :: ·) ih

theorem firstFieldBits_field (bits : List Bool)
    (suffix : List (Option Bool)) :
    firstFieldBits (bits.map some ++ none :: suffix) = bits :=
  firstCopy bits suffix

inductive SecondMode | skip | copy | done
deriving DecidableEq, Fintype

private def secondSpec :
    StatefulFlatMapSpec SecondMode (Option Bool) Bool where
  initial := .skip
  action mode symbol :=
    match mode, symbol with
    | .skip, some _ => ([], .skip)
    | .skip, none => ([], .copy)
    | .copy, some bit => ([bit], .copy)
    | .copy, none => ([], .done)
    | .done, _ => ([], .done)
  finish _ := []

def secondFieldBits (input : List (Option Bool)) : List Bool :=
  rewriteStatefulFlatMap secondSpec input

private theorem secondDone (input : List (Option Bool)) :
    rewriteStatefulFlatMapFrom secondSpec .done input = [] := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [secondSpec] using ih

private theorem secondSkip (bits : List Bool)
    (suffix : List (Option Bool)) :
    rewriteStatefulFlatMapFrom secondSpec .skip
        (bits.map some ++ none :: suffix) =
      rewriteStatefulFlatMapFrom secondSpec .copy suffix := by
  induction bits with
  | nil =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      rfl
  | cons bit bits ih =>
      rw [List.map_cons, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      simpa [secondSpec] using ih

private theorem secondCopy (bits : List Bool)
    (suffix : List (Option Bool)) :
    rewriteStatefulFlatMapFrom secondSpec .copy
        (bits.map some ++ none :: suffix) = bits := by
  induction bits with
  | nil =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      exact secondDone suffix
  | cons bit bits ih =>
      rw [List.map_cons, List.cons_append,
        rewriteStatefulFlatMapFrom.eq_def]
      simpa [secondSpec] using congrArg (bit :: ·) ih

theorem secondFieldBits_fields (first second : List Bool)
    (suffix : List (Option Bool)) :
    secondFieldBits
        (first.map some ++
          (none :: (second.map some ++ (none :: suffix)))) =
      second := by
  unfold secondFieldBits rewriteStatefulFlatMap
  change rewriteStatefulFlatMapFrom secondSpec .skip
      (first.map some ++ (none :: (second.map some ++ (none :: suffix)))) =
        second
  calc
    _ = rewriteStatefulFlatMapFrom secondSpec .copy
        (second.map some ++ none :: suffix) := secondSkip first _
    _ = second := secondCopy second suffix

def vertexCountBits (input : List TSPSym) : List Bool :=
  firstFieldBits (FieldStream.extract input)

def budgetBits (input : List TSPSym) : List Bool :=
  secondFieldBits (FieldStream.extract input)

@[simp] theorem vertexCountBits_encode (data : TSPData) :
    vertexCountBits (encodeTSPData data) = encodeBinaryNat data.vertexCount := by
  rw [vertexCountBits, FieldStream.extract_encodeTSPData]
  rw [List.flatMap_cons]
  simpa only [List.singleton_append, List.append_assoc] using
    firstFieldBits_field (encodeBinaryNat data.vertexCount)
      ((data.budget :: data.weights).flatMap fun value =>
        (encodeBinaryNat value).map some ++ [none])

@[simp] theorem budgetBits_encode (data : TSPData) :
    budgetBits (encodeTSPData data) = encodeBinaryNat data.budget := by
  rw [budgetBits, FieldStream.extract_encodeTSPData]
  rw [List.flatMap_cons, List.flatMap_cons]
  simpa only [List.singleton_append, List.append_assoc] using
    secondFieldBits_fields (encodeBinaryNat data.vertexCount)
      (encodeBinaryNat data.budget)
      (data.weights.flatMap fun value =>
        (encodeBinaryNat value).map some ++ [none])

noncomputable def firstFieldBitsComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id firstFieldBits :=
  statefulFlatMap_computableInPolyTime firstSpec

noncomputable def secondFieldBitsComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id secondFieldBits :=
  statefulFlatMap_computableInPolyTime secondSpec

noncomputable def vertexCountBitsComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id vertexCountBits := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    FieldStream.computableInPolyTime firstFieldBitsComputableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [vertexCountBits, Function.comp_def] using output }

noncomputable def budgetBitsComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id budgetBits := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    FieldStream.computableInPolyTime secondFieldBitsComputableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [budgetBits, Function.comp_def] using output }

end CLRS.Chapter34.Turing.TSPVerifier.HeaderBits
