import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.GeneratedRecord
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.ThreeCNFCheck
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# Total guarded SUBSET-SUM reduction machine

A one-bit canonical three-CNF flag is joined with the generated candidate
record.  A fixed finite-state pass copies the record when the flag is true and
otherwise emits the repository's fixed no-instance.  Thus the resulting
machine computes the total public raw reduction on every source word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Nine-symbol transport alphabet: two flag symbols and the seven public
compact-record symbols. -/
inductive GuardedSubsetSumSym
  | flag (valid : Bool)
  | data (symbol : SubsetSumSym)
deriving DecidableEq, Fintype, Repr

def encodeGuardedSubsetSumSymPair :
    GuardedSubsetSumSym → UnaryFrameSym × UnaryFrameSym
  | .flag false => (.tick, .tick)
  | .flag true => (.tick, .separator)
  | .data .instanceMark => (.tick, .frameEnd)
  | .data .certificateMark => (.separator, .tick)
  | .data .numberMark => (.separator, .separator)
  | .data (.bit false) => (.separator, .frameEnd)
  | .data (.bit true) => (.frameEnd, .tick)
  | .data .fieldEnd => (.frameEnd, .separator)
  | .data .recordEnd => (.frameEnd, .frameEnd)

def decodeGuardedSubsetSumSymPair :
    UnaryFrameSym → UnaryFrameSym → GuardedSubsetSumSym
  | .tick, .tick => .flag false
  | .tick, .separator => .flag true
  | .tick, .frameEnd => .data .instanceMark
  | .separator, .tick => .data .certificateMark
  | .separator, .separator => .data .numberMark
  | .separator, .frameEnd => .data (.bit false)
  | .frameEnd, .tick => .data (.bit true)
  | .frameEnd, .separator => .data .fieldEnd
  | .frameEnd, .frameEnd => .data .recordEnd

@[simp] theorem decode_encodeGuardedSubsetSumSymPair
    (symbol : GuardedSubsetSumSym) :
    decodeGuardedSubsetSumSymPair
      (encodeGuardedSubsetSumSymPair symbol).1
      (encodeGuardedSubsetSumSymPair symbol).2 = symbol := by
  cases symbol with
  | flag valid => cases valid <;> rfl
  | data symbol =>
      cases symbol with
      | instanceMark => rfl
      | certificateMark => rfl
      | numberMark => rfl
      | bit value => cases value <;> rfl
      | fieldEnd => rfl
      | recordEnd => rfl

def taggedThreeCNFFlag (input : List CNFSym) :
    List GuardedSubsetSumSym :=
  (TMClique.canonicalThreeCNFFlag input).map .flag

def taggedGeneratedRecord (input : List CNFSym) :
    List GuardedSubsetSumSym :=
  (generatedTypedRecord input).map .data

/-- Flag-first input consumed by the fixed guard. -/
def canonicalGuardedSubsetSumInput (input : List CNFSym) :
    List GuardedSubsetSumSym :=
  taggedThreeCNFFlag input ++ taggedGeneratedRecord input

theorem canonicalGuardedSubsetSumInput_eq (input : List CNFSym) :
    canonicalGuardedSubsetSumInput input =
      [.flag (decide (IsThreeCNF (decodeCNF input)))] ++
        (generatedTypedRecord input).map .data := by
  rw [canonicalGuardedSubsetSumInput, taggedThreeCNFFlag,
    taggedGeneratedRecord, TMClique.canonicalThreeCNFFlag_eq]
  rfl

private noncomputable def taggedThreeCNFFlag_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      taggedThreeCNFFlag := by
  let tagger := listMap_computableInPolyTime
    (fun valid : Bool => GuardedSubsetSumSym.flag valid)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      TMClique.canonicalThreeCNFFlag_computableInPolyTime tagger
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (TMClique.canonicalThreeCNFFlag input).map
      GuardedSubsetSumSym.flag)
  simpa [taggedThreeCNFFlag, Function.comp_def] using
    Classical.choice composed

private noncomputable def taggedGeneratedRecord_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      taggedGeneratedRecord := by
  let tagger := listMap_computableInPolyTime
    (fun symbol : SubsetSumSym => GuardedSubsetSumSym.data symbol)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      generatedTypedRecord_computableInPolyTime tagger
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (generatedTypedRecord input).map
      GuardedSubsetSumSym.data)
  simpa [taggedGeneratedRecord, Function.comp_def] using
    Classical.choice composed

private noncomputable def canonicalGuardedSubsetSumInput_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalGuardedSubsetSumInput := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeGuardedSubsetSumSymPair decodeGuardedSubsetSumSymPair
    decode_encodeGuardedSubsetSumSymPair
    taggedThreeCNFFlag_computableInPolyTime
    taggedGeneratedRecord_computableInPolyTime

/-- The final guard only stores the validity bit. -/
def guardedSubsetSumSpec :
    StatefulFlatMapSpec Bool GuardedSubsetSumSym SubsetSumSym where
  initial := false
  action valid
    | .flag next => ([], next)
    | .data symbol => if valid then ([symbol], true) else ([], false)
  finish valid :=
    if valid then [] else encodeSubsetSumData subsetSumNoData

def guardedSubsetSumOutput (input : List GuardedSubsetSumSym) :
    List SubsetSumSym :=
  rewriteStatefulFlatMap guardedSubsetSumSpec input

private theorem guardedSubsetSumFrom_data (valid : Bool)
    (record : List SubsetSumSym) :
    rewriteStatefulFlatMapFrom guardedSubsetSumSpec valid
        (record.map GuardedSubsetSumSym.data) =
      if valid then record else encodeSubsetSumData subsetSumNoData := by
  induction record generalizing valid with
  | nil => cases valid <;> rfl
  | cons symbol record ih =>
      cases valid with
      | false =>
          rw [List.map_cons, rewriteStatefulFlatMapFrom.eq_def]
          change [] ++ rewriteStatefulFlatMapFrom guardedSubsetSumSpec false
              (record.map GuardedSubsetSumSym.data) = _
          rw [List.nil_append]
          simpa using ih false
      | true =>
          rw [List.map_cons, rewriteStatefulFlatMapFrom.eq_def]
          change [symbol] ++
              rewriteStatefulFlatMapFrom guardedSubsetSumSpec true
                (record.map GuardedSubsetSumSym.data) = symbol :: record
          rw [List.singleton_append]
          simpa using congrArg (List.cons symbol) (ih true)

theorem guardedSubsetSumOutput_flag (valid : Bool)
    (record : List SubsetSumSym) :
    guardedSubsetSumOutput
        (.flag valid :: record.map GuardedSubsetSumSym.data) =
      if valid then record else encodeSubsetSumData subsetSumNoData := by
  unfold guardedSubsetSumOutput rewriteStatefulFlatMap
  rw [rewriteStatefulFlatMapFrom]
  change rewriteStatefulFlatMapFrom guardedSubsetSumSpec valid
      (record.map GuardedSubsetSumSym.data) = _
  exact guardedSubsetSumFrom_data valid record

noncomputable def guardedSubsetSumOutput_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      guardedSubsetSumOutput :=
  statefulFlatMap_computableInPolyTime guardedSubsetSumSpec

/-- Composed guarded output from the original raw source word. -/
def generatedRawThreeCNFToSubsetSum (input : List CNFSym) :
    List SubsetSumSym :=
  guardedSubsetSumOutput (canonicalGuardedSubsetSumInput input)

theorem generatedRawThreeCNFToSubsetSum_eq (input : List CNFSym) :
    generatedRawThreeCNFToSubsetSum input =
      rawThreeCNFToSubsetSum input := by
  rw [generatedRawThreeCNFToSubsetSum,
    canonicalGuardedSubsetSumInput_eq]
  simp only [List.singleton_append]
  rw [guardedSubsetSumOutput_flag]
  by_cases hthree : IsThreeCNF (decodeCNF input)
  · simp [hthree, rawThreeCNFToSubsetSum,
      generatedTypedRecord_eq hthree]
  · simp [hthree, rawThreeCNFToSubsetSum]

private noncomputable def generatedRawThreeCNFToSubsetSum_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      generatedRawThreeCNFToSubsetSum := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalGuardedSubsetSumInput_computableInPolyTime
      guardedSubsetSumOutput_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => guardedSubsetSumOutput
      (canonicalGuardedSubsetSumInput input))
  simpa [generatedRawThreeCNFToSubsetSum, Function.comp_def] using
    Classical.choice composed

/-- Final machine-level closure: the total serialized textbook reduction is
computed by one fixed polynomial-time TM2. -/
noncomputable def rawThreeCNFToSubsetSum_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      rawThreeCNFToSubsetSum := by
  let generated := generatedRawThreeCNFToSubsetSum_computableInPolyTime
  exact
    { tm := generated.tm
      inputAlphabet := generated.inputAlphabet
      outputAlphabet := generated.outputAlphabet
      time := generated.time
      outputsFun := fun input => by
        have output := generated.outputsFun input
        simpa only [generatedRawThreeCNFToSubsetSum_eq input] using output }

end CLRS.Chapter34.Turing.SubsetSumReduction
