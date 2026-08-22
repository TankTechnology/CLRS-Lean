import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Header
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameAffinePrefixRows

/-!
# Candidate normalized-pair rows

The occurrence count is serialized as the runtime source of the verified
growing affine-prefix controller.  For a formula with a given number of
literal occurrences, each row contains exactly its smaller ordinal endpoints.  Consequently the rows
enumerate every normalized candidate pair `u < v < m` once, before the later
compatibility filter removes same-clause and complementary pairs.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Stream the two-field source with zero base and occurrence-count length
from an occurrence descriptor stream. -/
def occurrencePairRowSeedSpec :
    StatefulFlatMapSpec Bool GraphSym UnaryFrameSym where
  initial := false
  action started symbol :=
    let tick := if symbol = .vertexMark then [.tick] else []
    if started then (tick, true) else (.separator :: tick, true)
  finish started := if started then [.separator] else [.separator, .separator]

@[simp] theorem occurrencePairRowSeedSpec_action (started : Bool)
    (symbol : GraphSym) :
    occurrencePairRowSeedSpec.action started symbol =
      let tick := if symbol = .vertexMark then [.tick] else []
      if started then (tick, true) else (.separator :: tick, true) := rfl

@[simp] theorem occurrencePairRowSeedSpec_finish (started : Bool) :
    occurrencePairRowSeedSpec.finish started =
      if started then [.separator] else [.separator, .separator] := rfl

/-- Runtime affine-prefix source over an occurrence descriptor stream. -/
def occurrencePairRowSeed (stream : List GraphSym) : List UnaryFrameSym :=
  rewriteStatefulFlatMap occurrencePairRowSeedSpec stream

/-- Runtime affine-prefix source generated from an arbitrary raw CNF word. -/
def canonicalOccurrencePairRowSeed (input : List CNFSym) :
    List UnaryFrameSym :=
  occurrencePairRowSeed (canonicalOccurrenceStream input)

/-- Typed affine-prefix family associated with a raw CNF word. -/
def canonicalOccurrencePairRowFamily (input : List CNFSym) :
    UnaryFrameAffinePrefixRows where
  base := 0
  count := cnfLiteralCount (decodeCNF input)

/-- Marked triangular lower-endpoint rows generated from raw CNF. -/
def canonicalOccurrencePairRows (input : List CNFSym) :
    List UnaryFrameSym :=
  unaryFrameAffinePrefixRowsStream
    (canonicalOccurrencePairRowFamily input)

private theorem occurrencePairRowSeedFrom_true (stream : List GraphSym) :
    rewriteStatefulFlatMapFrom occurrencePairRowSeedSpec true stream =
      List.replicate (stream.count .vertexMark) UnaryFrameSym.tick ++
        [.separator] := by
  induction stream with
  | nil => rfl
  | cons symbol stream ih =>
      cases symbol <;>
        simp [rewriteStatefulFlatMapFrom, ih, List.replicate_succ]

/-- Exact source serialization over an arbitrary descriptor stream. -/
theorem occurrencePairRowSeed_eq (stream : List GraphSym) :
    occurrencePairRowSeed stream =
      encodeUnaryFrameAffinePrefixRows
        { base := 0, count := stream.count .vertexMark } := by
  unfold occurrencePairRowSeed rewriteStatefulFlatMap
  change rewriteStatefulFlatMapFrom occurrencePairRowSeedSpec false stream = _
  cases stream with
  | nil => rfl
  | cons symbol stream =>
      cases symbol <;>
        simp [rewriteStatefulFlatMapFrom, occurrencePairRowSeedFrom_true,
          encodeUnaryFrameAffinePrefixRows, encodeUnaryFrame,
          encodeUnaryFrameBlock, List.replicate_succ]

/-- Exact affine-prefix source generated from every raw input. -/
theorem canonicalOccurrencePairRowSeed_eq (input : List CNFSym) :
    canonicalOccurrencePairRowSeed input =
      encodeUnaryFrameAffinePrefixRows
        (canonicalOccurrencePairRowFamily input) := by
  rw [canonicalOccurrencePairRowSeed, occurrencePairRowSeed_eq]
  rw [canonicalOccurrencePairRowFamily,
    canonicalOccurrenceStream_vertexCount]

/-- The generated rows are precisely the row-major lower endpoints of all
normalized occurrence pairs. -/
theorem canonicalOccurrencePairRows_eq (input : List CNFSym) :
    canonicalOccurrencePairRows input =
      (List.ofFn fun vertex : Fin (cnfLiteralCount (decodeCNF input)) =>
        List.ofFn fun lower : Fin vertex.val => lower.val).flatMap fun row =>
          encodeUnaryFrame row ++ [.frameEnd] := by
  simp [canonicalOccurrencePairRows, canonicalOccurrencePairRowFamily,
    unaryFrameAffinePrefixRowsStream,
    unaryFrameAffinePrefixRowValues]

noncomputable def occurrencePairRowSeed_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id occurrencePairRowSeed :=
  statefulFlatMap_computableInPolyTime occurrencePairRowSeedSpec

noncomputable def canonicalOccurrencePairRowSeed_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalOccurrencePairRowSeed := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalOccurrenceStream_computableInPolyTime
      occurrencePairRowSeed_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => occurrencePairRowSeed (canonicalOccurrenceStream input))
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def canonicalOccurrencePairRowFamily_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameAffinePrefixRows canonicalOccurrencePairRowFamily := by
  let seed := canonicalOccurrencePairRowSeed_computableInPolyTime
  exact
    { tm := seed.tm
      inputAlphabet := seed.inputAlphabet
      outputAlphabet := seed.outputAlphabet
      time := seed.time
      outputsFun := fun input => by
        rw [← canonicalOccurrencePairRowSeed_eq]
        exact seed.outputsFun input }

/-- A fixed composed polynomial-time machine generates the full triangular
candidate-pair row family from the original raw CNF input. -/
noncomputable def canonicalOccurrencePairRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalOccurrencePairRows := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalOccurrencePairRowFamily_computableInPolyTime
      unaryFrameAffinePrefixRowsStream_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => unaryFrameAffinePrefixRowsStream
      (canonicalOccurrencePairRowFamily input))
  simpa [Function.comp_def] using Classical.choice composed

end TMClique
end Turing
end Chapter34
end CLRS
