import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Occurrences
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.ThreeCNFCheck
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# A flagged canonical occurrence stream

The first symbol records whether the decoded formula is in the project's
at-most-three-literals normal form.  The remaining symbols are the canonical
occurrence descriptor stream.  Both components are generated from the same
raw source word by concrete machines and joined by the verified same-input
concatenator.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Eight-symbol transport alphabet for one Boolean flag followed by graph
descriptor symbols. -/
inductive FlaggedOccurrenceSym
  | flag (valid : Bool)
  | graph (symbol : GraphSym)
deriving DecidableEq, Fintype, Repr

/-- Tagged validity component. -/
def taggedThreeCNFFlag (input : List CNFSym) : List FlaggedOccurrenceSym :=
  (canonicalThreeCNFFlag input).map .flag

/-- Tagged occurrence-descriptor component. -/
def taggedCanonicalOccurrenceStream (input : List CNFSym) :
    List FlaggedOccurrenceSym :=
  (canonicalOccurrenceStream input).map .graph

/-- The complete flag-first descriptor stream. -/
def canonicalFlaggedOccurrenceStream (input : List CNFSym) :
    List FlaggedOccurrenceSym :=
  taggedThreeCNFFlag input ++ taggedCanonicalOccurrenceStream input

/-- Exact all-input semantics of the flag-first descriptor stream. -/
theorem canonicalFlaggedOccurrenceStream_eq (input : List CNFSym) :
    canonicalFlaggedOccurrenceStream input =
      [.flag (decide (IsThreeCNF (decodeCNF input)))] ++
        (relabel (encCNF (decodeCNF input))).map .graph := by
  rw [canonicalFlaggedOccurrenceStream, taggedThreeCNFFlag,
    taggedCanonicalOccurrenceStream, canonicalThreeCNFFlag_eq,
    canonicalOccurrenceStream_eq]
  rfl

/-- Pair code transporting the eight-symbol tagged alphabet through the
unary-frame same-input concatenator. -/
def encodeFlaggedOccurrenceSymPair :
    FlaggedOccurrenceSym → UnaryFrameSym × UnaryFrameSym
  | .flag false => (.tick, .tick)
  | .flag true => (.tick, .separator)
  | .graph .vertexMark => (.tick, .frameEnd)
  | .graph .posMark => (.separator, .tick)
  | .graph .negMark => (.separator, .separator)
  | .graph .varMark => (.separator, .frameEnd)
  | .graph .endMark => (.frameEnd, .tick)
  | .graph .clauseMark => (.frameEnd, .separator)

/-- Left inverse of the tagged-symbol pair code. -/
def decodeFlaggedOccurrenceSymPair :
    UnaryFrameSym → UnaryFrameSym → FlaggedOccurrenceSym
  | .tick, .tick => .flag false
  | .tick, .separator => .flag true
  | .tick, .frameEnd => .graph .vertexMark
  | .separator, .tick => .graph .posMark
  | .separator, .separator => .graph .negMark
  | .separator, .frameEnd => .graph .varMark
  | .frameEnd, .tick => .graph .endMark
  | .frameEnd, .separator => .graph .clauseMark
  | .frameEnd, .frameEnd => .flag false

@[simp] theorem decode_encodeFlaggedOccurrenceSymPair
    (symbol : FlaggedOccurrenceSym) :
    decodeFlaggedOccurrenceSymPair (encodeFlaggedOccurrenceSymPair symbol).1
      (encodeFlaggedOccurrenceSymPair symbol).2 = symbol := by
  cases symbol with
  | flag valid => cases valid <;> rfl
  | graph symbol => cases symbol <;> rfl

noncomputable def taggedThreeCNFFlag_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id taggedThreeCNFFlag := by
  let tagger := listMap_computableInPolyTime
    (fun valid : Bool => FlaggedOccurrenceSym.flag valid)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalThreeCNFFlag_computableInPolyTime tagger
  unfold taggedThreeCNFFlag
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (canonicalThreeCNFFlag input).map
      (fun valid => FlaggedOccurrenceSym.flag valid))
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def taggedCanonicalOccurrenceStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      taggedCanonicalOccurrenceStream := by
  let tagger := listMap_computableInPolyTime
    (fun symbol : GraphSym => FlaggedOccurrenceSym.graph symbol)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalOccurrenceStream_computableInPolyTime tagger
  unfold taggedCanonicalOccurrenceStream
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (canonicalOccurrenceStream input).map
      (fun symbol => FlaggedOccurrenceSym.graph symbol))
  simpa [Function.comp_def] using Classical.choice composed

/-- One fixed polynomial-time machine emits the flag and occurrence stream in
that order while reading only the original raw input. -/
noncomputable def canonicalFlaggedOccurrenceStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalFlaggedOccurrenceStream := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => taggedThreeCNFFlag input ++
      taggedCanonicalOccurrenceStream input)
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeFlaggedOccurrenceSymPair decodeFlaggedOccurrenceSymPair
    decode_encodeFlaggedOccurrenceSymPair
    taggedThreeCNFFlag_computableInPolyTime
    taggedCanonicalOccurrenceStream_computableInPolyTime

end TMClique
end Turing
end Chapter34
end CLRS
