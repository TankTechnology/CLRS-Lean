import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Occurrences
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Concrete general-CLIQUE header generation

Two fixed streaming passes select occurrence and clause markers.  The reusable
same-input concatenator joins their outputs, yielding the canonical
instance marker, vertex count, and target-size prefix.  A final composition feeds
the canonical occurrence stream to this header generator.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- The left header half emits the instance marker, one tick per occurrence,
and the first field separator. -/
def occurrenceCountHeaderSpec : StatefulFlatMapSpec Bool GraphSym CliqueSym where
  initial := false
  action started symbol :=
    let tick := if symbol = .vertexMark then [.tick] else []
    if started then (tick, true) else (.instanceMark :: tick, true)
  finish started := if started then [.fieldSep] else [.instanceMark, .fieldSep]

/-- The right header half emits one tick per clause and the second separator. -/
def clauseCountHeaderSpec : StatefulFlatMapSpec Unit GraphSym CliqueSym where
  initial := ()
  action _ symbol :=
    (if symbol = .clauseMark then [.tick] else [], ())
  finish _ := [.fieldSep]

@[simp] theorem occurrenceCountHeaderSpec_action (started : Bool)
    (symbol : GraphSym) :
    occurrenceCountHeaderSpec.action started symbol =
      let tick := if symbol = .vertexMark then [.tick] else []
      if started then (tick, true) else (.instanceMark :: tick, true) := rfl

@[simp] theorem occurrenceCountHeaderSpec_finish (started : Bool) :
    occurrenceCountHeaderSpec.finish started =
      if started then [.fieldSep] else [.instanceMark, .fieldSep] := rfl

@[simp] theorem clauseCountHeaderSpec_action (symbol : GraphSym) :
    clauseCountHeaderSpec.action () symbol =
      (if symbol = .clauseMark then [.tick] else [], ()) := rfl

@[simp] theorem clauseCountHeaderSpec_finish :
    clauseCountHeaderSpec.finish () = [.fieldSep] := rfl

def occurrenceCountHeader (input : List GraphSym) : List CliqueSym :=
  rewriteStatefulFlatMap occurrenceCountHeaderSpec input

def clauseCountHeader (input : List GraphSym) : List CliqueSym :=
  rewriteStatefulFlatMap clauseCountHeaderSpec input

/-- Complete header over an already canonical occurrence stream. -/
def occurrenceCliqueHeader (input : List GraphSym) : List CliqueSym :=
  occurrenceCountHeader input ++ clauseCountHeader input

/-- Header generated directly from an arbitrary raw CNF word. -/
def canonicalCliqueHeader (input : List CNFSym) : List CliqueSym :=
  occurrenceCliqueHeader (canonicalOccurrenceStream input)

private theorem occurrenceCountHeaderFrom_true (input : List GraphSym) :
    rewriteStatefulFlatMapFrom occurrenceCountHeaderSpec true input =
      List.replicate (input.count .vertexMark) CliqueSym.tick ++
        [.fieldSep] := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simp [rewriteStatefulFlatMapFrom, ih, List.replicate_succ]

private theorem occurrenceCountHeaderFrom_false (input : List GraphSym) :
    rewriteStatefulFlatMapFrom occurrenceCountHeaderSpec false input =
      .instanceMark ::
        (List.replicate (input.count .vertexMark) CliqueSym.tick ++
          [.fieldSep]) := by
  cases input with
  | nil => rfl
  | cons symbol rest =>
      cases symbol <;>
        simp [rewriteStatefulFlatMapFrom,
          occurrenceCountHeaderFrom_true, List.replicate_succ]

private theorem clauseCountHeaderFrom (input : List GraphSym) :
    rewriteStatefulFlatMapFrom clauseCountHeaderSpec () input =
      List.replicate (input.count .clauseMark) CliqueSym.tick ++
        [.fieldSep] := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simp [rewriteStatefulFlatMapFrom, ih, List.replicate_succ]

private theorem replicateCliqueTicks_append (count : Nat)
    (suffix : List CliqueSym) :
    List.replicate count CliqueSym.tick ++ suffix =
      prependCliqueTicks count suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [List.replicate_succ, prependCliqueTicks, ih]

/-- Pure count semantics of the complete occurrence-stream header. -/
theorem occurrenceCliqueHeader_eq_counts (input : List GraphSym) :
    occurrenceCliqueHeader input =
      CliqueSym.instanceMark ::
        prependCliqueTicks (input.count .vertexMark)
          (CliqueSym.fieldSep ::
            prependCliqueTicks (input.count .clauseMark) [.fieldSep]) := by
  simp only [occurrenceCliqueHeader, occurrenceCountHeader,
    clauseCountHeader, rewriteStatefulFlatMap]
  change rewriteStatefulFlatMapFrom occurrenceCountHeaderSpec false input ++
      rewriteStatefulFlatMapFrom clauseCountHeaderSpec () input = _
  rw [
    occurrenceCountHeaderFrom_false, clauseCountHeaderFrom]
  apply congrArg (fun tail => CliqueSym.instanceMark :: tail)
  calc
    (List.replicate (input.count .vertexMark) CliqueSym.tick ++
          [.fieldSep]) ++
        (List.replicate (input.count .clauseMark) CliqueSym.tick ++
          [.fieldSep]) =
      prependCliqueTicks (input.count .vertexMark) [.fieldSep] ++
        prependCliqueTicks (input.count .clauseMark) [.fieldSep] := by
          rw [replicateCliqueTicks_append, replicateCliqueTicks_append]
    _ = prependCliqueTicks (input.count .vertexMark)
        ([.fieldSep] ++
          prependCliqueTicks (input.count .clauseMark) [.fieldSep]) :=
      prependCliqueTicks_append _ _ _
    _ = prependCliqueTicks (input.count .vertexMark)
        (.fieldSep ::
          prependCliqueTicks (input.count .clauseMark) [.fieldSep]) := rfl

private theorem relabel_append (left right : List CNFSym) :
    relabel (left ++ right) = relabel left ++ relabel right := by
  induction left with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol <;> simp [relabel, ih]

private theorem relabel_replicate_endMark (count : Nat) :
    relabel (List.replicate count CNFSym.endMark) =
      List.replicate count GraphSym.endMark := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, relabel, ih]

@[simp] private theorem relabel_encLit_vertexCount (literal : Literal) :
    (relabel (encLit literal)).count GraphSym.vertexMark = 1 := by
  cases literal <;>
    simp [encLit, litSym, relabel, relabel_replicate_endMark,
      List.count_replicate]

@[simp] private theorem relabel_encLit_clauseCount (literal : Literal) :
    (relabel (encLit literal)).count GraphSym.clauseMark = 0 := by
  cases literal <;>
    simp [encLit, litSym, relabel, relabel_replicate_endMark,
      List.count_replicate]

private theorem relabel_flatMap_encLit_vertexCount (clause : Clause) :
    (relabel (clause.flatMap encLit)).count GraphSym.vertexMark =
      clause.length := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      rw [List.flatMap_cons, relabel_append, List.count_append,
        relabel_encLit_vertexCount, ih]
      simp [Nat.add_comm]

private theorem relabel_flatMap_encLit_clauseCount (clause : Clause) :
    (relabel (clause.flatMap encLit)).count GraphSym.clauseMark = 0 := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      rw [List.flatMap_cons, relabel_append, List.count_append,
        relabel_encLit_clauseCount, ih]

private theorem relabel_encClause_vertexCount (clause : Clause) :
    (relabel (encClause clause)).count GraphSym.vertexMark = clause.length := by
  rw [show encClause clause = CNFSym.clauseMark :: clause.flatMap encLit by rfl]
  simp [relabel, relabel_flatMap_encLit_vertexCount]

private theorem relabel_encClause_clauseCount (clause : Clause) :
    (relabel (encClause clause)).count GraphSym.clauseMark = 1 := by
  simp [encClause, relabel, relabel_flatMap_encLit_clauseCount]

private theorem relabel_encCNF_vertexCount (formula : CNF) :
    (relabel (encCNF formula)).count GraphSym.vertexMark =
      cnfLiteralCount formula := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      rw [show encCNF (clause :: formula) =
          encClause clause ++ encCNF formula by rfl,
        relabel_append, List.count_append,
        relabel_encClause_vertexCount, ih]
      simp [cnfLiteralCount]

private theorem relabel_encCNF_clauseCount (formula : CNF) :
    (relabel (encCNF formula)).count GraphSym.clauseMark = formula.length := by
  induction formula with
  | nil => rfl
  | cons clause formula ih =>
      rw [show encCNF (clause :: formula) =
          encClause clause ++ encCNF formula by rfl,
        relabel_append, List.count_append,
        relabel_encClause_clauseCount, ih]
      simpa using Nat.add_comm 1 formula.length

/-- The canonical occurrence stream has one vertex marker per decoded literal
position. -/
theorem canonicalOccurrenceStream_vertexCount (input : List CNFSym) :
    (canonicalOccurrenceStream input).count GraphSym.vertexMark =
      cnfLiteralCount (decodeCNF input) := by
  rw [canonicalOccurrenceStream_eq, relabel_encCNF_vertexCount]

/-- The canonical occurrence stream has one clause marker per decoded clause. -/
theorem canonicalOccurrenceStream_clauseCount (input : List CNFSym) :
    (canonicalOccurrenceStream input).count GraphSym.clauseMark =
      (decodeCNF input).length := by
  rw [canonicalOccurrenceStream_eq, relabel_encCNF_clauseCount]

/-- The generated raw-input header carries exactly the vertex and target
counts of the decoded occurrence graph. -/
theorem canonicalCliqueHeader_eq (input : List CNFSym) :
    canonicalCliqueHeader input =
      CliqueSym.instanceMark ::
        prependCliqueTicks (cnfLiteralCount (decodeCNF input))
          (CliqueSym.fieldSep ::
            prependCliqueTicks (decodeCNF input).length [.fieldSep]) := by
  rw [canonicalCliqueHeader, occurrenceCliqueHeader_eq_counts,
    canonicalOccurrenceStream_eq, relabel_encCNF_vertexCount,
    relabel_encCNF_clauseCount]

/-- Two-symbol code used only to transport same-input concatenation through
the reusable unary-frame implementation. -/
def encodeCliqueSymPair : CliqueSym → UnaryFrameSym × UnaryFrameSym
  | .instanceMark => (.tick, .tick)
  | .certificateMark => (.tick, .separator)
  | .tick => (.tick, .frameEnd)
  | .fieldSep => (.separator, .tick)
  | .edgeMark => (.separator, .separator)
  | .vertexMark => (.separator, .frameEnd)
  | .pairSep => (.frameEnd, .tick)
  | .recordEnd => (.frameEnd, .separator)

def decodeCliqueSymPair : UnaryFrameSym → UnaryFrameSym → CliqueSym
  | .tick, .tick => .instanceMark
  | .tick, .separator => .certificateMark
  | .tick, .frameEnd => .tick
  | .separator, .tick => .fieldSep
  | .separator, .separator => .edgeMark
  | .separator, .frameEnd => .vertexMark
  | .frameEnd, .tick => .pairSep
  | .frameEnd, .separator => .recordEnd
  | .frameEnd, .frameEnd => .recordEnd

@[simp] theorem decode_encodeCliqueSymPair (symbol : CliqueSym) :
    decodeCliqueSymPair (encodeCliqueSymPair symbol).1
      (encodeCliqueSymPair symbol).2 = symbol := by
  cases symbol <;> rfl

noncomputable def occurrenceCountHeader_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id occurrenceCountHeader :=
  statefulFlatMap_computableInPolyTime occurrenceCountHeaderSpec

noncomputable def clauseCountHeader_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id clauseCountHeader :=
  statefulFlatMap_computableInPolyTime clauseCountHeaderSpec

/-- One fixed machine generates the complete header from an occurrence stream. -/
noncomputable def occurrenceCliqueHeader_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id occurrenceCliqueHeader := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    occurrenceCountHeader_computableInPolyTime
    clauseCountHeader_computableInPolyTime

/-- One composed fixed machine generates the complete header from raw CNF. -/
noncomputable def canonicalCliqueHeader_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id canonicalCliqueHeader := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalOccurrenceStream_computableInPolyTime
      occurrenceCliqueHeader_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => occurrenceCliqueHeader (canonicalOccurrenceStream input))
  simpa [Function.comp_def] using Classical.choice composed

end TMClique
end Turing
end Chapter34
end CLRS
