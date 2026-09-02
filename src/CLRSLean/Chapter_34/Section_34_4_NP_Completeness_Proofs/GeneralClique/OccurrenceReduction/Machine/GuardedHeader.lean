import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.FlaggedOccurrences
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Header

/-!
# A three-CNF-guarded general-CLIQUE header

The prefixed validity bit selects the target-size counter.  A valid formula
uses its clause count.  An invalid formula uses one more than its occurrence
count, making the resulting decoded graph instance structurally invalid and
therefore a guaranteed no-instance.  Both header halves are fixed streaming
passes joined by the verified same-input concatenator.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Left header pass: instance marker, occurrence count, and separator. -/
def guardedVertexHeaderSpec :
    StatefulFlatMapSpec Bool FlaggedOccurrenceSym CliqueSym where
  initial := false
  action started symbol :=
    let tick := if symbol = .graph .vertexMark then [.tick] else []
    if started then (tick, true) else (.instanceMark :: tick, true)
  finish started := if started then [.fieldSep] else [.instanceMark, .fieldSep]

/-- Right header pass: clause count when valid, otherwise occurrence count
plus one. -/
def guardedTargetHeaderSpec :
    StatefulFlatMapSpec Bool FlaggedOccurrenceSym CliqueSym where
  initial := false
  action valid
    | .flag next => ([], next)
    | .graph symbol =>
        let selected :=
          if valid then symbol = .clauseMark else symbol = .vertexMark
        (if selected then [.tick] else [], valid)
  finish valid := if valid then [.fieldSep] else [.tick, .fieldSep]

@[simp] theorem guardedVertexHeaderSpec_action (started : Bool)
    (symbol : FlaggedOccurrenceSym) :
    guardedVertexHeaderSpec.action started symbol =
      let tick := if symbol = .graph .vertexMark then [.tick] else []
      if started then (tick, true) else (.instanceMark :: tick, true) := rfl

@[simp] theorem guardedVertexHeaderSpec_finish (started : Bool) :
    guardedVertexHeaderSpec.finish started =
      if started then [.fieldSep] else [.instanceMark, .fieldSep] := rfl

@[simp] theorem guardedTargetHeaderSpec_action_flag
    (valid next : Bool) :
    guardedTargetHeaderSpec.action valid (.flag next) = ([], next) := rfl

@[simp] theorem guardedTargetHeaderSpec_action_graph
    (valid : Bool) (symbol : GraphSym) :
    guardedTargetHeaderSpec.action valid (.graph symbol) =
      (if (if valid then symbol = .clauseMark else symbol = .vertexMark)
        then [.tick] else [], valid) := rfl

@[simp] theorem guardedTargetHeaderSpec_finish (valid : Bool) :
    guardedTargetHeaderSpec.finish valid =
      if valid then [.fieldSep] else [.tick, .fieldSep] := rfl

def guardedVertexHeader (input : List FlaggedOccurrenceSym) : List CliqueSym :=
  rewriteStatefulFlatMap guardedVertexHeaderSpec input

def guardedTargetHeader (input : List FlaggedOccurrenceSym) : List CliqueSym :=
  rewriteStatefulFlatMap guardedTargetHeaderSpec input

/-- Complete guarded header over a flag-first descriptor stream. -/
def guardedOccurrenceCliqueHeader (input : List FlaggedOccurrenceSym) :
    List CliqueSym :=
  guardedVertexHeader input ++ guardedTargetHeader input

/-- Guarded header generated directly from an arbitrary raw CNF word. -/
def canonicalGuardedCliqueHeader (input : List CNFSym) : List CliqueSym :=
  guardedOccurrenceCliqueHeader (canonicalFlaggedOccurrenceStream input)

private theorem guardedVertexHeaderFrom_true (stream : List GraphSym) :
    rewriteStatefulFlatMapFrom guardedVertexHeaderSpec true
        (stream.map .graph) =
      List.replicate (stream.count .vertexMark) CliqueSym.tick ++
        [.fieldSep] := by
  induction stream with
  | nil => rfl
  | cons symbol stream ih =>
      cases symbol <;>
        simp [rewriteStatefulFlatMapFrom, ih, List.replicate_succ]

private theorem guardedVertexHeader_flag (valid : Bool)
    (stream : List GraphSym) :
    guardedVertexHeader (.flag valid :: stream.map .graph) =
      CliqueSym.instanceMark ::
        (List.replicate (stream.count .vertexMark) CliqueSym.tick ++
          [.fieldSep]) := by
  unfold guardedVertexHeader rewriteStatefulFlatMap
  change rewriteStatefulFlatMapFrom guardedVertexHeaderSpec false
      (.flag valid :: stream.map .graph) = _
  simp [rewriteStatefulFlatMapFrom, guardedVertexHeaderFrom_true]

private theorem guardedTargetHeader_graph (valid : Bool)
    (stream : List GraphSym) :
    rewriteStatefulFlatMapFrom guardedTargetHeaderSpec valid
        (stream.map .graph) =
      List.replicate
          (if valid then stream.count .clauseMark else
            stream.count .vertexMark)
          CliqueSym.tick ++
        (if valid then [.fieldSep] else [.tick, .fieldSep]) := by
  induction stream with
  | nil => cases valid <;> rfl
  | cons symbol stream ih =>
      cases valid <;> cases symbol <;>
        simp [rewriteStatefulFlatMapFrom, ih, List.replicate_succ]

private theorem guardedTargetHeader_flag (valid : Bool)
    (stream : List GraphSym) :
    guardedTargetHeader (.flag valid :: stream.map .graph) =
      List.replicate
          (if valid then stream.count .clauseMark else
            stream.count .vertexMark)
          CliqueSym.tick ++
        (if valid then [.fieldSep] else [.tick, .fieldSep]) := by
  simp [guardedTargetHeader, rewriteStatefulFlatMap,
    rewriteStatefulFlatMapFrom, guardedTargetHeader_graph]

private theorem replicateCliqueTicks_eq_prepend (count : Nat)
    (suffix : List CliqueSym) :
    List.replicate count CliqueSym.tick ++ suffix =
      prependCliqueTicks count suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [List.replicate_succ, prependCliqueTicks, ih]

private theorem replicateCliqueTicks_extra (count : Nat)
    (suffix : List CliqueSym) :
    List.replicate count CliqueSym.tick ++ CliqueSym.tick :: suffix =
      prependCliqueTicks (count + 1) suffix := by
  calc
    List.replicate count CliqueSym.tick ++ CliqueSym.tick :: suffix =
        (List.replicate count CliqueSym.tick ++ [CliqueSym.tick]) ++
          suffix := by rw [List.append_assoc]; rfl
    _ = List.replicate (count + 1) CliqueSym.tick ++ suffix := by
      rw [← List.replicate_one, ← List.replicate_add]
    _ = prependCliqueTicks (count + 1) suffix :=
      replicateCliqueTicks_eq_prepend _ _

private theorem cliqueHeaderHalves_append (vertexCount targetSize : Nat) :
    (List.replicate vertexCount CliqueSym.tick ++ [.fieldSep]) ++
        (List.replicate targetSize CliqueSym.tick ++ [.fieldSep]) =
      prependCliqueTicks vertexCount
        (.fieldSep :: prependCliqueTicks targetSize [.fieldSep]) := by
  rw [replicateCliqueTicks_eq_prepend,
    replicateCliqueTicks_eq_prepend]
  exact prependCliqueTicks_append _ _ _

private theorem cliqueHeaderLeft_append_prepend
    (vertexCount targetSize : Nat) :
    (List.replicate vertexCount CliqueSym.tick ++ [.fieldSep]) ++
        prependCliqueTicks targetSize [.fieldSep] =
      prependCliqueTicks vertexCount
        (.fieldSep :: prependCliqueTicks targetSize [.fieldSep]) := by
  rw [replicateCliqueTicks_eq_prepend]
  exact prependCliqueTicks_append _ _ _

/-- Pure semantics of the guarded header on a flag-first graph stream. -/
theorem guardedOccurrenceCliqueHeader_eq_counts (valid : Bool)
    (stream : List GraphSym) :
    guardedOccurrenceCliqueHeader (.flag valid :: stream.map .graph) =
      CliqueSym.instanceMark ::
        prependCliqueTicks (stream.count .vertexMark)
          (CliqueSym.fieldSep ::
            prependCliqueTicks
              (if valid then stream.count .clauseMark
                else stream.count .vertexMark + 1)
              [.fieldSep]) := by
  rw [guardedOccurrenceCliqueHeader, guardedVertexHeader_flag,
    guardedTargetHeader_flag]
  apply congrArg (fun tail => CliqueSym.instanceMark :: tail)
  cases valid
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [replicateCliqueTicks_extra]
    exact cliqueHeaderLeft_append_prepend _ _
  · simp only [↓reduceIte]
    exact cliqueHeaderHalves_append _ _

/-- Exact raw-input header: valid formulas use their clause count, while
invalid formulas use one more than their vertex count. -/
theorem canonicalGuardedCliqueHeader_eq (input : List CNFSym) :
    canonicalGuardedCliqueHeader input =
      CliqueSym.instanceMark ::
        prependCliqueTicks (cnfLiteralCount (decodeCNF input))
          (CliqueSym.fieldSep ::
            prependCliqueTicks
              (if IsThreeCNF (decodeCNF input) then
                (decodeCNF input).length
              else cnfLiteralCount (decodeCNF input) + 1)
              [.fieldSep]) := by
  rw [canonicalGuardedCliqueHeader,
    canonicalFlaggedOccurrenceStream_eq]
  change guardedOccurrenceCliqueHeader
      (.flag (decide (IsThreeCNF (decodeCNF input))) ::
        (relabel (encCNF (decodeCNF input))).map .graph) = _
  rw [guardedOccurrenceCliqueHeader_eq_counts]
  have hvertices := canonicalOccurrenceStream_vertexCount input
  have hclauses := canonicalOccurrenceStream_clauseCount input
  rw [canonicalOccurrenceStream_eq] at hvertices hclauses
  rw [hvertices, hclauses]
  by_cases hthree : IsThreeCNF (decodeCNF input) <;> simp [hthree]

noncomputable def guardedVertexHeader_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id guardedVertexHeader :=
  statefulFlatMap_computableInPolyTime guardedVertexHeaderSpec

noncomputable def guardedTargetHeader_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id guardedTargetHeader :=
  statefulFlatMap_computableInPolyTime guardedTargetHeaderSpec

/-- One fixed machine generates the complete header from a flagged stream. -/
noncomputable def guardedOccurrenceCliqueHeader_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      guardedOccurrenceCliqueHeader := by
  exact fixedPairSameInputConcat_computableInPolyTime
    encodeCliqueSymPair decodeCliqueSymPair decode_encodeCliqueSymPair
    guardedVertexHeader_computableInPolyTime
    guardedTargetHeader_computableInPolyTime

/-- One composed fixed machine generates the guarded header from raw CNF. -/
noncomputable def canonicalGuardedCliqueHeader_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalGuardedCliqueHeader := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      canonicalFlaggedOccurrenceStream_computableInPolyTime
      guardedOccurrenceCliqueHeader_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => guardedOccurrenceCliqueHeader
      (canonicalFlaggedOccurrenceStream input))
  simpa [Function.comp_def] using Classical.choice composed

end TMClique
end Turing
end Chapter34
end CLRS
