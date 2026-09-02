import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.RoundTrip

/-!
# General CLIQUE verifier: parsing semantics and concrete TM2

The parser preserves both raw halves with explicit tags, appends exactly one
syntax-status marker, and is implemented by the verified finite-state
flat-map compiler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

open _root_.Turing
open PolyBuilder

private theorem rewrite_some_symbols_append (mode : ParseMode)
    (input : List CliqueSym) (tail : List (Option CliqueSym)) :
    rewriteStatefulFlatMapFrom parsePairSpec mode (input.map some ++ tail) =
      input.map (tagSymbol mode.side) ++
        rewriteStatefulFlatMapFrom parsePairSpec (scanSymbols mode input) tail := by
  induction input generalizing mode with
  | nil => simp [scanSymbols]
  | cons symbol rest ih =>
      simp only [List.map_cons, List.cons_append, rewriteStatefulFlatMapFrom,
        parsePairSpec, parseAction, scanSymbols, List.foldl_cons]
      change
        tagSymbol mode.side symbol ::
            rewriteStatefulFlatMapFrom parsePairSpec (stepSymbol mode symbol)
              (List.map some rest ++ tail) =
          tagSymbol mode.side symbol ::
            (List.map (tagSymbol mode.side) rest ++
              rewriteStatefulFlatMapFrom parsePairSpec
                (List.foldl stepSymbol (stepSymbol mode symbol) rest) tail)
      rw [ih (stepSymbol mode symbol), stepSymbol_side]
      simp [scanSymbols]

private theorem rewrite_some_symbols (mode : ParseMode)
    (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom parsePairSpec mode (input.map some) =
      input.map (tagSymbol mode.side) ++
        parseFinish (scanSymbols mode input) := by
  simpa [rewriteStatefulFlatMapFrom, parsePairSpec] using
    rewrite_some_symbols_append mode input []

/-- Exact pure stream on the public paired encoding. -/
theorem parsePairStream_pairEncoding (certificate input : List CliqueSym) :
    parsePairStream (pairEncoding certificate input) =
      certificate.map TaggedSym.certificate ++
        input.map TaggedSym.instance ++ [parsePairStatus certificate input] := by
  unfold parsePairStream rewriteStatefulFlatMap pairEncoding
  rw [List.append_assoc]
  rw [rewrite_some_symbols_append]
  rw [show parsePairSpec.initial = initialParseMode by rfl]
  rw [show tagSymbol initialParseMode.side = TaggedSym.certificate by
    funext symbol
    rfl]
  simp only [List.singleton_append]
  rw [List.append_assoc]
  apply (List.append_right_inj _).2
  simp only [rewriteStatefulFlatMapFrom, parsePairSpec, parseAction,
    List.nil_append]
  change
    rewriteStatefulFlatMapFrom parsePairSpec
        (stepSeparator (scanSymbols initialParseMode certificate))
        (input.map some) =
      input.map TaggedSym.instance ++ [parsePairStatus certificate input]
  rw [rewrite_some_symbols]
  simp [parsePairStatus, parseFinish, scanSymbols]
  split <;> rfl

private theorem scan_prepend_ticks (mode : ParseMode)
    (hstep : stepSymbol mode .tick = mode) (count : Nat)
    (suffix : List CliqueSym) :
    scanSymbols mode (prependCliqueTicks count suffix) =
      scanSymbols mode suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [prependCliqueTicks, scanSymbols, List.foldl_cons, hstep]
      simpa [scanSymbols] using ih

private def certificateVerticesMode : ParseMode :=
  { side := .certificate, grammar := .certificateVertices, valid := true }

private def certificateVertexMode : ParseMode :=
  { side := .certificate, grammar := .certificateVertex, valid := true }

private def instanceStartMode : ParseMode :=
  { side := .instance, grammar := .instanceStart, valid := true }

private def instanceVertexCountMode : ParseMode :=
  { side := .instance, grammar := .instanceVertexCount, valid := true }

private def instanceTargetSizeMode : ParseMode :=
  { side := .instance, grammar := .instanceTargetSize, valid := true }

private def instanceEdgesMode : ParseMode :=
  { side := .instance, grammar := .instanceEdges, valid := true }

private def instanceEdgeLeftMode : ParseMode :=
  { side := .instance, grammar := .instanceEdgeLeft, valid := true }

private def instanceEdgeRightMode : ParseMode :=
  { side := .instance, grammar := .instanceEdgeRight, valid := true }

private theorem scan_encodedVertex (vertex : Nat) :
    scanSymbols certificateVerticesMode (encodeCliqueVertex vertex) =
      certificateVerticesMode := by
  simp only [encodeCliqueVertex, scanSymbols, List.foldl_cons]
  change
    scanSymbols certificateVertexMode
        (prependCliqueTicks vertex [.recordEnd]) = certificateVerticesMode
  rw [scan_prepend_ticks certificateVertexMode (by rfl)]
  rfl

private theorem scan_encodedCertificate (vertices : List Nat) :
    scanSymbols initialParseMode (encodeCliqueCertificate vertices) =
      certificateVerticesMode := by
  simp only [encodeCliqueCertificate, scanSymbols, List.foldl_cons]
  change
    scanSymbols certificateVerticesMode
        (vertices.flatMap encodeCliqueVertex) = certificateVerticesMode
  induction vertices with
  | nil => rfl
  | cons vertex rest ih =>
      simp only [List.flatMap_cons, scanSymbols, List.foldl_append]
      change
        scanSymbols (scanSymbols certificateVerticesMode
          (encodeCliqueVertex vertex))
          (rest.flatMap encodeCliqueVertex) = certificateVerticesMode
      rw [scan_encodedVertex, ih]

private theorem scan_encodedEdge (edge : Nat × Nat) :
    scanSymbols instanceEdgesMode (encodeCliqueEdge edge) =
      instanceEdgesMode := by
  simp only [encodeCliqueEdge, scanSymbols, List.foldl_cons]
  change
    scanSymbols instanceEdgeLeftMode
        (prependCliqueTicks edge.1
          (.pairSep :: prependCliqueTicks edge.2 [.recordEnd])) =
      instanceEdgesMode
  rw [scan_prepend_ticks instanceEdgeLeftMode (by rfl)]
  simp only [scanSymbols, List.foldl_cons]
  change
    scanSymbols instanceEdgeRightMode
        (prependCliqueTicks edge.2 [.recordEnd]) = instanceEdgesMode
  rw [scan_prepend_ticks instanceEdgeRightMode (by rfl)]
  rfl

private theorem scan_encodedEdges (edges : List (Nat × Nat)) :
    scanSymbols instanceEdgesMode (edges.flatMap encodeCliqueEdge) =
      instanceEdgesMode := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      simp only [List.flatMap_cons, scanSymbols, List.foldl_append]
      change
        scanSymbols (scanSymbols instanceEdgesMode (encodeCliqueEdge edge))
          (rest.flatMap encodeCliqueEdge) = instanceEdgesMode
      rw [scan_encodedEdge, ih]

private theorem scan_encodedInstance (I : CliqueInstance) :
    scanSymbols instanceStartMode (encodeCliqueInstance I) =
      instanceEdgesMode := by
  simp only [encodeCliqueInstance, scanSymbols, List.foldl_cons]
  change
    scanSymbols instanceVertexCountMode
      (prependCliqueTicks I.vertexCount
        (.fieldSep :: prependCliqueTicks I.targetSize
          (.fieldSep :: I.edges.flatMap encodeCliqueEdge))) =
      instanceEdgesMode
  rw [scan_prepend_ticks instanceVertexCountMode (by rfl)]
  simp only [scanSymbols, List.foldl_cons]
  change
    scanSymbols instanceTargetSizeMode
      (prependCliqueTicks I.targetSize
        (.fieldSep :: I.edges.flatMap encodeCliqueEdge)) = instanceEdgesMode
  rw [scan_prepend_ticks instanceTargetSizeMode (by rfl)]
  simp only [scanSymbols, List.foldl_cons]
  exact scan_encodedEdges I.edges

/-- Canonically encoded certificates and instances pass the complete syntax
front end and retain their two tagged raw strings. -/
theorem parsePairStream_encoded (vertices : List Nat) (I : CliqueInstance) :
    parsePairStream
        (pairEncoding (encodeCliqueCertificate vertices) (encodeCliqueInstance I)) =
      (encodeCliqueCertificate vertices).map TaggedSym.certificate ++
        (encodeCliqueInstance I).map TaggedSym.instance ++ [.syntaxOK] := by
  rw [parsePairStream_pairEncoding]
  congr 1
  simp [parsePairStatus, scan_encodedCertificate, certificateVerticesMode,
    stepSeparator]
  have hinstance := scan_encodedInstance I
  simp [instanceStartMode, instanceEdgesMode] at hinstance
  rw [hinstance]
  exact ⟨rfl, rfl, rfl⟩

/-- The parsing front end is a fixed concrete polynomial-time TM2. -/
noncomputable def parsePairComputableInPolyTime :
    TM2ComputableInPolyTime id id parsePairStream :=
  statefulFlatMap_computableInPolyTime parsePairSpec

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
