import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.PairGenerator.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import Mathlib.Tactic.DeriveFintype

/-!
# VERTEX-COVER pair stream: range-certificate controller

The controller reads the unary vertex-count field of a canonical graph and
emits, in reverse physical order, the certificate encoding of
`[0, ..., vertexCount - 1]`.  A verified reversal pass supplies the public
forward stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream.RangeCertificate

open PolyBuilder

/-- Graph suffix following the first field separator. -/
def graphSuffix (I : CliqueInstance) : List CliqueSym :=
  prependCliqueTicks I.targetSize
    (.fieldSep :: I.edges.flatMap encodeCliqueEdge)

/-- The exact typed range certificate requested by the existing pair
generator. -/
def rangeCertificate (I : CliqueInstance) : List CliqueSym :=
  encodeCliqueCertificate (List.range I.vertexCount)

/-- Rows generated from `start` through `start + count - 1`. -/
def rangeRowsFrom (start count : Nat) : List CliqueSym :=
  (List.range' start count).flatMap encodeCliqueVertex

/-- Finite control for loading the vertex bound, serializing every range
vertex, clearing counters, and draining the untouched graph suffix. -/
inductive Label
  | start | pushCertificate | scanVertexCount | saveVertex
  | next | pushVertex | copyIndex | saveIndex | emitTick | pushRecordEnd
  | restoreIndex | restoreIndexTick | advance
  | clearIndex | drain | halt
deriving DecidableEq, Fintype

/-- Fixed range-certificate controller. -/
def program : Program CliqueSym CliqueSym where
  Label := Label
  main := .start
  op
    | .start => .popInput .drain fun
        | .instanceMark => .pushCertificate
        | _ => .drain
    | .pushCertificate => .pushOutput .certificateMark .scanVertexCount
    | .scanVertexCount => .popInput .next fun
        | .tick => .saveVertex
        | .fieldSep => .next
        | _ => .drain
    | .saveVertex => .inc₁ .scanVertexCount
    | .next => .dec₁ .clearIndex .pushVertex
    | .pushVertex => .pushOutput .vertexMark .copyIndex
    | .copyIndex => .dec₂ .pushRecordEnd .saveIndex
    | .saveIndex => .inc₃ .emitTick
    | .emitTick => .pushOutput .tick .copyIndex
    | .pushRecordEnd => .pushOutput .recordEnd .restoreIndex
    | .restoreIndex => .dec₃ .advance .restoreIndexTick
    | .restoreIndexTick => .inc₂ .restoreIndex
    | .advance => .inc₂ .next
    | .clearIndex => .dec₂ .drain .clearIndex
    | .drain => .popInput .halt fun _ => .drain
    | .halt => .halt

/-- Proof-facing controller configuration. -/
def cfg (label : Label) (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) (remaining index scratch : List Unit) :
    BuilderCfg program where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := remaining
  counter₂ := index
  counter₃ := scratch

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream.RangeCertificate
