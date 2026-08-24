import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# Decision-TSP verifier: unary tour certificates

The weighted instance remains compact binary.  For the nondeterministic tour
witness we use unary vertex records so that the already verified CLIQUE and
HAM-CYCLE range, cardinality, pair-generation, and duplicate machinery can be
reused.  On a well-formed complete-matrix input this certificate is still
polynomially bounded because every tour vertex is below `n` while the input
already contains `n²` weight fields.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.UnaryCertificate

open PolyBuilder

def encodeVertex (vertex : Nat) : List TSPSym :=
  .numberMark :: List.replicate vertex (.bit true) ++ [.fieldEnd]

def encode (vertices : List Nat) : List TSPSym :=
  .certificateMark :: vertices.flatMap encodeVertex

def toCliqueSym : TSPSym → CliqueSym
  | .certificateMark => .certificateMark
  | .numberMark => .vertexMark
  | .bit true => .tick
  | .fieldEnd => .recordEnd
  | .instanceMark | .bit false | .recordEnd => .instanceMark

def toCliqueCertificate (input : List TSPSym) : List CliqueSym :=
  input.map toCliqueSym

private theorem map_replicate_true (count : Nat) :
    (List.replicate count (TSPSym.bit true)).map toCliqueSym =
      List.replicate count CliqueSym.tick := by
  simp [toCliqueSym]

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (suffix : List CliqueSym) :
    prependCliqueTicks count suffix =
      List.replicate count .tick ++ suffix := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, List.replicate_succ, ih]

theorem toCliqueVertex_encode (vertex : Nat) :
    (encodeVertex vertex).map toCliqueSym = encodeCliqueVertex vertex := by
  rw [encodeVertex, List.map_append, List.map_cons,
    map_replicate_true, encodeCliqueVertex, prependCliqueTicks_eq_replicate]
  simp [toCliqueSym]

private theorem map_flatMap_encodeVertex (vertices : List Nat) :
    (vertices.flatMap encodeVertex).map toCliqueSym =
      vertices.flatMap encodeCliqueVertex := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices ih =>
      rw [List.flatMap_cons, List.map_append, toCliqueVertex_encode,
        List.flatMap_cons, ih]

theorem toCliqueCertificate_encode (vertices : List Nat) :
    toCliqueCertificate (encode vertices) = encodeCliqueCertificate vertices := by
  unfold toCliqueCertificate encode encodeCliqueCertificate
  rw [List.map_cons, map_flatMap_encodeVertex]
  rfl

@[simp] theorem decode_toCliqueCertificate_encode (vertices : List Nat) :
    decodeCliqueCertificate (toCliqueCertificate (encode vertices)) =
      some vertices := by
  rw [toCliqueCertificate_encode]
  exact decode_encodeCliqueCertificate vertices

@[simp] theorem encodeVertex_length (vertex : Nat) :
    (encodeVertex vertex).length = vertex + 2 := by
  simp [encodeVertex]

theorem encode_length (vertices : List Nat) :
    (encode vertices).length =
      1 + (vertices.map fun vertex => vertex + 2).sum := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices ih =>
      simp [encode, encodeVertex]
      omega

noncomputable def toCliqueCertificateComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id toCliqueCertificate :=
  listMap_computableInPolyTime toCliqueSym

end CLRS.Chapter34.Turing.TSPVerifier.UnaryCertificate
