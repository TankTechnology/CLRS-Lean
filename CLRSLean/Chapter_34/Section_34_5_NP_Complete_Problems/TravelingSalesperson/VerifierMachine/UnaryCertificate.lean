import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Canonicality
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

/-- Partial inverse on the four CLIQUE symbols used by a tour certificate. -/
private def fromCliqueSym : CliqueSym → TSPSym
  | .certificateMark => .certificateMark
  | .vertexMark => .numberMark
  | .tick => .bit true
  | .recordEnd => .fieldEnd
  | .instanceMark | .fieldSep | .edgeMark | .pairSep => .recordEnd

private theorem from_toCliqueSym_of_ne_instanceMark (symbol : TSPSym)
    (hvalid : toCliqueSym symbol ≠ .instanceMark) :
    fromCliqueSym (toCliqueSym symbol) = symbol := by
  cases symbol <;> simp_all [toCliqueSym, fromCliqueSym]
  case bit value => cases value <;> simp_all

private theorem instanceMark_not_mem_prependCliqueTicks (count : Nat)
    (suffix : List CliqueSym) (h : .instanceMark ∉ suffix) :
    .instanceMark ∉ prependCliqueTicks count suffix := by
  induction count with
  | zero => exact h
  | succ count ih => simpa [prependCliqueTicks] using ih

private theorem instanceMark_not_mem_encodeCliqueVertex (vertex : Nat) :
    .instanceMark ∉ encodeCliqueVertex vertex := by
  simp only [encodeCliqueVertex, List.mem_cons, reduceCtorEq, false_or]
  exact instanceMark_not_mem_prependCliqueTicks vertex [.recordEnd] (by simp)

private theorem instanceMark_not_mem_encodeCliqueCertificate
    (vertices : List Nat) :
    .instanceMark ∉ encodeCliqueCertificate vertices := by
  simp only [encodeCliqueCertificate, List.mem_cons, reduceCtorEq, false_or,
    List.mem_flatMap]
  rintro ⟨vertex, _, hmem⟩
  exact instanceMark_not_mem_encodeCliqueVertex vertex hmem

private theorem map_from_toCliqueSym_eq_self (input : List TSPSym)
    (hvalid : ∀ symbol ∈ input, toCliqueSym symbol ≠ .instanceMark) :
    input.map (fun symbol => fromCliqueSym (toCliqueSym symbol)) = input := by
  have hmap : input.map (fun symbol => fromCliqueSym (toCliqueSym symbol)) =
      input.map id := by
    apply List.map_congr_left
    intro symbol hsymbol
    exact from_toCliqueSym_of_ne_instanceMark symbol (hvalid symbol hsymbol)
  simpa using hmap

/-- Successful parsing after the symbol adapter forces the original word to
be exactly the canonical unary tour encoding.  Although `toCliqueSym` is not
globally injective, all of its collisions map to `.instanceMark`, which never
occurs in a canonical CLIQUE certificate. -/
theorem eq_encode_of_decode_toCliqueCertificate_eq_some
    (input : List TSPSym) (vertices : List Nat)
    (hdecode : decodeCliqueCertificate (toCliqueCertificate input) =
      some vertices) :
    input = encode vertices := by
  have hcanonical := encodeCliqueCertificate_eq_of_decode_eq_some
    (toCliqueCertificate input) vertices hdecode
  have hvalid : ∀ symbol ∈ input, toCliqueSym symbol ≠ .instanceMark := by
    intro symbol hsymbol heq
    have hmem : CliqueSym.instanceMark ∈ toCliqueCertificate input := by
      simp only [toCliqueCertificate, List.mem_map]
      exact ⟨symbol, hsymbol, heq⟩
    rw [← hcanonical] at hmem
    exact instanceMark_not_mem_encodeCliqueCertificate vertices hmem
  calc
    input = input.map (fun symbol => fromCliqueSym (toCliqueSym symbol)) := by
      exact (map_from_toCliqueSym_eq_self input hvalid).symm
    _ = (toCliqueCertificate input).map fromCliqueSym := by
      simp [toCliqueCertificate, List.map_map]
    _ = (encodeCliqueCertificate vertices).map fromCliqueSym := by
      rw [hcanonical]
    _ = encode vertices := by
      rw [← toCliqueCertificate_encode vertices]
      rw [toCliqueCertificate, List.map_map]
      apply map_from_toCliqueSym_eq_self
      intro symbol hsymbol heq
      have hmem : CliqueSym.instanceMark ∈
          toCliqueCertificate (encode vertices) := by
        simp only [toCliqueCertificate, List.mem_map]
        exact ⟨symbol, hsymbol, heq⟩
      rw [toCliqueCertificate_encode vertices] at hmem
      exact instanceMark_not_mem_encodeCliqueCertificate vertices hmem

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
