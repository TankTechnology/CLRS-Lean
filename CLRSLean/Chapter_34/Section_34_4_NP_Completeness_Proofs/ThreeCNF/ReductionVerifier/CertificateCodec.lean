import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.Certificate
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Length

/-!
# Re-encoding CLIQUE witnesses in the 3-CNF alphabet

The definition of `PolyTimeVerifiable` keeps certificates in the language's
own alphabet.  This small codec represents the four symbols used by canonical
CLIQUE certificates with four `CNFSym` constructors.  It lets the existing
concrete CLIQUE verifier serve as a verifier backend without changing the
public 3-CNF alphabet.
-/

namespace CLRS.Chapter34

/-- Interpret one 3-CNF certificate symbol as a CLIQUE certificate symbol.
The unused fifth source symbol maps to an instance marker, so malformed
certificates remain total and are rejected by the downstream verifier. -/
def cnfToCliqueCertificateSymbol : CNFSym → CliqueSym
  | .clauseMark => .certificateMark
  | .posMark => .vertexMark
  | .negMark => .tick
  | .varMark => .recordEnd
  | .endMark => .instanceMark

/-- Symbol-wise translation consumed by the concrete CLIQUE verifier. -/
def cnfToCliqueCertificate (certificate : List CNFSym) : List CliqueSym :=
  certificate.map cnfToCliqueCertificateSymbol

/-- Encode one unary CLIQUE vertex record in the 3-CNF alphabet. -/
def encodeCNFCliqueVertex (vertex : Nat) : List CNFSym :=
  .posMark :: List.replicate vertex .negMark ++ [.varMark]

/-- Canonical 3-CNF-alphabet preimage of a CLIQUE vertex-list certificate. -/
def encodeCNFCliqueCertificate (vertices : List Nat) : List CNFSym :=
  .clauseMark :: vertices.flatMap encodeCNFCliqueVertex

private theorem replicate_tick_append_eq_prependCliqueTicks
    (vertex : Nat) (suffix : List CliqueSym) :
    List.replicate vertex CliqueSym.tick ++ suffix =
      prependCliqueTicks vertex suffix := by
  induction vertex with
  | zero => rfl
  | succ vertex ih =>
      simp [List.replicate_succ, prependCliqueTicks, ih]

@[simp] theorem cnfToCliqueCertificate_encodeCNFCliqueVertex
    (vertex : Nat) :
    (encodeCNFCliqueVertex vertex).map cnfToCliqueCertificateSymbol =
      encodeCliqueVertex vertex := by
  simp [encodeCNFCliqueVertex, encodeCliqueVertex,
    cnfToCliqueCertificateSymbol,
    replicate_tick_append_eq_prependCliqueTicks]

@[simp] theorem cnfToCliqueCertificate_encodeCNFCliqueCertificate
    (vertices : List Nat) :
    cnfToCliqueCertificate (encodeCNFCliqueCertificate vertices) =
      encodeCliqueCertificate vertices := by
  simp [cnfToCliqueCertificate, encodeCNFCliqueCertificate,
    encodeCliqueCertificate, cnfToCliqueCertificateSymbol,
    List.map_flatMap]

@[simp] theorem encodeCNFCliqueCertificate_length (vertices : List Nat) :
    (encodeCNFCliqueCertificate vertices).length =
      (encodeCliqueCertificate vertices).length := by
  have h := congrArg List.length
    (cnfToCliqueCertificate_encodeCNFCliqueCertificate vertices)
  simpa [cnfToCliqueCertificate] using h

end CLRS.Chapter34
