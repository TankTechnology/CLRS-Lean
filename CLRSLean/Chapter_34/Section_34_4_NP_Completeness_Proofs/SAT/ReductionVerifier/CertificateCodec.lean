import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.NPCompleteness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.Certificate

/-!
# Re-encoding 3-CNF verifier certificates in the SAT alphabet

`FormulaSym` has enough constructors to represent every `CNFSym` value with a
one-symbol code.  The explicit right inverse makes witness transport and its
length bound exact rather than merely asymptotic.
-/

namespace CLRS.Chapter34

/-- Total one-symbol translation from SAT certificates to 3-CNF verifier
certificates. -/
def formulaToCNFCertificateSymbol : FormulaSym → CNFSym
  | .lit false => .clauseMark
  | .lit true => .posMark
  | .varMark => .negMark
  | .endMark => .varMark
  | .notMark => .endMark
  | .andMark | .orMark | .iffMark => .clauseMark

/-- A fixed right inverse used to pull every 3-CNF verifier certificate back
to the SAT alphabet. -/
def cnfToFormulaCertificateSymbol : CNFSym → FormulaSym
  | .clauseMark => .lit false
  | .posMark => .lit true
  | .negMark => .varMark
  | .varMark => .endMark
  | .endMark => .notMark

def formulaToCNFCertificate (certificate : List FormulaSym) : List CNFSym :=
  certificate.map formulaToCNFCertificateSymbol

def cnfToFormulaCertificate (certificate : List CNFSym) : List FormulaSym :=
  certificate.map cnfToFormulaCertificateSymbol

@[simp] theorem formulaToCNFCertificateSymbol_rightInverse
    (symbol : CNFSym) :
    formulaToCNFCertificateSymbol (cnfToFormulaCertificateSymbol symbol) =
      symbol := by
  cases symbol <;> rfl

@[simp] theorem formulaToCNFCertificate_rightInverse
    (certificate : List CNFSym) :
    formulaToCNFCertificate (cnfToFormulaCertificate certificate) =
      certificate := by
  simp [formulaToCNFCertificate, cnfToFormulaCertificate, List.map_map,
    Function.comp_def]

@[simp] theorem cnfToFormulaCertificate_length
    (certificate : List CNFSym) :
    (cnfToFormulaCertificate certificate).length = certificate.length := by
  simp [cnfToFormulaCertificate]

end CLRS.Chapter34
