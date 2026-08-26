import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.ReductionVerifier.CertificateCodec
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFMachine

/-!
# Named SAT-to-3-CNF map and its serialized size

The existing reduction machine computes this map.  The explicit quadratic
length theorem is separated here because it is the only additional resource
fact needed to transport the 3-CNF certificate polynomial back to SAT.
-/

namespace CLRS.Chapter34

/-- The exact length-indexed Tseitin map computed by the existing fixed TM2. -/
def satToThreeCNFMap (input : List FormulaSym) : List CNFSym :=
  encCNF (to3CNF_len (decode input) input.length)

/-- Exact raw-language semantics of the named reduction map. -/
theorem satToThreeCNFMap_mem_iff (input : List FormulaSym) :
    satToThreeCNFMap input ∈ ThreeCNFSat ↔ input ∈ SAT := by
  change IsThreeCNF (decodeCNF (satToThreeCNFMap input)) ∧
      CnfSatisfiable (decodeCNF (satToThreeCNFMap input)) ↔
    Formula.Satisfiable (decode input)
  rw [satToThreeCNFMap, decodeCNF_encCNF]
  constructor
  · intro h
    exact (cnfSatisfiable_to3CNF_len_iff (decode input) input.length
      (numVars_decode_le input)).1 h.2
  · intro h
    exact ⟨isThreeCNF_to3CNF_len (decode input) input.length,
      (cnfSatisfiable_to3CNF_len_iff (decode input) input.length
        (numVars_decode_le input)).2 h⟩

/-- The serialized length-indexed Tseitin output is quadratically bounded by
the original raw formula length. -/
theorem satToThreeCNFMap_length_le (input : List FormulaSym) :
    (satToThreeCNFMap input).length ≤
      800 * (input.length + 1) ^ 2 := by
  let n := input.length
  let formula := decode input
  rcases hbuild : to3CNF' formula n with ⟨clauses, root, next⟩
  have hformula : (enc formula).length ≤ 2 * n + 3 := by
    simpa [formula, n] using Turing.TM3CNF.enc_decode_le input
  have hroot0 : root ≤ n + (enc formula).length := by
    simpa [hbuild] using (Turing.TM3CNF.to3CNF'_bounds formula n).1
  have hroot : root ≤ 3 * n + 3 := by
    nlinarith
  have hclauses0 : (encCNF clauses).length ≤
      12 * (enc formula).length * (n + (enc formula).length + 1) +
        6 * (enc formula).length := by
    simpa [hbuild] using Turing.TM3CNF.encCNF_to3CNF'_le formula n
  have hclauses : (encCNF clauses).length ≤
      72 * n * n + 216 * n + 162 := by
    nlinarith [hclauses0, hformula]
  have hlength : (satToThreeCNFMap input).length =
      (encCNF clauses).length + root + 4 := by
    simp [satToThreeCNFMap, to3CNF_len, formula, n, hbuild,
      encCNF, forceTrue, encClause, encLit, litSym, litIndex]
    omega
  rw [hlength]
  nlinarith

end CLRS.Chapter34
