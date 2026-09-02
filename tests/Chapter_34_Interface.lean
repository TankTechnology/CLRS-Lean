import CLRSLean.Chapter_34

namespace CLRS.Chapter34

-- 34.1 framework definitions are public
#check Language
#check PolyTimeComputable
#check PolyTimeDecidable
#check ClassP
#check mem_ClassP

-- 34.2 NP definitions
#check pairEncoding
#check PolyTimeVerifiable
#check ClassNP
#check mem_ClassNP

-- 34.3 reducibility and NP-completeness definitions
#check PolyTimeReducible
#check NPHard
#check NPComplete
#check ClassNPC

-- 34.4 concrete reduction boundary
#check IsThreeCNF
#check isThreeCNF_to3CNF_len
#check Turing.TM3CNF.sat_reducible_to_threeCNFSat
example : PolyTimeReducible SAT ThreeCNFSat :=
  Turing.TM3CNF.sat_reducible_to_threeCNFSat
example (x : List CNFSym) (hx : x ∈ ThreeCNFSat) :
    IsThreeCNF (decodeCNF x) := hx.1
#check ThreeCNFOccurrenceCLIQUE
#check Turing.TMClique.threeCNFSat_reducible_to_threeCNFOccurrenceCLIQUE
#check CLIQUE
#check generalCLIQUE_mem_ClassNP
#check Turing.TMClique.threeCNFSat_reducible_to_CLIQUE
#check generalCircuitSAT_reducible_to_SAT
#check SAT_npHard
#check threeCNFSat_npHard
#check CLIQUE_npComplete
#check satVerifier_accepts_iff
#check mem_SAT_iff_exists_bounded_certificate
#check threeCNFSatVerifier_accepts_iff
#check mem_threeCNFSat_iff_exists_bounded_certificate
#check Turing.SATVerifier.reductionVerifierComputableInPolyTime
#check SAT_mem_ClassNP
#check SAT_npComplete
#check Turing.ThreeCNFVerifier.reductionVerifierComputableInPolyTime
#check threeCNFSat_mem_ClassNP
#check threeCNFSat_npComplete

-- basic sanity checks
example (Γ : Type) : ClassP Γ ⊆ (Set.univ : Set (Language Γ)) := by simp
example (Γ : Type) : ClassNP Γ ⊆ (Set.univ : Set (Language Γ)) := by simp
example (Γ : Type) : ClassNPC Γ ⊆ (Set.univ : Set (Language Γ)) := by simp

end CLRS.Chapter34
