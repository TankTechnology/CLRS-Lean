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

-- basic sanity checks
example (Γ : Type) : ClassP Γ ⊆ Set (Language Γ) := by intro L hL; exact hL
example (Γ : Type) : ClassNP Γ ⊆ Set (Language Γ) := by intro L hL; exact hL
example (Γ : Type) : ClassNPC Γ ⊆ Set (Language Γ) := by intro L hL; exact hL

end CLRS.Chapter34
