import CLRSLean.Chapter_34

namespace CLRS.Chapter34

-- framework definitions are public
#check Language
#check PolyTimeComputable
#check PolyTimeDecidable
#check ClassP
#check mem_ClassP

-- a basic sanity: the empty language is a Language, and ClassP is a set of languages
example (Γ : Type) : ∅ ∈ Set (Language Γ) := by simp
example (Γ : Type) : ClassP Γ ⊆ Set (Language Γ) := by intro L hL; exact hL

end CLRS.Chapter34
