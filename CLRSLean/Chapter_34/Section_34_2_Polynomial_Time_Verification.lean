import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time

/-!
# 34.2 Polynomial-Time Verification

CLRS §34.2: the complexity class **NP** — languages whose membership can be
verified in polynomial time given a polynomial-size certificate.

Main results:

- Definition `PolyTimeVerifiable`: a language verifiable by a polynomial-time
  verifier with polynomial-size certificates.
- Definition `ClassNP`: the class of polynomially verifiable languages.

The verifier takes a certificate and an input (encoded as a single string
with a separator); the certificate is required to have length bounded by a
polynomial in the input length.
-/

namespace CLRS

namespace Chapter34

/-- Encode a pair of strings over `Γ` as a single string over `Option Γ`,
using `none` as a separator.  The length is `|x| + |y| + 1`. -/
def pairEncoding {Γ : Type} (x y : List Γ) : List (Option Γ) :=
  List.map some x ++ [none] ++ List.map some y

/--
A language `L` is **polynomially verifiable** (`L ∈ NP`) when there is a
polynomial-time computable verifier `V : List Γ → List Γ → Bool` and a
polynomial `p` such that `x ∈ L` iff some certificate `c` of length at most
`p(|x|)` satisfies `V c x = true` (CLRS §34.2).
-/
def PolyTimeVerifiable {Γ : Type} (L : Language Γ) : Prop :=
  ∃ V : List Γ → List Γ → Bool, ∃ p : Polynomial ℕ,
    PolyTimeComputable (fun pr : List Γ × List Γ => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr : List Γ × List Γ => V pr.1 pr.2) ∧
    (∀ x : List Γ, x ∈ L ↔ ∃ c : List Γ, c.length ≤ p.eval x.length ∧ V c x = true)

/-- The complexity class **NP**: polynomially verifiable languages. -/
def ClassNP (Γ : Type) : Set (Language Γ) :=
  { L | PolyTimeVerifiable (Γ := Γ) L }

/-- A language is in `NP` iff it is polynomially verifiable. -/
theorem mem_ClassNP {Γ : Type} (L : Language Γ) : L ∈ ClassNP Γ ↔ PolyTimeVerifiable L := by
  rfl

end Chapter34

end CLRS
