import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification.PairProjection

/-!
# 34.2 Polynomial-Time Verification

CLRS §34.2: the complexity class **NP** — languages whose membership can be
verified in polynomial time given a polynomial-size certificate.

Main results:

- Definition `PolyTimeVerifiable`: a language verifiable by a polynomial-time
  verifier with polynomial-size certificates.
- Definition `ClassNP`: the class of polynomially verifiable languages.
- Theorem `PolyTimeVerifiable.of_decidable`: every `P` language is verifiable
  (the decider is a verifier that ignores the certificate).
- Theorem `ClassP_subset_ClassNP`: `P ⊆ NP` (CLRS Theorem 34.2).

The verifier takes a certificate and an input (encoded as a single string
with a separator); the certificate is required to have length bounded by a
polynomial in the input length.
-/

namespace CLRS

namespace Chapter34

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

/--
**Theorem 34.2 (`P ⊆ NP`).**  A polynomial-time decidable language is
polynomially verifiable: the decider `f` is a verifier `V c x := f x` that
ignores the certificate, run on the pair-encoded input via the projection
machine `Turing.Prj.prjComputableInPolyTime`.
-/
theorem PolyTimeVerifiable.of_decidable {Γ : Type} [Inhabited Γ] (L : Language Γ)
    (hL : PolyTimeDecidable L) :
    PolyTimeVerifiable L := by
  rcases hL with ⟨f, hf, hf_iff⟩
  have hf' := hf
  rcases hf with ⟨M⟩
  letI : Fintype (M.tm.Γ M.tm.k₀) := M.tm.Γk₀Fin
  letI : Fintype Γ := Fintype.ofEquiv (M.tm.Γ M.tm.k₀) M.inputAlphabet
  refine ⟨fun c x => f x, 0, ?comp, ?iff⟩
  · -- the verifier machine is the projection machine composed with the decider
    exact PolyTimeComputable.comp ⟨Turing.Prj.prjComputableInPolyTime (Γ := Γ)⟩ hf'
  · intro x
    rw [← hf_iff x]
    constructor
    · intro hfx
      exact ⟨[], by simpa using hfx⟩
    · rintro ⟨c, hc, hfx⟩
      exact hfx

/-- **Theorem 34.2**: `P ⊆ NP` (CLRS §34.2). -/
theorem ClassP_subset_ClassNP {Γ : Type} [Inhabited Γ] : ClassP Γ ⊆ ClassNP Γ := by
  intro L hL
  exact (mem_ClassNP L).mpr (PolyTimeVerifiable.of_decidable (L := L) hL)

end Chapter34

end CLRS
