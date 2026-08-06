import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification

/-!
# 34.3 NP-Completeness and Reducibility

CLRS §34.3: polynomial-time reducibility and the definitions of NP-hard and
NP-complete languages.

Main results:

- Definition `PolyTimeReducible`: `L₁ ≤_P L₂` — a polynomial-time computable
  reduction maps `L₁` into `L₂`.
- Definition `NPHard`: every polynomially verifiable language reduces to `L`.
- Definition `NPComplete`: `L ∈ NP` and `L` is NP-hard.

The transitivity of `PolyTimeReducible` (which needs the composition of
polynomial-time machines) is a documented follow-up; see the chapter guide.
-/

namespace CLRS

namespace Chapter34

/--
A language `L₁` over `Γ₁` is **polynomial-time reducible** to `L₂` over `Γ₂`
(`L₁ ≤_P L₂`) when there is a polynomial-time computable function `f` with
`x ∈ L₁` iff `f x ∈ L₂` (CLRS §34.3).
-/
def PolyTimeReducible {Γ₁ Γ₂ : Type} (L₁ : Language Γ₁) (L₂ : Language Γ₂) : Prop :=
  ∃ f : List Γ₁ → List Γ₂,
    PolyTimeComputable (id : List Γ₁ → List Γ₁) (id : List Γ₂ → List Γ₂) f ∧
    (∀ x : List Γ₁, x ∈ L₁ ↔ f x ∈ L₂)

/-- A language `L` is **NP-hard** when every polynomially verifiable language
is polynomial-time reducible to `L`. -/
def NPHard {Γ : Type} (L : Language Γ) : Prop :=
  ∀ (Γ' : Type) (L' : Language Γ'), PolyTimeVerifiable L' → PolyTimeReducible L' L

/-- A language `L` is **NP-complete** when `L ∈ NP` and `L` is NP-hard. -/
def NPComplete {Γ : Type} (L : Language Γ) : Prop :=
  PolyTimeVerifiable L ∧ NPHard L

/-- Membership in the class of NP-complete languages. -/
def ClassNPC (Γ : Type) : Set (Language Γ) :=
  { L | NPComplete (Γ := Γ) L }

end Chapter34

end CLRS
