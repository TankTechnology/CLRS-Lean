import Mathlib.Computability.TuringMachine.Computable

/-!
# 34.1 Polynomial Time

CLRS §34.1: the complexity class **P** — languages that can be decided in
polynomial time.  We build on Mathlib's `Turing.TM2ComputableInPolyTime`
(machine-level polynomial-time computability, using `Polynomial ℕ` time
bounds) to define languages, polynomial-time decision, and the class `P`.

Main results:

- Definition `Language`: a set of strings over an alphabet.
- Definition `PolyTimeComputable`: a function computable by a TM2
  machine in time bounded by a polynomial in the input length.
- Definition `PolyTimeDecidable`: a language decided by a
  polynomial-time decision function.
- Definition `ClassP`: the class of polynomial-time decidable
  languages.

The framework is deliberately abstract: the decision machine is existential.
Concrete machine constructions and the closure properties (composition,
`P ⊆ NP`) are developed in the sections that follow.  Open problems (whether
`P = NP`) are intentionally not addressed.
-/

namespace CLRS

namespace Chapter34

/-- A **language** over an alphabet `Γ` is a set of finite strings over `Γ`. -/
abbrev Language (Γ : Type) := Set (List Γ)

/--
A function `f : α → β` is **polynomial-time computable** if there is a TM2
machine computing `f` (via the input/output encodings `ea`/`eb`) whose running
time is bounded by a polynomial in the length of the encoded input.
-/
def PolyTimeComputable {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
    (f : α → β) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

/-- Encode a Boolean decision result as a one-symbol string over `Bool`. -/
def boolEncoding : Bool → List Bool := fun b => [b]

/--
A language `L` over `Γ` is **polynomial-time decidable** (`L ∈ P`) when there
is a polynomial-time computable decision function `f : List Γ → Bool` such
that `x ∈ L` iff `f x = true` (CLRS §34.1).
-/
def PolyTimeDecidable {Γ : Type} (L : Language Γ) : Prop :=
  ∃ f : List Γ → Bool,
    PolyTimeComputable (id : List Γ → List Γ) boolEncoding f ∧
      ∀ x : List Γ, (f x = true) ↔ x ∈ L

/-- The complexity class **P**: the languages decidable in polynomial time. -/
def ClassP (Γ : Type) : Set (Language Γ) :=
  { L | PolyTimeDecidable (Γ := Γ) L }

/-- A language is in `P` iff it is polynomial-time decidable. -/
theorem mem_ClassP {Γ : Type} (L : Language Γ) : L ∈ ClassP Γ ↔ PolyTimeDecidable L := by
  rfl

end Chapter34

end CLRS
