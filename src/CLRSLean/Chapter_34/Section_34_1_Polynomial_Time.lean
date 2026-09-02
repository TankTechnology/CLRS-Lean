import Mathlib.Computability.TuringMachine.Computable
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr

noncomputable section

open Computability StateTransition

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
- Theorem `PolyTimeComputable.comp`: `P` is closed under function
  composition (via `Turing.TM2Comp.comp_scratch`).
- Theorem `PolyTimeDecidable.compl` / `ClassP_compl`: `P` is closed
  under complement.
- Theorem `PolyTimeDecidable.union` / `ClassP_union`: `P` is closed
  under union (via the AND/OR machine `Turing.TM2AndOr`).
- Theorem `PolyTimeDecidable.inter` / `ClassP_inter`: `P` is closed
  under intersection.

The framework is deliberately abstract: the decision machine is existential.
Concrete machine constructions and the closure properties (composition,
complement, union, intersection) are developed in the sections that follow.
Open problems (whether `P = NP`) are intentionally not addressed.
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
abbrev boolEncoding : Bool → List Bool := Turing.TM2Comp.boolEncoding

/-- Encode a pair of strings over `Γ` as a single string over `Option Γ`,
using `none` as a separator.  The length is `|x| + |y| + 1`. -/
def pairEncoding {Γ : Type} (x y : List Γ) : List (Option Γ) :=
  List.map some x ++ [none] ++ List.map some y

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

/--
**Theorem (composition closure).**  The composition of two polynomial-time
computable functions is polynomial-time computable (CLRS §34.1, closure of `P`
under function composition).  Backed by `Turing.TM2ComputableInPolyTime.comp`
(via `Turing.TM2Comp.comp_scratch`).
-/
theorem PolyTimeComputable.comp {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ} {f : α → β} {g : β → γ}
    (hf : PolyTimeComputable ea eb f) (hg : PolyTimeComputable eb ec g) :
    PolyTimeComputable ea ec (g ∘ f) := by
  rcases hf with ⟨M₁⟩
  rcases hg with ⟨M₂⟩
  exact Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch M₁ M₂

/--
**Closure under complement.**  The complement of a polynomial-time decidable
language is polynomial-time decidable (CLRS §34.1): negate the decider.
-/
theorem PolyTimeDecidable.compl {Γ : Type} (L : Language Γ) (hL : PolyTimeDecidable L) :
    PolyTimeDecidable (Lᶜ) := by
  rcases hL with ⟨f, hf, hf_iff⟩
  refine ⟨fun x => !f x, ?comp, ?iff⟩
  · exact PolyTimeComputable.comp hf ⟨Turing.TM2Comp.notComputableInPolyTime⟩
  · intro x
    simp only [Set.mem_compl_iff]
    rw [← hf_iff x]
    by_cases h : f x = true <;> simp [h, Bool.not_eq_true]

/--
**Closure under complement.**  `P` is closed under complement: `L ∈ P` implies
`Lᶜ ∈ P`.
-/
theorem ClassP_compl {Γ : Type} (L : Language Γ) (hL : L ∈ ClassP Γ) : Lᶜ ∈ ClassP Γ := by
  exact (mem_ClassP (Lᶜ)).mpr (PolyTimeDecidable.compl L hL)

/--
**Closure under union.**  The union of two polynomial-time decidable languages
is polynomial-time decidable (CLRS §34.1): the decider ORs the two decision
functions, run on the duplicated input by the AND/OR machine.
-/
theorem PolyTimeDecidable.union {Γ : Type} [Inhabited Γ] (L₁ L₂ : Language Γ)
    (h₁ : PolyTimeDecidable L₁) (h₂ : PolyTimeDecidable L₂) :
    PolyTimeDecidable (L₁ ∪ L₂) := by
  rcases h₁ with ⟨f₁, hf₁, hf₁_iff⟩
  rcases h₂ with ⟨f₂, hf₂, hf₂_iff⟩
  rcases hf₁ with ⟨M₁⟩
  rcases hf₂ with ⟨M₂⟩
  letI : Fintype (M₁.tm.Γ M₁.tm.k₀) := M₁.tm.Γk₀Fin
  letI : Fintype Γ := Fintype.ofEquiv (M₁.tm.Γ M₁.tm.k₀) M₁.inputAlphabet
  refine ⟨fun x => f₁ x || f₂ x, ?comp, ?iff⟩
  · exact ⟨Turing.TM2AndOr.andOrComputableInPolyTime (M₁ := M₁) (M₂ := M₂) (op := Bool.or)⟩
  · intro x
    simp [hf₁_iff x, hf₂_iff x]

/-- **Closure under union.**  `P` is closed under union: `L₁ ∈ P` and `L₂ ∈ P`
imply `L₁ ∪ L₂ ∈ P`.
-/
theorem ClassP_union {Γ : Type} [Inhabited Γ] (L₁ L₂ : Language Γ)
    (h₁ : L₁ ∈ ClassP Γ) (h₂ : L₂ ∈ ClassP Γ) : L₁ ∪ L₂ ∈ ClassP Γ := by
  exact (mem_ClassP (L₁ ∪ L₂)).mpr (PolyTimeDecidable.union L₁ L₂ h₁ h₂)

/--
**Closure under intersection.**  The intersection of two polynomial-time
decidable languages is polynomial-time decidable (CLRS §34.1): the decider
ANDs the two decision functions.
-/
theorem PolyTimeDecidable.inter {Γ : Type} [Inhabited Γ] (L₁ L₂ : Language Γ)
    (h₁ : PolyTimeDecidable L₁) (h₂ : PolyTimeDecidable L₂) :
    PolyTimeDecidable (L₁ ∩ L₂) := by
  rcases h₁ with ⟨f₁, hf₁, hf₁_iff⟩
  rcases h₂ with ⟨f₂, hf₂, hf₂_iff⟩
  rcases hf₁ with ⟨M₁⟩
  rcases hf₂ with ⟨M₂⟩
  letI : Fintype (M₁.tm.Γ M₁.tm.k₀) := M₁.tm.Γk₀Fin
  letI : Fintype Γ := Fintype.ofEquiv (M₁.tm.Γ M₁.tm.k₀) M₁.inputAlphabet
  refine ⟨fun x => f₁ x && f₂ x, ?comp, ?iff⟩
  · exact ⟨Turing.TM2AndOr.andOrComputableInPolyTime (M₁ := M₁) (M₂ := M₂) (op := Bool.and)⟩
  · intro x
    simp [hf₁_iff x, hf₂_iff x]

/-- **Closure under intersection.**  `P` is closed under intersection: `L₁ ∈ P`
and `L₂ ∈ P` imply `L₁ ∩ L₂ ∈ P`.
-/
theorem ClassP_inter {Γ : Type} [Inhabited Γ] (L₁ L₂ : Language Γ)
    (h₁ : L₁ ∈ ClassP Γ) (h₂ : L₂ ∈ ClassP Γ) : L₁ ∩ L₂ ∈ ClassP Γ := by
  exact (mem_ClassP (L₁ ∩ L₂)).mpr (PolyTimeDecidable.inter L₁ L₂ h₁ h₂)

end Chapter34

end CLRS
