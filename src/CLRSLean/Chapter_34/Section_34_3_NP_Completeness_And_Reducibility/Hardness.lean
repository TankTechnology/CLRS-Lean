import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Core

/-!
# NP-hardness transport

Polynomial-time reductions transport polynomial-time decidability and
NP-hardness, and expose the two components of an NP-completeness proof.

Main results:

- Theorem `PolyTimeDecidable.of_reducible`: decidability transports backward
  along a polynomial-time reduction.
- Theorem `NPHard.of_reducible`: NP-hardness transports forward along a
  polynomial-time reduction.
- Theorem `NPComplete.of_reducible`: a verifiable target of a reduction from
  an NP-complete language is NP-complete.
- Theorems `NPComplete.verifiable` and `NPComplete.hard`: direct projections
  from NP-completeness.
-/

namespace CLRS

namespace Chapter34

/-- Polynomial-time decidability transports backward along a polynomial-time
reduction: deciding the target after computing the reduction decides the
source language. -/
theorem PolyTimeDecidable.of_reducible {Γ₁ Γ₂ : Type}
    {L₁ : Language Γ₁} {L₂ : Language Γ₂}
    (hred : PolyTimeReducible L₁ L₂)
    (hdec : PolyTimeDecidable L₂) :
    PolyTimeDecidable L₁ := by
  rcases hred with ⟨f, hf, hiff⟩
  rcases hdec with ⟨d, hd, hdiff⟩
  exact ⟨d ∘ f, PolyTimeComputable.comp hf hd,
    fun x => (hdiff (f x)).trans (hiff x).symm⟩

/-- NP-hardness transports forward along a polynomial-time reduction from an
NP-hard source language. -/
theorem NPHard.of_reducible {Γ₁ Γ₂ : Type} {L₁ : Language Γ₁}
    {L₂ : Language Γ₂} (hhard : NPHard L₁)
    (hred : PolyTimeReducible L₁ L₂) : NPHard L₂ := by
  intro Γ L hL
  exact (hhard Γ L hL).trans hred

/-- A polynomially verifiable target is NP-complete when an NP-complete
language reduces to it in polynomial time. -/
theorem NPComplete.of_reducible {Γ₁ Γ₂ : Type} {L₁ : Language Γ₁}
    {L₂ : Language Γ₂} (hcomplete : NPComplete L₁)
    (hred : PolyTimeReducible L₁ L₂)
    (hmem : PolyTimeVerifiable L₂) : NPComplete L₂ :=
  ⟨hmem, NPHard.of_reducible hcomplete.2 hred⟩

/-- Extract polynomial-time verifiability from an NP-completeness proof. -/
theorem NPComplete.verifiable {Γ : Type} {L : Language Γ}
    (h : NPComplete L) : PolyTimeVerifiable L := h.1

/-- Extract NP-hardness from an NP-completeness proof. -/
theorem NPComplete.hard {Γ : Type} {L : Language Γ}
    (h : NPComplete L) : NPHard L := h.2

end Chapter34

end CLRS
