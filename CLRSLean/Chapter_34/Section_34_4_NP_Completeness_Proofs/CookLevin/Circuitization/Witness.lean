import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification

/-!
# Cook--Levin normalized verifier witnesses

This module turns the existential definition of polynomial-time verification
into data that later circuitization layers can consume.  It deliberately does
not allocate tableau rows or assemble a circuit.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing

noncomputable section

/-- A polynomial verifier packaged with a concrete machine and certificate
bound.  This is the normalized input to Cook--Levin circuitization. -/
structure VerifierWitness {Γ : Type} (L : Language Γ) where
  verify : List Γ → List Γ → Bool
  certificateBound : Polynomial Nat
  machine : TM2ComputableInPolyTime
    (fun pr : List Γ × List Γ => pairEncoding pr.1 pr.2) boolEncoding
    (fun pr => verify pr.1 pr.2)
  correct : ∀ x, x ∈ L ↔ ∃ c,
    c.length ≤ certificateBound.eval x.length ∧ verify c x = true

namespace VerifierWitness

/-- Choose the verifier, polynomial, and concrete machine carried by a
`PolyTimeVerifiable` proof. -/
noncomputable def ofPolyTimeVerifiable {Γ : Type} {L : Language Γ}
    (h : PolyTimeVerifiable L) : VerifierWitness L := by
  let verify := Classical.choose h
  let h₁ := Classical.choose_spec h
  let certificateBound := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  exact
    { verify
      certificateBound
      machine := Classical.choice h₂.1
      correct := h₂.2 }

/-- Normalization depends only on the proposition, not on the particular proof
term supplied by a caller. -/
theorem ofPolyTimeVerifiable_proof_irrel {Γ : Type} {L : Language Γ}
    (h₁ h₂ : PolyTimeVerifiable L) :
    ofPolyTimeVerifiable h₁ = ofPolyTimeVerifiable h₂ := by
  have : h₁ = h₂ := Subsingleton.elim _ _
  subst h₂
  rfl

end VerifierWitness

/-- Stable public length law for the separator-based pair encoding. -/
@[simp] theorem pairEncoding_length {Γ : Type} (c x : List Γ) :
    (pairEncoding c x).length = c.length + x.length + 1 := by
  simp [pairEncoding, Nat.add_assoc]

/-- Mapping a pair encoding into a machine alphabet preserves its length. -/
@[simp] theorem VerifierWitness.machineInput_length {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (c x : List Γ) :
    (List.map W.machine.inputAlphabet.invFun (pairEncoding c x)).length =
      c.length + x.length + 1 := by
  simp

end

end CLRS.Chapter34.Turing.CookLevin
