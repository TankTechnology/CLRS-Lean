import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Horizon
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackSemantics

/-!
# Cook--Levin verifier-input support bridges

This pure layer connects the verifier machine's input-alphabet equivalence to
the finite supported-symbol codes used by tableau stacks.  It also exposes the
small semantic projections needed to read certificate-shaped data from a
canonically represented first-row stack.  No circuit gates or layouts are
constructed here.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing

noncomputable section

/-! ## Verifier input symbols -/

/-- Every symbol of the verifier's external input alphabet gives a supported
symbol on the machine's designated input stack. -/
def verifierInputSymbol {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (symbol : Option Γ) : SupportedSymbol W.machine.tm W.machine.tm.k₀ := by
  refine ⟨W.machine.inputAlphabet.invFun symbol, ?_⟩
  letI := W.machine.tm.Γk₀Fin
  classical
  unfold reachableAlphabet
  apply Finset.mem_union_left
  simp

/-- The underlying machine symbol is the inverse image supplied by the
verifier machine's input-alphabet equivalence. -/
@[simp] theorem verifierInputSymbol_val {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (symbol : Option Γ) :
    (verifierInputSymbol W symbol).val =
      W.machine.inputAlphabet.invFun symbol := by
  rfl

/-- Mapping a supported verifier input symbol back to the external alphabet
recovers the original optional symbol. -/
@[simp] theorem verifierInputSymbol_apply {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (symbol : Option Γ) :
    W.machine.inputAlphabet (verifierInputSymbol W symbol).val = symbol := by
  exact W.machine.inputAlphabet.apply_symm_apply symbol

/-- Canonical nonblank tableau-cell code for one verifier input symbol. -/
def verifierInputCode {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (symbol : Option Γ) :
    Fin ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1) :=
  encodeAlphabetSymbol W.machine.tm W.machine.tm.k₀
    (verifierInputSymbol W symbol).val (verifierInputSymbol W symbol).property

/-- A verifier input symbol always uses a nonblank cell coordinate. -/
theorem verifierInputCode_ne_blank {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (symbol : Option Γ) :
    verifierInputCode W symbol ≠
      Fin.last (reachableAlphabet W.machine.tm W.machine.tm.k₀).card := by
  intro heq
  have hval := congrArg Fin.val heq
  have hlt : (verifierInputCode W symbol).val <
      (reachableAlphabet W.machine.tm W.machine.tm.k₀).card := by
    exact (alphabetEquivFin W.machine.tm W.machine.tm.k₀
      (verifierInputSymbol W symbol)).isLt
  simp only [Fin.val_last] at hval
  omega

/-! ## Certificate-shaped machine inputs -/

/-- A represented verifier input is the mapped separator encoding of one
certificate satisfying the normalized polynomial certificate bound and the
fixed public instance. -/
def IsVerifierInput {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (input : List (W.machine.tm.Γ W.machine.tm.k₀)) : Prop :=
  ∃ c : List Γ,
    c.length ≤ W.certificateBound.eval x.length ∧
      input = List.map W.machine.inputAlphabet.invFun (pairEncoding c x)

/-- The maximum pair-encoded verifier input fits the published tableau height.
This bound is independent of the particular certificate. -/
theorem verifierInputBound_le_height {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (n : Nat) :
    (verifierInputBound W).eval n ≤ (verifierHeight W).eval n := by
  rw [verifierHeight_eval]
  omega

/-! ## Canonical stack point projections -/

namespace StackBits.Represents

/-- In a represented stack, a height coordinate is selected exactly at the
length of the represented list. -/
theorem height_eq_true_iff
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {stack : StackBits tm H k} {xs : List (tm.Γ k)}
    (hrep : stack.Represents xs) (height : Fin (H + 1)) :
    stack.height height = true ↔ height.val = xs.length := by
  rcases hrep.eq_encode with ⟨halphabet, hheight, hstack⟩
  rw [hstack]
  simp [encodeBoundedStackBits, encodeBoundedStack, encodeOneHot]
  constructor
  · intro heq
    exact congrArg Fin.val heq
  · intro hval
    apply Fin.ext
    exact hval

/-- At an active physical cell, a supported-symbol coordinate is selected
exactly when the represented list contains that original machine symbol there.
No inhabitant or partial option extraction is needed. -/
theorem active_cell_eq_true_iff
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {stack : StackBits tm H k} {xs : List (tm.Γ k)}
    (hrep : stack.Represents xs) (cell : Fin H)
    (hactive : cell.val < xs.length) (symbol : SupportedSymbol tm k) :
    stack.cell cell
        (encodeAlphabetSymbol tm k symbol.val symbol.property) = true ↔
      xs.get ⟨cell.val, hactive⟩ = symbol.val := by
  rcases hrep.eq_encode with ⟨halphabet, hheight, hstack⟩
  rw [hstack]
  simp only [encodeBoundedStackBits_cell, encodeBoundedStack, dif_pos hactive]
  simp [encodeOneHot, encodeAlphabetSymbol]
  constructor
  · intro heq
    exact (congrArg Subtype.val heq).symm
  · intro hval
    apply Subtype.ext
    exact hval.symm

end StackBits.Represents

end


end CLRS.Chapter34.Turing.CookLevin
