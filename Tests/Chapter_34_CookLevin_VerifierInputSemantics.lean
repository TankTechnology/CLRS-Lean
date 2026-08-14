import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Semantics

/-!
# Chapter 34 verifier-input shape semantics regressions

The public contract is exact: on a canonically represented input stack, the
shape circuit accepts exactly the bounded separator encodings of `(c, x)`.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

#check VerifierInputArmMatches
#check verifierInputShapeCircuit_eval_iff_exists_length
#check verifierInputShapeCircuit_eval_iff
#check verifierInputShapeCircuit_sound
#check verifierInputShapeCircuit_complete
#check verifierInputShapeCircuit_eval_extends
#check verifierInputShapeCircuit_eval_proof_irrel

private def allTrueBits {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) :
    StackBits W.machine.tm H W.machine.tm.k₀ where
  height := fun _ => true
  cell := fun _ _ => true

private def allFalseHeightBits {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) :
    StackBits W.machine.tm H W.machine.tm.k₀ where
  height := fun _ => false
  cell := fun _ _ => true

private def allFalseCellBits {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) :
    StackBits W.machine.tm H W.machine.tm.k₀ where
  height := fun _ => true
  cell := fun _ _ => false

private def separatorCellOnlyBits {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) :
    StackBits W.machine.tm H W.machine.tm.k₀ where
  height := fun _ => true
  cell := fun cell _ => decide (cell.val = 0)

-- Empty alphabet, bound-zero arm: precisely the separator-only shape fits.
example {L : Language Empty} (W : VerifierWitness L)
    (hbound : W.certificateBound.eval 0 = 0) :
    VerifierInputArmMatches W 1 [] (allTrueBits W 1) 0 ∧
      W.certificateBound.eval 0 = 0 := by
  exact ⟨by simp [VerifierInputArmMatches, allTrueBits], hbound⟩

-- A one-symbol public Bool instance fits the zero-certificate arm.
example {L : Language Bool} (W : VerifierWitness L) :
    VerifierInputArmMatches W 2 [true] (allTrueBits W 2) 0 := by
  simp [VerifierInputArmMatches, allTrueBits]

-- Negative: the selected height coordinate is wrong.
example {L : Language Empty} (W : VerifierWitness L) :
    ¬ VerifierInputArmMatches W 1 [] (allFalseHeightBits W 1) 0 := by
  simp [VerifierInputArmMatches, allFalseHeightBits]

-- Negative: the separator cell is absent.
example {L : Language Empty} (W : VerifierWitness L) :
    ¬ VerifierInputArmMatches W 1 [] (allFalseCellBits W 1) 0 := by
  simp [VerifierInputArmMatches, allFalseCellBits]

-- Negative: the fixed public Bool suffix is absent.
example {L : Language Bool} (W : VerifierWitness L) :
    ¬ VerifierInputArmMatches W 2 [true] (separatorCellOnlyBits W 2) 0 := by
  simp [VerifierInputArmMatches, separatorCellOnlyBits]

end

end CLRS.Chapter34.Turing.CookLevin
