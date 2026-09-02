import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauSemantics

/-!
# Concrete satisfying verifier tableaux

This module turns one bounded certificate into the canonical sequence of
machine configurations, bounded row encodings, and external circuit inputs.
It is the completeness witness used by whole-tableau circuit assembly.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing

noncomputable section

/-- Configuration at row `t` of the verifier's padded computation. -/
def verifierTableauCfg {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (c x : List Γ) (t : Nat) : W.machine.tm.Cfg :=
  (stutterStep W.machine.tm)^[t] (verifierInitialCfg W c x)

@[simp] theorem verifierTableauCfg_initial {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (c x : List Γ) :
    verifierTableauCfg W c x 0 = verifierInitialCfg W c x := rfl

/-- Consecutive witness rows satisfy the exact total transition relation. -/
theorem verifierTableauCfg_step {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (c x : List Γ) (t : Nat) :
    verifierTableauCfg W c x (t + 1) =
      stutterStep W.machine.tm (verifierTableauCfg W c x t) := by
  exact Function.iterate_succ_apply' (stutterStep W.machine.tm) t
    (verifierInitialCfg W c x)

/-- Every concrete witness row stays inside the machine's finite alphabet
support. -/
theorem VerifierWitness.verifierTableauCfg_alphabetBounded
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (c x : List Γ) (t : Nat) :
    CfgAlphabetBounded W.machine.tm (verifierTableauCfg W c x t) := by
  apply stutter_iterate_alphabetBounded
  exact initList_alphabetBounded W.machine.tm _

/-- Every witness row through the uniform horizon fits the published height. -/
theorem VerifierWitness.verifierTableauCfg_height
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length)
    {t : Nat} (ht : t ≤ (verifierHorizon W).eval x.length)
    (k : W.machine.tm.K) :
    ((verifierTableauCfg W c x t).stk k).length ≤
      (verifierHeight W).eval x.length := by
  simpa [verifierTableauCfg, verifierInitialCfg] using
    W.stack_length_le_height hc ht k

/-- Canonical bounded Boolean row at time `t`. -/
def verifierTableauBits {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (c x : List Γ)
    (hc : c.length ≤ W.certificateBound.eval x.length)
    (t : Fin (tableauRowCount ((verifierHorizon W).eval x.length))) :
    CfgBits W.machine.tm ((verifierHeight W).eval x.length) :=
  encodeRawCfgBits
    (encodeCfg W.machine.tm
      (W.verifierTableauCfg_alphabetBounded c x t.val)
      (W.verifierTableauCfg_height hc (Nat.le_of_lt_succ t.isLt)))

/-- Finite tableau assignment induced by one bounded certificate. -/
def verifierTableauAssignment {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (c x : List Γ)
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    let allocation := allocateTableauRows W.machine.tm
      ((verifierHeight W).eval x.length) ((verifierHorizon W).eval x.length)
    Fin allocation.builder.inputCount → Bool := fun input =>
  writeTableauBits W.machine.tm ((verifierHeight W).eval x.length)
    ((verifierHorizon W).eval x.length) (fun _ => false)
    (verifierTableauBits W c x hc) input.val

/-- Every allocated public row decodes to the corresponding witness
configuration under the finite certificate-induced assignment. -/
theorem VerifierWitness.allocateTableauRows_eval_verifierTableau
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval x.length))) :
    let H := (verifierHeight W).eval x.length
    let T := (verifierHorizon W).eval x.length
    let allocation := allocateTableauRows W.machine.tm H T
    evalBundle allocation.builder
        (fun i => if hi : i < allocation.builder.inputCount then
          verifierTableauAssignment W c x hc ⟨i, hi⟩ else false)
        (allocation.rows row) (allocation.rowValid row) =
      some (verifierTableauCfg W c x row.val) := by
  dsimp only
  let allocation := allocateTableauRows W.machine.tm
    ((verifierHeight W).eval x.length) ((verifierHorizon W).eval x.length)
  apply evalBundle_encodeCfg
  have hinputs :
      (fun i => if hi : i < allocation.builder.inputCount then
          verifierTableauAssignment W c x hc ⟨i, hi⟩ else false) =
        writeTableauBits W.machine.tm ((verifierHeight W).eval x.length)
          ((verifierHorizon W).eval x.length) (fun _ => false)
          (verifierTableauBits W c x hc) := by
    funext i
    by_cases hi : i < allocation.builder.inputCount
    · simp [hi, verifierTableauAssignment, allocation]
    · rw [dif_neg hi]
      apply Eq.symm
      apply writeTableauBitsAt_outside
      right
      have hcount := allocateTableauRows_inputCount W.machine.tm
        ((verifierHeight W).eval x.length)
        ((verifierHorizon W).eval x.length)
      dsimp only [allocation] at hi hcount
      rw [hcount] at hi
      simpa [writeTableauBits, tableauInputCount] using Nat.le_of_not_gt hi
  rw [hinputs]
  change evalCfgBits allocation.builder
      (writeTableauBits W.machine.tm ((verifierHeight W).eval x.length)
        ((verifierHorizon W).eval x.length) (fun _ => false)
        (verifierTableauBits W c x hc))
      (allocation.rows row) = _
  unfold writeTableauBits
  rw [allocation.evalCfgBits_writeTableau]
  rfl

/-- An accepting certificate makes the final witness row exactly the canonical
true-output halt configuration. -/
theorem verifierTableauCfg_last_of_accepts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length)
    (hverify : W.verify c x = true) :
    verifierTableauCfg W c x ((verifierHorizon W).eval x.length) =
      verifierAcceptingCfg W := by
  simpa [verifierTableauCfg, verifierInitialCfg, verifierAcceptingCfg, hverify]
    using W.stutter_horizon_eq_haltList (c := c) (x := x) hc

end

end CLRS.Chapter34.Turing.CookLevin
