import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Horizon

/-!
# Semantic verifier tableaux

This module isolates the machine-level statement implemented by the final
Cook--Levin circuit.  It contains no circuit construction: a tableau starts
from one bounded certificate/input pair, follows the total stuttering step,
and ends in the canonical accepting configuration.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing

noncomputable section

/-- The verifier machine's initial configuration for certificate `c` and
instance `x`. -/
def verifierInitialCfg {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (c x : List Γ) : W.machine.tm.Cfg :=
  initList W.machine.tm
    (List.map W.machine.inputAlphabet.invFun (pairEncoding c x))

/-- The unique accepting target used by the verifier tableau. -/
def verifierAcceptingCfg {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) : W.machine.tm.Cfg :=
  haltList W.machine.tm
    (List.map W.machine.outputAlphabet.invFun (boolEncoding true))

/-- A complete semantic tableau for `x` at the verifier's uniform horizon.
The certificate is existential, but its polynomial length bound is explicit. -/
def IsVerifierTableau {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ)
    (rows : Fin ((verifierHorizon W).eval x.length + 1) → W.machine.tm.Cfg) :
    Prop :=
  ∃ c : List Γ,
    c.length ≤ W.certificateBound.eval x.length ∧
    rows 0 = verifierInitialCfg W c x ∧
    (∀ t : Fin ((verifierHorizon W).eval x.length),
      rows t.succ = stutterStep W.machine.tm (rows t.castSucc)) ∧
    rows (Fin.last ((verifierHorizon W).eval x.length)) =
      verifierAcceptingCfg W

/-- Local adjacent-row equations determine every row as the corresponding
iterate of the initial configuration. -/
theorem verifierTableau_row_eq_iterate {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ)
    (rows : Fin ((verifierHorizon W).eval x.length + 1) → W.machine.tm.Cfg)
    {c : List Γ}
    (hinitial : rows 0 = verifierInitialCfg W c x)
    (hstep : ∀ t : Fin ((verifierHorizon W).eval x.length),
      rows t.succ = stutterStep W.machine.tm (rows t.castSucc))
    (t : Fin ((verifierHorizon W).eval x.length + 1)) :
    rows t = (stutterStep W.machine.tm)^[t.val]
      (verifierInitialCfg W c x) := by
  induction t using Fin.induction with
  | zero => simpa using hinitial
  | succ i ih =>
      rw [hstep i, ih]
      change stutterStep W.machine.tm
          ((stutterStep W.machine.tm)^[i.val]
            (verifierInitialCfg W c x)) =
        (stutterStep W.machine.tm)^[i.val + 1]
          (verifierInitialCfg W c x)
      rw [Function.iterate_succ_apply']

/-- The machine-level tableau specification is equivalent to language
membership.  This is the semantic core later inherited by the generated
general circuit. -/
theorem exists_isVerifierTableau_iff {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (∃ rows, IsVerifierTableau W x rows) ↔ x ∈ L := by
  constructor
  · rintro ⟨rows, c, hc, hinitial, hstep, haccept⟩
    have hlast := verifierTableau_row_eq_iterate W x rows hinitial hstep
      (Fin.last ((verifierHorizon W).eval x.length))
    have hrun := W.stutter_horizon_eq_haltList (c := c) (x := x) hc
    have hfinalRun :
        (stutterStep W.machine.tm)^[(verifierHorizon W).eval x.length]
            (verifierInitialCfg W c x) = verifierAcceptingCfg W := by
      simpa using hlast.symm.trans haccept
    have hrun' :
        (stutterStep W.machine.tm)^[(verifierHorizon W).eval x.length]
            (verifierInitialCfg W c x) =
          haltList W.machine.tm
            (List.map W.machine.outputAlphabet.invFun
              (boolEncoding (W.verify c x))) := by
      simpa [verifierInitialCfg] using hrun
    have htargets :
        haltList W.machine.tm
            (List.map W.machine.outputAlphabet.invFun
              (boolEncoding (W.verify c x))) =
          verifierAcceptingCfg W := by
      exact hrun'.symm.trans hfinalRun
    have houtputs := congrArg
      (fun cfg : W.machine.tm.Cfg => cfg.stk W.machine.tm.k₁) htargets
    have hverify : W.verify c x = true := by
      cases h : W.verify c x <;>
        simp [verifierAcceptingCfg, _root_.Turing.haltList,
          Turing.TM2Comp.boolEncoding, h] at houtputs ⊢
    exact (W.correct x).2 ⟨c, hc, hverify⟩
  · intro hx
    rcases (W.correct x).1 hx with ⟨c, hc, hverify⟩
    let initial := verifierInitialCfg W c x
    let rows : Fin ((verifierHorizon W).eval x.length + 1) →
        W.machine.tm.Cfg := fun t =>
      (stutterStep W.machine.tm)^[t.val] initial
    refine ⟨rows, c, hc, ?_, ?_, ?_⟩
    · rfl
    · intro t
      change (stutterStep W.machine.tm)^[t.val + 1] initial =
        stutterStep W.machine.tm
          ((stutterStep W.machine.tm)^[t.val] initial)
      exact Function.iterate_succ_apply' (stutterStep W.machine.tm) t.val initial
    · change (stutterStep W.machine.tm)^[(verifierHorizon W).eval x.length]
          (verifierInitialCfg W c x) = verifierAcceptingCfg W
      simpa [verifierInitialCfg, verifierAcceptingCfg, hverify] using
        (W.stutter_horizon_eq_haltList (c := c) (x := x) hc)

end

end CLRS.Chapter34.Turing.CookLevin
