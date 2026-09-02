import Mathlib.Computability.TuringMachine.Computable

/-!
# CLRS Section 34.4 - Finite alphabet support for Cook--Levin

A bundled {lit}`FinTM2` requires only its input alphabet to be finite. For a fixed
machine, however, every symbol that its finite program can push comes from a
finite image of the finite control state.  This file collects those images,
together with the input alphabet, into a finite program-support
over-approximation and proves that executions stay inside it.

The set is intentionally an over-approximation: it collects both arms of every
branch and the program rooted at every label.  It does not claim that every
collected symbol occurs in an actually reachable configuration.
-/

open Computability StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-! ## Finite program support -/

/-- Symbols pushed by a statement tree onto a designated stack. -/
noncomputable def stmtPushSet (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) (k : tm.K) : Finset (tm.Γ k) := by
  letI := tm.σFin
  classical
  induction q with
  | push j f q ih =>
      exact (if h : j = k then
        Finset.univ.image (fun s => cast (congrArg tm.Γ h) (f s))
      else ∅) ∪ ih
  | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ ih₁ ih₂ => exact ih₁ ∪ ih₂
  | goto _ | halt => exact ∅

/-- Input symbols and all symbols pushed anywhere in the finite program.

This is a finite program-support over-approximation, not the exact semantic
reachable alphabet. -/
noncomputable def reachableAlphabet (tm : _root_.Turing.FinTM2)
    (k : tm.K) : Finset (tm.Γ k) := by
  letI := tm.ΛFin
  letI := tm.Γk₀Fin
  classical
  exact (if h : k = tm.k₀ then
      Finset.univ.image (fun a : tm.Γ tm.k₀ => cast (congrArg tm.Γ h.symm) a)
    else ∅) ∪ Finset.univ.biUnion fun label => stmtPushSet tm (tm.m label) k

/-- Every stack symbol of a configuration belongs to the fixed machine's
finite program-support alphabet. -/
def CfgAlphabetBounded (tm : _root_.Turing.FinTM2) (c : tm.Cfg) : Prop :=
  ∀ k a, a ∈ c.stk k → a ∈ reachableAlphabet tm k

/-- Every statement rooted at a program label contributes its push support to
the machine-wide support. -/
theorem stmtPushSet_program_subset (tm : _root_.Turing.FinTM2)
    (label : tm.Λ) (k : tm.K) :
    stmtPushSet tm (tm.m label) k ⊆ reachableAlphabet tm k := by
  letI := tm.ΛFin
  classical
  intro a ha
  unfold reachableAlphabet
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨label, Finset.mem_univ _, ha⟩

/-! ## Preservation -/

/-- Initial configurations use only the finite input part of the support. -/
theorem initList_alphabetBounded (tm : _root_.Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) :
    CfgAlphabetBounded tm (_root_.Turing.initList tm input) := by
  letI := tm.Γk₀Fin
  classical
  intro k a ha
  unfold _root_.Turing.initList at ha
  dsimp only at ha
  split at ha
  next h =>
    subst k
    unfold reachableAlphabet
    apply Finset.mem_union_left
    simp
  next h => simp at ha

/-- Executing an arbitrary statement preserves alphabet boundedness when its
push support is already included in the fixed machine's support. -/
theorem stepAux_alphabetBounded (tm : _root_.Turing.FinTM2)
    {q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ} {c c' : tm.Cfg}
    (hq : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hc : CfgAlphabetBounded tm c)
    (hstep : _root_.Turing.TM2.stepAux q c.var c.stk = c') :
    CfgAlphabetBounded tm c' := by
  classical
  subst c'
  induction q generalizing c with
  | push j f q ih =>
      apply ih (c := { c with stk := Function.update c.stk j (f c.var :: c.stk j) })
      · intro k a ha
        exact hq k (Finset.mem_union_right _ ha)
      · intro k a ha
        by_cases hkj : k = j
        · subst k
          simp only [Function.update_self] at ha
          simp only [List.mem_cons] at ha
          rcases ha with ha | ha
          · subst a
            apply hq j
            apply Finset.mem_union_left
            simp
          · exact hc j a ha
        · simp only [Function.update_of_ne hkj] at ha
          exact hc k a ha
  | peek j f q ih =>
      apply ih (c := { c with var := f c.var (c.stk j).head? })
      · simpa [stmtPushSet] using hq
      · exact hc
  | pop j f q ih =>
      apply ih (c :=
        { c with
          var := f c.var (c.stk j).head?
          stk := Function.update c.stk j (c.stk j).tail })
      · simpa [stmtPushSet] using hq
      · intro k a ha
        by_cases hkj : k = j
        · subst k
          simp only [Function.update_self] at ha
          exact hc j a (List.mem_of_mem_tail ha)
        · simp only [Function.update_of_ne hkj] at ha
          exact hc k a ha
  | load f q ih =>
      apply ih (c := { c with var := f c.var })
      · simpa [stmtPushSet] using hq
      · exact hc
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases hfc : f c.var
      · simp only [_root_.Turing.TM2.stepAux, hfc]
        apply ih₂ (c := c)
        · intro k a ha
          exact hq k (Finset.mem_union_right _ ha)
        · exact hc
      · simp only [_root_.Turing.TM2.stepAux, hfc]
        apply ih₁ (c := c)
        · intro k a ha
          exact hq k (Finset.mem_union_left _ ha)
        · exact hc
  | goto f => exact hc
  | halt => exact hc

/-- The generic preservation premise is automatically available for a
statement rooted at a machine program label. -/
theorem stepAux_program_alphabetBounded (tm : _root_.Turing.FinTM2)
    (label : tm.Λ) {c c' : tm.Cfg}
    (hc : CfgAlphabetBounded tm c)
    (hstep : _root_.Turing.TM2.stepAux (tm.m label) c.var c.stk = c') :
    CfgAlphabetBounded tm c' :=
  stepAux_alphabetBounded tm (fun k => stmtPushSet_program_subset tm label k) hc hstep

/-- One machine step preserves the finite alphabet-support invariant. -/
theorem step_alphabetBounded (tm : _root_.Turing.FinTM2) {c c' : tm.Cfg}
    (hc : CfgAlphabetBounded tm c) (hstep : tm.step c = some c') :
    CfgAlphabetBounded tm c' := by
  rcases c with ⟨l, v, stk⟩
  cases l with
  | none => simp [_root_.Turing.FinTM2.step, _root_.Turing.TM2.step] at hstep
  | some label =>
      simp only [_root_.Turing.FinTM2.step, _root_.Turing.TM2.step] at hstep
      exact stepAux_program_alphabetBounded tm label hc (Option.some.inj hstep)

/-- Bounded iteration of the transition function preserves finite alphabet
support. -/
theorem evalsInSteps_alphabetBounded (tm : _root_.Turing.FinTM2)
    {c c' : tm.Cfg} {n : Nat}
    (hc : CfgAlphabetBounded tm c)
    (h : (flip bind tm.step)^[n] (some c) = some c') :
    CfgAlphabetBounded tm c' := by
  induction n generalizing c with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at h
      simpa [h] using hc
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      change (flip bind tm.step)^[n] (tm.step c) = some c' at h
      cases hstep : tm.step c with
      | none =>
          rw [hstep] at h
          have hnone : ∀ m : Nat, (flip bind tm.step)^[m] (none : Option tm.Cfg) = none := by
            intro m
            induction m with
            | zero => rfl
            | succ m ihm =>
                rw [Function.iterate_succ_apply]
                exact ihm
          rw [hnone] at h
          contradiction
      | some c₁ =>
          rw [hstep] at h
          exact ih (step_alphabetBounded tm hc hstep) h

/-- The support alphabet for every fixed stack is finite. -/
theorem reachableAlphabet_finite (tm : _root_.Turing.FinTM2) (k : tm.K) :
    Set.Finite {a | a ∈ reachableAlphabet tm k} :=
  (reachableAlphabet tm k).finite_toSet

end CLRS.Chapter34.Turing.CookLevin
