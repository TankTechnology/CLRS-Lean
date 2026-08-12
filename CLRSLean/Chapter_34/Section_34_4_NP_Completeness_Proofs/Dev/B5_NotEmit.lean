import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B4_Park

/-!
# Dev B5: the `not` clause emission

The `not` clause emission: `Formula.not f` emits `notClauses c y₁`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- not clause emit: `Formula.not f` emits `notClauses c y₁`
-- ============================================================

/-- `emitNot`: pop the child value-variable's `false` separator and push the
first clause's header `[clauseMark, negMark, varMark]`, entering the counter
loop. -/
lemma emitNot_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitNot, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.not₂ Op.auxEmit, stk inp T c V' F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveCnt`: one counter unit emits one `endMark` and one scratch marker. -/
lemma moveCnt_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T (c + 1) V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T c V F
          (() :: S) (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `moveCnt`: an empty counter routes to `go` with the counter parked. -/
lemma moveCnt_final (go : Label) (inp T : List FormulaSym) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `moveCnt` loop: `c` counter units become `c` `endMark`s and `c`
scratch markers, ending at `go`. -/
lemma moveCnt_phase (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[c + 1]
        (some (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F
          (List.replicate c () ++ S) (List.replicate c CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction c generalizing S O with
  | zero =>
      have h := moveCnt_final go inp T V F S O U
      change (flip bind Sstep) (some (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T 0 V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ c ih =>
      have h := moveCnt_step go inp T c V F S O U
      rw [show Nat.succ c + 1 = c + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[c + 1]
          (Sstep (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T (Nat.succ c) V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F
            (List.replicate (Nat.succ c) () ++ S) (List.replicate (Nat.succ c) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (S := () :: S) (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[c + 1]
            (some (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T c V F (() :: S)
              (CNFSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F
              (List.replicate c () ++ (() :: S)) (List.replicate c CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F
            (List.replicate (Nat.succ c) () ++ S) (List.replicate (Nat.succ c) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · rw [show (() :: S) = [()] ++ S by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]
              · rw [show (CNFSym.endMark :: O) = [CNFSym.endMark] ++ O by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

/-- `not₂`: route through `restoreCnt` so the counter is restored before the
child's value variable is parked (keeping `scr` to one kind of unit). -/
lemma not₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₂, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.not₃ Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `restoreCnt`: one scratch marker restores one counter unit. -/
lemma restoreCnt_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F (() :: S) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T (c + 1) V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `restoreCnt`: an empty scratch routes to `go` with the counter restored. -/
lemma restoreCnt_final (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    Sstep (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T c V F [] O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `restoreCnt` loop: `k` scratch markers restore `k` counter units. -/
lemma restoreCnt_phase (go : Label) (inp T : List FormulaSym) (c k : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F (List.replicate k ()) O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T (c + k) V F [] O U⟩ : (mach).Cfg) := by
  induction k generalizing c with
  | zero =>
      have h := restoreCnt_final go inp T c V F O U
      change (flip bind Sstep) (some (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F [] O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T c V F [] O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := restoreCnt_step go inp T c V F (List.replicate k ()) O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F
            (() :: List.replicate k ()) O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T (c + Nat.succ k) V F [] O U⟩ : (mach).Cfg)
      have hih := ih (c := c + 1)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F
              (() :: List.replicate k ()) O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T (c + 1) V F
                (List.replicate k ()) O U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T ((c + 1) + k) V F [] O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T (c + Nat.succ k) V F [] O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- `not₃`: push the first clause's second-literal header `[varMark, negMark]`
and the completing `endMark`, entering the value loop. -/
lemma not₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₃, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.not₄ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varEmit`): one `true` in the run emits one `endMark` and parks
a scratch marker. -/
lemma moveVal_varEmit_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (true :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c V' F
          (() :: S) (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varEmit`): a non-`true` head stops the run, routing to `go`. -/
lemma moveVal_varEmit_stop (go : Label) (b : Bool) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hb : b ≠ true) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg) := by
  cases b with
  | true => simp at hb
  | false =>
      apply congrArg some
      apply Turing.TM2Comp.Cfg_ext
      · simp [prog, Sstep]
      · simp [prog, Sstep]
      · funext k
        cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varEmit`): an empty value tape stops the run, routing to `go`. -/
lemma moveVal_varEmit_empty (go : Label) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c [] F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c [] F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varEmit`): the run stops at any non-`true` remainder. -/
lemma moveVal_varEmit_end (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hV : V.head? ≠ some true) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  cases V with
  | nil =>
      exact moveVal_varEmit_empty go inp T c F S O U
  | cons b V' =>
      have hb : b ≠ true := by
        intro h
        apply hV
        simp [h]
      exact moveVal_varEmit_stop go b inp T c V' F S O U hb

/-- The `moveVal` (`varEmit`) loop: `k` `true`s become `k` `endMark`s and `k`
parked markers, ending at `go`. -/
lemma moveVal_varEmit_phase (go : Label) (k : Nat) (inp T : List FormulaSym) (c : Nat)
    (V : List Bool) (F : List Frame) (S : List Unit) (O U : List CNFSym)
    (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F
          (List.replicate k () ++ S) (List.replicate k CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction k generalizing S O with
  | zero =>
      have h := moveVal_varEmit_end go inp T c V F S O U hV
      change (flip bind Sstep) (some (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := moveVal_varEmit_step go inp T c (List.replicate k true ++ V) F S O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F
            (List.replicate (Nat.succ k) () ++ S) (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      have hih := ih (S := () :: S) (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (List.replicate k true ++ V) F (() :: S)
                (CNFSym.endMark :: O) U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F
            (List.replicate k () ++ (() :: S)) (List.replicate k CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F
            (List.replicate (Nat.succ k) () ++ S) (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · rw [show (() :: S) = [()] ++ S by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]
              · rw [show (CNFSym.endMark :: O) = [CNFSym.endMark] ++ O by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

/-- `not₄`: push the second clause's header `[clauseMark, posMark, varMark]`,
entering the value restore. -/
lemma not₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₄, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.not₅ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `restoreVal`: one scratch marker restores one `true` to the value tape. -/
lemma restoreVal_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F (() :: S) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c (true :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `restoreVal`: an empty scratch routes to `go` with the value restored. -/
lemma restoreVal_final (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    Sstep (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F [] O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `restoreVal` loop: `k` scratch markers restore `k` `true`s. -/
lemma restoreVal_phase (go : Label) (k : Nat) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F (List.replicate k ()) O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (List.replicate k true ++ V) F [] O U⟩ : (mach).Cfg) := by
  induction k generalizing V with
  | zero =>
      have h := restoreVal_final go inp T c V F O U
      change (flip bind Sstep) (some (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F [] O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F [] O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := restoreVal_step go inp T c V F (List.replicate k ()) O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F
            (() :: List.replicate k ()) O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (List.replicate (Nat.succ k) true ++ V) F [] O U⟩ : (mach).Cfg)
      have hih := ih (V := true :: V)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F
              (() :: List.replicate k ()) O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c (true :: V) F
                (List.replicate k ()) O U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (List.replicate k true ++ (true :: V)) F [] O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (List.replicate (Nat.succ k) true ++ V) F [] O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
              rw [← List.append_assoc]
              rw [replicate_append_one]

/-- `not₅`: re-enter the counter loop for the second clause's index run. -/
lemma not₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₅, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.not₆ Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `not₆`: push the completing `endMark` and the second clause's first-literal
header `[posMark, varMark]`, entering the (consuming) value loop. -/
lemma not₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.constMake Op.varPop, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varPop`): one `true` in the run emits one `endMark`, consuming
the run without parking it. -/
lemma moveVal_varPop_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (true :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c V' F S (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varPop`): a non-`true` head stops the run, routing to `go`. -/
lemma moveVal_varPop_stop (go : Label) (b : Bool) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hb : b ≠ true) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varPop, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg) := by
  cases b with
  | true => simp at hb
  | false =>
      apply congrArg some
      apply Turing.TM2Comp.Cfg_ext
      · simp [prog, Sstep]
      · simp [prog, Sstep]
      · funext k
        cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varPop`): an empty value tape stops the run, routing to `go`. -/
lemma moveVal_varPop_empty (go : Label) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c [] F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varPop, stk inp T c [] F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varPop`): the run stops at any non-`true` remainder. -/
lemma moveVal_varPop_end (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hV : V.head? ≠ some true) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  cases V with
  | nil =>
      exact moveVal_varPop_empty go inp T c F S O U
  | cons b V' =>
      have hb : b ≠ true := by
        intro h
        apply hV
        simp [h]
      exact moveVal_varPop_stop go b inp T c V' F S O U hb

/-- The `moveVal` (`varPop`) loop: `k` `true`s become `k` `endMark`s, ending at
`go`. -/
lemma moveVal_varPop_phase (go : Label) (k : Nat) (inp T : List FormulaSym) (c : Nat)
    (V : List Bool) (F : List Frame) (S : List Unit) (O U : List CNFSym)
    (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S (List.replicate k CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction k generalizing O with
  | zero =>
      have h := moveVal_varPop_end go inp T c V F S O U hV
      change (flip bind Sstep) (some (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := moveVal_varPop_step go inp T c (List.replicate k true ++ V) F S O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      have hih := ih (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (List.replicate k true ++ V) F S (CNFSym.endMark :: O) U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S
            (List.replicate k CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S
            (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              rw [show CNFSym.endMark :: O = [CNFSym.endMark] ++ O by simp [List.cons_append]]
              rw [← List.append_assoc]
              rw [replicate_append_one]

/-- The `emitNot` phase for `Formula.not f`: emit the two clauses
`[¬c, ¬y₁]` and `[c, y₁]` of `notClauses c y₁` onto `o` (reversed), build the
result value variable `c` on `val`, restore the counter to `c + 1`, and reach
`reduce`.  (`c` is the result variable's index, equal to the counter at entry;
`y₁` is the child value variable's index, stored on top of `val`.) -/
lemma not_phase (inp T : List FormulaSym) (c : Nat) (y₁ : Nat) (V : List Bool) (F : List Frame)
    (O U : List CNFSym) (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[4 * c + 3 * y₁ + 16]
        (some (⟨some Label.emitNot, St.emitNot, stk inp T c (false :: List.replicate (y₁ + 1) true ++ V) F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          ((encCNF (notClauses c y₁)).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := emitNot_step St.emitNot inp T c false (List.replicate (y₁ + 1) true ++ V) F [] O U
  have h2 := moveCnt_phase Label.not₂ inp T c (List.replicate (y₁ + 1) true ++ V) F []
      (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
  rw [List.append_nil] at h2
  have h3 := not₂_step (St.rsDone Label.not₂ Op.auxEmit) inp T 0 (List.replicate (y₁ + 1) true ++ V) F
      (List.replicate c ()) (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  have h4 := restoreCnt_phase Label.not₃ inp T 0 c (List.replicate (y₁ + 1) true ++ V) F
      (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  rw [Nat.zero_add] at h4
  have h5 := not₃_step (St.rsDone Label.not₃ Op.auxEmit) inp T c (List.replicate (y₁ + 1) true ++ V) F []
      (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  have h6 := moveVal_varEmit_phase Label.not₄ (y₁ + 1) inp T c V F []
      (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))) U hV
  rw [List.append_nil] at h6
  have h7 := not₄_step (St.rsDone Label.not₄ Op.varEmit) inp T c V F
      (List.replicate (y₁ + 1) ()) (List.replicate (y₁ + 1) CNFSym.endMark ++
        (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)))) U
  have h8 := restoreVal_phase Label.not₅ (y₁ + 1) inp T c V F
      (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: (List.replicate (y₁ + 1) CNFSym.endMark ++
        (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))))) U
  have h9 := not₅_step (St.rsDone Label.not₅ Op.varEmit) inp T c (List.replicate (y₁ + 1) true ++ V) F []
      (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: (List.replicate (y₁ + 1) CNFSym.endMark ++
        (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))))) U
  have h10 := moveCnt_phase Label.not₆ inp T c (List.replicate (y₁ + 1) true ++ V) F []
      (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: (List.replicate (y₁ + 1) CNFSym.endMark ++
        (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))))) U
  rw [List.append_nil] at h10
  have h11 := not₆_step (St.rsDone Label.not₆ Op.auxEmit) inp T 0 (List.replicate (y₁ + 1) true ++ V) F
      (List.replicate c ()) (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark ::
        (List.replicate (y₁ + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark ::
          (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)))))) U
  have h12 := moveVal_varPop_phase Label.constMake (y₁ + 1) inp T 0 V F
      (List.replicate c ()) (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++
        (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: (List.replicate (y₁ + 1) CNFSym.endMark ++
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))))))) U hV
  have h13 := constMake_phase c (St.rsDone Label.constMake Op.varPop) inp T 0 V F
      (List.replicate (y₁ + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark ::
        (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark ::
          (List.replicate (y₁ + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark ::
            (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)))))))) U
  calc
    (flip bind Sstep)^[4 * c + 3 * y₁ + 16]
        (some (⟨some Label.emitNot, St.emitNot, stk inp T c (false :: List.replicate (y₁ + 1) true ++ V) F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[4 * c + 3 * y₁ + 15]
          (some (⟨some Label.moveCnt, St.mv Label.not₂ Op.auxEmit, stk inp T c (List.replicate (y₁ + 1) true ++ V) F []
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
          rw [show 4 * c + 3 * y₁ + 16 = (4 * c + 3 * y₁ + 15) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 15] x) h1
    _ = (flip bind Sstep)^[3 * c + 3 * y₁ + 14]
          (some (⟨some Label.not₂, St.rsDone Label.not₂ Op.auxEmit, stk inp T 0 (List.replicate (y₁ + 1) true ++ V) F
            (List.replicate c ()) (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          rw [show 4 * c + 3 * y₁ + 15 = (3 * c + 3 * y₁ + 14) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[3 * c + 3 * y₁ + 14] x) h2
    _ = (flip bind Sstep)^[3 * c + 3 * y₁ + 13]
          (some (⟨some Label.restoreCnt, St.rs Label.not₃ Op.auxEmit, stk inp T 0 (List.replicate (y₁ + 1) true ++ V) F
            (List.replicate c ()) (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          rw [show 3 * c + 3 * y₁ + 14 = (3 * c + 3 * y₁ + 13) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[3 * c + 3 * y₁ + 13] x) h3
    _ = (flip bind Sstep)^[2 * c + 3 * y₁ + 12]
          (some (⟨some Label.not₃, St.rsDone Label.not₃ Op.auxEmit, stk inp T c (List.replicate (y₁ + 1) true ++ V) F []
            (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          rw [show 3 * c + 3 * y₁ + 13 = (2 * c + 3 * y₁ + 12) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3 * y₁ + 12] x) h4
    _ = (flip bind Sstep)^[2 * c + 3 * y₁ + 11]
          (some (⟨some Label.moveVal, St.mv Label.not₄ Op.varEmit, stk inp T c (List.replicate (y₁ + 1) true ++ V) F []
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 3 * y₁ + 12 = (2 * c + 3 * y₁ + 11) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3 * y₁ + 11] x) h5
    _ = (flip bind Sstep)^[2 * c + 2 * y₁ + 9]
          (some (⟨some Label.not₄, St.rsDone Label.not₄ Op.varEmit, stk inp T c V F
            (List.replicate (y₁ + 1) ()) (List.replicate (y₁ + 1) CNFSym.endMark ++
              (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)))) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 3 * y₁ + 11 = (2 * c + 2 * y₁ + 9) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2 * y₁ + 9] x) h6
    _ = (flip bind Sstep)^[2 * c + 2 * y₁ + 8]
          (some (⟨some Label.restoreVal, St.rs Label.not₅ Op.varEmit, stk inp T c V F
            (List.replicate (y₁ + 1) ()) (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: (List.replicate (y₁ + 1) CNFSym.endMark ++
              (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))))) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 2 * y₁ + 9 = (2 * c + 2 * y₁ + 8) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2 * y₁ + 8] x) h7
    _ = (flip bind Sstep)^[2 * c + y₁ + 6]
          (some (⟨some Label.not₅, St.rsDone Label.not₅ Op.varEmit, stk inp T c (List.replicate (y₁ + 1) true ++ V) F []
            (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: (List.replicate (y₁ + 1) CNFSym.endMark ++
              (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))))) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 2 * y₁ + 8 = (2 * c + y₁ + 6) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 6] x) h8
    _ = (flip bind Sstep)^[2 * c + y₁ + 5]
          (some (⟨some Label.moveCnt, St.mv Label.not₆ Op.auxEmit, stk inp T c (List.replicate (y₁ + 1) true ++ V) F []
            (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: (List.replicate (y₁ + 1) CNFSym.endMark ++
              (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))))) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + y₁ + 6 = (2 * c + y₁ + 5) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 5] x) h9
    _ = (flip bind Sstep)^[c + y₁ + 4]
          (some (⟨some Label.not₆, St.rsDone Label.not₆ Op.auxEmit, stk inp T 0 (List.replicate (y₁ + 1) true ++ V) F
            (List.replicate c ()) (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark ::
              (List.replicate (y₁ + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark ::
                (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)))))) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + y₁ + 5 = (c + y₁ + 4) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + y₁ + 4] x) h10
    _ = (flip bind Sstep)^[c + y₁ + 3]
          (some (⟨some Label.moveVal, St.mv Label.constMake Op.varPop, stk inp T 0 (List.replicate (y₁ + 1) true ++ V) F
            (List.replicate c ()) (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++
              (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: (List.replicate (y₁ + 1) CNFSym.endMark ++
                (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: (List.replicate c CNFSym.endMark ++
                  (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O))))))) U⟩ : (mach).Cfg)) := by
          rw [show c + y₁ + 4 = (c + y₁ + 3) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[c + y₁ + 3] x) h11
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.rsDone Label.constMake Op.varPop, stk inp T 0 V F
            (List.replicate c ()) (List.replicate (y₁ + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark ::
              (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark ::
                (List.replicate (y₁ + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark ::
                  (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)))))))) U⟩ : (mach).Cfg)) := by
          rw [show c + y₁ + 3 = (c + 1) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h12
    _ = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          (List.replicate (y₁ + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark ::
            (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark ::
              (List.replicate (y₁ + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark ::
                (List.replicate c CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)))))))) U⟩ : (mach).Cfg) := by
          rw [show c + 1 = 0 + (c + 1) by omega]
          rw [Function.iterate_add]
          simpa using h13
    _ = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          ((encCNF (notClauses c y₁)).reverse ++ O) U⟩ : (mach).Cfg) := by
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk]
            rw [encCNF_notClauses_reverse, encClause_pos_reverse, encClause_neg_reverse]
            simp [List.append_assoc, List.cons_append, List.replicate_succ]


end TM3CNF

end Turing

end Chapter34

end CLRS
