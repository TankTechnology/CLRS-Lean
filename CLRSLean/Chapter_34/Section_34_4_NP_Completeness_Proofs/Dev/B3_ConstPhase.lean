import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B3_ConstEmit

/-!
# Dev B3: the `const` phase and the root unit clause

Development split of `SatTo3CNFMachine`: `const_phase_true` / `const_phase_false` and the root unit clause `emitTrue` phase.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

/-- The `const` phase for a positive literal: emit the clause `[pos m]` onto
`o`, build the value variable `m` on `val`, restore the counter to `m + 1`,
and reach `reduce`.  (`m` is the auxiliary index, i.e. the counter at entry.) -/
lemma const_phase_true (m : Nat) (rest T : List FormulaSym) (V : List Bool) (F : List Frame)
    (O U : List CNFSym) :
    (flip bind Sstep)^[2 * m + 3]
        (some (⟨some Label.const, St.rd (FormulaSym.lit true), stk rest T m V F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, St.done, stk rest T (m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          ((encClause [Literal.pos m]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have hconst := const_true_step rest T m V F [] O U
  have hem := constEmit_phase m (St.rd (FormulaSym.lit true)) rest T V F []
      (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U
  have hmk := constMake_phase m (St.done) rest T 0 V F
      (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U
  calc
    (flip bind Sstep)^[2 * m + 3]
        (some (⟨some Label.const, St.rd (FormulaSym.lit true), stk rest T m V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] (Sstep
          (⟨some Label.const, St.rd (FormulaSym.lit true), stk rest T m V F [] O U⟩ : (mach).Cfg))) := by
          rw [show 2 * m + 3 = Nat.succ ((m + 1) + (m + 1)) by omega]
          rw [Function.iterate_succ_apply]
          rw [Function.iterate_add]
          rfl
    _ = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1]
          (some (⟨some Label.constEmit, St.rd (FormulaSym.lit true), stk rest T m V F []
            (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg))) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] x)) hconst
    _ = (flip bind Sstep)^[m + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F
            (List.replicate m () ++ [])
            (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] x) hem
    _ = (flip bind Sstep)^[m + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F (List.replicate m ())
            (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep)^[m + 1] x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> simp [stk, List.append_nil]
    _ = some (⟨some Label.reduce, St.done, stk rest T (0 + m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
          rw [hmk]
    _ = some (⟨some Label.reduce, St.done, stk rest T (m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          ((encClause [Literal.pos m]).reverse ++ O) U⟩ : (mach).Cfg) := by
          have hrev : (encClause [Literal.pos m]).reverse =
              List.replicate (m + 1) CNFSym.endMark ++ [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] := by
            simp [encClause, encLit, litSym, litIndex, List.reverse_replicate]
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk]
            rw [show CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O =
                [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] ++ O by rfl]
            rw [← List.append_assoc]
            rw [← hrev]

/-- The `const` phase for a negative literal: emit the clause `[neg m]` onto
`o`, build the value variable `m` on `val`, restore the counter to `m + 1`,
and reach `reduce`. -/
lemma const_phase_false (m : Nat) (rest T : List FormulaSym) (V : List Bool) (F : List Frame)
    (O U : List CNFSym) :
    (flip bind Sstep)^[2 * m + 4]
        (some (⟨some Label.const, St.rd (FormulaSym.lit false), stk rest T m V F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, St.done, stk rest T (m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          ((encClause [Literal.neg m]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := const_false_step rest T m V F [] O U
  have h2 := constFalse_step rest T m V F [] O U
  have hem := constEmit_phase m (St.rd (FormulaSym.lit false)) rest T V F []
      (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
  have hmk := constMake_phase m (St.done) rest T 0 V F
      (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  calc
    (flip bind Sstep)^[2 * m + 4]
        (some (⟨some Label.const, St.rd (FormulaSym.lit false), stk rest T m V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] ((flip bind Sstep) (Sstep
          (⟨some Label.const, St.rd (FormulaSym.lit false), stk rest T m V F [] O U⟩ : (mach).Cfg)))) := by
          rw [show 2 * m + 4 = Nat.succ (Nat.succ ((m + 1) + (m + 1))) by omega]
          rw [Function.iterate_succ_apply]
          rw [Function.iterate_succ_apply]
          rw [Function.iterate_add]
          rfl
    _ = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] ((flip bind Sstep)
          (some (⟨some Label.constFalse, St.rd (FormulaSym.lit false), stk rest T m V F [] O U⟩ : (mach).Cfg)))) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] ((flip bind Sstep) x))) h1
    _ = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1]
          (some (⟨some Label.constEmit, St.rd (FormulaSym.lit false), stk rest T m V F []
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg))) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] x)) h2
    _ = (flip bind Sstep)^[m + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F
            (List.replicate m () ++ [])
            (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] x) hem
    _ = (flip bind Sstep)^[m + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F (List.replicate m ())
            (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep)^[m + 1] x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> simp [stk, List.append_nil]
    _ = some (⟨some Label.reduce, St.done, stk rest T (0 + m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
          rw [hmk]
    _ = some (⟨some Label.reduce, St.done, stk rest T (m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          ((encClause [Literal.neg m]).reverse ++ O) U⟩ : (mach).Cfg) := by
          have hrev : (encClause [Literal.neg m]).reverse =
              List.replicate (m + 1) CNFSym.endMark ++ [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
            simp [encClause, encLit, litSym, litIndex, List.reverse_replicate]
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk]
            rw [show CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O =
                [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] ++ O by rfl]
            rw [← List.append_assoc]
            rw [← hrev]

-- ============================================================
-- emitTrue: the root unit clause `[[pos y]]`
-- ============================================================

/-- `emitTrue`: push the clause and literal markers, then pop the root
value-variable's `false` separator, entering the index-emission loop. -/
lemma emitTrue_push (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitTrue, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c V' F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `emitTrueRestore`: a `true` in the root value-variable's run emits one
`endMark` and continues. -/
lemma emitTrueRestore_true (v : St) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitTrueRestore, v, stk inp T c (true :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c V' F S (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `emitTrueRestore`: an empty `val` ends the run; the emission moves to
`copyOut`. -/
lemma emitTrueRestore_empty (v : St) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitTrueRestore, v, stk inp T c [] F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.copyOut, St.done, stk inp T c [] F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `emitTrueRestore` loop: popping `k` `true`s emits `k` `endMark`s and
finishes at `copyOut`. -/
lemma emitTrueRestore_loop (k : Nat) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c (List.replicate k true) F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.copyOut, St.done, stk inp T c [] F S (List.replicate k CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction k generalizing O with
  | zero =>
      have h := emitTrueRestore_empty St.emitTrue inp T c F S O U
      change (flip bind Sstep) (some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c [] F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.done, stk inp T c [] F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := emitTrueRestore_true St.emitTrue inp T c (List.replicate k true) F S O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c (true :: List.replicate k true) F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.done, stk inp T c [] F S (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[k + 1]
            (some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c (List.replicate k true) F S
              (CNFSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.copyOut, St.done, stk inp T c [] F S
              (List.replicate k CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.copyOut, St.done, stk inp T c [] F S
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

/-- `emitTrue` phase: the root value variable `y` (stored as `y + 1` `true`s
below a `false` separator) is emitted as the unit clause `[[pos y]]`, leaving
the encoded clause (reversed) on `o`. -/
lemma emitTrue_phase (y : Nat) (v : St) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[(y + 1) + 2]
        (some (⟨some Label.emitTrue, v, stk inp T c (false :: List.replicate (y + 1) true) F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.copyOut, St.done, stk inp T c [] F S ((encCNF [[Literal.pos y]]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have hpush := emitTrue_push v inp T c false (List.replicate (y + 1) true) F S O U
  rw [show (y + 1) + 2 = ((y + 1) + 1) + 1 by omega]
  rw [Function.iterate_succ_apply]
  change (flip bind Sstep)^[(y + 1) + 1]
      (Sstep (⟨some Label.emitTrue, v, stk inp T c (false :: List.replicate (y + 1) true) F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.copyOut, St.done, stk inp T c [] F S ((encCNF [[Literal.pos y]]).reverse ++ O) U⟩ : (mach).Cfg)
  rw [hpush]
  have hloop := emitTrueRestore_loop (y + 1) inp T c F S
      (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U
  calc
    (flip bind Sstep)^[(y + 1) + 1]
        (some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c (List.replicate (y + 1) true) F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg))
      = some (⟨some Label.copyOut, St.done, stk inp T c [] F S
          (List.replicate (y + 1) CNFSym.endMark ++
            (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := hloop
    _ = some (⟨some Label.copyOut, St.done, stk inp T c [] F S
        ((encCNF [[Literal.pos y]]).reverse ++ O) U⟩ : (mach).Cfg) := by
        apply congrArg some
        apply Turing.TM2Comp.Cfg_ext
        · rfl
        · rfl
        · funext kk
          cases kk <;> try simp [stk]
          rw [show CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O =
              [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] ++ O by rfl]
          have hrev : (encCNF [[Literal.pos y]]).reverse =
              List.replicate (y + 1) CNFSym.endMark ++
                [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] := by
            simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
          rw [hrev]
          rw [List.append_assoc]

end TM3CNF

end Turing

end Chapter34

end CLRS
