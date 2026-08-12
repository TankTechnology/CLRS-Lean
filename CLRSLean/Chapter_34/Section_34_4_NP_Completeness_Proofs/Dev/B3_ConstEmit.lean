import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B2_Reduce

/-!
# Dev B3: the `const` clause and `emitTrue` phases

The `const`-clause emission (`Formula.const b` becomes `[pos/neg m]`) and the root unit clause `emitTrue` phase.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- const clause emit: `Formula.const b` becomes `[pos/neg m]`
-- ============================================================

/-- Reading a literal (`lit b`) enters the constant-clause phase. -/
lemma rd_lit_step (v : St) (b : Bool) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk (FormulaSym.lit b :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.const, St.rd (FormulaSym.lit b), stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `const`: a positive literal emits the `clauseMark posMark varMark` header
and enters the index-emission loop. -/
lemma const_true_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.const, St.rd (FormulaSym.lit true), stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constEmit, St.rd (FormulaSym.lit true), stk rest T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `const`: a negative literal routes through `constFalse`. -/
lemma const_false_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.const, St.rd (FormulaSym.lit false), stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.rd (FormulaSym.lit false), stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `constFalse`: a negative literal emits the `clauseMark negMark varMark`
header and enters the index-emission loop. -/
lemma constFalse_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.constFalse, St.rd (FormulaSym.lit false), stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constEmit, St.rd (FormulaSym.lit false), stk rest T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `const` with a non-positive-literal state routes through `constFalse` (the
junk `const false` path).  The pre-state is preserved. -/
lemma const_to_constFalse_step (v : St) (hv : v ≠ St.rd (FormulaSym.lit true))
    (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.const, v, stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, v, stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep, hv]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, hv]

/-- `constFalse` emits the `clauseMark negMark varMark` header from any
pre-state (the junk `const false` path).  The pre-state is preserved. -/
lemma constFalse_generic_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.constFalse, v, stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constEmit, v, stk rest T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `pv0` on a non-`endMark` symbol routes to `constFalse`, restoring the symbol
(the junk `const false` path).  The pre-state is irrelevant. -/
lemma pv0_junk_step (v : St) (s : FormulaSym) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hs : s ≠ FormulaSym.endMark) :
    Sstep (⟨some Label.pv0, v, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.rd s, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep, hs]
  · simp [stk, prog, Sstep, hs]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, hs]

/-- `pv0` on an empty input routes to `constFalse` (the junk `const false`
path).  The pre-state is irrelevant. -/
lemma pv0_empty_step (v : St) (T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.pv0, v, stk [] T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.reduce, stk [] T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `constEmit`: a counter unit emits one `endMark` (extending the unary index
run) and one scratch marker, looping back to `constEmit`. -/
lemma constEmit_loop_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.constEmit, v, stk inp T (c + 1) V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constEmit, St.constLoop, stk inp T c V F
          (() :: S) (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `constEmit`: an exhausted counter ends the index run with one final
`endMark` and moves to `constMake`. -/
lemma constEmit_final_step (v : St) (inp T : List FormulaSym) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.constEmit, v, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constMake, St.done, stk inp T 0 V F S (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `replicate k a ++ [a]` is the `k + 1`-fold repetition. -/
lemma replicate_append_one {α : Type} (k : Nat) (a : α) :
    List.replicate k a ++ [a] = List.replicate (k + 1) a := by
  induction k with
  | zero => simp
  | succ k ih =>
      simpa [List.replicate_succ, List.cons_append] using ih

/-- The `constEmit` loop: `m` counter units emit `m` `endMark`s (plus one
final) and `m` scratch markers, ending at `constMake` with the counter
exhausted. -/
lemma constEmit_phase (m : Nat) (v : St) (inp T : List FormulaSym) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[m + 1]
        (some (⟨some Label.constEmit, v, stk inp T m V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.constMake, St.done, stk inp T 0 V F (List.replicate m () ++ S)
          (List.replicate (m + 1) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction m generalizing S O v with
  | zero =>
      have h := constEmit_final_step v inp T V F S O U
      change (flip bind Sstep) (some (⟨some Label.constEmit, v, stk inp T 0 V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.constMake, St.done, stk inp T 0 V F
            (List.replicate 0 () ++ S) (List.replicate 1 CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip, List.replicate_one] using h
  | succ m ih =>
      have h := constEmit_loop_step v inp T m V F S O U
      rw [show Nat.succ m + 1 = m + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[m + 1]
          (Sstep (⟨some Label.constEmit, v, stk inp T (Nat.succ m) V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.constMake, St.done, stk inp T 0 V F
            (List.replicate (Nat.succ m) () ++ S) (List.replicate (Nat.succ m + 1) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (v := St.constLoop) (S := () :: S) (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[m + 1]
            (some (⟨some Label.constEmit, St.constLoop, stk inp T m V F (() :: S)
              (CNFSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.constMake, St.done, stk inp T 0 V F
              (List.replicate m () ++ (() :: S))
              (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.constMake, St.done, stk inp T 0 V F
            (List.replicate (Nat.succ m) () ++ S) (List.replicate (Nat.succ m + 1) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
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

/-- `constMake`: a scratch marker rebuilds one `true` in the value variable's
run and one counter unit, looping back to `constMake`. -/
lemma constMake_loop_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (d : Nat) (O U : List CNFSym) :
    Sstep (⟨some Label.constMake, v, stk inp T c V F (() :: List.replicate d ()) O U⟩ : (mach).Cfg)
      = some (⟨some Label.constMake, St.constLoop, stk inp T (c + 1) (true :: V) F
          (List.replicate d ()) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `constMake`: an empty scratch stack finishes the value variable with a final
`true` (and counter unit) and a `false` separator, moving to `reduce`. -/
lemma constMake_final_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    Sstep (⟨some Label.constMake, v, stk inp T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
          (false :: true :: V) F [] O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- The `constMake` loop: `m` scratch markers build the `false :: replicate (m+1) true`
value variable for index `m`, restore `m + 1` counter units, and reach `reduce`. -/
lemma constMake_phase (m : Nat) (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[m + 1]
        (some (⟨some Label.constMake, v, stk inp T c V F (List.replicate m ()) O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, St.done, stk inp T (c + m + 1)
          (false :: List.replicate (m + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
  induction m generalizing c V v with
  | zero =>
      have h := constMake_final_step v inp T c V F O U
      change (flip bind Sstep) (some (⟨some Label.constMake, v, stk inp T c V F [] O U⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, St.done, stk inp T (c + 0 + 1)
            (false :: List.replicate 1 true ++ V) F [] O U⟩ : (mach).Cfg)
      simpa [flip, List.replicate_one] using h
  | succ m ih =>
      have h := constMake_loop_step v inp T c V F m O U
      rw [show Nat.succ m + 1 = m + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[m + 1]
          (Sstep (⟨some Label.constMake, v, stk inp T c V F (() :: List.replicate m ()) O U⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, St.done, stk inp T (c + Nat.succ m + 1)
            (false :: List.replicate (Nat.succ m + 1) true ++ V) F [] O U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (v := St.constLoop) (c := c + 1) (V := true :: V)
      calc
        (flip bind Sstep)^[m + 1]
            (some (⟨some Label.constMake, St.constLoop, stk inp T (c + 1) (true :: V) F
              (List.replicate m ()) O U⟩ : (mach).Cfg))
          = some (⟨some Label.reduce, St.done, stk inp T ((c + 1) + m + 1)
              (false :: List.replicate (m + 1) true ++ (true :: V)) F [] O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reduce, St.done, stk inp T (c + Nat.succ m + 1)
            (false :: List.replicate (Nat.succ m + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              · rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

end TM3CNF

end Turing

end Chapter34

end CLRS
