import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B10_ParsePhase

/-!
# Dev B11: `copyOut`, transfer `o` to `out` and halt

The `copyOut` phase that transfers the output tape `o` back to `out` (reversing it) and the halting `done_step`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- copyOut: transfer `o` to `out` (reversing it back), then halt
-- ============================================================

/-- `copyOut` pops one symbol from `o` and pushes it onto `out`. -/
lemma copyOut_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (s : CNFSym) (O U : List CNFSym) :
    Sstep (⟨some Label.copyOut, v, stk inp T c V F S (s :: O) U⟩ : (mach).Cfg)
      = some (⟨some Label.copyOut, St.copySym s, stk inp T c V F S O (s :: U)⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `copyOut` with `o` empty goes to `clearIn`, resetting the state to `init`. -/
lemma copyOut_done (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (U : List CNFSym) :
    Sstep (⟨some Label.copyOut, v, stk inp T c V F S [] U⟩ : (mach).Cfg)
      = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `copyOut` phase: transfer `o` to `out` (reversing it back), then reach
`clearIn` with the state reset to `init`. -/
lemma copyOut_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[O.length + 1]
      (some (⟨some Label.copyOut, v, stk inp T c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] (O.reverse ++ U)⟩ : (mach).Cfg) := by
  induction O generalizing v U with
  | nil =>
      have h := copyOut_done v inp T c V F S U
      change (flip bind Sstep) (some (⟨some Label.copyOut, v, stk inp T c V F S [] U⟩ : (mach).Cfg))
        = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] U⟩ : (mach).Cfg)
      simpa [flip] using h
  | cons s rest ih =>
      have h := copyOut_step v inp T c V F S s rest U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.copyOut, v, stk inp T c V F S (s :: rest) U⟩ : (mach).Cfg))
        = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] ((s :: rest).reverse ++ U)⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (St.copySym s) (s :: U)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.copyOut, St.copySym s, stk inp T c V F S rest (s :: U)⟩ : (mach).Cfg))
          = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] (rest.reverse ++ (s :: U))⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] ((s :: rest).reverse ++ U)⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.append_assoc]

/-- The `done` label halts, leaving the state at `init`. -/
lemma done_step (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (U : List CNFSym) :
    Sstep (⟨some Label.done, St.init, stk inp T c V F S [] U⟩ : (mach).Cfg)
      = some (⟨none, St.init, stk inp T c V F S [] U⟩ : (mach).Cfg) := by
  simp [Sstep, prog]

/-- `clearIn` pops one junk symbol from `in` and discards it.  The pre-state is
irrelevant (the `clearIn` pop overwrites it). -/
lemma clearIn_step (v : St) (s : FormulaSym) (inp T : List FormulaSym) (c : Nat)
    (V : List Bool) (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.clearIn, v, stk (s :: inp) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.clearIn, St.rd s, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `clearIn` with `in` empty goes to `clearCnt`, setting the state to `done`.
The pre-state is irrelevant (the `clearIn` pop overwrites it). -/
lemma clearIn_done (v : St) (T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.clearIn, v, stk [] T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.clearCnt, St.done, stk [] T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `clearIn` phase: discard the junk left on `in`, then reach `clearCnt`. -/
lemma clearIn_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[inp.length + 1]
      (some (⟨some Label.clearIn, v, stk inp T c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.clearCnt, St.done, stk [] T c V F S O U⟩ : (mach).Cfg) := by
  induction inp generalizing v with
  | nil =>
      have h := clearIn_done v T c V F S O U
      change (flip bind Sstep) (some (⟨some Label.clearIn, v, stk [] T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.clearCnt, St.done, stk [] T c V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | cons s rest ih =>
      have h := clearIn_step v s rest T c V F S O U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.clearIn, v, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.clearCnt, St.done, stk [] T c V F S O U⟩ : (mach).Cfg)
      rw [h]
      exact ih (v := St.rd s)

/-- `clearCnt` pops one counter unit and discards it.  The pre-state is
irrelevant (the `clearCnt` pop overwrites it). -/
lemma clearCnt_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.clearCnt, v, stk inp T (c + 1) V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.clearCnt, St.done, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `clearCnt` with the counter empty goes to `done`, resetting the state to
`init`.  The pre-state is irrelevant (the `clearCnt` pop overwrites it). -/
lemma clearCnt_done (v : St) (inp T : List FormulaSym) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.clearCnt, v, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.done, St.init, stk inp T 0 V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `clearCnt` phase: discard the remaining counter units, then reach `done`
with the counter empty. -/
lemma clearCnt_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[c + 1]
      (some (⟨some Label.clearCnt, v, stk inp T c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.done, St.init, stk inp T 0 V F S O U⟩ : (mach).Cfg) := by
  induction c generalizing v with
  | zero =>
      have h := clearCnt_done v inp T V F S O U
      change (flip bind Sstep) (some (⟨some Label.clearCnt, v, stk inp T 0 V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ c ih =>
      have h := clearCnt_step v inp T c V F S O U
      rw [show Nat.succ c + 1 = (c + 1) + 1 by rfl]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[c + 1]
          (Sstep (⟨some Label.clearCnt, v, stk inp T (Nat.succ c) V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      rw [show Nat.succ c = c + 1 by rfl]
      rw [h]
      exact ih (v := St.done)


end TM3CNF

end Turing

end Chapter34

end CLRS
