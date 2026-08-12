import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B8_IffPhase

/-!
# Dev B9: the junk `const false` phases

The junk `const false` phases that handle malformed or over-budget input.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- junk `const false` phases
--
-- On malformed input (end of input, a stray `endMark`, or a `varMark` with no
-- unary index run), `decode` yields `const false`.  The machine's junk path
-- emits `forceFalse c` (the `[¬c]` clause) and builds the value variable `c`,
-- matching `to3CNF' (const false) c` exactly.  All three paths take `2c + 5`
-- steps from `rd`.
-- ============================================================

/-- `pv0` reading an `endMark` pushes a `true` unit and enters `pv`.  The
pre-state is irrelevant. -/
lemma pv0_end_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.pv0, v, stk (FormulaSym.endMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (true :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `pv` loop: `i` `endMark`s become `i` `true` units on `val`.  The
pre-state is `St.rd endMark` (the state after `pv0` consumed its first
`endMark`), and the loop preserves it. -/
lemma pv_end_loop (i : Nat) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[i]
      (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk (List.replicate i FormulaSym.endMark ++ rest) T c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (List.replicate i true ++ V) F S O U⟩ : (mach).Cfg) := by
  induction i generalizing V with
  | zero =>
      rfl
  | succ i ih =>
      have h := pv_end_step (St.rd FormulaSym.endMark) (List.replicate i FormulaSym.endMark ++ rest) T c V F S O U
      rw [show (List.replicate (Nat.succ i) FormulaSym.endMark ++ rest) =
          FormulaSym.endMark :: (List.replicate i FormulaSym.endMark ++ rest) by
            rw [List.replicate_succ, List.cons_append]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[i]
          (Sstep (⟨some Label.pv, St.rd FormulaSym.endMark, stk (FormulaSym.endMark :: (List.replicate i FormulaSym.endMark ++ rest)) T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (List.replicate (Nat.succ i) true ++ V) F S O U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (V := true :: V)
      calc
        (flip bind Sstep)^[i]
            (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk (List.replicate i FormulaSym.endMark ++ rest) T c (true :: V) F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (List.replicate i true ++ (true :: V)) F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (List.replicate (Nat.succ i) true ++ V) F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> try simp [stk]
              · rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

/-- The junk `const false` phase for a stray `endMark` (or end of input): emit
`[¬c]`, build the value variable `c`, restore the counter to `c + 1`, and reach
`reduce`. -/
lemma junkEnd_phase (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[2 * c + 5]
      (some (⟨some Label.rd, v, stk (FormulaSym.endMark :: rest) T c V F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk rest T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := rd_end_step v rest T c V F [] O U
  have h2 : Sstep (⟨some Label.const, St.rd FormulaSym.endMark, stk rest T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.rd FormulaSym.endMark, stk rest T c V F [] O U⟩ : (mach).Cfg) := by
    exact const_to_constFalse_step (St.rd FormulaSym.endMark) (by simp) rest T c V F [] O U
  have h3 := constFalse_generic_step (St.rd FormulaSym.endMark) rest T c V F [] O U
  have h4 := constEmit_phase c (St.rd FormulaSym.endMark) rest T V F []
      (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
  have h5 := constMake_phase c (St.done) rest T 0 V F
      (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  calc
    (flip bind Sstep)^[2 * c + 5]
        (some (⟨some Label.rd, v, stk (FormulaSym.endMark :: rest) T c V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[2 * c + 4]
          (some (⟨some Label.const, St.rd FormulaSym.endMark, stk rest T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 5 = (2 * c + 4) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h1
    _ = (flip bind Sstep)^[2 * c + 3]
          (some (⟨some Label.constFalse, St.rd FormulaSym.endMark, stk rest T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h2
    _ = (flip bind Sstep)^[2 * c + 2]
          (some (⟨some Label.constEmit, St.rd FormulaSym.endMark, stk rest T c V F []
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 3 = (2 * c + 2) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2] x) h3
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F
            (List.replicate c () ++ [])
            (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 2 = (c + 1) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h4
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F (List.replicate c ())
            (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep)^[c + 1] x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> simp [stk, List.append_nil]
    _ = some (⟨some Label.reduce, St.done, stk rest T (0 + c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
          rw [h5]
    _ = some (⟨some Label.reduce, St.done, stk rest T (c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
          have hrev : (encCNF [[Literal.neg c]]).reverse =
              List.replicate (c + 1) CNFSym.endMark ++
                [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
            simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
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

/-- The junk `const false` phase for an empty input: emit `[¬c]`, build the
value variable `c`, restore the counter to `c + 1`, and reach `reduce`. -/
lemma junkEmpty_phase (v : St) (T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[2 * c + 5]
      (some (⟨some Label.rd, v, stk [] T c V F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk [] T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := rd_empty_step v T c V F [] O U
  have h2 : Sstep (⟨some Label.const, St.done, stk [] T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.done, stk [] T c V F [] O U⟩ : (mach).Cfg) := by
    exact const_to_constFalse_step St.done (by simp) [] T c V F [] O U
  have h3 := constFalse_generic_step St.done [] T c V F [] O U
  have h4 := constEmit_phase c St.done [] T V F []
      (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
  have h5 := constMake_phase c St.done [] T 0 V F
      (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  calc
    (flip bind Sstep)^[2 * c + 5]
        (some (⟨some Label.rd, v, stk [] T c V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[2 * c + 4]
          (some (⟨some Label.const, St.done, stk [] T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 5 = (2 * c + 4) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h1
    _ = (flip bind Sstep)^[2 * c + 3]
          (some (⟨some Label.constFalse, St.done, stk [] T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h2
    _ = (flip bind Sstep)^[2 * c + 2]
          (some (⟨some Label.constEmit, St.done, stk [] T c V F []
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 3 = (2 * c + 2) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2] x) h3
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.done, stk [] T 0 V F
            (List.replicate c () ++ [])
            (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 2 = (c + 1) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h4
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.done, stk [] T 0 V F (List.replicate c ())
            (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep)^[c + 1] x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> simp [stk, List.append_nil]
    _ = some (⟨some Label.reduce, St.done, stk [] T (0 + c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
          rw [h5]
    _ = some (⟨some Label.reduce, St.done, stk [] T (c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
          have hrev : (encCNF [[Literal.neg c]]).reverse =
              List.replicate (c + 1) CNFSym.endMark ++
                [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
            simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
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

/-- The junk `const false` phase for a `varMark` with no unary index run: emit
`[¬c]`, build the value variable `c`, restore the counter to `c + 1`, and reach
`reduce`. -/
lemma junkVar_phase (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) (hrest : rest.head? ≠ some FormulaSym.endMark) :
    (flip bind Sstep)^[2 * c + 5]
      (some (⟨some Label.rd, v, stk (FormulaSym.varMark :: rest) T c V F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk rest T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := rd_var_step v rest T c V F [] O U
  -- after `pv0` (which restores `rest`), the junk const machinery runs from
  -- `constFalse` with either the restored symbol's state or `St.reduce`.
  cases rest with
  | nil =>
      have h2 : Sstep (⟨some Label.pv0, St.rd FormulaSym.varMark, stk [] T c V F [] O U⟩ : (mach).Cfg)
          = some (⟨some Label.constFalse, St.reduce, stk [] T c V F [] O U⟩ : (mach).Cfg) := by
        exact pv0_empty_step (St.rd FormulaSym.varMark) T c V F [] O U
      have h3 := constFalse_generic_step St.reduce [] T c V F [] O U
      have h4 := constEmit_phase c St.reduce [] T V F []
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
      have h5 := constMake_phase c (St.done) [] T 0 V F
          (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
      calc
        (flip bind Sstep)^[2 * c + 5]
            (some (⟨some Label.rd, v, stk [FormulaSym.varMark] T c V F [] O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[2 * c + 4]
              (some (⟨some Label.pv0, St.rd FormulaSym.varMark, stk [] T c V F [] O U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 5 = (2 * c + 4) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h1
        _ = (flip bind Sstep)^[2 * c + 3]
              (some (⟨some Label.constFalse, St.reduce, stk [] T c V F [] O U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h2
        _ = (flip bind Sstep)^[2 * c + 2]
              (some (⟨some Label.constEmit, St.reduce, stk [] T c V F []
                (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 3 = (2 * c + 2) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2] x) h3
        _ = (flip bind Sstep)^[c + 1]
              (some (⟨some Label.constMake, St.done, stk [] T 0 V F
                (List.replicate c () ++ [])
                (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 2 = (c + 1) + (c + 1) by omega]
              rw [Function.iterate_add]
              exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h4
        _ = (flip bind Sstep)^[c + 1]
              (some (⟨some Label.constMake, St.done, stk [] T 0 V F (List.replicate c ())
                (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
              apply congrArg (fun x => (flip bind Sstep)^[c + 1] x)
              apply congrArg some
              apply Turing.TM2Comp.Cfg_ext
              · rfl
              · rfl
              · funext kk
                cases kk <;> simp [stk, List.append_nil]
        _ = some (⟨some Label.reduce, St.done, stk [] T (0 + c + 1)
              (false :: List.replicate (c + 1) true ++ V) F []
              (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
              rw [h5]
        _ = some (⟨some Label.reduce, St.done, stk [] T (c + 1)
              (false :: List.replicate (c + 1) true ++ V) F []
              ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
              have hrev : (encCNF [[Literal.neg c]]).reverse =
                  List.replicate (c + 1) CNFSym.endMark ++
                    [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
                simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
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
  | cons s rest' =>
      have hs : s ≠ FormulaSym.endMark := by
        intro hse
        apply hrest
        simp [hse]
      have h2 : Sstep (⟨some Label.pv0, St.rd FormulaSym.varMark, stk (s :: rest') T c V F [] O U⟩ : (mach).Cfg)
          = some (⟨some Label.constFalse, St.rd s, stk (s :: rest') T c V F [] O U⟩ : (mach).Cfg) := by
        exact pv0_junk_step (St.rd FormulaSym.varMark) s rest' T c V F [] O U hs
      have h3 := constFalse_generic_step (St.rd s) (s :: rest') T c V F [] O U
      have h4 := constEmit_phase c (St.rd s) (s :: rest') T V F []
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
      have h5 := constMake_phase c (St.done) (s :: rest') T 0 V F
          (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
      calc
        (flip bind Sstep)^[2 * c + 5]
            (some (⟨some Label.rd, v, stk (FormulaSym.varMark :: s :: rest') T c V F [] O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[2 * c + 4]
              (some (⟨some Label.pv0, St.rd FormulaSym.varMark, stk (s :: rest') T c V F [] O U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 5 = (2 * c + 4) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h1
        _ = (flip bind Sstep)^[2 * c + 3]
              (some (⟨some Label.constFalse, St.rd s, stk (s :: rest') T c V F [] O U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h2
        _ = (flip bind Sstep)^[2 * c + 2]
              (some (⟨some Label.constEmit, St.rd s, stk (s :: rest') T c V F []
                (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 3 = (2 * c + 2) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2] x) h3
        _ = (flip bind Sstep)^[c + 1]
              (some (⟨some Label.constMake, St.done, stk (s :: rest') T 0 V F
                (List.replicate c () ++ [])
                (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 2 = (c + 1) + (c + 1) by omega]
              rw [Function.iterate_add]
              exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h4
        _ = (flip bind Sstep)^[c + 1]
              (some (⟨some Label.constMake, St.done, stk (s :: rest') T 0 V F (List.replicate c ())
                (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
              apply congrArg (fun x => (flip bind Sstep)^[c + 1] x)
              apply congrArg some
              apply Turing.TM2Comp.Cfg_ext
              · rfl
              · rfl
              · funext kk
                cases kk <;> simp [stk, List.append_nil]
        _ = some (⟨some Label.reduce, St.done, stk (s :: rest') T (0 + c + 1)
              (false :: List.replicate (c + 1) true ++ V) F []
              (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
              rw [h5]
        _ = some (⟨some Label.reduce, St.done, stk (s :: rest') T (c + 1)
              (false :: List.replicate (c + 1) true ++ V) F []
              ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
              have hrev : (encCNF [[Literal.neg c]]).reverse =
                  List.replicate (c + 1) CNFSym.endMark ++
                    [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
                simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
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

/-- The variable phase: read `varEnc i`, push the value variable `i` onto `val`
(leaving the counter unchanged), and reach `reduce`. -/
lemma var_phase (i : Nat) (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) (hrest : rest.head? ≠ some FormulaSym.endMark) :
    ∃ v₁ : St, (flip bind Sstep)^[i + 3]
      (some (⟨some Label.rd, v, stk (varEnc i ++ rest) T c V F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, v₁, stk rest T c
          (false :: List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
  have h1 := rd_var_step v (List.replicate (i + 1) FormulaSym.endMark ++ rest) T c V F [] O U
  have h2 : Sstep (⟨some Label.pv0, St.rd FormulaSym.varMark, stk
      (List.replicate (i + 1) FormulaSym.endMark ++ rest) T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk
          (List.replicate i FormulaSym.endMark ++ rest) T c (true :: V) F [] O U⟩ : (mach).Cfg) := by
      have hrep : List.replicate (i + 1) FormulaSym.endMark =
          FormulaSym.endMark :: List.replicate i FormulaSym.endMark := by
        rw [show i + 1 = Nat.succ i by omega]
        simp [List.replicate_succ]
      rw [hrep, List.cons_append]
      exact pv0_end_step (St.rd FormulaSym.varMark) (List.replicate i FormulaSym.endMark ++ rest) T c V F [] O U
  have h3 := pv_end_loop i rest T c (true :: V) F [] O U
  have h4 : ∃ w : St, Sstep (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c
      (List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.reduce, w, stk rest T c
          (false :: List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
      cases rest with
      | nil => refine ⟨St.reduce, ?_⟩
               exact pv_empty_step (St.rd FormulaSym.endMark) T c (List.replicate (i + 1) true ++ V) F [] O U
      | cons s rest' =>
          have hs : s ≠ FormulaSym.endMark := by
            intro hse
            apply hrest
            simp [hse]
          refine ⟨St.rd s, ?_⟩
          exact pv_done_step (St.rd FormulaSym.endMark) s rest' T c (List.replicate (i + 1) true ++ V) F [] O U hs
  rcases h4 with ⟨w, h4⟩
  refine ⟨w, ?_⟩
  calc
    (flip bind Sstep)^[i + 3]
        (some (⟨some Label.rd, v, stk (varEnc i ++ rest) T c V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[i + 2]
          (some (⟨some Label.pv0, St.rd FormulaSym.varMark, stk
            (List.replicate (i + 1) FormulaSym.endMark ++ rest) T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show i + 3 = (i + 2) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[i + 2] x) h1
    _ = (flip bind Sstep)^[i + 1]
          (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk
            (List.replicate i FormulaSym.endMark ++ rest) T c (true :: V) F [] O U⟩ : (mach).Cfg)) := by
          rw [show i + 2 = (i + 1) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[i + 1] x) h2
    _ = (flip bind Sstep)
          (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c
            (List.replicate i true ++ (true :: V)) F [] O U⟩ : (mach).Cfg)) := by
          rw [Function.iterate_succ_apply']
          exact congrArg (fun x => (flip bind Sstep) x) h3
    _ = (flip bind Sstep)
          (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c
            (List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep) x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk]
            rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
            rw [← List.append_assoc]
            rw [replicate_append_one]
    _ = some (⟨some Label.reduce, w, stk rest T c
          (false :: List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
          exact h4


end TM3CNF

end Turing

end Chapter34

end CLRS
