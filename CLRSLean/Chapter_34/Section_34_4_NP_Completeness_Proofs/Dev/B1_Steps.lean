import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B1_Prog

/-!
# Dev B1: the step relation and the count/reorder step lemmas

Development split of `SatTo3CNFMachine`: the machine `mach`, its step
relation `Sstep`, and the single-step lemmas for the `count`, `reorder`, and
`rd`/`pv` subroutines.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

abbrev mach : Turing.FinTM2 :=
  @Turing.FinTM2.mk K (by infer_instance) (by infer_instance) K.inK K.out Γk Label Label.count
    (by infer_instance) St St.init (by infer_instance) (by infer_instance) prog

def Sstep : (mach).Cfg → Option (mach).Cfg := mach.step

/-- one count step on a nonempty `in` -/
lemma count_step (s : FormulaSym) (rest : List FormulaSym) (T : List FormulaSym)
    (c : Nat) (V : List Bool) (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.count, St.rd s, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.count, St.rd s, stk rest (s :: T) (c + 1) V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ, Nat.add_comm, Nat.add_assoc]

/-- count phase: move all symbols from `in` to `temp` (reversed), counting into `cnt` -/
lemma count_phase_aux (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[inp.length + 1]
        (some (⟨some Label.count, St.rd default, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.reorder, St.done, stk [] (inp.reverse ++ T) (c + inp.length) V F S O U⟩ : (mach).Cfg) := by
  induction inp generalizing T c with
  | nil =>
      simp [stk, Sstep, prog, flip]
  | cons s rest ih =>
      have hone := count_step s rest T c V F S O U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.count, St.rd s, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.reorder, St.done, stk [] ((s :: rest).reverse ++ T) (c + (s :: rest).length) V F S O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (T := s :: T) (c := c + 1)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.count, St.rd default, stk rest (s :: T) (c + 1) V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.reorder, St.done, stk [] (rest.reverse ++ (s :: T)) ((c + 1) + rest.length) V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reorder, St.done, stk [] ((s :: rest).reverse ++ T) (c + (s :: rest).length) V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, List.length_cons, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- reorder phase: move all symbols from `temp` back to `in` (restoring the order),
routing to the parser (`rd`) with the input restored -/
lemma reorder_phase_aux (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[T.length + 1]
        (some (⟨some Label.reorder, St.rd default, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.rd, St.done, stk (T.reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
  induction T generalizing inp with
  | nil =>
      simp [stk, Sstep, prog, flip]
  | cons s rest ih =>
      have hone : Sstep (⟨some Label.reorder, St.rd s, stk inp (s :: rest) c V F S O U⟩ : (mach).Cfg)
          = some (⟨some Label.reorder, St.rd s, stk (s :: inp) rest c V F S O U⟩ : (mach).Cfg) := by
        apply congrArg some
        apply Turing.TM2Comp.Cfg_ext
        · rfl
        · rfl
        · funext k
          cases k <;> simp [stk, Function.update, prog, Sstep]
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.reorder, St.rd s, stk inp (s :: rest) c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.rd, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (inp := s :: inp)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.reorder, St.rd default, stk (s :: inp) rest c V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.rd, St.done, stk (rest.reverse ++ (s :: inp)) [] c V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.rd, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- Reading a `notMark` pushes a `not` continuation frame.  The pre-state is
irrelevant (the `rd` pop overwrites it). -/
lemma rd_not_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk (FormulaSym.notMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.rd FormulaSym.notMark, stk rest T c V (Frame.not :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading an `andMark` pushes an `and₁` continuation frame.  The pre-state is
irrelevant (the `rd` pop overwrites it). -/
lemma rd_and_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk (FormulaSym.andMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.rd FormulaSym.andMark, stk rest T c V (Frame.and₁ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading an `orMark` pushes an `or₁` continuation frame.  The pre-state is
irrelevant (the `rd` pop overwrites it). -/
lemma rd_or_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk (FormulaSym.orMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.rd FormulaSym.orMark, stk rest T c V (Frame.or₁ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading an `iffMark` pushes an `iff₁` continuation frame.  The pre-state is
irrelevant (the `rd` pop overwrites it). -/
lemma rd_iff_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk (FormulaSym.iffMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.rd FormulaSym.iffMark, stk rest T c V (Frame.iff₁ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading a `varMark` enters the variable-index phase.  The pre-state is
irrelevant (the `rd` pop overwrites it). -/
lemma rd_var_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk (FormulaSym.varMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.pv0, St.rd FormulaSym.varMark, stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading an `endMark` in the variable phase transfers it to `val` as a unit.
The pre-state is irrelevant (the `pv` pop overwrites it). -/
lemma pv_end_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.pv, v, stk (FormulaSym.endMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (true :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- A non-`endMark` ends the variable phase: push a `false` separator, restore
the symbol to the input, and reduce.  The pre-state is irrelevant (the `pv` pop
overwrites it). -/
lemma pv_done_step (v : St) (s : FormulaSym) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hs : s ≠ FormulaSym.endMark) :
    Sstep (⟨some Label.pv, v, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.reduce, St.rd s, stk (s :: rest) T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep, hs]
  · simp [stk, prog, Sstep, hs]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, hs]

/-- `rd` with an empty input routes to `const` (the junk `const false` path).
The pre-state is irrelevant. -/
lemma rd_empty_step (v : St) (T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk [] T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.const, St.done, stk [] T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `rd` reading an `endMark` routes to `const` (the junk `const false` path).
The pre-state is irrelevant. -/
lemma rd_end_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk (FormulaSym.endMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.const, St.rd FormulaSym.endMark, stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `pv` with an empty input finishes the variable with a `false` separator and
reduces (the junk `const false` path).  The pre-state is irrelevant. -/
lemma pv_empty_step (v : St) (T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.pv, v, stk [] T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.reduce, St.reduce, stk [] T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

end TM3CNF

end Turing

end Chapter34

end CLRS
