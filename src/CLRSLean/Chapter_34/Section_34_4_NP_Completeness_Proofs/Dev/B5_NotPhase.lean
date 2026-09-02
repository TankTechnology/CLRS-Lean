import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B5_NotEmit

/-!
# Dev B5: the `not` phase run lemma

Development split of `SatTo3CNFMachine`: `not_phase`, the full run lemma for the `not` clause emission.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

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
