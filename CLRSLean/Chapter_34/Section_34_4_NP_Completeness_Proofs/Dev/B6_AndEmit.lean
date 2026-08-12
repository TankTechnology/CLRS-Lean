import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B5_NotPhase

/-!
# Dev B6: the `and` clause emission

The `and` clause emission: `Formula.and f g` emits `andClauses c y₁ y₂`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- and clause emit: `Formula.and f g` emits `andClauses c y₁ y₂`
-- ============================================================

/-- `emitAnd`: enter the `parkVal` routine, parking the second child's value
variable (on top of `val`) while the first child is emitted first. -/
lemma emitAnd_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitAnd, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkVal, St.mv Label.and₂ Op.park, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₂`: push the first clause's header `[clauseMark, negMark, varMark]` for
the clause `(¬y₁ ∨ y)` and emit the auxiliary variable `y` from the counter. -/
lemma and₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₂, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.and₃ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₃`: close the first clause's auxiliary literal with `[endMark, posMark,
varMark]` and restore the counter. -/
lemma and₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₃, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.and₄ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₄`: pop the first child's `false` separator and emit its value run via
`moveVal` (`varEmit`). -/
lemma and₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₄, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.and₅ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₅`: push the second clause's header `[clauseMark, negMark, varMark]`
for `(¬y₂ ∨ y)` and restore the first child's run. -/
lemma and₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₅, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.and₆ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₆`: re-push the first child's `false` separator and emit the second
clause's auxiliary literal. -/
lemma and₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.and₇ Op.auxEmit, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₇`: close the second clause's auxiliary literal with `[endMark,
posMark, varMark]` and restore the counter. -/
lemma and₇_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₇, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.and₈ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₈`: restore the second child's run from `temp` via `unparkVal`. -/
lemma and₈_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₈, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs Label.and₉ Op.unpark, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₉`: pop the second child's `false` separator and emit its run via
`moveVal` (`varEmit`), completing the clause `(¬y₂ ∨ y)`. -/
lemma and₉_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₉, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.and₁₀ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₁₀`: push the third clause's header `[clauseMark, negMark, varMark]`
for `(¬y₁ ∨ ¬y₂ ∨ y)` and restore the second child's run. -/
lemma and₁₀_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₁₀, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.and₁₁ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₁₁`: re-push the second child's `false` separator and park it again so
the first child is on top of `val` for the third clause. -/
lemma and₁₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₁₁, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkVal, St.mv Label.and₁₂ Op.park, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₁₂`: pop the first child's `false` separator and emit its run via
`moveVal` (`varPop`, not restoring it). -/
lemma and₁₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₁₂, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.and₁₃ Op.varPop, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₁₃`: push the third clause's `[varMark, negMark]` for `¬y₁` and
restore the second child from `temp`. -/
lemma and₁₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₁₃, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs Label.and₁₄ Op.unpark, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₁₄`: pop the second child's `false` separator and emit its run via
`moveVal` (`varPop`). -/
lemma and₁₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₁₄, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.and₁₅ Op.varPop, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₁₅`: push the third clause's `[varMark, posMark]` for `y` and emit the
auxiliary variable from the counter. -/
lemma and₁₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₁₅, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.and₁₆ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `and₁₆`: push the final `endMark` of the third clause and enter
`constMake`, which allocates the auxiliary variable `y` on `val`. -/
lemma and₁₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.and₁₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constMake, St.done, stk inp T c V F S
          (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

end TM3CNF

end Turing

end Chapter34

end CLRS
