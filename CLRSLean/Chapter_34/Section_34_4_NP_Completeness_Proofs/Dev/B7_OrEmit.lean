import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B6_AndPhase

/-!
# Dev B7: the `or` clause emission

The `or` clause emission: `Formula.or f g` emits `orClauses c y₁ y₂`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- or clause emit: `Formula.or f g` emits `orClauses c y₁ y₂`
-- ============================================================

/-- `emitOr`: enter the `parkVal` routine, parking the second child's value
variable (on top of `val`) while the first child is emitted first. -/
lemma emitOr_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitOr, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkVal, St.mv Label.or₂ Op.park, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₂`: push the first clause's header `[clauseMark, posMark, varMark]` for
the clause `(y ∨ ¬y₁)` and emit the auxiliary variable `y` from the counter. -/
lemma or₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₂, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.or₃ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₃`: close the first clause's auxiliary literal with `[endMark, negMark,
varMark]` and restore the counter. -/
lemma or₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₃, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.or₄ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₄`: pop the first child's `false` separator and emit its value run via
`moveVal` (`varEmit`). -/
lemma or₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₄, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.or₅ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₅`: push the second clause's header `[clauseMark, posMark, varMark]`
for `(y ∨ ¬y₂)` and restore the first child's run. -/
lemma or₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₅, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.or₆ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₆`: re-push the first child's `false` separator and emit the second
clause's auxiliary literal. -/
lemma or₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.or₇ Op.auxEmit, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₇`: close the second clause's auxiliary literal with `[endMark,
negMark, varMark]` and restore the counter. -/
lemma or₇_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₇, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.or₈ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₈`: restore the second child's run from `temp` via `unparkVal`. -/
lemma or₈_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₈, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs Label.or₉ Op.unpark, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₉`: pop the second child's `false` separator and emit its run via
`moveVal` (`varEmit`), completing the clause `(y ∨ ¬y₂)`. -/
lemma or₉_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₉, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.or₁₀ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₁₀`: push the third clause's header `[clauseMark, posMark, varMark]`
for `(y₁ ∨ y₂ ∨ ¬y)` and restore the second child's run. -/
lemma or₁₀_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₁₀, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.or₁₁ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₁₁`: re-push the second child's `false` separator and park it again so
the first child is on top of `val` for the third clause. -/
lemma or₁₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₁₁, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkVal, St.mv Label.or₁₂ Op.park, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₁₂`: pop the first child's `false` separator and emit its run via
`moveVal` (`varPop`, not restoring it). -/
lemma or₁₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₁₂, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.or₁₃ Op.varPop, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₁₃`: push the third clause's `[varMark, posMark]` for `y₁` and restore
the second child from `temp`. -/
lemma or₁₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₁₃, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs Label.or₁₄ Op.unpark, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₁₄`: pop the second child's `false` separator and emit its run via
`moveVal` (`varPop`). -/
lemma or₁₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₁₄, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.or₁₅ Op.varPop, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₁₅`: push the third clause's `[varMark, negMark]` for `¬y` and emit the
auxiliary variable from the counter. -/
lemma or₁₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₁₅, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.or₁₆ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `or₁₆`: push the final `endMark` of the third clause and enter
`constMake`, which allocates the auxiliary variable `y` on `val`. -/
lemma or₁₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.or₁₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
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
