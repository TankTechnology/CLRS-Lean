import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B7_OrEmit

/-!
# Dev B8: the `iff` clause emission

The `iff` clause emission: `Formula.iff f g` emits `iffClauses c y₁ y₂`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- iff clause emit: `Formula.iff f g` emits `iffClauses c y₁ y₂`
-- ============================================================

/-- `emitIff`: enter the `parkVal` routine, parking the second child's value
(on top of `val`) while the first child is emitted first. -/
lemma emitIff_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitIff, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkVal, St.mv Label.iff₂ Op.park, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂`: push the first clause's header `[clauseMark, negMark, varMark]` for
the clause `(¬y ∨ ¬y₁ ∨ y₂)` and emit the auxiliary variable `y` from the
counter. -/
lemma iff₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.iff₃ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₃`: close the first clause's auxiliary literal `¬y` with a final
`endMark` and start the literal `¬y₁`, restoring the counter. -/
lemma iff₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₃, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.iff₄ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₄`: pop the first child's `false` separator and emit its value run via
`moveVal` (`varEmit`), completing `¬y₁`. -/
lemma iff₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₄, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.iff₅ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₅`: start the first clause's third literal `y₂` with `[posMark,
varMark]` and restore the first child's run. -/
lemma iff₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₅, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.iff₆ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₆`: re-push the first child's `false` separator and restore the second
child's run from `temp` via `unparkVal`. -/
lemma iff₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs Label.iff₇ Op.unpark, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₇`: pop the second child's `false` separator and emit its run via
`moveVal` (`varEmit`), completing the clause `(¬y ∨ ¬y₁ ∨ y₂)`. -/
lemma iff₇_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₇, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.iff₈ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₈`: push the second clause's header `[clauseMark, negMark, varMark]`
for `(¬y ∨ y₁ ∨ ¬y₂)` and restore the second child's run. -/
lemma iff₈_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₈, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.iff₉ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₉`: emit the second clause's auxiliary literal `¬y` from the counter. -/
lemma iff₉_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₉, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.iff₁₀ Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₀`: close the second clause's auxiliary literal `¬y` and start the
literal `y₁`, restoring the counter. -/
lemma iff₁₀_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₀, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.iff₁₁ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₁`: re-form the second child's run on `val` (with its `false`
separator) and park it on `temp` again. -/
lemma iff₁₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₁, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkVal, St.mv Label.iff₁₂ Op.park, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₂`: pop the first child's `false` separator and emit its value run,
completing `y₁`. -/
lemma iff₁₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₂, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.iff₁₃ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₃`: start the second clause's third literal `¬y₂` with `[negMark,
varMark]` and restore the first child's run. -/
lemma iff₁₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₃, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.iff₁₄ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₄`: re-push the first child's `false` separator and restore the second
child's run from `temp`. -/
lemma iff₁₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₄, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs Label.iff₁₅ Op.unpark, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₅`: pop the second child's `false` separator and emit its run,
completing the clause `(¬y ∨ y₁ ∨ ¬y₂)`. -/
lemma iff₁₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₅, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.iff₁₆ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₆`: push the third clause's header `[clauseMark, posMark, varMark]`
for `(y ∨ y₁ ∨ y₂)` and restore the second child's run. -/
lemma iff₁₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.iff₁₇ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₇`: emit the third clause's auxiliary literal `y` from the counter. -/
lemma iff₁₇_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₇, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.iff₁₈ Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₈`: close the third clause's auxiliary literal `y` and start the
literal `y₁`, restoring the counter. -/
lemma iff₁₈_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₈, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.iff₁₉ Op.auxEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₁₉`: re-form the second child's run on `val` and park it on `temp`
again. -/
lemma iff₁₉_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₁₉, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkVal, St.mv Label.iff₂₀ Op.park, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₀`: pop the first child's `false` separator and emit its value run,
completing `y₁`. -/
lemma iff₂₀_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₀, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.iff₂₁ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₁`: start the third clause's third literal `y₂` with `[posMark,
varMark]` and restore the first child's run. -/
lemma iff₂₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₁, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.iff₂₂ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₂`: re-push the first child's `false` separator and restore the second
child's run from `temp`. -/
lemma iff₂₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₂, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs Label.iff₂₃ Op.unpark, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₃`: pop the second child's `false` separator and emit its run,
completing the clause `(y ∨ y₁ ∨ y₂)`. -/
lemma iff₂₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₃, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.iff₂₄ Op.varEmit, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₄`: push the fourth clause's header `[clauseMark, posMark, varMark]`
for `(y ∨ ¬y₁ ∨ ¬y₂)` and restore the second child's run. -/
lemma iff₂₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₄, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.iff₂₅ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₅`: emit the fourth clause's auxiliary literal `y` from the counter. -/
lemma iff₂₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₅, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.iff₂₆ Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₆`: close the fourth clause's auxiliary literal `y`, start the literal
`¬y₁`, and re-form the second child's run on `val` before parking it. -/
lemma iff₂₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkVal, St.mv Label.iff₂₇ Op.park, stk inp T c (false :: V) F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₇`: pop the first child's `false` separator and emit its value run via
`moveVal` (`varPop`), consuming it for the last time. -/
lemma iff₂₇_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₇, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.iff₂₈ Op.varPop, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₈`: start the fourth clause's third literal `¬y₂` with `[negMark,
varMark]` and restore the second child's run from `temp`. -/
lemma iff₂₈_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₈, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs Label.iff₂₉ Op.unpark, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₂₉`: pop the second child's `false` separator and emit its run via
`moveVal` (`varPop`), consuming it for the last time. -/
lemma iff₂₉_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₂₉, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.iff₃₀ Op.varPop, stk inp T c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `iff₃₀`: route to `constMake` with the state reset to `done`, allocating
the auxiliary variable `y = c`. -/
lemma iff₃₀_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.iff₃₀, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constMake, St.done, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `emitIff` phase: with the two children's value runs on top of `val`
(the second child's above the first's), emit `iffClauses c y₁ y₂` and allocate
the auxiliary variable `y = c` via `constMake`.  The second child is parked on
`temp` while the first is emitted, then restored; each child is consumed twice
(once per emitted clause mentioning it, first via `varEmit` and finally via
`varPop`), and both children are left consumed beneath the new auxiliary run. -/
lemma emitIff_phase (inp T : List FormulaSym) (c : Nat) (y₁ y₂ : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[8 * c + 7 * y₁ + 15 * y₂ + 86]
      (some (⟨some Label.emitIff, St.emitIff, stk inp T c
        (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF (iffClauses c y₁ y₂)).reverse ++ O) U⟩ : (mach).Cfg) := by
  let Tp : List FormulaSym := List.replicate (y₂ + 1) (FormulaSym.lit true) ++ ([FormulaSym.lit false] ++ T)
  let V0 : List Bool := false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)
  let V1 : List Bool := false :: List.replicate (y₁ + 1) true ++ V
  let V1t : List Bool := List.replicate (y₁ + 1) true ++ V
  let V37 : List Bool := false :: List.replicate (c + 1) true ++ V
  let O1 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O
  let O2 : List CNFSym := List.replicate c CNFSym.endMark ++ O1
  let O3 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O2
  let O4 : List CNFSym := List.replicate (y₁ + 1) CNFSym.endMark ++ O3
  let O5 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: O4
  let O6 : List CNFSym := List.replicate (y₂ + 1) CNFSym.endMark ++ O5
  let O7 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O6
  let O8 : List CNFSym := List.replicate c CNFSym.endMark ++ O7
  let O9 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O8
  let O10 : List CNFSym := List.replicate (y₁ + 1) CNFSym.endMark ++ O9
  let O11 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: O10
  let O12 : List CNFSym := List.replicate (y₂ + 1) CNFSym.endMark ++ O11
  let O13 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O12
  let O14 : List CNFSym := List.replicate c CNFSym.endMark ++ O13
  let O15 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O14
  let O16 : List CNFSym := List.replicate (y₁ + 1) CNFSym.endMark ++ O15
  let O17 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: O16
  let O18 : List CNFSym := List.replicate (y₂ + 1) CNFSym.endMark ++ O17
  let O19 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O18
  let O20 : List CNFSym := List.replicate c CNFSym.endMark ++ O19
  let O21 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O20
  let O22 : List CNFSym := List.replicate (y₁ + 1) CNFSym.endMark ++ O21
  let O23 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: O22
  let O24 : List CNFSym := List.replicate (y₂ + 1) CNFSym.endMark ++ O23
  let c0 : (mach).Cfg := ⟨some Label.emitIff, St.emitIff, stk inp T c V0 F [] O U⟩
  let c1 : (mach).Cfg := ⟨some Label.parkVal, St.mv Label.iff₂ Op.park, stk inp T c V0 F [] O U⟩
  let c2 : (mach).Cfg := ⟨some Label.iff₂, St.rsDone Label.iff₂ Op.park, stk inp Tp c V1 F [] O U⟩
  let c3 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.iff₃ Op.auxEmit, stk inp Tp c V1 F [] O1 U⟩
  let c4 : (mach).Cfg := ⟨some Label.iff₃, St.rsDone Label.iff₃ Op.auxEmit, stk inp Tp 0 V1 F (List.replicate c ()) O2 U⟩
  let c5 : (mach).Cfg := ⟨some Label.restoreCnt, St.rs Label.iff₄ Op.auxEmit, stk inp Tp 0 V1 F (List.replicate c ()) O3 U⟩
  let c6 : (mach).Cfg := ⟨some Label.iff₄, St.rsDone Label.iff₄ Op.auxEmit, stk inp Tp c V1 F [] O3 U⟩
  let c7 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.iff₅ Op.varEmit, stk inp Tp c V1t F [] O3 U⟩
  let c8 : (mach).Cfg := ⟨some Label.iff₅, St.rsDone Label.iff₅ Op.varEmit, stk inp Tp c V F (List.replicate (y₁ + 1) ()) O4 U⟩
  let c9 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.iff₆ Op.varEmit, stk inp Tp c V F (List.replicate (y₁ + 1) ()) O5 U⟩
  let c10 : (mach).Cfg := ⟨some Label.iff₆, St.rsDone Label.iff₆ Op.varEmit, stk inp Tp c V1t F [] O5 U⟩
  let c11 : (mach).Cfg := ⟨some Label.unparkVal, St.rs Label.iff₇ Op.unpark, stk inp Tp c V1 F [] O5 U⟩
  let c12 : (mach).Cfg := ⟨some Label.iff₇, St.rsDone Label.iff₇ Op.unpark, stk inp T c V0 F [] O5 U⟩
  let c13 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.iff₈ Op.varEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O5 U⟩
  let c14 : (mach).Cfg := ⟨some Label.iff₈, St.rsDone Label.iff₈ Op.varEmit, stk inp T c V1 F
      (List.replicate (y₂ + 1) ()) O6 U⟩
  let c15 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.iff₉ Op.varEmit, stk inp T c V1 F
      (List.replicate (y₂ + 1) ()) O7 U⟩
  let c16 : (mach).Cfg := ⟨some Label.iff₉, St.rsDone Label.iff₉ Op.varEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O7 U⟩
  let c17 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.iff₁₀ Op.auxEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O7 U⟩
  let c18 : (mach).Cfg := ⟨some Label.iff₁₀, St.rsDone Label.iff₁₀ Op.auxEmit, stk inp T 0
      (List.replicate (y₂ + 1) true ++ V1) F (List.replicate c ()) O8 U⟩
  let c19 : (mach).Cfg := ⟨some Label.restoreCnt, St.rs Label.iff₁₁ Op.auxEmit, stk inp T 0
      (List.replicate (y₂ + 1) true ++ V1) F (List.replicate c ()) O9 U⟩
  let c20 : (mach).Cfg := ⟨some Label.iff₁₁, St.rsDone Label.iff₁₁ Op.auxEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O9 U⟩
  let c21 : (mach).Cfg := ⟨some Label.parkVal, St.mv Label.iff₁₂ Op.park, stk inp T c V0 F [] O9 U⟩
  let c22 : (mach).Cfg := ⟨some Label.iff₁₂, St.rsDone Label.iff₁₂ Op.park, stk inp Tp c V1 F [] O9 U⟩
  let c23 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.iff₁₃ Op.varEmit, stk inp Tp c V1t F [] O9 U⟩
  let c24 : (mach).Cfg := ⟨some Label.iff₁₃, St.rsDone Label.iff₁₃ Op.varEmit, stk inp Tp c V F
      (List.replicate (y₁ + 1) ()) O10 U⟩
  let c25 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.iff₁₄ Op.varEmit, stk inp Tp c V F
      (List.replicate (y₁ + 1) ()) O11 U⟩
  let c26 : (mach).Cfg := ⟨some Label.iff₁₄, St.rsDone Label.iff₁₄ Op.varEmit, stk inp Tp c V1t F [] O11 U⟩
  let c27 : (mach).Cfg := ⟨some Label.unparkVal, St.rs Label.iff₁₅ Op.unpark, stk inp Tp c V1 F [] O11 U⟩
  let c28 : (mach).Cfg := ⟨some Label.iff₁₅, St.rsDone Label.iff₁₅ Op.unpark, stk inp T c V0 F [] O11 U⟩
  let c29 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.iff₁₆ Op.varEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O11 U⟩
  let c30 : (mach).Cfg := ⟨some Label.iff₁₆, St.rsDone Label.iff₁₆ Op.varEmit, stk inp T c V1 F
      (List.replicate (y₂ + 1) ()) O12 U⟩
  let c31 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.iff₁₇ Op.varEmit, stk inp T c V1 F
      (List.replicate (y₂ + 1) ()) O13 U⟩
  let c32 : (mach).Cfg := ⟨some Label.iff₁₇, St.rsDone Label.iff₁₇ Op.varEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O13 U⟩
  let c33 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.iff₁₈ Op.auxEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O13 U⟩
  let c34 : (mach).Cfg := ⟨some Label.iff₁₈, St.rsDone Label.iff₁₈ Op.auxEmit, stk inp T 0
      (List.replicate (y₂ + 1) true ++ V1) F (List.replicate c ()) O14 U⟩
  let c35 : (mach).Cfg := ⟨some Label.restoreCnt, St.rs Label.iff₁₉ Op.auxEmit, stk inp T 0
      (List.replicate (y₂ + 1) true ++ V1) F (List.replicate c ()) O15 U⟩
  let c36 : (mach).Cfg := ⟨some Label.iff₁₉, St.rsDone Label.iff₁₉ Op.auxEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O15 U⟩
  let c37 : (mach).Cfg := ⟨some Label.parkVal, St.mv Label.iff₂₀ Op.park, stk inp T c V0 F [] O15 U⟩
  let c38 : (mach).Cfg := ⟨some Label.iff₂₀, St.rsDone Label.iff₂₀ Op.park, stk inp Tp c V1 F [] O15 U⟩
  let c39 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.iff₂₁ Op.varEmit, stk inp Tp c V1t F [] O15 U⟩
  let c40 : (mach).Cfg := ⟨some Label.iff₂₁, St.rsDone Label.iff₂₁ Op.varEmit, stk inp Tp c V F
      (List.replicate (y₁ + 1) ()) O16 U⟩
  let c41 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.iff₂₂ Op.varEmit, stk inp Tp c V F
      (List.replicate (y₁ + 1) ()) O17 U⟩
  let c42 : (mach).Cfg := ⟨some Label.iff₂₂, St.rsDone Label.iff₂₂ Op.varEmit, stk inp Tp c V1t F [] O17 U⟩
  let c43 : (mach).Cfg := ⟨some Label.unparkVal, St.rs Label.iff₂₃ Op.unpark, stk inp Tp c V1 F [] O17 U⟩
  let c44 : (mach).Cfg := ⟨some Label.iff₂₃, St.rsDone Label.iff₂₃ Op.unpark, stk inp T c V0 F [] O17 U⟩
  let c45 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.iff₂₄ Op.varEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O17 U⟩
  let c46 : (mach).Cfg := ⟨some Label.iff₂₄, St.rsDone Label.iff₂₄ Op.varEmit, stk inp T c V1 F
      (List.replicate (y₂ + 1) ()) O18 U⟩
  let c47 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.iff₂₅ Op.varEmit, stk inp T c V1 F
      (List.replicate (y₂ + 1) ()) O19 U⟩
  let c48 : (mach).Cfg := ⟨some Label.iff₂₅, St.rsDone Label.iff₂₅ Op.varEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O19 U⟩
  let c49 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.iff₂₆ Op.auxEmit, stk inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O19 U⟩
  let c50 : (mach).Cfg := ⟨some Label.iff₂₆, St.rsDone Label.iff₂₆ Op.auxEmit, stk inp T 0
      (List.replicate (y₂ + 1) true ++ V1) F (List.replicate c ()) O20 U⟩
  let c51 : (mach).Cfg := ⟨some Label.parkVal, St.mv Label.iff₂₇ Op.park, stk inp T 0 V0 F
      (List.replicate c ()) O21 U⟩
  let c52 : (mach).Cfg := ⟨some Label.iff₂₇, St.rsDone Label.iff₂₇ Op.park, stk inp Tp 0 V1 F
      (List.replicate c ()) O21 U⟩
  let c53 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.iff₂₈ Op.varPop, stk inp Tp 0 V1t F
      (List.replicate c ()) O21 U⟩
  let c54 : (mach).Cfg := ⟨some Label.iff₂₈, St.rsDone Label.iff₂₈ Op.varPop, stk inp Tp 0 V F
      (List.replicate c ()) O22 U⟩
  let c55 : (mach).Cfg := ⟨some Label.unparkVal, St.rs Label.iff₂₉ Op.unpark, stk inp Tp 0 V F
      (List.replicate c ()) O23 U⟩
  let c56 : (mach).Cfg := ⟨some Label.iff₂₉, St.rsDone Label.iff₂₉ Op.unpark, stk inp T 0
      (false :: List.replicate (y₂ + 1) true ++ V) F (List.replicate c ()) O23 U⟩
  let c57 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.iff₃₀ Op.varPop, stk inp T 0
      (List.replicate (y₂ + 1) true ++ V) F (List.replicate c ()) O23 U⟩
  let c58 : (mach).Cfg := ⟨some Label.iff₃₀, St.rsDone Label.iff₃₀ Op.varPop, stk inp T 0 V F
      (List.replicate c ()) O24 U⟩
  let c59 : (mach).Cfg := ⟨some Label.constMake, St.done, stk inp T 0 V F (List.replicate c ()) O24 U⟩
  let c60 : (mach).Cfg := ⟨some Label.reduce, St.done, stk inp T (c + 1) V37 F [] O24 U⟩
  have h1 : Sstep c0 = some c1 := by
    exact emitIff_step St.emitIff inp T c V0 F [] O U
  have h2 : (flip bind Sstep)^[y₂ + 3] (some c1) = some c2 := by
    have h := parkVal_phase Label.iff₂ y₂ V1 inp T c F [] O U (by simp [V1])
    exact h
  have h3 : Sstep c2 = some c3 := by
    exact iff₂_step (St.rsDone Label.iff₂ Op.park) inp Tp c V1 F [] O U
  have h4 : (flip bind Sstep)^[c + 1] (some c3) = some c4 := by
    have h := moveCnt_phase Label.iff₃ inp Tp c V1 F [] O1 U
    rw [List.append_nil] at h
    exact h
  have h5 : Sstep c4 = some c5 := by
    exact iff₃_step (St.rsDone Label.iff₃ Op.auxEmit) inp Tp 0 V1 F (List.replicate c ()) O2 U
  have h6 : (flip bind Sstep)^[c + 1] (some c5) = some c6 := by
    have h := restoreCnt_phase Label.iff₄ inp Tp 0 c V1 F O3 U
    rw [Nat.zero_add] at h
    exact h
  have h7 : Sstep c6 = some c7 := by
    exact iff₄_step (St.rsDone Label.iff₄ Op.auxEmit) inp Tp c false (List.replicate (y₁ + 1) true ++ V) F [] O3 U
  have h8 : (flip bind Sstep)^[y₁ + 2] (some c7) = some c8 := by
    have h := moveVal_varEmit_phase Label.iff₅ (y₁ + 1) inp Tp c V F [] O3 U hV
    rw [List.append_nil] at h
    exact h
  have h9 : Sstep c8 = some c9 := by
    exact iff₅_step (St.rsDone Label.iff₅ Op.varEmit) inp Tp c V F (List.replicate (y₁ + 1) ()) O4 U
  have h10 : (flip bind Sstep)^[y₁ + 2] (some c9) = some c10 := by
    have h := restoreVal_phase Label.iff₆ (y₁ + 1) inp Tp c V F O5 U
    exact h
  have h11 : Sstep c10 = some c11 := by
    exact iff₆_step (St.rsDone Label.iff₆ Op.varEmit) inp Tp c (List.replicate (y₁ + 1) true ++ V) F [] O5 U
  have h12 : (flip bind Sstep)^[y₂ + 2] (some c11) = some c12 := by
    have h := unparkVal_phase Label.iff₇ y₂ V1 inp T c F [] O5 U
    exact h
  have h13 : Sstep c12 = some c13 := by
    exact iff₇_step (St.rsDone Label.iff₇ Op.unpark) inp T c false
      (List.replicate (y₂ + 1) true ++ V1) F [] O5 U
  have h14 : (flip bind Sstep)^[y₂ + 2] (some c13) = some c14 := by
    have h := moveVal_varEmit_phase Label.iff₈ (y₂ + 1) inp T c V1 F [] O5 U (by simp [V1])
    rw [List.append_nil] at h
    exact h
  have h15 : Sstep c14 = some c15 := by
    exact iff₈_step (St.rsDone Label.iff₈ Op.varEmit) inp T c V1 F (List.replicate (y₂ + 1) ()) O6 U
  have h16 : (flip bind Sstep)^[y₂ + 2] (some c15) = some c16 := by
    have h := restoreVal_phase Label.iff₉ (y₂ + 1) inp T c V1 F O7 U
    exact h
  have h17 : Sstep c16 = some c17 := by
    exact iff₉_step (St.rsDone Label.iff₉ Op.varEmit) inp T c (List.replicate (y₂ + 1) true ++ V1) F [] O7 U
  have h18 : (flip bind Sstep)^[c + 1] (some c17) = some c18 := by
    have h := moveCnt_phase Label.iff₁₀ inp T c (List.replicate (y₂ + 1) true ++ V1) F [] O7 U
    rw [List.append_nil] at h
    exact h
  have h19 : Sstep c18 = some c19 := by
    exact iff₁₀_step (St.rsDone Label.iff₁₀ Op.auxEmit) inp T 0
      (List.replicate (y₂ + 1) true ++ V1) F (List.replicate c ()) O8 U
  have h20 : (flip bind Sstep)^[c + 1] (some c19) = some c20 := by
    have h := restoreCnt_phase Label.iff₁₁ inp T 0 c (List.replicate (y₂ + 1) true ++ V1) F O9 U
    rw [Nat.zero_add] at h
    exact h
  have h21 : Sstep c20 = some c21 := by
    exact iff₁₁_step (St.rsDone Label.iff₁₁ Op.auxEmit) inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O9 U
  have h22 : (flip bind Sstep)^[y₂ + 3] (some c21) = some c22 := by
    have h := parkVal_phase Label.iff₁₂ y₂ V1 inp T c F [] O9 U (by simp [V1])
    exact h
  have h23 : Sstep c22 = some c23 := by
    exact iff₁₂_step (St.rsDone Label.iff₁₂ Op.park) inp Tp c false
      (List.replicate (y₁ + 1) true ++ V) F [] O9 U
  have h24 : (flip bind Sstep)^[y₁ + 2] (some c23) = some c24 := by
    have h := moveVal_varEmit_phase Label.iff₁₃ (y₁ + 1) inp Tp c V F [] O9 U hV
    rw [List.append_nil] at h
    exact h
  have h25 : Sstep c24 = some c25 := by
    exact iff₁₃_step (St.rsDone Label.iff₁₃ Op.varEmit) inp Tp c V F (List.replicate (y₁ + 1) ()) O10 U
  have h26 : (flip bind Sstep)^[y₁ + 2] (some c25) = some c26 := by
    have h := restoreVal_phase Label.iff₁₄ (y₁ + 1) inp Tp c V F O11 U
    exact h
  have h27 : Sstep c26 = some c27 := by
    exact iff₁₄_step (St.rsDone Label.iff₁₄ Op.varEmit) inp Tp c (List.replicate (y₁ + 1) true ++ V) F [] O11 U
  have h28 : (flip bind Sstep)^[y₂ + 2] (some c27) = some c28 := by
    have h := unparkVal_phase Label.iff₁₅ y₂ V1 inp T c F [] O11 U
    exact h
  have h29 : Sstep c28 = some c29 := by
    exact iff₁₅_step (St.rsDone Label.iff₁₅ Op.unpark) inp T c false
      (List.replicate (y₂ + 1) true ++ V1) F [] O11 U
  have h30 : (flip bind Sstep)^[y₂ + 2] (some c29) = some c30 := by
    have h := moveVal_varEmit_phase Label.iff₁₆ (y₂ + 1) inp T c V1 F [] O11 U (by simp [V1])
    rw [List.append_nil] at h
    exact h
  have h31 : Sstep c30 = some c31 := by
    exact iff₁₆_step (St.rsDone Label.iff₁₆ Op.varEmit) inp T c V1 F (List.replicate (y₂ + 1) ()) O12 U
  have h32 : (flip bind Sstep)^[y₂ + 2] (some c31) = some c32 := by
    have h := restoreVal_phase Label.iff₁₇ (y₂ + 1) inp T c V1 F O13 U
    exact h
  have h33 : Sstep c32 = some c33 := by
    exact iff₁₇_step (St.rsDone Label.iff₁₇ Op.varEmit) inp T c (List.replicate (y₂ + 1) true ++ V1) F [] O13 U
  have h34 : (flip bind Sstep)^[c + 1] (some c33) = some c34 := by
    have h := moveCnt_phase Label.iff₁₈ inp T c (List.replicate (y₂ + 1) true ++ V1) F [] O13 U
    rw [List.append_nil] at h
    exact h
  have h35 : Sstep c34 = some c35 := by
    exact iff₁₈_step (St.rsDone Label.iff₁₈ Op.auxEmit) inp T 0
      (List.replicate (y₂ + 1) true ++ V1) F (List.replicate c ()) O14 U
  have h36 : (flip bind Sstep)^[c + 1] (some c35) = some c36 := by
    have h := restoreCnt_phase Label.iff₁₉ inp T 0 c (List.replicate (y₂ + 1) true ++ V1) F O15 U
    rw [Nat.zero_add] at h
    exact h
  have h37 : Sstep c36 = some c37 := by
    exact iff₁₉_step (St.rsDone Label.iff₁₉ Op.auxEmit) inp T c
      (List.replicate (y₂ + 1) true ++ V1) F [] O15 U
  have h38 : (flip bind Sstep)^[y₂ + 3] (some c37) = some c38 := by
    have h := parkVal_phase Label.iff₂₀ y₂ V1 inp T c F [] O15 U (by simp [V1])
    exact h
  have h39 : Sstep c38 = some c39 := by
    exact iff₂₀_step (St.rsDone Label.iff₂₀ Op.park) inp Tp c false
      (List.replicate (y₁ + 1) true ++ V) F [] O15 U
  have h40 : (flip bind Sstep)^[y₁ + 2] (some c39) = some c40 := by
    have h := moveVal_varEmit_phase Label.iff₂₁ (y₁ + 1) inp Tp c V F [] O15 U hV
    rw [List.append_nil] at h
    exact h
  have h41 : Sstep c40 = some c41 := by
    exact iff₂₁_step (St.rsDone Label.iff₂₁ Op.varEmit) inp Tp c V F (List.replicate (y₁ + 1) ()) O16 U
  have h42 : (flip bind Sstep)^[y₁ + 2] (some c41) = some c42 := by
    have h := restoreVal_phase Label.iff₂₂ (y₁ + 1) inp Tp c V F O17 U
    exact h
  have h43 : Sstep c42 = some c43 := by
    exact iff₂₂_step (St.rsDone Label.iff₂₂ Op.varEmit) inp Tp c (List.replicate (y₁ + 1) true ++ V) F [] O17 U
  have h44 : (flip bind Sstep)^[y₂ + 2] (some c43) = some c44 := by
    have h := unparkVal_phase Label.iff₂₃ y₂ V1 inp T c F [] O17 U
    exact h
  have h45 : Sstep c44 = some c45 := by
    exact iff₂₃_step (St.rsDone Label.iff₂₃ Op.unpark) inp T c false
      (List.replicate (y₂ + 1) true ++ V1) F [] O17 U
  have h46 : (flip bind Sstep)^[y₂ + 2] (some c45) = some c46 := by
    have h := moveVal_varEmit_phase Label.iff₂₄ (y₂ + 1) inp T c V1 F [] O17 U (by simp [V1])
    rw [List.append_nil] at h
    exact h
  have h47 : Sstep c46 = some c47 := by
    exact iff₂₄_step (St.rsDone Label.iff₂₄ Op.varEmit) inp T c V1 F (List.replicate (y₂ + 1) ()) O18 U
  have h48 : (flip bind Sstep)^[y₂ + 2] (some c47) = some c48 := by
    have h := restoreVal_phase Label.iff₂₅ (y₂ + 1) inp T c V1 F O19 U
    exact h
  have h49 : Sstep c48 = some c49 := by
    exact iff₂₅_step (St.rsDone Label.iff₂₅ Op.varEmit) inp T c (List.replicate (y₂ + 1) true ++ V1) F [] O19 U
  have h50 : (flip bind Sstep)^[c + 1] (some c49) = some c50 := by
    have h := moveCnt_phase Label.iff₂₆ inp T c (List.replicate (y₂ + 1) true ++ V1) F [] O19 U
    rw [List.append_nil] at h
    exact h
  have h51 : Sstep c50 = some c51 := by
    exact iff₂₆_step (St.rsDone Label.iff₂₆ Op.auxEmit) inp T 0
      (List.replicate (y₂ + 1) true ++ V1) F (List.replicate c ()) O20 U
  have h52 : (flip bind Sstep)^[y₂ + 3] (some c51) = some c52 := by
    have h := parkVal_phase Label.iff₂₇ y₂ V1 inp T 0 F (List.replicate c ()) O21 U (by simp [V1])
    exact h
  have h53 : Sstep c52 = some c53 := by
    exact iff₂₇_step (St.rsDone Label.iff₂₇ Op.park) inp Tp 0 false
      (List.replicate (y₁ + 1) true ++ V) F (List.replicate c ()) O21 U
  have h54 : (flip bind Sstep)^[y₁ + 2] (some c53) = some c54 := by
    have h := moveVal_varPop_phase Label.iff₂₈ (y₁ + 1) inp Tp 0 V F (List.replicate c ()) O21 U hV
    exact h
  have h55 : Sstep c54 = some c55 := by
    exact iff₂₈_step (St.rsDone Label.iff₂₈ Op.varPop) inp Tp 0 V F (List.replicate c ()) O22 U
  have h56 : (flip bind Sstep)^[y₂ + 2] (some c55) = some c56 := by
    have h := unparkVal_phase Label.iff₂₉ y₂ V inp T 0 F (List.replicate c ()) O23 U
    exact h
  have h57 : Sstep c56 = some c57 := by
    exact iff₂₉_step (St.rsDone Label.iff₂₉ Op.unpark) inp T 0 false
      (List.replicate (y₂ + 1) true ++ V) F (List.replicate c ()) O23 U
  have h58 : (flip bind Sstep)^[y₂ + 2] (some c57) = some c58 := by
    have h := moveVal_varPop_phase Label.iff₃₀ (y₂ + 1) inp T 0 V F (List.replicate c ()) O23 U hV
    exact h
  have h59 : Sstep c58 = some c59 := by
    exact iff₃₀_step (St.rsDone Label.iff₃₀ Op.varPop) inp T 0 V F (List.replicate c ()) O24 U
  have h60 : (flip bind Sstep)^[c + 1] (some c59) = some c60 := by
    have h := constMake_phase c St.done inp T 0 V F O24 U
    rw [Nat.zero_add] at h
    exact h
  calc
    (flip bind Sstep)^[8 * c + 7 * y₁ + 15 * y₂ + 86] (some c0)
      = (flip bind Sstep)^[8 * c + 7 * y₁ + 15 * y₂ + 85] (some c1) := by
          rw [show 8 * c + 7 * y₁ + 15 * y₂ + 86 = (8 * c + 7 * y₁ + 15 * y₂ + 85) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[8 * c + 7 * y₁ + 15 * y₂ + 85] x) h1
    _ = (flip bind Sstep)^[8 * c + 7 * y₁ + 14 * y₂ + 82] (some c2) := by
          rw [show 8 * c + 7 * y₁ + 15 * y₂ + 85 = (8 * c + 7 * y₁ + 14 * y₂ + 82) + (y₂ + 3) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[8 * c + 7 * y₁ + 14 * y₂ + 82] x) h2
    _ = (flip bind Sstep)^[8 * c + 7 * y₁ + 14 * y₂ + 81] (some c3) := by
          rw [show 8 * c + 7 * y₁ + 14 * y₂ + 82 = (8 * c + 7 * y₁ + 14 * y₂ + 81) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[8 * c + 7 * y₁ + 14 * y₂ + 81] x) h3
    _ = (flip bind Sstep)^[7 * c + 7 * y₁ + 14 * y₂ + 80] (some c4) := by
          rw [show 8 * c + 7 * y₁ + 14 * y₂ + 81 = (7 * c + 7 * y₁ + 14 * y₂ + 80) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[7 * c + 7 * y₁ + 14 * y₂ + 80] x) h4
    _ = (flip bind Sstep)^[7 * c + 7 * y₁ + 14 * y₂ + 79] (some c5) := by
          rw [show 7 * c + 7 * y₁ + 14 * y₂ + 80 = (7 * c + 7 * y₁ + 14 * y₂ + 79) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[7 * c + 7 * y₁ + 14 * y₂ + 79] x) h5
    _ = (flip bind Sstep)^[6 * c + 7 * y₁ + 14 * y₂ + 78] (some c6) := by
          rw [show 7 * c + 7 * y₁ + 14 * y₂ + 79 = (6 * c + 7 * y₁ + 14 * y₂ + 78) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 7 * y₁ + 14 * y₂ + 78] x) h6
    _ = (flip bind Sstep)^[6 * c + 7 * y₁ + 14 * y₂ + 77] (some c7) := by
          rw [show 6 * c + 7 * y₁ + 14 * y₂ + 78 = (6 * c + 7 * y₁ + 14 * y₂ + 77) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 7 * y₁ + 14 * y₂ + 77] x) h7
    _ = (flip bind Sstep)^[6 * c + 6 * y₁ + 14 * y₂ + 75] (some c8) := by
          rw [show 6 * c + 7 * y₁ + 14 * y₂ + 77 = (6 * c + 6 * y₁ + 14 * y₂ + 75) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 6 * y₁ + 14 * y₂ + 75] x) h8
    _ = (flip bind Sstep)^[6 * c + 6 * y₁ + 14 * y₂ + 74] (some c9) := by
          rw [show 6 * c + 6 * y₁ + 14 * y₂ + 75 = (6 * c + 6 * y₁ + 14 * y₂ + 74) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 6 * y₁ + 14 * y₂ + 74] x) h9
    _ = (flip bind Sstep)^[6 * c + 5 * y₁ + 14 * y₂ + 72] (some c10) := by
          rw [show 6 * c + 6 * y₁ + 14 * y₂ + 74 = (6 * c + 5 * y₁ + 14 * y₂ + 72) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 5 * y₁ + 14 * y₂ + 72] x) h10
    _ = (flip bind Sstep)^[6 * c + 5 * y₁ + 14 * y₂ + 71] (some c11) := by
          rw [show 6 * c + 5 * y₁ + 14 * y₂ + 72 = (6 * c + 5 * y₁ + 14 * y₂ + 71) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 5 * y₁ + 14 * y₂ + 71] x) h11
    _ = (flip bind Sstep)^[6 * c + 5 * y₁ + 13 * y₂ + 69] (some c12) := by
          rw [show 6 * c + 5 * y₁ + 14 * y₂ + 71 = (6 * c + 5 * y₁ + 13 * y₂ + 69) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 5 * y₁ + 13 * y₂ + 69] x) h12
    _ = (flip bind Sstep)^[6 * c + 5 * y₁ + 13 * y₂ + 68] (some c13) := by
          rw [show 6 * c + 5 * y₁ + 13 * y₂ + 69 = (6 * c + 5 * y₁ + 13 * y₂ + 68) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 5 * y₁ + 13 * y₂ + 68] x) h13
    _ = (flip bind Sstep)^[6 * c + 5 * y₁ + 12 * y₂ + 66] (some c14) := by
          rw [show 6 * c + 5 * y₁ + 13 * y₂ + 68 = (6 * c + 5 * y₁ + 12 * y₂ + 66) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 5 * y₁ + 12 * y₂ + 66] x) h14
    _ = (flip bind Sstep)^[6 * c + 5 * y₁ + 12 * y₂ + 65] (some c15) := by
          rw [show 6 * c + 5 * y₁ + 12 * y₂ + 66 = (6 * c + 5 * y₁ + 12 * y₂ + 65) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 5 * y₁ + 12 * y₂ + 65] x) h15
    _ = (flip bind Sstep)^[6 * c + 5 * y₁ + 11 * y₂ + 63] (some c16) := by
          rw [show 6 * c + 5 * y₁ + 12 * y₂ + 65 = (6 * c + 5 * y₁ + 11 * y₂ + 63) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 5 * y₁ + 11 * y₂ + 63] x) h16
    _ = (flip bind Sstep)^[6 * c + 5 * y₁ + 11 * y₂ + 62] (some c17) := by
          rw [show 6 * c + 5 * y₁ + 11 * y₂ + 63 = (6 * c + 5 * y₁ + 11 * y₂ + 62) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 5 * y₁ + 11 * y₂ + 62] x) h17
    _ = (flip bind Sstep)^[5 * c + 5 * y₁ + 11 * y₂ + 61] (some c18) := by
          rw [show 6 * c + 5 * y₁ + 11 * y₂ + 62 = (5 * c + 5 * y₁ + 11 * y₂ + 61) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[5 * c + 5 * y₁ + 11 * y₂ + 61] x) h18
    _ = (flip bind Sstep)^[5 * c + 5 * y₁ + 11 * y₂ + 60] (some c19) := by
          rw [show 5 * c + 5 * y₁ + 11 * y₂ + 61 = (5 * c + 5 * y₁ + 11 * y₂ + 60) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[5 * c + 5 * y₁ + 11 * y₂ + 60] x) h19
    _ = (flip bind Sstep)^[4 * c + 5 * y₁ + 11 * y₂ + 59] (some c20) := by
          rw [show 5 * c + 5 * y₁ + 11 * y₂ + 60 = (4 * c + 5 * y₁ + 11 * y₂ + 59) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 5 * y₁ + 11 * y₂ + 59] x) h20
    _ = (flip bind Sstep)^[4 * c + 5 * y₁ + 11 * y₂ + 58] (some c21) := by
          rw [show 4 * c + 5 * y₁ + 11 * y₂ + 59 = (4 * c + 5 * y₁ + 11 * y₂ + 58) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 5 * y₁ + 11 * y₂ + 58] x) h21
    _ = (flip bind Sstep)^[4 * c + 5 * y₁ + 10 * y₂ + 55] (some c22) := by
          rw [show 4 * c + 5 * y₁ + 11 * y₂ + 58 = (4 * c + 5 * y₁ + 10 * y₂ + 55) + (y₂ + 3) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 5 * y₁ + 10 * y₂ + 55] x) h22
    _ = (flip bind Sstep)^[4 * c + 5 * y₁ + 10 * y₂ + 54] (some c23) := by
          rw [show 4 * c + 5 * y₁ + 10 * y₂ + 55 = (4 * c + 5 * y₁ + 10 * y₂ + 54) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 5 * y₁ + 10 * y₂ + 54] x) h23
    _ = (flip bind Sstep)^[4 * c + 4 * y₁ + 10 * y₂ + 52] (some c24) := by
          rw [show 4 * c + 5 * y₁ + 10 * y₂ + 54 = (4 * c + 4 * y₁ + 10 * y₂ + 52) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 4 * y₁ + 10 * y₂ + 52] x) h24
    _ = (flip bind Sstep)^[4 * c + 4 * y₁ + 10 * y₂ + 51] (some c25) := by
          rw [show 4 * c + 4 * y₁ + 10 * y₂ + 52 = (4 * c + 4 * y₁ + 10 * y₂ + 51) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 4 * y₁ + 10 * y₂ + 51] x) h25
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 10 * y₂ + 49] (some c26) := by
          rw [show 4 * c + 4 * y₁ + 10 * y₂ + 51 = (4 * c + 3 * y₁ + 10 * y₂ + 49) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 10 * y₂ + 49] x) h26
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 10 * y₂ + 48] (some c27) := by
          rw [show 4 * c + 3 * y₁ + 10 * y₂ + 49 = (4 * c + 3 * y₁ + 10 * y₂ + 48) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 10 * y₂ + 48] x) h27
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 9 * y₂ + 46] (some c28) := by
          rw [show 4 * c + 3 * y₁ + 10 * y₂ + 48 = (4 * c + 3 * y₁ + 9 * y₂ + 46) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 9 * y₂ + 46] x) h28
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 9 * y₂ + 45] (some c29) := by
          rw [show 4 * c + 3 * y₁ + 9 * y₂ + 46 = (4 * c + 3 * y₁ + 9 * y₂ + 45) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 9 * y₂ + 45] x) h29
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 8 * y₂ + 43] (some c30) := by
          rw [show 4 * c + 3 * y₁ + 9 * y₂ + 45 = (4 * c + 3 * y₁ + 8 * y₂ + 43) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 8 * y₂ + 43] x) h30
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 8 * y₂ + 42] (some c31) := by
          rw [show 4 * c + 3 * y₁ + 8 * y₂ + 43 = (4 * c + 3 * y₁ + 8 * y₂ + 42) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 8 * y₂ + 42] x) h31
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 7 * y₂ + 40] (some c32) := by
          rw [show 4 * c + 3 * y₁ + 8 * y₂ + 42 = (4 * c + 3 * y₁ + 7 * y₂ + 40) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 7 * y₂ + 40] x) h32
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 7 * y₂ + 39] (some c33) := by
          rw [show 4 * c + 3 * y₁ + 7 * y₂ + 40 = (4 * c + 3 * y₁ + 7 * y₂ + 39) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 7 * y₂ + 39] x) h33
    _ = (flip bind Sstep)^[3 * c + 3 * y₁ + 7 * y₂ + 38] (some c34) := by
          rw [show 4 * c + 3 * y₁ + 7 * y₂ + 39 = (3 * c + 3 * y₁ + 7 * y₂ + 38) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[3 * c + 3 * y₁ + 7 * y₂ + 38] x) h34
    _ = (flip bind Sstep)^[3 * c + 3 * y₁ + 7 * y₂ + 37] (some c35) := by
          rw [show 3 * c + 3 * y₁ + 7 * y₂ + 38 = (3 * c + 3 * y₁ + 7 * y₂ + 37) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[3 * c + 3 * y₁ + 7 * y₂ + 37] x) h35
    _ = (flip bind Sstep)^[2 * c + 3 * y₁ + 7 * y₂ + 36] (some c36) := by
          rw [show 3 * c + 3 * y₁ + 7 * y₂ + 37 = (2 * c + 3 * y₁ + 7 * y₂ + 36) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3 * y₁ + 7 * y₂ + 36] x) h36
    _ = (flip bind Sstep)^[2 * c + 3 * y₁ + 7 * y₂ + 35] (some c37) := by
          rw [show 2 * c + 3 * y₁ + 7 * y₂ + 36 = (2 * c + 3 * y₁ + 7 * y₂ + 35) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3 * y₁ + 7 * y₂ + 35] x) h37
    _ = (flip bind Sstep)^[2 * c + 3 * y₁ + 6 * y₂ + 32] (some c38) := by
          rw [show 2 * c + 3 * y₁ + 7 * y₂ + 35 = (2 * c + 3 * y₁ + 6 * y₂ + 32) + (y₂ + 3) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3 * y₁ + 6 * y₂ + 32] x) h38
    _ = (flip bind Sstep)^[2 * c + 3 * y₁ + 6 * y₂ + 31] (some c39) := by
          rw [show 2 * c + 3 * y₁ + 6 * y₂ + 32 = (2 * c + 3 * y₁ + 6 * y₂ + 31) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3 * y₁ + 6 * y₂ + 31] x) h39
    _ = (flip bind Sstep)^[2 * c + 2 * y₁ + 6 * y₂ + 29] (some c40) := by
          rw [show 2 * c + 3 * y₁ + 6 * y₂ + 31 = (2 * c + 2 * y₁ + 6 * y₂ + 29) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2 * y₁ + 6 * y₂ + 29] x) h40
    _ = (flip bind Sstep)^[2 * c + 2 * y₁ + 6 * y₂ + 28] (some c41) := by
          rw [show 2 * c + 2 * y₁ + 6 * y₂ + 29 = (2 * c + 2 * y₁ + 6 * y₂ + 28) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2 * y₁ + 6 * y₂ + 28] x) h41
    _ = (flip bind Sstep)^[2 * c + y₁ + 6 * y₂ + 26] (some c42) := by
          rw [show 2 * c + 2 * y₁ + 6 * y₂ + 28 = (2 * c + y₁ + 6 * y₂ + 26) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 6 * y₂ + 26] x) h42
    _ = (flip bind Sstep)^[2 * c + y₁ + 6 * y₂ + 25] (some c43) := by
          rw [show 2 * c + y₁ + 6 * y₂ + 26 = (2 * c + y₁ + 6 * y₂ + 25) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 6 * y₂ + 25] x) h43
    _ = (flip bind Sstep)^[2 * c + y₁ + 5 * y₂ + 23] (some c44) := by
          rw [show 2 * c + y₁ + 6 * y₂ + 25 = (2 * c + y₁ + 5 * y₂ + 23) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 5 * y₂ + 23] x) h44
    _ = (flip bind Sstep)^[2 * c + y₁ + 5 * y₂ + 22] (some c45) := by
          rw [show 2 * c + y₁ + 5 * y₂ + 23 = (2 * c + y₁ + 5 * y₂ + 22) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 5 * y₂ + 22] x) h45
    _ = (flip bind Sstep)^[2 * c + y₁ + 4 * y₂ + 20] (some c46) := by
          rw [show 2 * c + y₁ + 5 * y₂ + 22 = (2 * c + y₁ + 4 * y₂ + 20) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 4 * y₂ + 20] x) h46
    _ = (flip bind Sstep)^[2 * c + y₁ + 4 * y₂ + 19] (some c47) := by
          rw [show 2 * c + y₁ + 4 * y₂ + 20 = (2 * c + y₁ + 4 * y₂ + 19) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 4 * y₂ + 19] x) h47
    _ = (flip bind Sstep)^[2 * c + y₁ + 3 * y₂ + 17] (some c48) := by
          rw [show 2 * c + y₁ + 4 * y₂ + 19 = (2 * c + y₁ + 3 * y₂ + 17) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 3 * y₂ + 17] x) h48
    _ = (flip bind Sstep)^[2 * c + y₁ + 3 * y₂ + 16] (some c49) := by
          rw [show 2 * c + y₁ + 3 * y₂ + 17 = (2 * c + y₁ + 3 * y₂ + 16) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 3 * y₂ + 16] x) h49
    _ = (flip bind Sstep)^[c + y₁ + 3 * y₂ + 15] (some c50) := by
          rw [show 2 * c + y₁ + 3 * y₂ + 16 = (c + y₁ + 3 * y₂ + 15) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + y₁ + 3 * y₂ + 15] x) h50
    _ = (flip bind Sstep)^[c + y₁ + 3 * y₂ + 14] (some c51) := by
          rw [show c + y₁ + 3 * y₂ + 15 = (c + y₁ + 3 * y₂ + 14) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[c + y₁ + 3 * y₂ + 14] x) h51
    _ = (flip bind Sstep)^[c + y₁ + 2 * y₂ + 11] (some c52) := by
          rw [show c + y₁ + 3 * y₂ + 14 = (c + y₁ + 2 * y₂ + 11) + (y₂ + 3) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + y₁ + 2 * y₂ + 11] x) h52
    _ = (flip bind Sstep)^[c + y₁ + 2 * y₂ + 10] (some c53) := by
          rw [show c + y₁ + 2 * y₂ + 11 = (c + y₁ + 2 * y₂ + 10) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[c + y₁ + 2 * y₂ + 10] x) h53
    _ = (flip bind Sstep)^[c + 2 * y₂ + 8] (some c54) := by
          rw [show c + y₁ + 2 * y₂ + 10 = (c + 2 * y₂ + 8) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + 2 * y₂ + 8] x) h54
    _ = (flip bind Sstep)^[c + 2 * y₂ + 7] (some c55) := by
          rw [show c + 2 * y₂ + 8 = (c + 2 * y₂ + 7) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[c + 2 * y₂ + 7] x) h55
    _ = (flip bind Sstep)^[c + y₂ + 5] (some c56) := by
          rw [show c + 2 * y₂ + 7 = (c + y₂ + 5) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + y₂ + 5] x) h56
    _ = (flip bind Sstep)^[c + y₂ + 4] (some c57) := by
          rw [show c + y₂ + 5 = (c + y₂ + 4) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[c + y₂ + 4] x) h57
    _ = (flip bind Sstep)^[c + 2] (some c58) := by
          rw [show c + y₂ + 4 = (c + 2) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + 2] x) h58
    _ = (flip bind Sstep)^[c + 1] (some c59) := by
          rw [show c + 2 = (c + 1) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h59
    _ = some c60 := by
          rw [show c + 1 = 0 + (c + 1) by omega]
          rw [Function.iterate_add]
          simpa using h60
    _ = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF (iffClauses c y₁ y₂)).reverse ++ O) U⟩ : (mach).Cfg) := by
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk, c60, V37]
            rw [encCNF_iffClauses_reverse]
            rw [encClause_three_reverse (Literal.pos c) (Literal.neg y₁) (Literal.neg y₂)]
            rw [encClause_three_reverse (Literal.pos c) (Literal.pos y₁) (Literal.pos y₂)]
            rw [encClause_three_reverse (Literal.neg c) (Literal.pos y₁) (Literal.neg y₂)]
            rw [encClause_three_reverse (Literal.neg c) (Literal.neg y₁) (Literal.pos y₂)]
            simp [O1, O2, O3, O4, O5, O6, O7, O8, O9, O10, O11, O12, O13, O14, O15, O16, O17, O18, O19, O20, O21, O22, O23, O24,
              encLit_reverse, encLit, litSym, litIndex, List.append_assoc, List.cons_append,
              List.replicate_succ, replicate_append_one]


end TM3CNF

end Turing

end Chapter34

end CLRS
