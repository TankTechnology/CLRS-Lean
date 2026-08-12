import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B7_OrPhase

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

end TM3CNF

end Turing

end Chapter34

end CLRS
