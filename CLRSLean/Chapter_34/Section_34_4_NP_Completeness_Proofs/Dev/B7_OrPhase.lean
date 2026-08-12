import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B7_OrEmit

/-!
# Dev B7: the `or` phase run lemma

Development split of `SatTo3CNFMachine`: `emitOr_phase`, the full run lemma for the `or` clause emission.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

/-- The `emitOr` phase: with the two children's value runs on top of `val`
(the second child's above the first's), emit `orClauses c y₁ y₂` and allocate
the auxiliary variable `y = c` via `constMake`.  The second child is parked on
`temp` while the first is emitted, then restored; the first child is consumed
twice (once per emitted clause mentioning it), and both children are left
restored beneath the new auxiliary run. -/
lemma emitOr_phase (inp T : List FormulaSym) (c : Nat) (y₁ y₂ : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[6 * c + 3 * y₁ + 7 * y₂ + 44]
      (some (⟨some Label.emitOr, St.emitOr, stk inp T c
        (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF (orClauses c y₁ y₂)).reverse ++ O) U⟩ : (mach).Cfg) := by
  let Tp : List FormulaSym := List.replicate (y₂ + 1) (FormulaSym.lit true) ++ ([FormulaSym.lit false] ++ T)
  let V0 : List Bool := false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)
  let V1 : List Bool := false :: List.replicate (y₁ + 1) true ++ V
  let V2 : List Bool := List.replicate (y₁ + 1) true ++ V
  let V3 : List Bool := V
  let V4 : List Bool := List.replicate (y₁ + 1) true ++ V
  let V5 : List Bool := false :: List.replicate (y₁ + 1) true ++ V
  let V6 : List Bool := false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)
  let V7 : List Bool := List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)
  let V8 : List Bool := false :: List.replicate (y₁ + 1) true ++ V
  let V9 : List Bool := List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)
  let V10 : List Bool := false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)
  let V11 : List Bool := false :: List.replicate (y₁ + 1) true ++ V
  let V12 : List Bool := List.replicate (y₁ + 1) true ++ V
  let V13 : List Bool := V
  let V14 : List Bool := false :: List.replicate (y₂ + 1) true ++ V
  let V15 : List Bool := List.replicate (y₂ + 1) true ++ V
  let V16 : List Bool := V
  let V17 : List Bool := false :: List.replicate (c + 1) true ++ V
  let O1 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O
  let O2 : List CNFSym := List.replicate c CNFSym.endMark ++ O1
  let O3 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O2
  let O4 : List CNFSym := List.replicate (y₁ + 1) CNFSym.endMark ++ O3
  let O5 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O4
  let O6 : List CNFSym := List.replicate c CNFSym.endMark ++ O5
  let O7 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O6
  let O8 : List CNFSym := List.replicate (y₂ + 1) CNFSym.endMark ++ O7
  let O9 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O8
  let O10 : List CNFSym := List.replicate (y₁ + 1) CNFSym.endMark ++ O9
  let O11 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: O10
  let O12 : List CNFSym := List.replicate (y₂ + 1) CNFSym.endMark ++ O11
  let O13 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: O12
  let O14 : List CNFSym := List.replicate c CNFSym.endMark ++ O13
  let O15 : List CNFSym := CNFSym.endMark :: O14
  let c0 : (mach).Cfg := ⟨some Label.emitOr, St.emitOr, stk inp T c V0 F [] O U⟩
  let c1 : (mach).Cfg := ⟨some Label.parkVal, St.mv Label.or₂ Op.park, stk inp T c V0 F [] O U⟩
  let c2 : (mach).Cfg := ⟨some Label.or₂, St.rsDone Label.or₂ Op.park, stk inp Tp c V1 F [] O U⟩
  let c3 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.or₃ Op.auxEmit, stk inp Tp c V1 F [] O1 U⟩
  let c4 : (mach).Cfg := ⟨some Label.or₃, St.rsDone Label.or₃ Op.auxEmit, stk inp Tp 0 V1 F (List.replicate c ()) O2 U⟩
  let c5 : (mach).Cfg := ⟨some Label.restoreCnt, St.rs Label.or₄ Op.auxEmit, stk inp Tp 0 V1 F (List.replicate c ()) O3 U⟩
  let c6 : (mach).Cfg := ⟨some Label.or₄, St.rsDone Label.or₄ Op.auxEmit, stk inp Tp c V1 F [] O3 U⟩
  let c7 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.or₅ Op.varEmit, stk inp Tp c V2 F [] O3 U⟩
  let c8 : (mach).Cfg := ⟨some Label.or₅, St.rsDone Label.or₅ Op.varEmit, stk inp Tp c V3 F (List.replicate (y₁ + 1) ()) O4 U⟩
  let c9 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.or₆ Op.varEmit, stk inp Tp c V3 F (List.replicate (y₁ + 1) ()) O5 U⟩
  let c10 : (mach).Cfg := ⟨some Label.or₆, St.rsDone Label.or₆ Op.varEmit, stk inp Tp c V4 F [] O5 U⟩
  let c11 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.or₇ Op.auxEmit, stk inp Tp c V5 F [] O5 U⟩
  let c12 : (mach).Cfg := ⟨some Label.or₇, St.rsDone Label.or₇ Op.auxEmit, stk inp Tp 0 V5 F (List.replicate c ()) O6 U⟩
  let c13 : (mach).Cfg := ⟨some Label.restoreCnt, St.rs Label.or₈ Op.auxEmit, stk inp Tp 0 V5 F (List.replicate c ()) O7 U⟩
  let c14 : (mach).Cfg := ⟨some Label.or₈, St.rsDone Label.or₈ Op.auxEmit, stk inp Tp c V5 F [] O7 U⟩
  let c15 : (mach).Cfg := ⟨some Label.unparkVal, St.rs Label.or₉ Op.unpark, stk inp Tp c V5 F [] O7 U⟩
  let c16 : (mach).Cfg := ⟨some Label.or₉, St.rsDone Label.or₉ Op.unpark, stk inp T c V6 F [] O7 U⟩
  let c17 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.or₁₀ Op.varEmit, stk inp T c V7 F [] O7 U⟩
  let c18 : (mach).Cfg := ⟨some Label.or₁₀, St.rsDone Label.or₁₀ Op.varEmit, stk inp T c V8 F (List.replicate (y₂ + 1) ()) O8 U⟩
  let c19 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.or₁₁ Op.varEmit, stk inp T c V8 F (List.replicate (y₂ + 1) ()) O9 U⟩
  let c20 : (mach).Cfg := ⟨some Label.or₁₁, St.rsDone Label.or₁₁ Op.varEmit, stk inp T c V9 F [] O9 U⟩
  let c21 : (mach).Cfg := ⟨some Label.parkVal, St.mv Label.or₁₂ Op.park, stk inp T c V10 F [] O9 U⟩
  let c22 : (mach).Cfg := ⟨some Label.or₁₂, St.rsDone Label.or₁₂ Op.park, stk inp Tp c V11 F [] O9 U⟩
  let c23 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.or₁₃ Op.varPop, stk inp Tp c V12 F [] O9 U⟩
  let c24 : (mach).Cfg := ⟨some Label.or₁₃, St.rsDone Label.or₁₃ Op.varPop, stk inp Tp c V13 F [] O10 U⟩
  let c25 : (mach).Cfg := ⟨some Label.unparkVal, St.rs Label.or₁₄ Op.unpark, stk inp Tp c V13 F [] O11 U⟩
  let c26 : (mach).Cfg := ⟨some Label.or₁₄, St.rsDone Label.or₁₄ Op.unpark, stk inp T c V14 F [] O11 U⟩
  let c27 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.or₁₅ Op.varPop, stk inp T c V15 F [] O11 U⟩
  let c28 : (mach).Cfg := ⟨some Label.or₁₅, St.rsDone Label.or₁₅ Op.varPop, stk inp T c V16 F [] O12 U⟩
  let c29 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.or₁₆ Op.auxEmit, stk inp T c V16 F [] O13 U⟩
  let c30 : (mach).Cfg := ⟨some Label.or₁₆, St.rsDone Label.or₁₆ Op.auxEmit, stk inp T 0 V16 F (List.replicate c ()) O14 U⟩
  let c31 : (mach).Cfg := ⟨some Label.constMake, St.done, stk inp T 0 V16 F (List.replicate c ()) O15 U⟩
  let c32 : (mach).Cfg := ⟨some Label.reduce, St.done, stk inp T (c + 1) V17 F [] O15 U⟩
  have h1 : Sstep c0 = some c1 := by
    exact emitOr_step St.emitOr inp T c V0 F [] O U
  have h2 : (flip bind Sstep)^[y₂ + 3] (some c1) = some c2 := by
    have h := parkVal_phase Label.or₂ y₂ V1 inp T c F [] O U (by simp [V1])
    exact h
  have h3 : Sstep c2 = some c3 := by
    exact or₂_step (St.rsDone Label.or₂ Op.park) inp Tp c V1 F [] O U
  have h4 : (flip bind Sstep)^[c + 1] (some c3) = some c4 := by
    have h := moveCnt_phase Label.or₃ inp Tp c V1 F [] O1 U
    rw [List.append_nil] at h
    exact h
  have h5 : Sstep c4 = some c5 := by
    exact or₃_step (St.rsDone Label.or₃ Op.auxEmit) inp Tp 0 V1 F (List.replicate c ()) O2 U
  have h6 : (flip bind Sstep)^[c + 1] (some c5) = some c6 := by
    have h := restoreCnt_phase Label.or₄ inp Tp 0 c V1 F O3 U
    rw [Nat.zero_add] at h
    exact h
  have h7 : Sstep c6 = some c7 := by
    exact or₄_step (St.rsDone Label.or₄ Op.auxEmit) inp Tp c false (List.replicate (y₁ + 1) true ++ V) F [] O3 U
  have h8 : (flip bind Sstep)^[y₁ + 2] (some c7) = some c8 := by
    have h := moveVal_varEmit_phase Label.or₅ (y₁ + 1) inp Tp c V F [] O3 U hV
    rw [List.append_nil] at h
    exact h
  have h9 : Sstep c8 = some c9 := by
    exact or₅_step (St.rsDone Label.or₅ Op.varEmit) inp Tp c V F (List.replicate (y₁ + 1) ()) O4 U
  have h10 : (flip bind Sstep)^[y₁ + 2] (some c9) = some c10 := by
    have h := restoreVal_phase Label.or₆ (y₁ + 1) inp Tp c V F O5 U
    exact h
  have h11 : Sstep c10 = some c11 := by
    exact or₆_step (St.rsDone Label.or₆ Op.varEmit) inp Tp c (List.replicate (y₁ + 1) true ++ V) F [] O5 U
  have h12 : (flip bind Sstep)^[c + 1] (some c11) = some c12 := by
    have h := moveCnt_phase Label.or₇ inp Tp c V5 F [] O5 U
    rw [List.append_nil] at h
    exact h
  have h13 : Sstep c12 = some c13 := by
    exact or₇_step (St.rsDone Label.or₇ Op.auxEmit) inp Tp 0 V5 F (List.replicate c ()) O6 U
  have h14 : (flip bind Sstep)^[c + 1] (some c13) = some c14 := by
    have h := restoreCnt_phase Label.or₈ inp Tp 0 c V5 F O7 U
    rw [Nat.zero_add] at h
    exact h
  have h15 : Sstep c14 = some c15 := by
    exact or₈_step (St.rsDone Label.or₈ Op.auxEmit) inp Tp c V5 F [] O7 U
  have h16 : (flip bind Sstep)^[y₂ + 2] (some c15) = some c16 := by
    exact unparkVal_phase Label.or₉ y₂ V1 inp T c F [] O7 U
  have h17 : Sstep c16 = some c17 := by
    exact or₉_step (St.rsDone Label.or₉ Op.unpark) inp T c false
      (List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] O7 U
  have h18 : (flip bind Sstep)^[y₂ + 2] (some c17) = some c18 := by
    have h := moveVal_varEmit_phase Label.or₁₀ (y₂ + 1) inp T c V1 F [] O7 U (by simp [V1])
    rw [List.append_nil] at h
    exact h
  have h19 : Sstep c18 = some c19 := by
    exact or₁₀_step (St.rsDone Label.or₁₀ Op.varEmit) inp T c V1 F (List.replicate (y₂ + 1) ()) O8 U
  have h20 : (flip bind Sstep)^[y₂ + 2] (some c19) = some c20 := by
    have h := restoreVal_phase Label.or₁₁ (y₂ + 1) inp T c V1 F O9 U
    exact h
  have h21 : Sstep c20 = some c21 := by
    exact or₁₁_step (St.rsDone Label.or₁₁ Op.varEmit) inp T c
      (List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] O9 U
  have h22 : (flip bind Sstep)^[y₂ + 3] (some c21) = some c22 := by
    have h := parkVal_phase Label.or₁₂ y₂ V1 inp T c F [] O9 U (by simp [V1])
    exact h
  have h23 : Sstep c22 = some c23 := by
    exact or₁₂_step (St.rsDone Label.or₁₂ Op.park) inp Tp c false (List.replicate (y₁ + 1) true ++ V) F [] O9 U
  have h24 : (flip bind Sstep)^[y₁ + 2] (some c23) = some c24 := by
    exact moveVal_varPop_phase Label.or₁₃ (y₁ + 1) inp Tp c V F [] O9 U hV
  have h25 : Sstep c24 = some c25 := by
    exact or₁₃_step (St.rsDone Label.or₁₃ Op.varPop) inp Tp c V F [] O10 U
  have h26 : (flip bind Sstep)^[y₂ + 2] (some c25) = some c26 := by
    exact unparkVal_phase Label.or₁₄ y₂ V inp T c F [] O11 U
  have h27 : Sstep c26 = some c27 := by
    exact or₁₄_step (St.rsDone Label.or₁₄ Op.unpark) inp T c false (List.replicate (y₂ + 1) true ++ V) F [] O11 U
  have h28 : (flip bind Sstep)^[y₂ + 2] (some c27) = some c28 := by
    exact moveVal_varPop_phase Label.or₁₅ (y₂ + 1) inp T c V F [] O11 U hV
  have h29 : Sstep c28 = some c29 := by
    exact or₁₅_step (St.rsDone Label.or₁₅ Op.varPop) inp T c V F [] O12 U
  have h30 : (flip bind Sstep)^[c + 1] (some c29) = some c30 := by
    have h := moveCnt_phase Label.or₁₆ inp T c V F [] O13 U
    rw [List.append_nil] at h
    exact h
  have h31 : Sstep c30 = some c31 := by
    exact or₁₆_step (St.rsDone Label.or₁₆ Op.auxEmit) inp T 0 V F (List.replicate c ()) O14 U
  have h32 : (flip bind Sstep)^[c + 1] (some c31) = some c32 := by
    have h := constMake_phase c St.done inp T 0 V F O15 U
    rw [Nat.zero_add] at h
    exact h
  calc
    (flip bind Sstep)^[6 * c + 3 * y₁ + 7 * y₂ + 44] (some c0)
      = (flip bind Sstep)^[6 * c + 3 * y₁ + 7 * y₂ + 43] (some c1) := by
          rw [show 6 * c + 3 * y₁ + 7 * y₂ + 44 = (6 * c + 3 * y₁ + 7 * y₂ + 43) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 3 * y₁ + 7 * y₂ + 43] x) h1
    _ = (flip bind Sstep)^[6 * c + 3 * y₁ + 6 * y₂ + 40] (some c2) := by
          rw [show 6 * c + 3 * y₁ + 7 * y₂ + 43 = (6 * c + 3 * y₁ + 6 * y₂ + 40) + (y₂ + 3) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 3 * y₁ + 6 * y₂ + 40] x) h2
    _ = (flip bind Sstep)^[6 * c + 3 * y₁ + 6 * y₂ + 39] (some c3) := by
          rw [show 6 * c + 3 * y₁ + 6 * y₂ + 40 = (6 * c + 3 * y₁ + 6 * y₂ + 39) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[6 * c + 3 * y₁ + 6 * y₂ + 39] x) h3
    _ = (flip bind Sstep)^[5 * c + 3 * y₁ + 6 * y₂ + 38] (some c4) := by
          rw [show 6 * c + 3 * y₁ + 6 * y₂ + 39 = (5 * c + 3 * y₁ + 6 * y₂ + 38) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[5 * c + 3 * y₁ + 6 * y₂ + 38] x) h4
    _ = (flip bind Sstep)^[5 * c + 3 * y₁ + 6 * y₂ + 37] (some c5) := by
          rw [show 5 * c + 3 * y₁ + 6 * y₂ + 38 = (5 * c + 3 * y₁ + 6 * y₂ + 37) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[5 * c + 3 * y₁ + 6 * y₂ + 37] x) h5
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 6 * y₂ + 36] (some c6) := by
          rw [show 5 * c + 3 * y₁ + 6 * y₂ + 37 = (4 * c + 3 * y₁ + 6 * y₂ + 36) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 6 * y₂ + 36] x) h6
    _ = (flip bind Sstep)^[4 * c + 3 * y₁ + 6 * y₂ + 35] (some c7) := by
          rw [show 4 * c + 3 * y₁ + 6 * y₂ + 36 = (4 * c + 3 * y₁ + 6 * y₂ + 35) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 3 * y₁ + 6 * y₂ + 35] x) h7
    _ = (flip bind Sstep)^[4 * c + 2 * y₁ + 6 * y₂ + 33] (some c8) := by
          rw [show 4 * c + 3 * y₁ + 6 * y₂ + 35 = (4 * c + 2 * y₁ + 6 * y₂ + 33) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 2 * y₁ + 6 * y₂ + 33] x) h8
    _ = (flip bind Sstep)^[4 * c + 2 * y₁ + 6 * y₂ + 32] (some c9) := by
          rw [show 4 * c + 2 * y₁ + 6 * y₂ + 33 = (4 * c + 2 * y₁ + 6 * y₂ + 32) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + 2 * y₁ + 6 * y₂ + 32] x) h9
    _ = (flip bind Sstep)^[4 * c + y₁ + 6 * y₂ + 30] (some c10) := by
          rw [show 4 * c + 2 * y₁ + 6 * y₂ + 32 = (4 * c + y₁ + 6 * y₂ + 30) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + y₁ + 6 * y₂ + 30] x) h10
    _ = (flip bind Sstep)^[4 * c + y₁ + 6 * y₂ + 29] (some c11) := by
          rw [show 4 * c + y₁ + 6 * y₂ + 30 = (4 * c + y₁ + 6 * y₂ + 29) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[4 * c + y₁ + 6 * y₂ + 29] x) h11
    _ = (flip bind Sstep)^[3 * c + y₁ + 6 * y₂ + 28] (some c12) := by
          rw [show 4 * c + y₁ + 6 * y₂ + 29 = (3 * c + y₁ + 6 * y₂ + 28) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[3 * c + y₁ + 6 * y₂ + 28] x) h12
    _ = (flip bind Sstep)^[3 * c + y₁ + 6 * y₂ + 27] (some c13) := by
          rw [show 3 * c + y₁ + 6 * y₂ + 28 = (3 * c + y₁ + 6 * y₂ + 27) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[3 * c + y₁ + 6 * y₂ + 27] x) h13
    _ = (flip bind Sstep)^[2 * c + y₁ + 6 * y₂ + 26] (some c14) := by
          rw [show 3 * c + y₁ + 6 * y₂ + 27 = (2 * c + y₁ + 6 * y₂ + 26) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 6 * y₂ + 26] x) h14
    _ = (flip bind Sstep)^[2 * c + y₁ + 6 * y₂ + 25] (some c15) := by
          rw [show 2 * c + y₁ + 6 * y₂ + 26 = (2 * c + y₁ + 6 * y₂ + 25) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 6 * y₂ + 25] x) h15
    _ = (flip bind Sstep)^[2 * c + y₁ + 5 * y₂ + 23] (some c16) := by
          rw [show 2 * c + y₁ + 6 * y₂ + 25 = (2 * c + y₁ + 5 * y₂ + 23) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 5 * y₂ + 23] x) h16
    _ = (flip bind Sstep)^[2 * c + y₁ + 5 * y₂ + 22] (some c17) := by
          rw [show 2 * c + y₁ + 5 * y₂ + 23 = (2 * c + y₁ + 5 * y₂ + 22) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 5 * y₂ + 22] x) h17
    _ = (flip bind Sstep)^[2 * c + y₁ + 4 * y₂ + 20] (some c18) := by
          rw [show 2 * c + y₁ + 5 * y₂ + 22 = (2 * c + y₁ + 4 * y₂ + 20) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 4 * y₂ + 20] x) h18
    _ = (flip bind Sstep)^[2 * c + y₁ + 4 * y₂ + 19] (some c19) := by
          rw [show 2 * c + y₁ + 4 * y₂ + 20 = (2 * c + y₁ + 4 * y₂ + 19) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 4 * y₂ + 19] x) h19
    _ = (flip bind Sstep)^[2 * c + y₁ + 3 * y₂ + 17] (some c20) := by
          rw [show 2 * c + y₁ + 4 * y₂ + 19 = (2 * c + y₁ + 3 * y₂ + 17) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 3 * y₂ + 17] x) h20
    _ = (flip bind Sstep)^[2 * c + y₁ + 3 * y₂ + 16] (some c21) := by
          rw [show 2 * c + y₁ + 3 * y₂ + 17 = (2 * c + y₁ + 3 * y₂ + 16) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 3 * y₂ + 16] x) h21
    _ = (flip bind Sstep)^[2 * c + y₁ + 2 * y₂ + 13] (some c22) := by
          rw [show 2 * c + y₁ + 3 * y₂ + 16 = (2 * c + y₁ + 2 * y₂ + 13) + (y₂ + 3) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 2 * y₂ + 13] x) h22
    _ = (flip bind Sstep)^[2 * c + y₁ + 2 * y₂ + 12] (some c23) := by
          rw [show 2 * c + y₁ + 2 * y₂ + 13 = (2 * c + y₁ + 2 * y₂ + 12) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₁ + 2 * y₂ + 12] x) h23
    _ = (flip bind Sstep)^[2 * c + 2 * y₂ + 10] (some c24) := by
          rw [show 2 * c + y₁ + 2 * y₂ + 12 = (2 * c + 2 * y₂ + 10) + (y₁ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2 * y₂ + 10] x) h24
    _ = (flip bind Sstep)^[2 * c + 2 * y₂ + 9] (some c25) := by
          rw [show 2 * c + 2 * y₂ + 10 = (2 * c + 2 * y₂ + 9) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2 * y₂ + 9] x) h25
    _ = (flip bind Sstep)^[2 * c + y₂ + 7] (some c26) := by
          rw [show 2 * c + 2 * y₂ + 9 = (2 * c + y₂ + 7) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₂ + 7] x) h26
    _ = (flip bind Sstep)^[2 * c + y₂ + 6] (some c27) := by
          rw [show 2 * c + y₂ + 7 = (2 * c + y₂ + 6) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + y₂ + 6] x) h27
    _ = (flip bind Sstep)^[2 * c + 4] (some c28) := by
          rw [show 2 * c + y₂ + 6 = (2 * c + 4) + (y₂ + 2) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h28
    _ = (flip bind Sstep)^[2 * c + 3] (some c29) := by
          rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h29
    _ = (flip bind Sstep)^[c + 2] (some c30) := by
          rw [show 2 * c + 3 = (c + 2) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + 2] x) h30
    _ = (flip bind Sstep)^[c + 1] (some c31) := by
          rw [show c + 2 = (c + 1) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h31
    _ = some c32 := by
          rw [show c + 1 = 0 + (c + 1) by omega]
          rw [Function.iterate_add]
          simpa using h32
    _ = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF (orClauses c y₁ y₂)).reverse ++ O) U⟩ : (mach).Cfg) := by
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk, c32, V17]
            rw [encCNF_orClauses_reverse]
            rw [encClause_three_reverse (Literal.pos y₁) (Literal.pos y₂) (Literal.neg c)]
            rw [encClause_two_reverse (Literal.pos c) (Literal.neg y₂)]
            rw [encClause_two_reverse (Literal.pos c) (Literal.neg y₁)]
            simp [O1, O2, O3, O4, O5, O6, O7, O8, O9, O10, O11, O12, O13, O14, O15,
              encLit_reverse, encLit, litSym, litIndex, List.append_assoc, List.cons_append,
              List.replicate_succ, replicate_append_one]

end TM3CNF

end Turing

end Chapter34

end CLRS
