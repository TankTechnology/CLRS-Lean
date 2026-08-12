import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B3_ConstEmit

/-!
# Dev B4: parking and unparking value variables

The generic `parkVal`/`unparkVal` temp-tape subroutines that move a value variable to `temp` and back.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- park/unpark value variables on `temp`
--
-- The `val` tape is a single stack, so a binary operator's two child value
-- variables cannot both be inspected while the output order requires emitting
-- the first child's run before the second's.  `parkVal`/`unparkVal` move a
-- value variable off `val` onto the idle `temp` tape (as `lit false` followed
-- by `y + 1` `lit true`s) and back again.
-- ============================================================

/-- `parkVal`: pop the top of `val` (the `false` separator of the value
variable being parked) onto `temp` as a `lit false`, entering the run loop. -/
lemma parkVal_step (go : Label) (b : Bool) (V' : List Bool) (inp T : List FormulaSym)
    (c : Nat) (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.parkVal, St.mv go Op.park, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkRest, St.mv go Op.park, stk inp (FormulaSym.lit false :: T) c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `parkRest`: a `true` in the run is popped onto `temp` as a `lit true`,
looping back to `parkRest`. -/
lemma parkRest_true_step (go : Label) (V' : List Bool) (inp T : List FormulaSym)
    (c : Nat) (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.parkRest, St.mv go Op.park, stk inp T c (true :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.parkRest, St.mv go Op.park, stk inp (FormulaSym.lit true :: T) c V' F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `parkRest`: a non-`true` head (`b ≠ true`, i.e. the next value variable's
`false` separator) stops the run, routing to `go` without consuming. -/
lemma parkRest_stop (go : Label) (b : Bool) (V' : List Bool) (inp T : List FormulaSym)
    (c : Nat) (F : List Frame) (S : List Unit) (O U : List CNFSym) (hb : b ≠ true) :
    Sstep (⟨some Label.parkRest, St.mv go Op.park, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.park, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg) := by
  cases b with
  | true => simp at hb
  | false =>
      apply congrArg some
      apply Turing.TM2Comp.Cfg_ext
      · simp [prog, Sstep]
      · simp [prog, Sstep]
      · funext k
        cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `parkRest`: an empty `val` stops the run, routing to `go`. -/
lemma parkRest_empty (go : Label) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.parkRest, St.mv go Op.park, stk inp T c [] F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.park, stk inp T c [] F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `parkRest`: the run stops at any non-`true` remainder. -/
lemma parkRest_end (go : Label) (V : List Bool) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hV : V.head? ≠ some true) :
    Sstep (⟨some Label.parkRest, St.mv go Op.park, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.park, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  cases V with
  | nil =>
      exact parkRest_empty go inp T c F S O U
  | cons b V' =>
      have hb : b ≠ true := by
        intro h
        apply hV
        simp [h]
      exact parkRest_stop go b V' inp T c F S O U hb

/-- The `parkRest` loop: `k` `true`s are parked as `k` `lit true`s on `temp`,
ending at `go` when the run stops at a non-`true` head. -/
lemma parkRest_loop (go : Label) (k : Nat) (V : List Bool) (inp T : List FormulaSym)
    (c : Nat) (F : List Frame) (S : List Unit) (O U : List CNFSym)
    (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[k + 1]
      (some (⟨some Label.parkRest, St.mv go Op.park, stk inp T c (List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
    = some (⟨some go, St.rsDone go Op.park, stk inp (List.replicate k (FormulaSym.lit true) ++ T) c V F S O U⟩ : (mach).Cfg) := by
  induction k generalizing T with
  | zero =>
      have h := parkRest_end go V inp T c F S O U hV
      change (flip bind Sstep) (some (⟨some Label.parkRest, St.mv go Op.park, stk inp T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.park, stk inp T c V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := parkRest_true_step go (List.replicate k true ++ V) inp T c F S O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.parkRest, St.mv go Op.park, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.park, stk inp (List.replicate (Nat.succ k) (FormulaSym.lit true) ++ T) c V F S O U⟩ : (mach).Cfg)
      have hih := ih (T := FormulaSym.lit true :: T)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.parkRest, St.mv go Op.park, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.parkRest, St.mv go Op.park, stk inp (FormulaSym.lit true :: T) c (List.replicate k true ++ V) F S O U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.park, stk inp
            (List.replicate k (FormulaSym.lit true) ++ (FormulaSym.lit true :: T)) c V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.park, stk inp
            (List.replicate (Nat.succ k) (FormulaSym.lit true) ++ T) c V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              rw [show FormulaSym.lit true :: T = [FormulaSym.lit true] ++ T by simp [List.cons_append]]
              rw [← List.append_assoc]
              rw [replicate_append_one]

/-- The `parkVal` phase: park the value variable on top of `val` (index `y`,
stored as `false :: replicate (y + 1) true`) onto `temp` as `y + 1` `lit true`s
below a `lit false`, routing to `go`. -/
lemma parkVal_phase (go : Label) (y : Nat) (V : List Bool) (inp T : List FormulaSym)
    (c : Nat) (F : List Frame) (S : List Unit) (O U : List CNFSym)
    (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[y + 3]
      (some (⟨some Label.parkVal, St.mv go Op.park, stk inp T c (false :: List.replicate (y + 1) true ++ V) F S O U⟩ : (mach).Cfg))
    = some (⟨some go, St.rsDone go Op.park, stk inp
        (List.replicate (y + 1) (FormulaSym.lit true) ++ ([FormulaSym.lit false] ++ T)) c V F S O U⟩ : (mach).Cfg) := by
  have hstep := parkVal_step go false (List.replicate (y + 1) true ++ V) inp T c F S O U
  have hloop := parkRest_loop go (y + 1) V inp (FormulaSym.lit false :: T) c F S O U hV
  rw [show y + 3 = Nat.succ (y + 2) by omega]
  rw [Function.iterate_succ_apply]
  change (flip bind Sstep)^[y + 2]
      (Sstep (⟨some Label.parkVal, St.mv go Op.park, stk inp T c (false :: List.replicate (y + 1) true ++ V) F S O U⟩ : (mach).Cfg))
    = some (⟨some go, St.rsDone go Op.park, stk inp
        (List.replicate (y + 1) (FormulaSym.lit true) ++ ([FormulaSym.lit false] ++ T)) c V F S O U⟩ : (mach).Cfg)
  calc
    (flip bind Sstep)^[y + 2]
        (Sstep (⟨some Label.parkVal, St.mv go Op.park, stk inp T c (false :: List.replicate (y + 1) true ++ V) F S O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[y + 2]
          (some (⟨some Label.parkRest, St.mv go Op.park, stk inp (FormulaSym.lit false :: T) c
            (List.replicate (y + 1) true ++ V) F S O U⟩ : (mach).Cfg)) := by
          exact congrArg (fun x => (flip bind Sstep)^[y + 2] x) hstep
    _ = some (⟨some go, St.rsDone go Op.park, stk inp
        (List.replicate (y + 1) (FormulaSym.lit true) ++ ([FormulaSym.lit false] ++ T)) c V F S O U⟩ : (mach).Cfg) := by
        rw [show y + 2 = (y + 1) + 1 by omega]
        exact hloop

/-- `unparkVal`: a `lit true` on `temp` is popped back onto `val` as a `true`,
looping back to `unparkVal`. -/
lemma unparkVal_true_step (go : Label) (V : List Bool) (inp T' : List FormulaSym)
    (c : Nat) (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp (FormulaSym.lit true :: T') c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp T' c (true :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `unparkVal`: the closing `lit false` on `temp` is popped back onto `val` as
a `false`, routing to `go`. -/
lemma unparkVal_final (go : Label) (V : List Bool) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp (FormulaSym.lit false :: T) c V F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.unpark, stk inp T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `unparkVal` run loop: `k` `lit true`s become `k` `true`s on `val`. -/
lemma unparkVal_loop (go : Label) (k : Nat) (V : List Bool) (inp T : List FormulaSym)
    (c : Nat) (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[k]
      (some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp (List.replicate k (FormulaSym.lit true) ++ T) c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp T c (List.replicate k true ++ V) F S O U⟩ : (mach).Cfg) := by
  induction k generalizing V T with
  | zero =>
      rfl
  | succ k ih =>
      have h := unparkVal_true_step go V inp (List.replicate k (FormulaSym.lit true) ++ T) c F S O U
      change (flip bind Sstep)^[Nat.succ k]
          (some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp
            (List.replicate (Nat.succ k) (FormulaSym.lit true) ++ T) c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp T c
            (List.replicate (Nat.succ k) true ++ V) F S O U⟩ : (mach).Cfg)
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k]
          (Sstep (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp
            (FormulaSym.lit true :: List.replicate k (FormulaSym.lit true) ++ T) c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp T c
            (List.replicate (Nat.succ k) true ++ V) F S O U⟩ : (mach).Cfg)
      have hih := ih (V := true :: V)
      calc
        (flip bind Sstep)^[k]
            (Sstep (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp
              (FormulaSym.lit true :: List.replicate k (FormulaSym.lit true) ++ T) c V F S O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k]
              (some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp
                (List.replicate k (FormulaSym.lit true) ++ T) c (true :: V) F S O U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k] x) h
        _ = some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp T c
            (List.replicate k true ++ (true :: V)) F S O U⟩ : (mach).Cfg) := hih T
        _ = some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp T c
            (List.replicate (Nat.succ k) true ++ V) F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              have hval : List.replicate k true ++ (true :: V) =
                  List.replicate (Nat.succ k) true ++ V := by
                calc
                  List.replicate k true ++ (true :: V)
                    = List.replicate k true ++ ([true] ++ V) := by
                        rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
                  _ = (List.replicate k true ++ [true]) ++ V := by rw [← List.append_assoc]
                  _ = List.replicate (k + 1) true ++ V := by rw [replicate_append_one]
                  _ = List.replicate (Nat.succ k) true ++ V := by rw [show k + 1 = Nat.succ k by omega]
              simp [hval]

/-- The `unparkVal` phase: restore the value variable parked on `temp` (index
`y`) back onto `val` as `false :: replicate (y + 1) true`, routing to `go`. -/
lemma unparkVal_phase (go : Label) (y : Nat) (V : List Bool) (inp T : List FormulaSym)
    (c : Nat) (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[y + 2]
      (some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp
        (List.replicate (y + 1) (FormulaSym.lit true) ++ ([FormulaSym.lit false] ++ T)) c V F S O U⟩ : (mach).Cfg))
    = some (⟨some go, St.rsDone go Op.unpark, stk inp T c (false :: List.replicate (y + 1) true ++ V) F S O U⟩ : (mach).Cfg) := by
  have hloop := unparkVal_loop go (y + 1) V inp ([FormulaSym.lit false] ++ T) c F S O U
  have hfinal := unparkVal_final go (List.replicate (y + 1) true ++ V) inp T c F S O U
  rw [show y + 2 = Nat.succ (y + 1) by omega]
  rw [Function.iterate_succ_apply']
  calc
    (flip bind Sstep) ((flip bind Sstep)^[y + 1]
        (some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp
          (List.replicate (y + 1) (FormulaSym.lit true) ++ ([FormulaSym.lit false] ++ T)) c V F S O U⟩ : (mach).Cfg)))
      = (flip bind Sstep) (some (⟨some Label.unparkVal, St.rs go Op.unpark, stk inp ([FormulaSym.lit false] ++ T) c
          (List.replicate (y + 1) true ++ V) F S O U⟩ : (mach).Cfg)) :=
          congrArg (flip bind Sstep) hloop
    _ = some (⟨some go, St.rsDone go Op.unpark, stk inp T c
        (false :: List.replicate (y + 1) true ++ V) F S O U⟩ : (mach).Cfg) := hfinal


end TM3CNF

end Turing

end Chapter34

end CLRS
