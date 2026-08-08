import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat

/-!
# SAT → 3-CNF-SAT reduction machine

The TM2 machine computing `encCNF (to3CNF_len (decode x) x.length)` for
`x : List FormulaSym`.  It counts the input length, then does a recursive
descent over the prefix-polish formula, emitting the Tseitin clause templates
with auxiliary variables allocated from the input length.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

/-- The machine tapes. -/
inductive K : Type
  | inK | temp | cnt | val | frm | scr | o | out
deriving DecidableEq, Fintype, Inhabited

/-- A continuation frame: an operator waiting for its children. -/
inductive Frame : Type
  | top
  | not
  | and₁ | and₂
  | or₁ | or₂
  | iff₁ | iff₂
deriving DecidableEq, Fintype, Inhabited

/-- The alphabet of each tape.  `val` holds value variables as runs of `true`s
followed by a `false` separator (index `y` is `y + 1` `true`s). -/
abbrev Γk : K → Type
  | K.inK => FormulaSym
  | K.temp => FormulaSym
  | K.cnt => Unit
  | K.val => Bool
  | K.frm => Frame
  | K.scr => Unit
  | K.o => CNFSym
  | K.out => CNFSym

/-- A move/restore operation: emit an auxiliary reference, build a value
variable, or emit/pop a value-variable reference. -/
inductive Op : Type
  | auxEmit | makeVal | varEmit | varPop
deriving DecidableEq, Fintype, Inhabited

/-- The program labels. -/
inductive Label : Type
  | count | reorder | done
  | rd | rdVar | pv | reduce | const | constFalse | constEmit | constMake
  | emitNot | not₂ | not₃ | not₄ | not₅
  | emitAnd | and₂ | and₃ | and₄ | and₅ | and₆ | and₇ | and₈ | and₉ | and₁₀ | and₁₁ | and₁₂
  | emitOr | or₂ | or₃ | or₄ | or₅ | or₆ | or₇ | or₈ | or₉ | or₁₀ | or₁₁ | or₁₂
  | emitIff | iff₂ | iff₃ | iff₄ | iff₅ | iff₆ | iff₇ | iff₈ | iff₉ | iff₁₀
    | iff₁₁ | iff₁₂ | iff₁₃ | iff₁₄ | iff₁₅ | iff₁₆ | iff₁₇ | iff₁₈ | iff₁₉ | iff₂₀ | iff₂₁
  | emitTrue | emitTrueRestore
  | moveCnt | restoreCnt | moveVal | restoreVal | parkVal | unparkVal
  | copyOut
deriving DecidableEq, Fintype, Inhabited

/-- The machine states. -/
inductive St : Type
  | init | done
  | count | reorder
  | rd (s : FormulaSym)
  | pv | reduce
  | and₁Done | or₁Done | iff₁Done
  | mv (go : Label) (k : Op) | rs (go : Label) (k : Op)
  | rsDone (go : Label) (k : Op)
  | emitNot | emitAnd | emitOr | emitIff
  | emitTrue
  | constLoop
  | copySym (s : CNFSym)
deriving DecidableEq, Fintype, Inhabited

/-- The full stack contents at the start of a phase. -/
abbrev stk (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) : ∀ k : K, List (Γk k) :=
  fun k => match k with
  | K.inK => inp | K.temp => T | K.cnt => List.replicate c ()
  | K.val => V | K.frm => F | K.scr => S
  | K.o => O | K.out => U

def prog : Label → Turing.TM2.Stmt Γk Label St
  | Label.count =>
      Turing.TM2.Stmt.pop K.inK (fun _ x => match x with
          | some s => St.rd s
          | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rd _ => true | _ => false)
          (Turing.TM2.Stmt.push K.temp (fun v => match v with | St.rd s => s | _ => default)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ()) (Turing.TM2.Stmt.goto (fun _ => Label.count))))
          (Turing.TM2.Stmt.goto (fun _ => Label.reorder)))
  | Label.reorder =>
      Turing.TM2.Stmt.pop K.temp (fun _ x => match x with
          | some s => St.rd s
          | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rd _ => true | _ => false)
          (Turing.TM2.Stmt.push K.inK (fun v => match v with | St.rd s => s | _ => default)
            (Turing.TM2.Stmt.goto (fun _ => Label.reorder)))
          (Turing.TM2.Stmt.goto (fun _ => Label.done)))
  | Label.done => Turing.TM2.Stmt.halt
  | Label.rd =>
      Turing.TM2.Stmt.pop K.inK (fun _ x => match x with
          | some s => St.rd s
          | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rd (FormulaSym.lit _) => true | _ => false)
          (Turing.TM2.Stmt.goto (fun _ => Label.const))
          (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.varMark => true | _ => false)
            (Turing.TM2.Stmt.goto (fun _ => Label.pv))
            (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.notMark => true | _ => false)
              (Turing.TM2.Stmt.push K.frm (fun _ => Frame.not)
                (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
              (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.andMark => true | _ => false)
                (Turing.TM2.Stmt.push K.frm (fun _ => Frame.and₁)
                  (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
                (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.orMark => true | _ => false)
                  (Turing.TM2.Stmt.push K.frm (fun _ => Frame.or₁)
                    (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
                  (Turing.TM2.Stmt.push K.frm (fun _ => Frame.iff₁)
                    (Turing.TM2.Stmt.goto (fun _ => Label.rd))))))))
  | Label.pv =>
      Turing.TM2.Stmt.pop K.inK (fun _ x => match x with
          | some s => St.rd s
          | none => St.reduce)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.endMark => true | _ => false)
          (Turing.TM2.Stmt.push K.val (fun _ => true) (Turing.TM2.Stmt.goto (fun _ => Label.pv)))
          (Turing.TM2.Stmt.push K.val (fun _ => false)
            (Turing.TM2.Stmt.push K.inK (fun v => match v with | St.rd s => s | _ => default)
              (Turing.TM2.Stmt.goto (fun _ => Label.reduce)))))
  | Label.reduce =>
      Turing.TM2.Stmt.pop K.frm (fun v x => match x with
          | some Frame.top => St.emitTrue
          | some Frame.not => St.emitNot
          | some Frame.and₁ => St.and₁Done
          | some Frame.and₂ => St.emitAnd
          | some Frame.or₁ => St.or₁Done
          | some Frame.or₂ => St.emitOr
          | some Frame.iff₁ => St.iff₁Done
          | some Frame.iff₂ => St.emitIff
          | none => St.emitTrue)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.emitTrue => true | _ => false)
          (Turing.TM2.Stmt.goto (fun _ => Label.emitTrue))
          (Turing.TM2.Stmt.branch (fun v => match v with | St.emitNot => true | _ => false)
            (Turing.TM2.Stmt.goto (fun _ => Label.emitNot))
            (Turing.TM2.Stmt.branch (fun v => match v with | St.emitAnd => true | _ => false)
              (Turing.TM2.Stmt.goto (fun _ => Label.emitAnd))
              (Turing.TM2.Stmt.branch (fun v => match v with | St.emitOr => true | _ => false)
                (Turing.TM2.Stmt.goto (fun _ => Label.emitOr))
                (Turing.TM2.Stmt.branch (fun v => match v with | St.emitIff => true | _ => false)
                  (Turing.TM2.Stmt.goto (fun _ => Label.emitIff))
                  (Turing.TM2.Stmt.branch (fun v => match v with | St.and₁Done => true | _ => false)
                    (Turing.TM2.Stmt.push K.frm (fun _ => Frame.and₂)
                      (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
                    (Turing.TM2.Stmt.branch (fun v => match v with | St.or₁Done => true | _ => false)
                      (Turing.TM2.Stmt.push K.frm (fun _ => Frame.or₂)
                        (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
                      (Turing.TM2.Stmt.push K.frm (fun _ => Frame.iff₂)
                        (Turing.TM2.Stmt.goto (fun _ => Label.rd))))))))))
  | Label.const =>
      Turing.TM2.Stmt.branch (fun v => match v with | St.rd (FormulaSym.lit true) => true | _ => false)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
            (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.constEmit)))))
        (Turing.TM2.Stmt.goto (fun _ => Label.constFalse))
  | Label.constFalse =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.goto (fun _ => Label.constEmit))))
  | Label.constEmit =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with
          | some _ => St.constLoop
          | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.constLoop => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
            (Turing.TM2.Stmt.push K.scr (fun _ => ())
              (Turing.TM2.Stmt.goto (fun _ => Label.constEmit))))
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
            (Turing.TM2.Stmt.goto (fun _ => Label.constMake))))
  | Label.constMake =>
      Turing.TM2.Stmt.pop K.scr (fun _ x => match x with
          | some _ => St.constLoop
          | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.constLoop => true | _ => false)
          (Turing.TM2.Stmt.push K.val (fun _ => true)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ())
              (Turing.TM2.Stmt.goto (fun _ => Label.constMake))))
          (Turing.TM2.Stmt.push K.val (fun _ => true)
            (Turing.TM2.Stmt.push K.cnt (fun _ => ())
              (Turing.TM2.Stmt.push K.val (fun _ => false)
                (Turing.TM2.Stmt.goto (fun _ => Label.reduce)))))
  | Label.emitTrue =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.pop K.val (fun _ x => match x with | some _ => St.emitTrue | none => St.emitTrue)
              (Turing.TM2.Stmt.goto (fun _ => Label.emitTrueRestore)))))
  | Label.emitTrueRestore =>
      Turing.TM2.Stmt.pop K.val (fun _ x => match x with
          | some true => St.emitTrue
          | some false => St.done
          | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.emitTrue => true | _ => false)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
            (Turing.TM2.Stmt.goto (fun _ => Label.emitTrueRestore)))
          (Turing.TM2.Stmt.goto (fun _ => Label.copyOut)))
  | Label.emitNot => Turing.TM2.Stmt.halt
  | Label.emitAnd => Turing.TM2.Stmt.halt
  | Label.emitOr => Turing.TM2.Stmt.halt
  | Label.emitIff => Turing.TM2.Stmt.halt
  | _ => Turing.TM2.Stmt.halt

abbrev mach : FinTM2 :=
  @FinTM2.mk K (by infer_instance) (by infer_instance) K.inK K.out Γk Label Label.count
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

/-- reorder phase: move all symbols from `temp` back to `in` (restoring the order) -/
lemma reorder_phase_aux (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[T.length + 1]
        (some (⟨some Label.reorder, St.rd default, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.done, St.done, stk (T.reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
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
        = some (⟨some Label.done, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (inp := s :: inp)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.reorder, St.rd default, stk (s :: inp) rest c V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.done, St.done, stk (rest.reverse ++ (s :: inp)) [] c V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.done, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- Reading a `notMark` pushes a `not` continuation frame. -/
lemma rd_not_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, St.rd FormulaSym.notMark, stk (FormulaSym.notMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.rd FormulaSym.notMark, stk rest T c V (Frame.not :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading an `andMark` pushes an `and₁` continuation frame. -/
lemma rd_and_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, St.rd FormulaSym.andMark, stk (FormulaSym.andMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.rd FormulaSym.andMark, stk rest T c V (Frame.and₁ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading an `orMark` pushes an `or₁` continuation frame. -/
lemma rd_or_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, St.rd FormulaSym.orMark, stk (FormulaSym.orMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.rd FormulaSym.orMark, stk rest T c V (Frame.or₁ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading an `iffMark` pushes an `iff₁` continuation frame. -/
lemma rd_iff_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, St.rd FormulaSym.iffMark, stk (FormulaSym.iffMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.rd FormulaSym.iffMark, stk rest T c V (Frame.iff₁ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading a `varMark` enters the variable-index phase. -/
lemma rd_var_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, St.rd FormulaSym.varMark, stk (FormulaSym.varMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.pv, St.rd FormulaSym.varMark, stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- Reading an `endMark` in the variable phase transfers it to `val` as a unit. -/
lemma pv_end_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.pv, St.rd FormulaSym.endMark, stk (FormulaSym.endMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (true :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- A non-`endMark` ends the variable phase: push a `false` separator, restore
the symbol to the input, and reduce. -/
lemma pv_done_step (s : FormulaSym) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hs : s ≠ FormulaSym.endMark) :
    Sstep (⟨some Label.pv, St.rd s, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.reduce, St.rd s, stk (s :: rest) T c (false :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep, hs]
  · simp [prog, Sstep, hs]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, hs]

-- ============================================================
-- emitTrue: the root unit clause `[[pos y]]`
-- ============================================================

/-- `emitTrue`: push the clause and literal markers, then pop the root
value-variable's `false` separator, entering the index-emission loop. -/
lemma emitTrue_push (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitTrue, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c V' F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `emitTrueRestore`: a `true` in the root value-variable's run emits one
`endMark` and continues. -/
lemma emitTrueRestore_true (v : St) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitTrueRestore, v, stk inp T c (true :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c V' F S (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `emitTrueRestore`: an empty `val` ends the run; the emission moves to
`copyOut`. -/
lemma emitTrueRestore_empty (v : St) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitTrueRestore, v, stk inp T c [] F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.copyOut, St.done, stk inp T c [] F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `replicate k a ++ [a]` is the `k + 1`-fold repetition. -/
lemma replicate_append_one {α : Type} (k : Nat) (a : α) :
    List.replicate k a ++ [a] = List.replicate (k + 1) a := by
  induction k with
  | zero => simp
  | succ k ih =>
      simpa [List.replicate_succ, List.cons_append] using ih

/-- The `emitTrueRestore` loop: popping `k` `true`s emits `k` `endMark`s and
finishes at `copyOut`. -/
lemma emitTrueRestore_loop (k : Nat) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c (List.replicate k true) F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.copyOut, St.done, stk inp T c [] F S (List.replicate k CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction k generalizing O with
  | zero =>
      have h := emitTrueRestore_empty St.emitTrue inp T c F S O U
      change (flip bind Sstep) (some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c [] F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.done, stk inp T c [] F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := emitTrueRestore_true St.emitTrue inp T c (List.replicate k true) F S O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c (true :: List.replicate k true) F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.copyOut, St.done, stk inp T c [] F S (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[k + 1]
            (some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c (List.replicate k true) F S
              (CNFSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.copyOut, St.done, stk inp T c [] F S
              (List.replicate k CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.copyOut, St.done, stk inp T c [] F S
            (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              rw [show CNFSym.endMark :: O = [CNFSym.endMark] ++ O by simp [List.cons_append]]
              rw [← List.append_assoc]
              rw [replicate_append_one]

/-- `emitTrue` phase: the root value variable `y` (stored as `y + 1` `true`s
below a `false` separator) is emitted as the unit clause `[[pos y]]`, leaving
the encoded clause (reversed) on `o`. -/
lemma emitTrue_phase (y : Nat) (v : St) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[(y + 1) + 2]
        (some (⟨some Label.emitTrue, v, stk inp T c (false :: List.replicate (y + 1) true) F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.copyOut, St.done, stk inp T c [] F S ((encCNF [[Literal.pos y]]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have hpush := emitTrue_push v inp T c false (List.replicate (y + 1) true) F S O U
  rw [show (y + 1) + 2 = ((y + 1) + 1) + 1 by omega]
  rw [Function.iterate_succ_apply]
  change (flip bind Sstep)^[(y + 1) + 1]
      (Sstep (⟨some Label.emitTrue, v, stk inp T c (false :: List.replicate (y + 1) true) F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.copyOut, St.done, stk inp T c [] F S ((encCNF [[Literal.pos y]]).reverse ++ O) U⟩ : (mach).Cfg)
  rw [hpush]
  have hloop := emitTrueRestore_loop (y + 1) inp T c F S
      (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U
  calc
    (flip bind Sstep)^[(y + 1) + 1]
        (some (⟨some Label.emitTrueRestore, St.emitTrue, stk inp T c (List.replicate (y + 1) true) F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg))
      = some (⟨some Label.copyOut, St.done, stk inp T c [] F S
          (List.replicate (y + 1) CNFSym.endMark ++
            (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := hloop
    _ = some (⟨some Label.copyOut, St.done, stk inp T c [] F S
        ((encCNF [[Literal.pos y]]).reverse ++ O) U⟩ : (mach).Cfg) := by
        apply congrArg some
        apply Turing.TM2Comp.Cfg_ext
        · rfl
        · rfl
        · funext kk
          cases kk <;> try simp [stk]
          rw [show CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O =
              [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] ++ O by rfl]
          have hrev : (encCNF [[Literal.pos y]]).reverse =
              List.replicate (y + 1) CNFSym.endMark ++
                [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] := by
            simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
          rw [hrev]
          rw [List.append_assoc]

end TM3CNF

end Turing

end Chapter34

end CLRS
