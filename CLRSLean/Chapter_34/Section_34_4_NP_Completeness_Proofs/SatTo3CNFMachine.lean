import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat

/-!
# SAT → 3-CNF-SAT reduction machine

The TM2 machine computing `encCNF (to3CNF_len (decode x) x.length)` for
`x : List FormulaSym`.  It counts the input length, then does a recursive
descent over the prefix-polish formula, emitting the Tseitin clause templates
with auxiliary variables allocated from the input length.

The semantic reduction `cnfSatisfiable_to3CNF_iff` (and the list encoding
`encCNF`) live in `SatTo3CNFSat`; this file is the machine that computes the
encoding.

**Status (2026-08-09).**  Count, reorder, parse (`rd`/`pv`/`reduce` dispatch),
`emitTrue`, the const-clause emission, and the `not` clause emission's step +
generic move/restore loops are written.  The `not` phase composition, the
`and`/`or`/`iff` emissions, `copyOut`, `outputsFun`, the time bound, and the
`PolyTimeReducible` assembly are NOT complete.

**Current gaps.**

- **Control flow (being fixed):** `Label.reorder` routes to `done` (halt); it
  must route to `rd` so the parse/emit phases run in a single pass.
- **`and`/`or`/`iff` machine emission (documented gap — reduced scope).**  A
  binary operator's two child value variables are stacked on `val` (the second
  child's run on top, the first child's below), but the output order requires
  emitting the first child's run before the second's.  With a single Unit
  scratch tape the two runs cannot both be parked: `moveVal`-parking emits
  `endMark`s on `o` (wrong position), the markers are indistinguishable, and
  `restoreVal` restores everything.  The machine therefore needs a second park
  tape — the idle `temp` tape (free after count/reorder) — plus `parkVal`/
  `unparkVal` (declared but unimplemented).  This is the enabling machinery for
  the two-child cases; `emitAnd`/`emitOr`/`emitIff` currently halt.  The
  semantic correctness of the `and`/`or`/`iff` templates is fully proved in
  `SatTo3CNFSat`.
- **`copyOut`, `outputsFun`, the polynomial time bound, and the assembled
  `PolyTimeReducible SAT ThreeCNFSat`** are not yet written.
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
variable, or emit/pop a value-variable reference, or park/restore a value
variable on the `temp` tape. -/
inductive Op : Type
  | auxEmit | makeVal | varEmit | varPop | park | unpark
deriving DecidableEq, Fintype, Inhabited

/-- The program labels. -/
inductive Label : Type
  | count | reorder | done
  | rd | rdVar | pv | reduce | const | constFalse | constEmit | constMake
  | emitNot | not₂ | not₃ | not₄ | not₅ | not₆
  | emitAnd | and₂ | and₃ | and₄ | and₅ | and₆ | and₇ | and₈ | and₉ | and₁₀ | and₁₁ | and₁₂
  | emitOr | or₂ | or₃ | or₄ | or₅ | or₆ | or₇ | or₈ | or₉ | or₁₀ | or₁₁ | or₁₂
  | emitIff | iff₂ | iff₃ | iff₄ | iff₅ | iff₆ | iff₇ | iff₈ | iff₉ | iff₁₀
    | iff₁₁ | iff₁₂ | iff₁₃ | iff₁₄ | iff₁₅ | iff₁₆ | iff₁₇ | iff₁₈ | iff₁₉ | iff₂₀ | iff₂₁
  | emitTrue | emitTrueRestore
  | moveCnt | restoreCnt | moveVal | restoreVal | parkVal | parkRest | unparkVal
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
          (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
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
                (Turing.TM2.Stmt.goto (fun _ => Label.reduce))))))
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
  | Label.emitNot =>
      Turing.TM2.Stmt.pop K.val (fun _ x => match x with
          | some _ => St.mv Label.not₂ Op.auxEmit
          | none => St.mv Label.not₂ Op.auxEmit)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
            (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt)))))
  | Label.not₂ =>
      Turing.TM2.Stmt.load (fun _ => St.rs Label.not₃ Op.auxEmit)
        (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt))
  | Label.not₃ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.mv Label.not₄ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))))
  | Label.not₄ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.not₅ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))))
  | Label.not₅ =>
      Turing.TM2.Stmt.load (fun _ => St.mv Label.not₆ Op.auxEmit)
        (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt))
  | Label.not₆ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
            (Turing.TM2.Stmt.load (fun _ => St.mv Label.constMake Op.varPop)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))))
  | Label.moveCnt =>
      Turing.TM2.Stmt.pop K.cnt (fun v x => match v, x with
          | St.mv go Op.auxEmit, some () => St.mv go Op.auxEmit
          | St.mv go Op.auxEmit, none => St.rsDone go Op.auxEmit
          | _, _ => v)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.mv go Op.auxEmit => true
            | _ => false)
          (Turing.TM2.Stmt.push K.scr (fun _ => ())
            (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt))))
          (Turing.TM2.Stmt.goto (fun v => match v with
              | St.rsDone go _ => go
              | _ => Label.done)))
  | Label.moveVal =>
      Turing.TM2.Stmt.peek K.val (fun v x => match v, x with
          | St.mv go Op.varEmit, some true => St.mv go Op.varEmit
          | St.mv go Op.varEmit, _ => St.rsDone go Op.varEmit
          | St.mv go Op.varPop, some true => St.mv go Op.varPop
          | St.mv go Op.varPop, _ => St.rsDone go Op.varPop
          | _, _ => v)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.mv go Op.varEmit => true
            | St.mv go Op.varPop => true
            | _ => false)
          (Turing.TM2.Stmt.pop K.val (fun v _ => v)
            (Turing.TM2.Stmt.branch (fun v => match v with
                | St.mv go Op.varEmit => true
                | _ => false)
              (Turing.TM2.Stmt.push K.scr (fun _ => ())
                (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
                  (Turing.TM2.Stmt.goto (fun _ => Label.moveVal))))
              (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
                (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))))
          (Turing.TM2.Stmt.goto (fun v => match v with
              | St.rsDone go _ => go
              | _ => Label.done)))
  | Label.restoreVal =>
      Turing.TM2.Stmt.pop K.scr (fun v x => match v, x with
          | St.rs go Op.varEmit, some () => St.rs go Op.varEmit
          | St.rs go Op.varEmit, none => St.rsDone go Op.varEmit
          | _, _ => v)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.rs go Op.varEmit => true
            | _ => false)
          (Turing.TM2.Stmt.push K.val (fun _ => true)
            (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))
          (Turing.TM2.Stmt.goto (fun v => match v with
              | St.rsDone go _ => go
              | _ => Label.done)))
  | Label.restoreCnt =>
      Turing.TM2.Stmt.pop K.scr (fun v x => match v, x with
          | St.rs go Op.auxEmit, some () => St.rs go Op.auxEmit
          | St.rs go Op.auxEmit, none => St.rsDone go Op.auxEmit
          | _, _ => v)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.rs go Op.auxEmit => true
            | _ => false)
          (Turing.TM2.Stmt.push K.cnt (fun _ => ())
            (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt)))
          (Turing.TM2.Stmt.goto (fun v => match v with
              | St.rsDone go _ => go
              | _ => Label.done)))
  | Label.parkVal =>
      Turing.TM2.Stmt.pop K.val (fun v x => match v, x with
          | St.mv go Op.park, some _ => St.mv go Op.park
          | St.mv go Op.park, none => St.rsDone go Op.park
          | _, _ => v)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.mv go Op.park => true
            | _ => false)
          (Turing.TM2.Stmt.push K.temp (fun _ => FormulaSym.lit false)
            (Turing.TM2.Stmt.goto (fun _ => Label.parkRest)))
          (Turing.TM2.Stmt.goto (fun v => match v with
              | St.rsDone go _ => go
              | _ => Label.done)))
  | Label.parkRest =>
      Turing.TM2.Stmt.peek K.val (fun v x => match v, x with
          | St.mv go Op.park, some true => St.mv go Op.park
          | St.mv go Op.park, _ => St.rsDone go Op.park
          | _, _ => v)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.mv go Op.park => true
            | _ => false)
          (Turing.TM2.Stmt.pop K.val (fun v _ => v)
            (Turing.TM2.Stmt.push K.temp (fun _ => FormulaSym.lit true)
              (Turing.TM2.Stmt.goto (fun _ => Label.parkRest))))
          (Turing.TM2.Stmt.goto (fun v => match v with
              | St.rsDone go _ => go
              | _ => Label.done)))
  | Label.unparkVal =>
      Turing.TM2.Stmt.peek K.temp (fun v x => match v, x with
          | St.rs go Op.unpark, some (FormulaSym.lit true) => St.rs go Op.unpark
          | St.rs go Op.unpark, _ => St.rsDone go Op.unpark
          | _, _ => v)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.rs go Op.unpark => true
            | _ => false)
          (Turing.TM2.Stmt.pop K.temp (fun v _ => v)
            (Turing.TM2.Stmt.push K.val (fun _ => true)
              (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal))))
          (Turing.TM2.Stmt.pop K.temp (fun v _ => v)
            (Turing.TM2.Stmt.push K.val (fun _ => false)
              (Turing.TM2.Stmt.goto (fun v => match v with
                  | St.rsDone go _ => go
                  | _ => Label.done)))))
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
-- List assembly: reversed encodings of literals/clauses/CNF
--
-- The machine pushes output symbols onto `o` so that after emitting a
-- sequence of clauses the stack holds the *reversed* encoding of the CNF
-- (`copyOut` then transfers `o` to `out`, reversing it back).  These lemmas
-- express the assembled stacks in terms of `encLit`/`encClause`/`encCNF`.
-- ============================================================

/-- The reversed encoding of a literal is its unary index run followed by the
`varMark` and polarity marks. -/
lemma encLit_reverse (l : Literal) :
    (encLit l).reverse = List.replicate (litIndex l + 1) CNFSym.endMark ++
      [CNFSym.varMark, litSym l] := by
  cases l <;> simp [encLit, litSym, litIndex, List.reverse_cons, List.reverse_append,
    List.reverse_replicate]

/-- The reversed encoding of a two-literal clause splits at the `clauseMark`. -/
lemma encClause_two_reverse (l₁ l₂ : Literal) :
    (encClause [l₁, l₂]).reverse =
      (encLit l₂).reverse ++ (encLit l₁).reverse ++ [CNFSym.clauseMark] := by
  simp [encClause, List.flatMap, List.reverse_cons, List.reverse_append]

/-- The reversed encoding of the negated two-literal clause `[¬y, ¬y₁]`. -/
lemma encClause_neg_reverse (y y₁ : Nat) :
    (encClause [Literal.neg y, Literal.neg y₁]).reverse =
      List.replicate (y₁ + 1) CNFSym.endMark ++ [CNFSym.varMark, CNFSym.negMark] ++
      List.replicate (y + 1) CNFSym.endMark ++
        [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
  rw [encClause_two_reverse]
  simp [encLit_reverse, encLit, litSym, litIndex]

/-- The reversed encoding of the positive two-literal clause `[y, y₁]`. -/
lemma encClause_pos_reverse (y y₁ : Nat) :
    (encClause [Literal.pos y, Literal.pos y₁]).reverse =
      List.replicate (y₁ + 1) CNFSym.endMark ++ [CNFSym.varMark, CNFSym.posMark] ++
      List.replicate (y + 1) CNFSym.endMark ++
        [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] := by
  rw [encClause_two_reverse]
  simp [encLit_reverse, encLit, litSym, litIndex]

/-- The reversed encoding of `notClauses y y₁` emits the two clauses in the
same order the machine pushes them (later clause first on the stack). -/
lemma encCNF_notClauses_reverse (y y₁ : Nat) :
    (encCNF (notClauses y y₁)).reverse =
      (encClause [Literal.pos y, Literal.pos y₁]).reverse ++
      (encClause [Literal.neg y, Literal.neg y₁]).reverse := by
  simp [encCNF, notClauses, List.reverse_append]

-- ============================================================
-- const clause emit: `Formula.const b` becomes `[pos/neg m]`
-- ============================================================

/-- Reading a literal (`lit b`) enters the constant-clause phase. -/
lemma rd_lit_step (b : Bool) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, St.rd (FormulaSym.lit b), stk (FormulaSym.lit b :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.const, St.rd (FormulaSym.lit b), stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `const`: a positive literal emits the `clauseMark posMark varMark` header
and enters the index-emission loop. -/
lemma const_true_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.const, St.rd (FormulaSym.lit true), stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constEmit, St.rd (FormulaSym.lit true), stk rest T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `const`: a negative literal routes through `constFalse`. -/
lemma const_false_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.const, St.rd (FormulaSym.lit false), stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.rd (FormulaSym.lit false), stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `constFalse`: a negative literal emits the `clauseMark negMark varMark`
header and enters the index-emission loop. -/
lemma constFalse_step (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.constFalse, St.rd (FormulaSym.lit false), stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constEmit, St.rd (FormulaSym.lit false), stk rest T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `constEmit`: a counter unit emits one `endMark` (extending the unary index
run) and one scratch marker, looping back to `constEmit`. -/
lemma constEmit_loop_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.constEmit, v, stk inp T (c + 1) V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constEmit, St.constLoop, stk inp T c V F
          (() :: S) (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `constEmit`: an exhausted counter ends the index run with one final
`endMark` and moves to `constMake`. -/
lemma constEmit_final_step (v : St) (inp T : List FormulaSym) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.constEmit, v, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constMake, St.done, stk inp T 0 V F S (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `replicate k a ++ [a]` is the `k + 1`-fold repetition. -/
lemma replicate_append_one {α : Type} (k : Nat) (a : α) :
    List.replicate k a ++ [a] = List.replicate (k + 1) a := by
  induction k with
  | zero => simp
  | succ k ih =>
      simpa [List.replicate_succ, List.cons_append] using ih

/-- The `constEmit` loop: `m` counter units emit `m` `endMark`s (plus one
final) and `m` scratch markers, ending at `constMake` with the counter
exhausted. -/
lemma constEmit_phase (m : Nat) (v : St) (inp T : List FormulaSym) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[m + 1]
        (some (⟨some Label.constEmit, v, stk inp T m V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.constMake, St.done, stk inp T 0 V F (List.replicate m () ++ S)
          (List.replicate (m + 1) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction m generalizing S O v with
  | zero =>
      have h := constEmit_final_step v inp T V F S O U
      change (flip bind Sstep) (some (⟨some Label.constEmit, v, stk inp T 0 V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.constMake, St.done, stk inp T 0 V F
            (List.replicate 0 () ++ S) (List.replicate 1 CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      simpa [flip, List.replicate_one] using h
  | succ m ih =>
      have h := constEmit_loop_step v inp T m V F S O U
      rw [show Nat.succ m + 1 = m + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[m + 1]
          (Sstep (⟨some Label.constEmit, v, stk inp T (Nat.succ m) V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.constMake, St.done, stk inp T 0 V F
            (List.replicate (Nat.succ m) () ++ S) (List.replicate (Nat.succ m + 1) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (v := St.constLoop) (S := () :: S) (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[m + 1]
            (some (⟨some Label.constEmit, St.constLoop, stk inp T m V F (() :: S)
              (CNFSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some Label.constMake, St.done, stk inp T 0 V F
              (List.replicate m () ++ (() :: S))
              (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.constMake, St.done, stk inp T 0 V F
            (List.replicate (Nat.succ m) () ++ S) (List.replicate (Nat.succ m + 1) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · rw [show (() :: S) = [()] ++ S by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]
              · rw [show (CNFSym.endMark :: O) = [CNFSym.endMark] ++ O by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

/-- `constMake`: a scratch marker rebuilds one `true` in the value variable's
run and one counter unit, looping back to `constMake`. -/
lemma constMake_loop_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (d : Nat) (O U : List CNFSym) :
    Sstep (⟨some Label.constMake, v, stk inp T c V F (() :: List.replicate d ()) O U⟩ : (mach).Cfg)
      = some (⟨some Label.constMake, St.constLoop, stk inp T (c + 1) (true :: V) F
          (List.replicate d ()) O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `constMake`: an empty scratch stack finishes the value variable with a final
`true` (and counter unit) and a `false` separator, moving to `reduce`. -/
lemma constMake_final_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    Sstep (⟨some Label.constMake, v, stk inp T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
          (false :: true :: V) F [] O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- The `constMake` loop: `m` scratch markers build the `false :: replicate (m+1) true`
value variable for index `m`, restore `m + 1` counter units, and reach `reduce`. -/
lemma constMake_phase (m : Nat) (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[m + 1]
        (some (⟨some Label.constMake, v, stk inp T c V F (List.replicate m ()) O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, St.done, stk inp T (c + m + 1)
          (false :: List.replicate (m + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
  induction m generalizing c V v with
  | zero =>
      have h := constMake_final_step v inp T c V F O U
      change (flip bind Sstep) (some (⟨some Label.constMake, v, stk inp T c V F [] O U⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, St.done, stk inp T (c + 0 + 1)
            (false :: List.replicate 1 true ++ V) F [] O U⟩ : (mach).Cfg)
      simpa [flip, List.replicate_one] using h
  | succ m ih =>
      have h := constMake_loop_step v inp T c V F m O U
      rw [show Nat.succ m + 1 = m + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[m + 1]
          (Sstep (⟨some Label.constMake, v, stk inp T c V F (() :: List.replicate m ()) O U⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, St.done, stk inp T (c + Nat.succ m + 1)
            (false :: List.replicate (Nat.succ m + 1) true ++ V) F [] O U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (v := St.constLoop) (c := c + 1) (V := true :: V)
      calc
        (flip bind Sstep)^[m + 1]
            (some (⟨some Label.constMake, St.constLoop, stk inp T (c + 1) (true :: V) F
              (List.replicate m ()) O U⟩ : (mach).Cfg))
          = some (⟨some Label.reduce, St.done, stk inp T ((c + 1) + m + 1)
              (false :: List.replicate (m + 1) true ++ (true :: V)) F [] O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reduce, St.done, stk inp T (c + Nat.succ m + 1)
            (false :: List.replicate (Nat.succ m + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              · rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

/-- The `const` phase for a positive literal: emit the clause `[pos m]` onto
`o`, build the value variable `m` on `val`, restore the counter to `m + 1`,
and reach `reduce`.  (`m` is the auxiliary index, i.e. the counter at entry.) -/
lemma const_phase_true (m : Nat) (rest T : List FormulaSym) (V : List Bool) (F : List Frame)
    (O U : List CNFSym) :
    (flip bind Sstep)^[2 * m + 3]
        (some (⟨some Label.const, St.rd (FormulaSym.lit true), stk rest T m V F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, St.done, stk rest T (m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          ((encClause [Literal.pos m]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have hconst := const_true_step rest T m V F [] O U
  have hem := constEmit_phase m (St.rd (FormulaSym.lit true)) rest T V F []
      (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U
  have hmk := constMake_phase m (St.done) rest T 0 V F
      (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U
  calc
    (flip bind Sstep)^[2 * m + 3]
        (some (⟨some Label.const, St.rd (FormulaSym.lit true), stk rest T m V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] (Sstep
          (⟨some Label.const, St.rd (FormulaSym.lit true), stk rest T m V F [] O U⟩ : (mach).Cfg))) := by
          rw [show 2 * m + 3 = Nat.succ ((m + 1) + (m + 1)) by omega]
          rw [Function.iterate_succ_apply]
          rw [Function.iterate_add]
          rfl
    _ = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1]
          (some (⟨some Label.constEmit, St.rd (FormulaSym.lit true), stk rest T m V F []
            (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg))) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] x)) hconst
    _ = (flip bind Sstep)^[m + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F
            (List.replicate m () ++ [])
            (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] x) hem
    _ = (flip bind Sstep)^[m + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F (List.replicate m ())
            (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep)^[m + 1] x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> simp [stk, List.append_nil]
    _ = some (⟨some Label.reduce, St.done, stk rest T (0 + m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
          rw [hmk]
    _ = some (⟨some Label.reduce, St.done, stk rest T (m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          ((encClause [Literal.pos m]).reverse ++ O) U⟩ : (mach).Cfg) := by
          have hrev : (encClause [Literal.pos m]).reverse =
              List.replicate (m + 1) CNFSym.endMark ++ [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] := by
            simp [encClause, encLit, litSym, litIndex, List.reverse_replicate]
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk]
            rw [show CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O =
                [CNFSym.varMark, CNFSym.posMark, CNFSym.clauseMark] ++ O by rfl]
            rw [← List.append_assoc]
            rw [← hrev]

/-- The `const` phase for a negative literal: emit the clause `[neg m]` onto
`o`, build the value variable `m` on `val`, restore the counter to `m + 1`,
and reach `reduce`. -/
lemma const_phase_false (m : Nat) (rest T : List FormulaSym) (V : List Bool) (F : List Frame)
    (O U : List CNFSym) :
    (flip bind Sstep)^[2 * m + 4]
        (some (⟨some Label.const, St.rd (FormulaSym.lit false), stk rest T m V F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, St.done, stk rest T (m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          ((encClause [Literal.neg m]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := const_false_step rest T m V F [] O U
  have h2 := constFalse_step rest T m V F [] O U
  have hem := constEmit_phase m (St.rd (FormulaSym.lit false)) rest T V F []
      (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
  have hmk := constMake_phase m (St.done) rest T 0 V F
      (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  calc
    (flip bind Sstep)^[2 * m + 4]
        (some (⟨some Label.const, St.rd (FormulaSym.lit false), stk rest T m V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] ((flip bind Sstep) (Sstep
          (⟨some Label.const, St.rd (FormulaSym.lit false), stk rest T m V F [] O U⟩ : (mach).Cfg)))) := by
          rw [show 2 * m + 4 = Nat.succ (Nat.succ ((m + 1) + (m + 1))) by omega]
          rw [Function.iterate_succ_apply]
          rw [Function.iterate_succ_apply]
          rw [Function.iterate_add]
          rfl
    _ = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] ((flip bind Sstep)
          (some (⟨some Label.constFalse, St.rd (FormulaSym.lit false), stk rest T m V F [] O U⟩ : (mach).Cfg)))) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] ((flip bind Sstep) x))) h1
    _ = (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1]
          (some (⟨some Label.constEmit, St.rd (FormulaSym.lit false), stk rest T m V F []
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg))) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] ((flip bind Sstep)^[m + 1] x)) h2
    _ = (flip bind Sstep)^[m + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F
            (List.replicate m () ++ [])
            (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) :=
          congrArg (fun x => (flip bind Sstep)^[m + 1] x) hem
    _ = (flip bind Sstep)^[m + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F (List.replicate m ())
            (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep)^[m + 1] x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> simp [stk, List.append_nil]
    _ = some (⟨some Label.reduce, St.done, stk rest T (0 + m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          (List.replicate (m + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
          rw [hmk]
    _ = some (⟨some Label.reduce, St.done, stk rest T (m + 1)
          (false :: List.replicate (m + 1) true ++ V) F []
          ((encClause [Literal.neg m]).reverse ++ O) U⟩ : (mach).Cfg) := by
          have hrev : (encClause [Literal.neg m]).reverse =
              List.replicate (m + 1) CNFSym.endMark ++ [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
            simp [encClause, encLit, litSym, litIndex, List.reverse_replicate]
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

-- ============================================================
-- not clause emit: `Formula.not f` emits `notClauses c y₁`
-- ============================================================

/-- `emitNot`: pop the child value-variable's `false` separator and push the
first clause's header `[clauseMark, negMark, varMark]`, entering the counter
loop. -/
lemma emitNot_step (v : St) (inp T : List FormulaSym) (c : Nat) (b : Bool) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.emitNot, v, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.not₂ Op.auxEmit, stk inp T c V' F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveCnt`: one counter unit emits one `endMark` and one scratch marker. -/
lemma moveCnt_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T (c + 1) V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T c V F
          (() :: S) (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `moveCnt`: an empty counter routes to `go` with the counter parked. -/
lemma moveCnt_final (go : Label) (inp T : List FormulaSym) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `moveCnt` loop: `c` counter units become `c` `endMark`s and `c`
scratch markers, ending at `go`. -/
lemma moveCnt_phase (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[c + 1]
        (some (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F
          (List.replicate c () ++ S) (List.replicate c CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction c generalizing S O with
  | zero =>
      have h := moveCnt_final go inp T V F S O U
      change (flip bind Sstep) (some (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T 0 V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ c ih =>
      have h := moveCnt_step go inp T c V F S O U
      rw [show Nat.succ c + 1 = c + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[c + 1]
          (Sstep (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T (Nat.succ c) V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F
            (List.replicate (Nat.succ c) () ++ S) (List.replicate (Nat.succ c) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (S := () :: S) (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[c + 1]
            (some (⟨some Label.moveCnt, St.mv go Op.auxEmit, stk inp T c V F (() :: S)
              (CNFSym.endMark :: O) U⟩ : (mach).Cfg))
          = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F
              (List.replicate c () ++ (() :: S)) (List.replicate c CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T 0 V F
            (List.replicate (Nat.succ c) () ++ S) (List.replicate (Nat.succ c) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · rw [show (() :: S) = [()] ++ S by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]
              · rw [show (CNFSym.endMark :: O) = [CNFSym.endMark] ++ O by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

/-- `not₂`: route through `restoreCnt` so the counter is restored before the
child's value variable is parked (keeping `scr` to one kind of unit). -/
lemma not₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₂, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs Label.not₃ Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `restoreCnt`: one scratch marker restores one counter unit. -/
lemma restoreCnt_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F (() :: S) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T (c + 1) V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `restoreCnt`: an empty scratch routes to `go` with the counter restored. -/
lemma restoreCnt_final (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    Sstep (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T c V F [] O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `restoreCnt` loop: `k` scratch markers restore `k` counter units. -/
lemma restoreCnt_phase (go : Label) (inp T : List FormulaSym) (c k : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F (List.replicate k ()) O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T (c + k) V F [] O U⟩ : (mach).Cfg) := by
  induction k generalizing c with
  | zero =>
      have h := restoreCnt_final go inp T c V F O U
      change (flip bind Sstep) (some (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F [] O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T c V F [] O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := restoreCnt_step go inp T c V F (List.replicate k ()) O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F
            (() :: List.replicate k ()) O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T (c + Nat.succ k) V F [] O U⟩ : (mach).Cfg)
      have hih := ih (c := c + 1)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T c V F
              (() :: List.replicate k ()) O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.restoreCnt, St.rs go Op.auxEmit, stk inp T (c + 1) V F
                (List.replicate k ()) O U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T ((c + 1) + k) V F [] O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.auxEmit, stk inp T (c + Nat.succ k) V F [] O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- `not₃`: push the first clause's second-literal header `[varMark, negMark]`
and the completing `endMark`, entering the value loop. -/
lemma not₃_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₃, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.not₄ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varEmit`): one `true` in the run emits one `endMark` and parks
a scratch marker. -/
lemma moveVal_varEmit_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (true :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c V' F
          (() :: S) (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varEmit`): a non-`true` head stops the run, routing to `go`. -/
lemma moveVal_varEmit_stop (go : Label) (b : Bool) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hb : b ≠ true) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg) := by
  cases b with
  | true => simp at hb
  | false =>
      apply congrArg some
      apply Turing.TM2Comp.Cfg_ext
      · simp [prog, Sstep]
      · simp [prog, Sstep]
      · funext k
        cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varEmit`): an empty value tape stops the run, routing to `go`. -/
lemma moveVal_varEmit_empty (go : Label) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c [] F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c [] F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varEmit`): the run stops at any non-`true` remainder. -/
lemma moveVal_varEmit_end (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hV : V.head? ≠ some true) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  cases V with
  | nil =>
      exact moveVal_varEmit_empty go inp T c F S O U
  | cons b V' =>
      have hb : b ≠ true := by
        intro h
        apply hV
        simp [h]
      exact moveVal_varEmit_stop go b inp T c V' F S O U hb

/-- The `moveVal` (`varEmit`) loop: `k` `true`s become `k` `endMark`s and `k`
parked markers, ending at `go`. -/
lemma moveVal_varEmit_phase (go : Label) (k : Nat) (inp T : List FormulaSym) (c : Nat)
    (V : List Bool) (F : List Frame) (S : List Unit) (O U : List CNFSym)
    (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F
          (List.replicate k () ++ S) (List.replicate k CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction k generalizing S O with
  | zero =>
      have h := moveVal_varEmit_end go inp T c V F S O U hV
      change (flip bind Sstep) (some (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := moveVal_varEmit_step go inp T c (List.replicate k true ++ V) F S O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F
            (List.replicate (Nat.succ k) () ++ S) (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      have hih := ih (S := () :: S) (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.moveVal, St.mv go Op.varEmit, stk inp T c (List.replicate k true ++ V) F (() :: S)
                (CNFSym.endMark :: O) U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F
            (List.replicate k () ++ (() :: S)) (List.replicate k CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F
            (List.replicate (Nat.succ k) () ++ S) (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              · rw [show (() :: S) = [()] ++ S by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]
              · rw [show (CNFSym.endMark :: O) = [CNFSym.endMark] ++ O by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

/-- `not₄`: push the second clause's header `[clauseMark, posMark, varMark]`,
entering the value restore. -/
lemma not₄_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₄, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs Label.not₅ Op.varEmit, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `restoreVal`: one scratch marker restores one `true` to the value tape. -/
lemma restoreVal_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F (() :: S) O U⟩ : (mach).Cfg)
      = some (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c (true :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `restoreVal`: an empty scratch routes to `go` with the value restored. -/
lemma restoreVal_final (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    Sstep (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F [] O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `restoreVal` loop: `k` scratch markers restore `k` `true`s. -/
lemma restoreVal_phase (go : Label) (k : Nat) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F (List.replicate k ()) O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (List.replicate k true ++ V) F [] O U⟩ : (mach).Cfg) := by
  induction k generalizing V with
  | zero =>
      have h := restoreVal_final go inp T c V F O U
      change (flip bind Sstep) (some (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F [] O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c V F [] O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := restoreVal_step go inp T c V F (List.replicate k ()) O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F
            (() :: List.replicate k ()) O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (List.replicate (Nat.succ k) true ++ V) F [] O U⟩ : (mach).Cfg)
      have hih := ih (V := true :: V)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c V F
              (() :: List.replicate k ()) O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.restoreVal, St.rs go Op.varEmit, stk inp T c (true :: V) F
                (List.replicate k ()) O U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (List.replicate k true ++ (true :: V)) F [] O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.varEmit, stk inp T c (List.replicate (Nat.succ k) true ++ V) F [] O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext kk
              cases kk <;> try simp [stk]
              rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
              rw [← List.append_assoc]
              rw [replicate_append_one]

/-- `not₅`: re-enter the counter loop for the second clause's index run. -/
lemma not₅_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₅, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveCnt, St.mv Label.not₆ Op.auxEmit, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `not₆`: push the second clause's second-literal header `[posMark, varMark]`
and the completing `endMark`, entering the (consuming) value loop. -/
lemma not₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.constMake Op.varPop, stk inp T c V F S
          (CNFSym.posMark :: CNFSym.varMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varPop`): one `true` in the run emits one `endMark`, consuming
the run without parking it. -/
lemma moveVal_varPop_step (go : Label) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (true :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c V' F S (CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varPop`): a non-`true` head stops the run, routing to `go`. -/
lemma moveVal_varPop_stop (go : Label) (b : Bool) (inp T : List FormulaSym) (c : Nat) (V' : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hb : b ≠ true) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varPop, stk inp T c (b :: V') F S O U⟩ : (mach).Cfg) := by
  cases b with
  | true => simp at hb
  | false =>
      apply congrArg some
      apply Turing.TM2Comp.Cfg_ext
      · simp [prog, Sstep]
      · simp [prog, Sstep]
      · funext k
        cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varPop`): an empty value tape stops the run, routing to `go`. -/
lemma moveVal_varPop_empty (go : Label) (inp T : List FormulaSym) (c : Nat)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c [] F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varPop, stk inp T c [] F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [prog, Sstep]
  · simp [prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `moveVal` (`varPop`): the run stops at any non-`true` remainder. -/
lemma moveVal_varPop_end (go : Label) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hV : V.head? ≠ some true) :
    Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  cases V with
  | nil =>
      exact moveVal_varPop_empty go inp T c F S O U
  | cons b V' =>
      have hb : b ≠ true := by
        intro h
        apply hV
        simp [h]
      exact moveVal_varPop_stop go b inp T c V' F S O U hb

/-- The `moveVal` (`varPop`) loop: `k` `true`s become `k` `endMark`s, ending at
`go`. -/
lemma moveVal_varPop_phase (go : Label) (k : Nat) (inp T : List FormulaSym) (c : Nat)
    (V : List Bool) (F : List Frame) (S : List Unit) (O U : List CNFSym)
    (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[k + 1]
        (some (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
      = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S (List.replicate k CNFSym.endMark ++ O) U⟩ : (mach).Cfg) := by
  induction k generalizing O with
  | zero =>
      have h := moveVal_varPop_end go inp T c V F S O U hV
      change (flip bind Sstep) (some (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ k ih =>
      have h := moveVal_varPop_step go inp T c (List.replicate k true ++ V) F S O U
      rw [show Nat.succ k + 1 = k + 1 + 1 by omega]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[k + 1]
          (Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
        = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S (List.replicate (Nat.succ k) CNFSym.endMark ++ O) U⟩ : (mach).Cfg)
      have hih := ih (O := CNFSym.endMark :: O)
      calc
        (flip bind Sstep)^[k + 1]
            (Sstep (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (true :: List.replicate k true ++ V) F S O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[k + 1]
              (some (⟨some Label.moveVal, St.mv go Op.varPop, stk inp T c (List.replicate k true ++ V) F S (CNFSym.endMark :: O) U⟩ : (mach).Cfg)) := by
              exact congrArg (fun x => (flip bind Sstep)^[k + 1] x) h
        _ = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S
            (List.replicate k CNFSym.endMark ++ (CNFSym.endMark :: O)) U⟩ : (mach).Cfg) := hih
        _ = some (⟨some go, St.rsDone go Op.varPop, stk inp T c V F S
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

end TM3CNF

end Turing

end Chapter34

end CLRS
