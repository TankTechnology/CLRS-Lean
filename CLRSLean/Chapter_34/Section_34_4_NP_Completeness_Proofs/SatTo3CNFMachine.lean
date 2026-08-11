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

**Status (2026-08-09).**  Count, reorder, the recursive descent
(`parse_phase`), `emitTrue`, the const-clause emission, the `not`/`and`/`or`/
`iff` clause emissions (`not_phase`/`emitAnd_phase`/`emitOr_phase`/
`emitIff_phase`), the generic move/restore loops, the `parkVal`/`unparkVal`
temp-tape subroutines, and `copyOut` (`copyOut_phase` + `done_step`,
transferring `o` to `out` and halting) are written.  The `parse_phase` lemma is
the full run lemma for the recursive descent: for any input `inp` with
`decodeAux b inp = (f, rest)` (and a sufficient budget `b`), the machine reads
`inp` from `rd`, emits the reversed Tseitin clauses of `f` onto `o`, pushes
`f`'s value variable, advances the counter, and reaches `reduce` with the
continuation `rest` on `in`.  It is proved by induction on the formula, with
malformed input handled by the junk `const false` phases.

**Current gaps.**

- **`outputsFun`, the full-machine phase composition, the polynomial time
  bound, and the assembled `PolyTimeReducible SAT ThreeCNFSat`** are not yet
  written.
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
  | rd | rdVar | pv0 | pv | reduce | const | constFalse | constEmit | constMake
  | emitNot | not₂ | not₃ | not₄ | not₅ | not₆
  | emitAnd | and₂ | and₃ | and₄ | and₅ | and₆ | and₇ | and₈ | and₉ | and₁₀ | and₁₁ | and₁₂
    | and₁₃ | and₁₄ | and₁₅ | and₁₆
  | emitOr | or₂ | or₃ | or₄ | or₅ | or₆ | or₇ | or₈ | or₉ | or₁₀ | or₁₁ | or₁₂
    | or₁₃ | or₁₄ | or₁₅ | or₁₆
  | emitIff | iff₂ | iff₃ | iff₄ | iff₅ | iff₆ | iff₇ | iff₈ | iff₉ | iff₁₀
    | iff₁₁ | iff₁₂ | iff₁₃ | iff₁₄ | iff₁₅ | iff₁₆ | iff₁₇ | iff₁₈ | iff₁₉ | iff₂₀ | iff₂₁
    | iff₂₂ | iff₂₃ | iff₂₄ | iff₂₅ | iff₂₆ | iff₂₇ | iff₂₈ | iff₂₉ | iff₃₀
  | emitTrue | emitTrueRestore
  | moveCnt | restoreCnt | moveVal | restoreVal | parkVal | parkRest | unparkVal
  | copyOut | clearIn | clearCnt
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
            (Turing.TM2.Stmt.goto (fun _ => Label.pv0))
            (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.notMark => true | _ => false)
              (Turing.TM2.Stmt.push K.frm (fun _ => Frame.not)
                (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
              (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.andMark => true | _ => false)
                (Turing.TM2.Stmt.push K.frm (fun _ => Frame.and₁)
                  (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
                (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.orMark => true | _ => false)
                  (Turing.TM2.Stmt.push K.frm (fun _ => Frame.or₁)
                    (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
                  (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.iffMark => true | _ => false)
                    (Turing.TM2.Stmt.push K.frm (fun _ => Frame.iff₁)
                      (Turing.TM2.Stmt.goto (fun _ => Label.rd)))
                    (Turing.TM2.Stmt.goto (fun _ => Label.const))))))))
  | Label.pv0 =>
      Turing.TM2.Stmt.pop K.inK (fun _ x => match x with
          | some s => St.rd s
          | none => St.reduce)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.endMark => true | _ => false)
          (Turing.TM2.Stmt.push K.val (fun _ => true) (Turing.TM2.Stmt.goto (fun _ => Label.pv)))
          (Turing.TM2.Stmt.branch (fun v => match v with | St.rd _ => true | _ => false)
            (Turing.TM2.Stmt.push K.inK (fun v => match v with | St.rd s => s | _ => default)
              (Turing.TM2.Stmt.goto (fun _ => Label.constFalse)))
            (Turing.TM2.Stmt.goto (fun _ => Label.constFalse))))
  | Label.pv =>
      Turing.TM2.Stmt.pop K.inK (fun _ x => match x with
          | some s => St.rd s
          | none => St.reduce)
        (Turing.TM2.Stmt.branch (fun v => match v with | St.rd FormulaSym.endMark => true | _ => false)
          (Turing.TM2.Stmt.push K.val (fun _ => true) (Turing.TM2.Stmt.goto (fun _ => Label.pv)))
          (Turing.TM2.Stmt.push K.val (fun _ => false)
            (Turing.TM2.Stmt.branch (fun v => match v with | St.rd _ => true | _ => false)
              (Turing.TM2.Stmt.push K.inK (fun v => match v with | St.rd s => s | _ => default)
                (Turing.TM2.Stmt.goto (fun _ => Label.reduce)))
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
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
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
  | Label.emitAnd =>
      Turing.TM2.Stmt.load (fun _ => St.mv Label.and₂ Op.park)
        (Turing.TM2.Stmt.goto (fun _ => Label.parkVal))
  | Label.and₂ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.mv Label.and₃ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt)))))
  | Label.and₃ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.and₄ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt)))))
  | Label.and₄ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.and₅ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.and₅ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.and₆ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))))
  | Label.and₆ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.and₇ Op.auxEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt)))
  | Label.and₇ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.and₈ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt)))))
  | Label.and₈ =>
      Turing.TM2.Stmt.load (fun _ => St.rs Label.and₉ Op.unpark)
        (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal))
  | Label.and₉ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.and₁₀ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.and₁₀ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.and₁₁ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))))
  | Label.and₁₁ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.and₁₂ Op.park)
          (Turing.TM2.Stmt.goto (fun _ => Label.parkVal)))
  | Label.and₁₂ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.and₁₃ Op.varPop)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.and₁₃ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.rs Label.and₁₄ Op.unpark)
            (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal))))
  | Label.and₁₄ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.and₁₅ Op.varPop)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.and₁₅ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.mv Label.and₁₆ Op.auxEmit)
            (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt))))
  | Label.and₁₆ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.load (fun _ => St.done)
          (Turing.TM2.Stmt.goto (fun _ => Label.constMake)))
  | Label.emitOr =>
      Turing.TM2.Stmt.load (fun _ => St.mv Label.or₂ Op.park)
        (Turing.TM2.Stmt.goto (fun _ => Label.parkVal))
  | Label.or₂ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.mv Label.or₃ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt)))))
  | Label.or₃ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.or₄ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt)))))
  | Label.or₄ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.or₅ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.or₅ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.or₆ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))))
  | Label.or₆ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.or₇ Op.auxEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt)))
  | Label.or₇ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.or₈ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt)))))
  | Label.or₈ =>
      Turing.TM2.Stmt.load (fun _ => St.rs Label.or₉ Op.unpark)
        (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal))
  | Label.or₉ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.or₁₀ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.or₁₀ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.or₁₁ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))))
  | Label.or₁₁ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.or₁₂ Op.park)
          (Turing.TM2.Stmt.goto (fun _ => Label.parkVal)))
  | Label.or₁₂ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.or₁₃ Op.varPop)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.or₁₃ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.rs Label.or₁₄ Op.unpark)
            (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal))))
  | Label.or₁₄ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.or₁₅ Op.varPop)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.or₁₅ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.mv Label.or₁₆ Op.auxEmit)
            (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt))))
  | Label.or₁₆ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.load (fun _ => St.done)
          (Turing.TM2.Stmt.goto (fun _ => Label.constMake)))
  | Label.emitIff =>
      Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₂ Op.park)
        (Turing.TM2.Stmt.goto (fun _ => Label.parkVal))
  | Label.iff₂ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₃ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt)))))
  | Label.iff₃ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₄ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt)))))
  | Label.iff₄ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₅ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.iff₅ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₆ Op.varEmit)
            (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal))))
  | Label.iff₆ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₇ Op.unpark)
          (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal)))
  | Label.iff₇ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₈ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.iff₈ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₉ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))))
  | Label.iff₉ =>
      Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₁₀ Op.auxEmit)
        (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt))
  | Label.iff₁₀ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₁₁ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt)))))
  | Label.iff₁₁ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₁₂ Op.park)
          (Turing.TM2.Stmt.goto (fun _ => Label.parkVal)))
  | Label.iff₁₂ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₁₃ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.iff₁₃ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₁₄ Op.varEmit)
            (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal))))
  | Label.iff₁₄ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₁₅ Op.unpark)
          (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal)))
  | Label.iff₁₅ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₁₆ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.iff₁₆ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₁₇ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))))
  | Label.iff₁₇ =>
      Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₁₈ Op.auxEmit)
        (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt))
  | Label.iff₁₈ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₁₉ Op.auxEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreCnt)))))
  | Label.iff₁₉ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₂₀ Op.park)
          (Turing.TM2.Stmt.goto (fun _ => Label.parkVal)))
  | Label.iff₂₀ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₂₁ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.iff₂₁ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₂₂ Op.varEmit)
            (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal))))
  | Label.iff₂₂ =>
      Turing.TM2.Stmt.push K.val (fun _ => false)
        (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₂₃ Op.unpark)
          (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal)))
  | Label.iff₂₃ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₂₄ Op.varEmit)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.iff₂₄ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.clauseMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.posMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₂₅ Op.varEmit)
              (Turing.TM2.Stmt.goto (fun _ => Label.restoreVal)))))
  | Label.iff₂₅ =>
      Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₂₆ Op.auxEmit)
        (Turing.TM2.Stmt.goto (fun _ => Label.moveCnt))
  | Label.iff₂₆ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.endMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
          (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
            (Turing.TM2.Stmt.push K.val (fun _ => false)
              (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₂₇ Op.park)
                (Turing.TM2.Stmt.goto (fun _ => Label.parkVal))))))
  | Label.iff₂₇ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₂₈ Op.varPop)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.iff₂₈ =>
      Turing.TM2.Stmt.push K.o (fun _ => CNFSym.negMark)
        (Turing.TM2.Stmt.push K.o (fun _ => CNFSym.varMark)
          (Turing.TM2.Stmt.load (fun _ => St.rs Label.iff₂₉ Op.unpark)
            (Turing.TM2.Stmt.goto (fun _ => Label.unparkVal))))
  | Label.iff₂₉ =>
      Turing.TM2.Stmt.pop K.val (fun _ _ => St.done)
        (Turing.TM2.Stmt.load (fun _ => St.mv Label.iff₃₀ Op.varPop)
          (Turing.TM2.Stmt.goto (fun _ => Label.moveVal)))
  | Label.iff₃₀ =>
      Turing.TM2.Stmt.load (fun _ => St.done)
        (Turing.TM2.Stmt.goto (fun _ => Label.constMake))
  | Label.copyOut =>
      Turing.TM2.Stmt.pop K.o (fun _ x => match x with
          | some s => St.copySym s
          | none => St.init)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.copySym _ => true
            | _ => false)
          (Turing.TM2.Stmt.push K.out (fun v => match v with
              | St.copySym s => s
              | _ => default)
            (Turing.TM2.Stmt.goto (fun _ => Label.copyOut)))
          (Turing.TM2.Stmt.goto (fun _ => Label.clearIn)))
  | Label.clearIn =>
      Turing.TM2.Stmt.pop K.inK (fun _ x => match x with
          | some s => St.rd s
          | none => St.done)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.rd _ => true
            | _ => false)
          (Turing.TM2.Stmt.goto (fun _ => Label.clearIn))
          (Turing.TM2.Stmt.goto (fun _ => Label.clearCnt)))
  | Label.clearCnt =>
      Turing.TM2.Stmt.pop K.cnt (fun _ x => match x with
          | some _ => St.done
          | none => St.init)
        (Turing.TM2.Stmt.branch (fun v => match v with
            | St.done => true
            | _ => false)
          (Turing.TM2.Stmt.goto (fun _ => Label.clearCnt))
          (Turing.TM2.Stmt.goto (fun _ => Label.done)))
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

-- ============================================================
-- reduce dispatch: pop a continuation frame and route to the emitter
--
-- The `reduce` label pops the top frame of `frm` and dispatches to the
-- matching emission phase (or pushes the `₂` frame for a binary operator's
-- second child and returns to `rd`).  The pre-state is irrelevant: the pop
-- overwrites it.
-- ============================================================

/-- `reduce` with an empty `frm` stack (the root) routes to `emitTrue`. -/
lemma reduce_top_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V [] S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitTrue, St.emitTrue, stk inp T c V [] S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with a `Frame.not` on top routes to `emitNot`. -/
lemma reduce_not_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.not :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitNot, St.emitNot, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `and₁` frame routes back to `rd` (with the second child's
`and₂` frame pushed). -/
lemma reduce_and₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.and₁ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.and₁Done, stk inp T c V (Frame.and₂ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `and₂` frame routes to `emitAnd`. -/
lemma reduce_and₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.and₂ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitAnd, St.emitAnd, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `or₁` frame routes back to `rd` (with the second child's
`or₂` frame pushed). -/
lemma reduce_or₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.or₁ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.or₁Done, stk inp T c V (Frame.or₂ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `or₂` frame routes to `emitOr`. -/
lemma reduce_or₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.or₂ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitOr, St.emitOr, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `iff₁` frame routes back to `rd` (with the second child's
`iff₂` frame pushed). -/
lemma reduce_iff₁_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.iff₁ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.rd, St.iff₁Done, stk inp T c V (Frame.iff₂ :: F) S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `reduce` with an `iff₂` frame routes to `emitIff`. -/
lemma reduce_iff₂_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.reduce, v, stk inp T c V (Frame.iff₂ :: F) S O U⟩ : (mach).Cfg)
      = some (⟨some Label.emitIff, St.emitIff, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

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

/-- The reversed encoding of a three-literal clause splits at the `clauseMark`. -/
lemma encClause_three_reverse (l₁ l₂ l₃ : Literal) :
    (encClause [l₁, l₂, l₃]).reverse =
      (encLit l₃).reverse ++ (encLit l₂).reverse ++ (encLit l₁).reverse ++
        [CNFSym.clauseMark] := by
  simp [encClause, List.flatMap, List.reverse_cons, List.reverse_append]

/-- The reversed encoding of `andClauses y y₁ y₂` emits the three clauses in
reverse output order (clause 3 `[¬y₁, ¬y₂, y]` first, then `[¬y, y₂]`, then
`[¬y, y₁]`). -/
lemma encCNF_andClauses_reverse (y y₁ y₂ : Nat) :
    (encCNF (andClauses y y₁ y₂)).reverse =
      (encClause [Literal.neg y₁, Literal.neg y₂, Literal.pos y]).reverse ++
      (encClause [Literal.neg y, Literal.pos y₂]).reverse ++
      (encClause [Literal.neg y, Literal.pos y₁]).reverse := by
  simp [encCNF, andClauses, List.reverse_append]

/-- The reversed encoding of `orClauses y y₁ y₂` emits the three clauses in
reverse output order (clause 3 `[y₁, y₂, ¬y]` first, then `[y, ¬y₂]`, then
`[y, ¬y₁]`). -/
lemma encCNF_orClauses_reverse (y y₁ y₂ : Nat) :
    (encCNF (orClauses y y₁ y₂)).reverse =
      (encClause [Literal.pos y₁, Literal.pos y₂, Literal.neg y]).reverse ++
      (encClause [Literal.pos y, Literal.neg y₂]).reverse ++
      (encClause [Literal.pos y, Literal.neg y₁]).reverse := by
  simp [encCNF, orClauses, List.reverse_append]

/-- The reversed encoding of `iffClauses y y₁ y₂` emits the four clauses in
reverse output order (clause 4 `[y, ¬y₁, ¬y₂]` first, then `[y, y₁, y₂]`, then
`[¬y, y₁, ¬y₂]`, then `[¬y, ¬y₁, y₂]`). -/
lemma encCNF_iffClauses_reverse (y y₁ y₂ : Nat) :
    (encCNF (iffClauses y y₁ y₂)).reverse =
      (encClause [Literal.pos y, Literal.neg y₁, Literal.neg y₂]).reverse ++
      (encClause [Literal.pos y, Literal.pos y₁, Literal.pos y₂]).reverse ++
      (encClause [Literal.neg y, Literal.pos y₁, Literal.neg y₂]).reverse ++
      (encClause [Literal.neg y, Literal.neg y₁, Literal.pos y₂]).reverse := by
  simp [encCNF, iffClauses, List.reverse_append]

-- ============================================================
-- const clause emit: `Formula.const b` becomes `[pos/neg m]`
-- ============================================================

/-- Reading a literal (`lit b`) enters the constant-clause phase. -/
lemma rd_lit_step (v : St) (b : Bool) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.rd, v, stk (FormulaSym.lit b :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.const, St.rd (FormulaSym.lit b), stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
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

/-- `const` with a non-positive-literal state routes through `constFalse` (the
junk `const false` path).  The pre-state is preserved. -/
lemma const_to_constFalse_step (v : St) (hv : v ≠ St.rd (FormulaSym.lit true))
    (rest T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.const, v, stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, v, stk rest T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep, hv]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, hv]

/-- `constFalse` emits the `clauseMark negMark varMark` header from any
pre-state (the junk `const false` path).  The pre-state is preserved. -/
lemma constFalse_generic_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.constFalse, v, stk rest T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constEmit, v, stk rest T c V F S
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `pv0` on a non-`endMark` symbol routes to `constFalse`, restoring the symbol
(the junk `const false` path).  The pre-state is irrelevant. -/
lemma pv0_junk_step (v : St) (s : FormulaSym) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) (hs : s ≠ FormulaSym.endMark) :
    Sstep (⟨some Label.pv0, v, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.rd s, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep, hs]
  · simp [stk, prog, Sstep, hs]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, hs]

/-- `pv0` on an empty input routes to `constFalse` (the junk `const false`
path).  The pre-state is irrelevant. -/
lemma pv0_empty_step (v : St) (T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.pv0, v, stk [] T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.reduce, stk [] T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
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

/-- `not₆`: push the completing `endMark` and the second clause's first-literal
header `[posMark, varMark]`, entering the (consuming) value loop. -/
lemma not₆_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.not₆, v, stk inp T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.moveVal, St.mv Label.constMake Op.varPop, stk inp T c V F S
          (CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O) U⟩ : (mach).Cfg) := by
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

/-- The `emitAnd` phase: with the two children's value runs on top of `val`
(the second child's above the first's), emit `andClauses c y₁ y₂` and allocate
the auxiliary variable `y = c` via `constMake`.  The second child is parked on
`temp` while the first is emitted, then restored; the first child is consumed
twice (once per emitted clause mentioning it), and both children are left
restored beneath the new auxiliary run. -/
lemma emitAnd_phase (inp T : List FormulaSym) (c : Nat) (y₁ y₂ : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) (hV : V.head? ≠ some true) :
    (flip bind Sstep)^[6 * c + 3 * y₁ + 7 * y₂ + 44]
      (some (⟨some Label.emitAnd, St.emitAnd, stk inp T c
        (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk inp T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF (andClauses c y₁ y₂)).reverse ++ O) U⟩ : (mach).Cfg) := by
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
  let O1 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O
  let O2 : List CNFSym := List.replicate c CNFSym.endMark ++ O1
  let O3 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O2
  let O4 : List CNFSym := List.replicate (y₁ + 1) CNFSym.endMark ++ O3
  let O5 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O4
  let O6 : List CNFSym := List.replicate c CNFSym.endMark ++ O5
  let O7 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: CNFSym.endMark :: O6
  let O8 : List CNFSym := List.replicate (y₂ + 1) CNFSym.endMark ++ O7
  let O9 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O8
  let O10 : List CNFSym := List.replicate (y₁ + 1) CNFSym.endMark ++ O9
  let O11 : List CNFSym := CNFSym.varMark :: CNFSym.negMark :: O10
  let O12 : List CNFSym := List.replicate (y₂ + 1) CNFSym.endMark ++ O11
  let O13 : List CNFSym := CNFSym.varMark :: CNFSym.posMark :: O12
  let O14 : List CNFSym := List.replicate c CNFSym.endMark ++ O13
  let O15 : List CNFSym := CNFSym.endMark :: O14
  let c0 : (mach).Cfg := ⟨some Label.emitAnd, St.emitAnd, stk inp T c V0 F [] O U⟩
  let c1 : (mach).Cfg := ⟨some Label.parkVal, St.mv Label.and₂ Op.park, stk inp T c V0 F [] O U⟩
  let c2 : (mach).Cfg := ⟨some Label.and₂, St.rsDone Label.and₂ Op.park, stk inp Tp c V1 F [] O U⟩
  let c3 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.and₃ Op.auxEmit, stk inp Tp c V1 F [] O1 U⟩
  let c4 : (mach).Cfg := ⟨some Label.and₃, St.rsDone Label.and₃ Op.auxEmit, stk inp Tp 0 V1 F (List.replicate c ()) O2 U⟩
  let c5 : (mach).Cfg := ⟨some Label.restoreCnt, St.rs Label.and₄ Op.auxEmit, stk inp Tp 0 V1 F (List.replicate c ()) O3 U⟩
  let c6 : (mach).Cfg := ⟨some Label.and₄, St.rsDone Label.and₄ Op.auxEmit, stk inp Tp c V1 F [] O3 U⟩
  let c7 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.and₅ Op.varEmit, stk inp Tp c V2 F [] O3 U⟩
  let c8 : (mach).Cfg := ⟨some Label.and₅, St.rsDone Label.and₅ Op.varEmit, stk inp Tp c V3 F (List.replicate (y₁ + 1) ()) O4 U⟩
  let c9 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.and₆ Op.varEmit, stk inp Tp c V3 F (List.replicate (y₁ + 1) ()) O5 U⟩
  let c10 : (mach).Cfg := ⟨some Label.and₆, St.rsDone Label.and₆ Op.varEmit, stk inp Tp c V4 F [] O5 U⟩
  let c11 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.and₇ Op.auxEmit, stk inp Tp c V5 F [] O5 U⟩
  let c12 : (mach).Cfg := ⟨some Label.and₇, St.rsDone Label.and₇ Op.auxEmit, stk inp Tp 0 V5 F (List.replicate c ()) O6 U⟩
  let c13 : (mach).Cfg := ⟨some Label.restoreCnt, St.rs Label.and₈ Op.auxEmit, stk inp Tp 0 V5 F (List.replicate c ()) O7 U⟩
  let c14 : (mach).Cfg := ⟨some Label.and₈, St.rsDone Label.and₈ Op.auxEmit, stk inp Tp c V5 F [] O7 U⟩
  let c15 : (mach).Cfg := ⟨some Label.unparkVal, St.rs Label.and₉ Op.unpark, stk inp Tp c V5 F [] O7 U⟩
  let c16 : (mach).Cfg := ⟨some Label.and₉, St.rsDone Label.and₉ Op.unpark, stk inp T c V6 F [] O7 U⟩
  let c17 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.and₁₀ Op.varEmit, stk inp T c V7 F [] O7 U⟩
  let c18 : (mach).Cfg := ⟨some Label.and₁₀, St.rsDone Label.and₁₀ Op.varEmit, stk inp T c V8 F (List.replicate (y₂ + 1) ()) O8 U⟩
  let c19 : (mach).Cfg := ⟨some Label.restoreVal, St.rs Label.and₁₁ Op.varEmit, stk inp T c V8 F (List.replicate (y₂ + 1) ()) O9 U⟩
  let c20 : (mach).Cfg := ⟨some Label.and₁₁, St.rsDone Label.and₁₁ Op.varEmit, stk inp T c V9 F [] O9 U⟩
  let c21 : (mach).Cfg := ⟨some Label.parkVal, St.mv Label.and₁₂ Op.park, stk inp T c V10 F [] O9 U⟩
  let c22 : (mach).Cfg := ⟨some Label.and₁₂, St.rsDone Label.and₁₂ Op.park, stk inp Tp c V11 F [] O9 U⟩
  let c23 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.and₁₃ Op.varPop, stk inp Tp c V12 F [] O9 U⟩
  let c24 : (mach).Cfg := ⟨some Label.and₁₃, St.rsDone Label.and₁₃ Op.varPop, stk inp Tp c V13 F [] O10 U⟩
  let c25 : (mach).Cfg := ⟨some Label.unparkVal, St.rs Label.and₁₄ Op.unpark, stk inp Tp c V13 F [] O11 U⟩
  let c26 : (mach).Cfg := ⟨some Label.and₁₄, St.rsDone Label.and₁₄ Op.unpark, stk inp T c V14 F [] O11 U⟩
  let c27 : (mach).Cfg := ⟨some Label.moveVal, St.mv Label.and₁₅ Op.varPop, stk inp T c V15 F [] O11 U⟩
  let c28 : (mach).Cfg := ⟨some Label.and₁₅, St.rsDone Label.and₁₅ Op.varPop, stk inp T c V16 F [] O12 U⟩
  let c29 : (mach).Cfg := ⟨some Label.moveCnt, St.mv Label.and₁₆ Op.auxEmit, stk inp T c V16 F [] O13 U⟩
  let c30 : (mach).Cfg := ⟨some Label.and₁₆, St.rsDone Label.and₁₆ Op.auxEmit, stk inp T 0 V16 F (List.replicate c ()) O14 U⟩
  let c31 : (mach).Cfg := ⟨some Label.constMake, St.done, stk inp T 0 V16 F (List.replicate c ()) O15 U⟩
  let c32 : (mach).Cfg := ⟨some Label.reduce, St.done, stk inp T (c + 1) V17 F [] O15 U⟩
  have h1 : Sstep c0 = some c1 := by
    exact emitAnd_step St.emitAnd inp T c V0 F [] O U
  have h2 : (flip bind Sstep)^[y₂ + 3] (some c1) = some c2 := by
    have h := parkVal_phase Label.and₂ y₂ V1 inp T c F [] O U (by simp [V1])
    exact h
  have h3 : Sstep c2 = some c3 := by
    exact and₂_step (St.rsDone Label.and₂ Op.park) inp Tp c V1 F [] O U
  have h4 : (flip bind Sstep)^[c + 1] (some c3) = some c4 := by
    have h := moveCnt_phase Label.and₃ inp Tp c V1 F [] O1 U
    rw [List.append_nil] at h
    exact h
  have h5 : Sstep c4 = some c5 := by
    exact and₃_step (St.rsDone Label.and₃ Op.auxEmit) inp Tp 0 V1 F (List.replicate c ()) O2 U
  have h6 : (flip bind Sstep)^[c + 1] (some c5) = some c6 := by
    have h := restoreCnt_phase Label.and₄ inp Tp 0 c V1 F O3 U
    rw [Nat.zero_add] at h
    exact h
  have h7 : Sstep c6 = some c7 := by
    exact and₄_step (St.rsDone Label.and₄ Op.auxEmit) inp Tp c false (List.replicate (y₁ + 1) true ++ V) F [] O3 U
  have h8 : (flip bind Sstep)^[y₁ + 2] (some c7) = some c8 := by
    have h := moveVal_varEmit_phase Label.and₅ (y₁ + 1) inp Tp c V F [] O3 U hV
    rw [List.append_nil] at h
    exact h
  have h9 : Sstep c8 = some c9 := by
    exact and₅_step (St.rsDone Label.and₅ Op.varEmit) inp Tp c V F (List.replicate (y₁ + 1) ()) O4 U
  have h10 : (flip bind Sstep)^[y₁ + 2] (some c9) = some c10 := by
    have h := restoreVal_phase Label.and₆ (y₁ + 1) inp Tp c V F O5 U
    exact h
  have h11 : Sstep c10 = some c11 := by
    exact and₆_step (St.rsDone Label.and₆ Op.varEmit) inp Tp c (List.replicate (y₁ + 1) true ++ V) F [] O5 U
  have h12 : (flip bind Sstep)^[c + 1] (some c11) = some c12 := by
    have h := moveCnt_phase Label.and₇ inp Tp c V5 F [] O5 U
    rw [List.append_nil] at h
    exact h
  have h13 : Sstep c12 = some c13 := by
    exact and₇_step (St.rsDone Label.and₇ Op.auxEmit) inp Tp 0 V5 F (List.replicate c ()) O6 U
  have h14 : (flip bind Sstep)^[c + 1] (some c13) = some c14 := by
    have h := restoreCnt_phase Label.and₈ inp Tp 0 c V5 F O7 U
    rw [Nat.zero_add] at h
    exact h
  have h15 : Sstep c14 = some c15 := by
    exact and₈_step (St.rsDone Label.and₈ Op.auxEmit) inp Tp c V5 F [] O7 U
  have h16 : (flip bind Sstep)^[y₂ + 2] (some c15) = some c16 := by
    exact unparkVal_phase Label.and₉ y₂ V1 inp T c F [] O7 U
  have h17 : Sstep c16 = some c17 := by
    exact and₉_step (St.rsDone Label.and₉ Op.unpark) inp T c false
      (List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] O7 U
  have h18 : (flip bind Sstep)^[y₂ + 2] (some c17) = some c18 := by
    have h := moveVal_varEmit_phase Label.and₁₀ (y₂ + 1) inp T c V1 F [] O7 U (by simp [V1])
    rw [List.append_nil] at h
    exact h
  have h19 : Sstep c18 = some c19 := by
    exact and₁₀_step (St.rsDone Label.and₁₀ Op.varEmit) inp T c V1 F (List.replicate (y₂ + 1) ()) O8 U
  have h20 : (flip bind Sstep)^[y₂ + 2] (some c19) = some c20 := by
    have h := restoreVal_phase Label.and₁₁ (y₂ + 1) inp T c V1 F O9 U
    exact h
  have h21 : Sstep c20 = some c21 := by
    exact and₁₁_step (St.rsDone Label.and₁₁ Op.varEmit) inp T c
      (List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] O9 U
  have h22 : (flip bind Sstep)^[y₂ + 3] (some c21) = some c22 := by
    have h := parkVal_phase Label.and₁₂ y₂ V1 inp T c F [] O9 U (by simp [V1])
    exact h
  have h23 : Sstep c22 = some c23 := by
    exact and₁₂_step (St.rsDone Label.and₁₂ Op.park) inp Tp c false (List.replicate (y₁ + 1) true ++ V) F [] O9 U
  have h24 : (flip bind Sstep)^[y₁ + 2] (some c23) = some c24 := by
    exact moveVal_varPop_phase Label.and₁₃ (y₁ + 1) inp Tp c V F [] O9 U hV
  have h25 : Sstep c24 = some c25 := by
    exact and₁₃_step (St.rsDone Label.and₁₃ Op.varPop) inp Tp c V F [] O10 U
  have h26 : (flip bind Sstep)^[y₂ + 2] (some c25) = some c26 := by
    exact unparkVal_phase Label.and₁₄ y₂ V inp T c F [] O11 U
  have h27 : Sstep c26 = some c27 := by
    exact and₁₄_step (St.rsDone Label.and₁₄ Op.unpark) inp T c false (List.replicate (y₂ + 1) true ++ V) F [] O11 U
  have h28 : (flip bind Sstep)^[y₂ + 2] (some c27) = some c28 := by
    exact moveVal_varPop_phase Label.and₁₅ (y₂ + 1) inp T c V F [] O11 U hV
  have h29 : Sstep c28 = some c29 := by
    exact and₁₅_step (St.rsDone Label.and₁₅ Op.varPop) inp T c V F [] O12 U
  have h30 : (flip bind Sstep)^[c + 1] (some c29) = some c30 := by
    have h := moveCnt_phase Label.and₁₆ inp T c V F [] O13 U
    rw [List.append_nil] at h
    exact h
  have h31 : Sstep c30 = some c31 := by
    exact and₁₆_step (St.rsDone Label.and₁₆ Op.auxEmit) inp T 0 V F (List.replicate c ()) O14 U
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
        ((encCNF (andClauses c y₁ y₂)).reverse ++ O) U⟩ : (mach).Cfg) := by
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk, c32, V17]
            rw [encCNF_andClauses_reverse]
            rw [encClause_three_reverse (Literal.neg y₁) (Literal.neg y₂) (Literal.pos c)]
            rw [encClause_two_reverse (Literal.neg c) (Literal.pos y₂)]
            rw [encClause_two_reverse (Literal.neg c) (Literal.pos y₁)]
            simp [O1, O2, O3, O4, O5, O6, O7, O8, O9, O10, O11, O12, O13, O14, O15,
              encLit_reverse, encLit, litSym, litIndex, List.append_assoc, List.cons_append,
              List.replicate_succ, replicate_append_one]

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

-- ============================================================
-- junk `const false` phases
--
-- On malformed input (end of input, a stray `endMark`, or a `varMark` with no
-- unary index run), `decode` yields `const false`.  The machine's junk path
-- emits `forceFalse c` (the `[¬c]` clause) and builds the value variable `c`,
-- matching `to3CNF' (const false) c` exactly.  All three paths take `2c + 5`
-- steps from `rd`.
-- ============================================================

/-- `pv0` reading an `endMark` pushes a `true` unit and enters `pv`.  The
pre-state is irrelevant. -/
lemma pv0_end_step (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.pv0, v, stk (FormulaSym.endMark :: rest) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (true :: V) F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · simp [stk, prog, Sstep]
  · simp [stk, prog, Sstep]
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `pv` loop: `i` `endMark`s become `i` `true` units on `val`.  The
pre-state is `St.rd endMark` (the state after `pv0` consumed its first
`endMark`), and the loop preserves it. -/
lemma pv_end_loop (i : Nat) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[i]
      (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk (List.replicate i FormulaSym.endMark ++ rest) T c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (List.replicate i true ++ V) F S O U⟩ : (mach).Cfg) := by
  induction i generalizing V with
  | zero =>
      rfl
  | succ i ih =>
      have h := pv_end_step (St.rd FormulaSym.endMark) (List.replicate i FormulaSym.endMark ++ rest) T c V F S O U
      rw [show (List.replicate (Nat.succ i) FormulaSym.endMark ++ rest) =
          FormulaSym.endMark :: (List.replicate i FormulaSym.endMark ++ rest) by
            rw [List.replicate_succ, List.cons_append]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[i]
          (Sstep (⟨some Label.pv, St.rd FormulaSym.endMark, stk (FormulaSym.endMark :: (List.replicate i FormulaSym.endMark ++ rest)) T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (List.replicate (Nat.succ i) true ++ V) F S O U⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (V := true :: V)
      calc
        (flip bind Sstep)^[i]
            (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk (List.replicate i FormulaSym.endMark ++ rest) T c (true :: V) F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (List.replicate i true ++ (true :: V)) F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c (List.replicate (Nat.succ i) true ++ V) F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> try simp [stk]
              · rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
                rw [← List.append_assoc]
                rw [replicate_append_one]

/-- The junk `const false` phase for a stray `endMark` (or end of input): emit
`[¬c]`, build the value variable `c`, restore the counter to `c + 1`, and reach
`reduce`. -/
lemma junkEnd_phase (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[2 * c + 5]
      (some (⟨some Label.rd, v, stk (FormulaSym.endMark :: rest) T c V F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk rest T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := rd_end_step v rest T c V F [] O U
  have h2 : Sstep (⟨some Label.const, St.rd FormulaSym.endMark, stk rest T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.rd FormulaSym.endMark, stk rest T c V F [] O U⟩ : (mach).Cfg) := by
    exact const_to_constFalse_step (St.rd FormulaSym.endMark) (by simp) rest T c V F [] O U
  have h3 := constFalse_generic_step (St.rd FormulaSym.endMark) rest T c V F [] O U
  have h4 := constEmit_phase c (St.rd FormulaSym.endMark) rest T V F []
      (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
  have h5 := constMake_phase c (St.done) rest T 0 V F
      (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  calc
    (flip bind Sstep)^[2 * c + 5]
        (some (⟨some Label.rd, v, stk (FormulaSym.endMark :: rest) T c V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[2 * c + 4]
          (some (⟨some Label.const, St.rd FormulaSym.endMark, stk rest T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 5 = (2 * c + 4) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h1
    _ = (flip bind Sstep)^[2 * c + 3]
          (some (⟨some Label.constFalse, St.rd FormulaSym.endMark, stk rest T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h2
    _ = (flip bind Sstep)^[2 * c + 2]
          (some (⟨some Label.constEmit, St.rd FormulaSym.endMark, stk rest T c V F []
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 3 = (2 * c + 2) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2] x) h3
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F
            (List.replicate c () ++ [])
            (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 2 = (c + 1) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h4
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.done, stk rest T 0 V F (List.replicate c ())
            (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep)^[c + 1] x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> simp [stk, List.append_nil]
    _ = some (⟨some Label.reduce, St.done, stk rest T (0 + c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
          rw [h5]
    _ = some (⟨some Label.reduce, St.done, stk rest T (c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
          have hrev : (encCNF [[Literal.neg c]]).reverse =
              List.replicate (c + 1) CNFSym.endMark ++
                [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
            simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
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

/-- The junk `const false` phase for an empty input: emit `[¬c]`, build the
value variable `c`, restore the counter to `c + 1`, and reach `reduce`. -/
lemma junkEmpty_phase (v : St) (T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) :
    (flip bind Sstep)^[2 * c + 5]
      (some (⟨some Label.rd, v, stk [] T c V F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk [] T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := rd_empty_step v T c V F [] O U
  have h2 : Sstep (⟨some Label.const, St.done, stk [] T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.constFalse, St.done, stk [] T c V F [] O U⟩ : (mach).Cfg) := by
    exact const_to_constFalse_step St.done (by simp) [] T c V F [] O U
  have h3 := constFalse_generic_step St.done [] T c V F [] O U
  have h4 := constEmit_phase c St.done [] T V F []
      (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
  have h5 := constMake_phase c St.done [] T 0 V F
      (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
  calc
    (flip bind Sstep)^[2 * c + 5]
        (some (⟨some Label.rd, v, stk [] T c V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[2 * c + 4]
          (some (⟨some Label.const, St.done, stk [] T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 5 = (2 * c + 4) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h1
    _ = (flip bind Sstep)^[2 * c + 3]
          (some (⟨some Label.constFalse, St.done, stk [] T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h2
    _ = (flip bind Sstep)^[2 * c + 2]
          (some (⟨some Label.constEmit, St.done, stk [] T c V F []
            (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 3 = (2 * c + 2) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2] x) h3
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.done, stk [] T 0 V F
            (List.replicate c () ++ [])
            (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          rw [show 2 * c + 2 = (c + 1) + (c + 1) by omega]
          rw [Function.iterate_add]
          exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h4
    _ = (flip bind Sstep)^[c + 1]
          (some (⟨some Label.constMake, St.done, stk [] T 0 V F (List.replicate c ())
            (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep)^[c + 1] x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> simp [stk, List.append_nil]
    _ = some (⟨some Label.reduce, St.done, stk [] T (0 + c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
          rw [h5]
    _ = some (⟨some Label.reduce, St.done, stk [] T (c + 1)
          (false :: List.replicate (c + 1) true ++ V) F []
          ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
          have hrev : (encCNF [[Literal.neg c]]).reverse =
              List.replicate (c + 1) CNFSym.endMark ++
                [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
            simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
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

/-- The junk `const false` phase for a `varMark` with no unary index run: emit
`[¬c]`, build the value variable `c`, restore the counter to `c + 1`, and reach
`reduce`. -/
lemma junkVar_phase (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) (hrest : rest.head? ≠ some FormulaSym.endMark) :
    (flip bind Sstep)^[2 * c + 5]
      (some (⟨some Label.rd, v, stk (FormulaSym.varMark :: rest) T c V F [] O U⟩ : (mach).Cfg))
    = some (⟨some Label.reduce, St.done, stk rest T (c + 1)
        (false :: List.replicate (c + 1) true ++ V) F []
        ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
  have h1 := rd_var_step v rest T c V F [] O U
  -- after `pv0` (which restores `rest`), the junk const machinery runs from
  -- `constFalse` with either the restored symbol's state or `St.reduce`.
  cases rest with
  | nil =>
      have h2 : Sstep (⟨some Label.pv0, St.rd FormulaSym.varMark, stk [] T c V F [] O U⟩ : (mach).Cfg)
          = some (⟨some Label.constFalse, St.reduce, stk [] T c V F [] O U⟩ : (mach).Cfg) := by
        exact pv0_empty_step (St.rd FormulaSym.varMark) T c V F [] O U
      have h3 := constFalse_generic_step St.reduce [] T c V F [] O U
      have h4 := constEmit_phase c St.reduce [] T V F []
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
      have h5 := constMake_phase c (St.done) [] T 0 V F
          (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
      calc
        (flip bind Sstep)^[2 * c + 5]
            (some (⟨some Label.rd, v, stk [FormulaSym.varMark] T c V F [] O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[2 * c + 4]
              (some (⟨some Label.pv0, St.rd FormulaSym.varMark, stk [] T c V F [] O U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 5 = (2 * c + 4) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h1
        _ = (flip bind Sstep)^[2 * c + 3]
              (some (⟨some Label.constFalse, St.reduce, stk [] T c V F [] O U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h2
        _ = (flip bind Sstep)^[2 * c + 2]
              (some (⟨some Label.constEmit, St.reduce, stk [] T c V F []
                (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 3 = (2 * c + 2) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2] x) h3
        _ = (flip bind Sstep)^[c + 1]
              (some (⟨some Label.constMake, St.done, stk [] T 0 V F
                (List.replicate c () ++ [])
                (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 2 = (c + 1) + (c + 1) by omega]
              rw [Function.iterate_add]
              exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h4
        _ = (flip bind Sstep)^[c + 1]
              (some (⟨some Label.constMake, St.done, stk [] T 0 V F (List.replicate c ())
                (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
              apply congrArg (fun x => (flip bind Sstep)^[c + 1] x)
              apply congrArg some
              apply Turing.TM2Comp.Cfg_ext
              · rfl
              · rfl
              · funext kk
                cases kk <;> simp [stk, List.append_nil]
        _ = some (⟨some Label.reduce, St.done, stk [] T (0 + c + 1)
              (false :: List.replicate (c + 1) true ++ V) F []
              (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
              rw [h5]
        _ = some (⟨some Label.reduce, St.done, stk [] T (c + 1)
              (false :: List.replicate (c + 1) true ++ V) F []
              ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
              have hrev : (encCNF [[Literal.neg c]]).reverse =
                  List.replicate (c + 1) CNFSym.endMark ++
                    [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
                simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
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
  | cons s rest' =>
      have hs : s ≠ FormulaSym.endMark := by
        intro hse
        apply hrest
        simp [hse]
      have h2 : Sstep (⟨some Label.pv0, St.rd FormulaSym.varMark, stk (s :: rest') T c V F [] O U⟩ : (mach).Cfg)
          = some (⟨some Label.constFalse, St.rd s, stk (s :: rest') T c V F [] O U⟩ : (mach).Cfg) := by
        exact pv0_junk_step (St.rd FormulaSym.varMark) s rest' T c V F [] O U hs
      have h3 := constFalse_generic_step (St.rd s) (s :: rest') T c V F [] O U
      have h4 := constEmit_phase c (St.rd s) (s :: rest') T V F []
          (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U
      have h5 := constMake_phase c (St.done) (s :: rest') T 0 V F
          (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U
      calc
        (flip bind Sstep)^[2 * c + 5]
            (some (⟨some Label.rd, v, stk (FormulaSym.varMark :: s :: rest') T c V F [] O U⟩ : (mach).Cfg))
          = (flip bind Sstep)^[2 * c + 4]
              (some (⟨some Label.pv0, St.rd FormulaSym.varMark, stk (s :: rest') T c V F [] O U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 5 = (2 * c + 4) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 4] x) h1
        _ = (flip bind Sstep)^[2 * c + 3]
              (some (⟨some Label.constFalse, St.rd s, stk (s :: rest') T c V F [] O U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 4 = (2 * c + 3) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 3] x) h2
        _ = (flip bind Sstep)^[2 * c + 2]
              (some (⟨some Label.constEmit, St.rd s, stk (s :: rest') T c V F []
                (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O) U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 3 = (2 * c + 2) + 1 by omega]
              rw [Function.iterate_add]
              rw [Function.iterate_one]
              exact congrArg (fun x => (flip bind Sstep)^[2 * c + 2] x) h3
        _ = (flip bind Sstep)^[c + 1]
              (some (⟨some Label.constMake, St.done, stk (s :: rest') T 0 V F
                (List.replicate c () ++ [])
                (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
              rw [show 2 * c + 2 = (c + 1) + (c + 1) by omega]
              rw [Function.iterate_add]
              exact congrArg (fun x => (flip bind Sstep)^[c + 1] x) h4
        _ = (flip bind Sstep)^[c + 1]
              (some (⟨some Label.constMake, St.done, stk (s :: rest') T 0 V F (List.replicate c ())
                (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg)) := by
              apply congrArg (fun x => (flip bind Sstep)^[c + 1] x)
              apply congrArg some
              apply Turing.TM2Comp.Cfg_ext
              · rfl
              · rfl
              · funext kk
                cases kk <;> simp [stk, List.append_nil]
        _ = some (⟨some Label.reduce, St.done, stk (s :: rest') T (0 + c + 1)
              (false :: List.replicate (c + 1) true ++ V) F []
              (List.replicate (c + 1) CNFSym.endMark ++ (CNFSym.varMark :: CNFSym.negMark :: CNFSym.clauseMark :: O)) U⟩ : (mach).Cfg) := by
              rw [h5]
        _ = some (⟨some Label.reduce, St.done, stk (s :: rest') T (c + 1)
              (false :: List.replicate (c + 1) true ++ V) F []
              ((encCNF [[Literal.neg c]]).reverse ++ O) U⟩ : (mach).Cfg) := by
              have hrev : (encCNF [[Literal.neg c]]).reverse =
                  List.replicate (c + 1) CNFSym.endMark ++
                    [CNFSym.varMark, CNFSym.negMark, CNFSym.clauseMark] := by
                simp [encCNF, encClause, encLit, litSym, litIndex, List.reverse_replicate]
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

/-- The variable phase: read `varEnc i`, push the value variable `i` onto `val`
(leaving the counter unchanged), and reach `reduce`. -/
lemma var_phase (i : Nat) (v : St) (rest T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (O U : List CNFSym) (hrest : rest.head? ≠ some FormulaSym.endMark) :
    ∃ v₁ : St, (flip bind Sstep)^[i + 3]
      (some (⟨some Label.rd, v, stk (varEnc i ++ rest) T c V F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, v₁, stk rest T c
          (false :: List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
  have h1 := rd_var_step v (List.replicate (i + 1) FormulaSym.endMark ++ rest) T c V F [] O U
  have h2 : Sstep (⟨some Label.pv0, St.rd FormulaSym.varMark, stk
      (List.replicate (i + 1) FormulaSym.endMark ++ rest) T c V F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.pv, St.rd FormulaSym.endMark, stk
          (List.replicate i FormulaSym.endMark ++ rest) T c (true :: V) F [] O U⟩ : (mach).Cfg) := by
      have hrep : List.replicate (i + 1) FormulaSym.endMark =
          FormulaSym.endMark :: List.replicate i FormulaSym.endMark := by
        rw [show i + 1 = Nat.succ i by omega]
        simp [List.replicate_succ]
      rw [hrep, List.cons_append]
      exact pv0_end_step (St.rd FormulaSym.varMark) (List.replicate i FormulaSym.endMark ++ rest) T c V F [] O U
  have h3 := pv_end_loop i rest T c (true :: V) F [] O U
  have h4 : ∃ w : St, Sstep (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c
      (List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg)
      = some (⟨some Label.reduce, w, stk rest T c
          (false :: List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
      cases rest with
      | nil => refine ⟨St.reduce, ?_⟩
               exact pv_empty_step (St.rd FormulaSym.endMark) T c (List.replicate (i + 1) true ++ V) F [] O U
      | cons s rest' =>
          have hs : s ≠ FormulaSym.endMark := by
            intro hse
            apply hrest
            simp [hse]
          refine ⟨St.rd s, ?_⟩
          exact pv_done_step (St.rd FormulaSym.endMark) s rest' T c (List.replicate (i + 1) true ++ V) F [] O U hs
  rcases h4 with ⟨w, h4⟩
  refine ⟨w, ?_⟩
  calc
    (flip bind Sstep)^[i + 3]
        (some (⟨some Label.rd, v, stk (varEnc i ++ rest) T c V F [] O U⟩ : (mach).Cfg))
      = (flip bind Sstep)^[i + 2]
          (some (⟨some Label.pv0, St.rd FormulaSym.varMark, stk
            (List.replicate (i + 1) FormulaSym.endMark ++ rest) T c V F [] O U⟩ : (mach).Cfg)) := by
          rw [show i + 3 = (i + 2) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[i + 2] x) h1
    _ = (flip bind Sstep)^[i + 1]
          (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk
            (List.replicate i FormulaSym.endMark ++ rest) T c (true :: V) F [] O U⟩ : (mach).Cfg)) := by
          rw [show i + 2 = (i + 1) + 1 by omega]
          rw [Function.iterate_add]
          rw [Function.iterate_one]
          exact congrArg (fun x => (flip bind Sstep)^[i + 1] x) h2
    _ = (flip bind Sstep)
          (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c
            (List.replicate i true ++ (true :: V)) F [] O U⟩ : (mach).Cfg)) := by
          rw [Function.iterate_succ_apply']
          exact congrArg (fun x => (flip bind Sstep) x) h3
    _ = (flip bind Sstep)
          (some (⟨some Label.pv, St.rd FormulaSym.endMark, stk rest T c
            (List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg)) := by
          apply congrArg (fun x => (flip bind Sstep) x)
          apply congrArg some
          apply Turing.TM2Comp.Cfg_ext
          · rfl
          · rfl
          · funext kk
            cases kk <;> try simp [stk]
            rw [show (true :: V) = [true] ++ V by simp [List.cons_append]]
            rw [← List.append_assoc]
            rw [replicate_append_one]
    _ = some (⟨some Label.reduce, w, stk rest T c
          (false :: List.replicate (i + 1) true ++ V) F [] O U⟩ : (mach).Cfg) := by
          exact h4

-- ============================================================
-- parse: the recursive descent (`parse_phase`)
--
-- The `parse_phase` lemma is the run lemma for the recursive descent.  For any
-- input `inp`, `decodeAux inp.length inp` extracts the first formula `f` and
-- the continuation `rest`; the machine reads `inp` from `rd`, emits the
-- reversed Tseitin clauses of `f` onto `o`, pushes `f`'s value variable onto
-- `val`, advances the counter past the auxiliary variables allocated for `f`,
-- and reaches `reduce` with the continuation `rest` on `in`.  Malformed input
-- (end of input, stray `endMark`, or a `varMark` with no index run) yields
-- `const false`, which the junk `const false` phases handle.
-- ============================================================

/-- Count the leading `endMark`s of a list, returning the count and the
suffix. -/
def endMarkRun : List FormulaSym → Nat × List FormulaSym
  | FormulaSym.endMark :: rest =>
      let (i, suf) := endMarkRun rest
      (i + 1, suf)
  | rest => (0, rest)

/-- `endMarkRun` splits a list at the first non-`endMark`. -/
lemma endMarkRun_spec (rest : List FormulaSym) :
    let (i, suf) := endMarkRun rest
    rest = List.replicate i FormulaSym.endMark ++ suf ∧ suf.head? ≠ some FormulaSym.endMark := by
  induction rest with
  | nil => simp [endMarkRun]
  | cons s rest' ih =>
      cases s with
      | endMark =>
          cases h : endMarkRun rest' with
          | mk i suf =>
              have hrest : rest' = List.replicate i FormulaSym.endMark ++ suf := by
                simpa [h] using ih.1
              have hsuf : suf.head? ≠ some FormulaSym.endMark := by
                simpa [h] using ih.2
              have hrun : endMarkRun (FormulaSym.endMark :: rest') = (i + 1, suf) := by
                rw [endMarkRun, h]
              rw [hrun]
              constructor
              · rw [hrest]
                rw [show FormulaSym.endMark :: (List.replicate i FormulaSym.endMark ++ suf) =
                    List.replicate (i + 1) FormulaSym.endMark ++ suf by
                      rw [show i + 1 = Nat.succ i by omega]
                      simp [List.replicate_succ, List.cons_append]]
              · simpa using hsuf
      | _ => simp [endMarkRun]

/-- `decodeVar` of a run of `k ≥ 1` `endMark`s yields the variable `k - 1`,
leaving the suffix untouched. -/
lemma decodeVar_endMarkRun (rest : List FormulaSym) (k : Nat) (suf : List FormulaSym)
    (hk : 1 ≤ k) (h : endMarkRun rest = (k, suf)) :
    decodeVar rest = (Formula.var (k - 1), suf) := by
  have hspec := endMarkRun_spec rest
  rw [h] at hspec
  have hrest : rest = List.replicate k FormulaSym.endMark ++ suf := by
    simpa using hspec.1
  have hsuf : ValidSuffix suf := by
    simpa [ValidSuffix] using hspec.2
  rw [hrest]
  have hk : k = (k - 1) + 1 := by omega
  rw [hk]
  exact decodeVar_enc (k - 1) hsuf

/-- A `var` decode means the input had a full unary index run: `decodeVar l =
(var i, rest)` implies `l` is `varEnc i` followed by a valid continuation. -/
lemma decodeVar_eq_var (l : List FormulaSym) (i : Nat) (rest : List FormulaSym)
    (h : decodeVar l = (Formula.var i, rest)) :
    l = List.replicate (i + 1) FormulaSym.endMark ++ rest ∧ rest.head? ≠ some FormulaSym.endMark := by
  have hl : l.head? = some FormulaSym.endMark := by
    by_contra hne
    cases l with
    | nil => simp [decodeVar] at h
    | cons s l' =>
        have hs : s ≠ FormulaSym.endMark := by
          intro hse
          apply hne
          simp [hse]
        simp [decodeVar, hs] at h
  cases hk : endMarkRun l with
  | mk k suf =>
      have hspec := endMarkRun_spec l
      rw [hk] at hspec
      have hk1 : 1 ≤ k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        rw [hk0'] at hspec
        have hsame : l = suf := by simpa using hspec.1
        have hne' : l.head? ≠ some FormulaSym.endMark := by
          rw [hsame]
          exact hspec.2
        exact hne' hl
      have hdec := decodeVar_endMarkRun l k suf hk1 hk
      rw [hdec] at h
      have hk' : k - 1 = i := by
        simpa using congrArg Prod.fst h
      have hsuf : suf = rest := congrArg Prod.snd h
      constructor
      · rw [hspec.1]
        rw [hsuf]
        rw [show k = i + 1 by omega]
      · rw [← hsuf]
        exact hspec.2

/-- The number of steps the machine takes to parse a formula `f` starting from
auxiliary index `c` (matching the phase lemma step counts). -/
def parseSteps : Formula → Nat → Nat
  | Formula.var i, c => i + 3
  | Formula.const b, c => if b then 2 * c + 4 else 2 * c + 5
  | Formula.not f, c =>
      let (_, y₁, c₁) := to3CNF' f c
      2 + parseSteps f c + (4 * c₁ + 3 * y₁ + 16)
  | Formula.and f g, c =>
      let (_, y₁, c₁) := to3CNF' f c
      let (_, y₂, c₂) := to3CNF' g c₁
      3 + parseSteps f c + parseSteps g c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)
  | Formula.or f g, c =>
      let (_, y₁, c₁) := to3CNF' f c
      let (_, y₂, c₂) := to3CNF' g c₁
      3 + parseSteps f c + parseSteps g c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)
  | Formula.iff f g, c =>
      let (_, y₁, c₁) := to3CNF' f c
      let (_, y₂, c₂) := to3CNF' g c₁
      3 + parseSteps f c + parseSteps g c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86)

/-- `decodeVarIdx` leaves a suffix no longer than its input. -/
lemma decodeVarIdx_suffix_le (i : Nat) (l : List FormulaSym) :
    (decodeVarIdx i l).2.length ≤ l.length := by
  induction l generalizing i with
  | nil => simp [decodeVarIdx]
  | cons s l' ih =>
      cases s with
      | endMark =>
          have h := ih (i + 1)
          simp [decodeVarIdx, List.length_cons]
          omega
      | _ => simp [decodeVarIdx]

/-- `decodeVar` leaves a suffix no longer than its input. -/
lemma decodeVar_suffix_le (l : List FormulaSym) :
    (decodeVar l).2.length ≤ l.length := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          have h := decodeVarIdx_suffix_le 0 l'
          simp [decodeVar, List.length_cons]
          omega
      | _ => simp [decodeVar]

lemma decodeAux_lit (b : Bool) (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.lit b :: l) = (Formula.const b, l) := by
  simp [decodeAux]

/-- `decodeAux` on the empty list is the junk `const false`. -/
lemma decodeAux_nil (b : Nat) :
    decodeAux b [] = (Formula.const false, []) := by
  cases b <;> simp [decodeAux]


/-- `decodeAux` on a `varMark` routes to `decodeVar`. -/
lemma decodeAux_varMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.varMark :: l) = decodeVar l := by
  simp [decodeAux]

/-- `decodeAux` on a stray `endMark` is the junk `const false`. -/
lemma decodeAux_endMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.endMark :: l) = (Formula.const false, l) := by
  simp [decodeAux]

/-- `decodeAux` on a `notMark` recurses with one less budget. -/
lemma decodeAux_notMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.notMark :: l) =
      (Formula.not (decodeAux n l).1, (decodeAux n l).2) := by
  simp [decodeAux]

/-- `decodeAux` on an `andMark` recurses with one less budget on both children. -/
lemma decodeAux_andMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.andMark :: l) =
      (Formula.and (decodeAux n l).1 (decodeAux n (decodeAux n l).2).1,
       (decodeAux n (decodeAux n l).2).2) := by
  simp [decodeAux]

/-- `decodeAux` on an `orMark` recurses with one less budget on both children. -/
lemma decodeAux_orMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.orMark :: l) =
      (Formula.or (decodeAux n l).1 (decodeAux n (decodeAux n l).2).1,
       (decodeAux n (decodeAux n l).2).2) := by
  simp [decodeAux]

/-- `decodeAux` on an `iffMark` recurses with one less budget on both children. -/
lemma decodeAux_iffMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.iffMark :: l) =
      (Formula.iff (decodeAux n l).1 (decodeAux n (decodeAux n l).2).1,
       (decodeAux n (decodeAux n l).2).2) := by
  simp [decodeAux]

/-- A non-empty input with a sufficient budget has `1 ≤ b`. -/
lemma budget_pos_of_cons (s : FormulaSym) (l : List FormulaSym) (b : Nat)
    (h : (s :: l).length ≤ b) : 1 ≤ b := by
  simp [List.length_cons] at h
  omega

/-- `decodeVarIdx` always yields a variable: it only ever counts `endMark`s. -/
lemma decodeVarIdx_is_var (i : Nat) (l : List FormulaSym) :
    ∃ k, (decodeVarIdx i l).1 = Formula.var k := by
  induction l generalizing i with
  | nil => refine ⟨i, ?_⟩; simp [decodeVarIdx]
  | cons s l' ih =>
      cases s with
      | endMark =>
          rcases ih (i + 1) with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          simp [decodeVarIdx] at hk ⊢
          exact hk
      | _ =>
          refine ⟨i, ?_⟩
          simp [decodeVarIdx]

/-- `decodeVar` never yields a `not` formula (only variables or the junk
`const false`). -/
lemma decodeVar_fst_ne_not (l : List FormulaSym) (f' : Formula) :
    (decodeVar l).1 ≠ Formula.not f' := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- `decodeVar` never yields `const true`. -/
lemma decodeVar_fst_ne_const_true (l : List FormulaSym) :
    (decodeVar l).1 ≠ Formula.const true := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- `decodeVar` never yields an `and`. -/
lemma decodeVar_fst_ne_and (l : List FormulaSym) (f' g' : Formula) :
    (decodeVar l).1 ≠ Formula.and f' g' := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- `decodeVar` never yields an `or`. -/
lemma decodeVar_fst_ne_or (l : List FormulaSym) (f' g' : Formula) :
    (decodeVar l).1 ≠ Formula.or f' g' := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- `decodeVar` never yields an `iff`. -/
lemma decodeVar_fst_ne_iff (l : List FormulaSym) (f' g' : Formula) :
    (decodeVar l).1 ≠ Formula.iff f' g' := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- Compose two machine segments: `^[n₁] A = B` and `^[n₂] B = C` give
`^[n₂ + n₁] A = C`. -/
lemma step_comp {A B C : Option (mach).Cfg} (n₁ n₂ : Nat)
    (h₁ : (flip bind Sstep)^[n₁] A = B) (h₂ : (flip bind Sstep)^[n₂] B = C) :
    (flip bind Sstep)^[n₂ + n₁] A = C := by
  rw [Function.iterate_add_apply]
  rw [h₁]
  rw [h₂]

/-- Three-step composition. -/
lemma step_comp3 {A B C D : Option (mach).Cfg} (n₁ n₂ n₃ : Nat)
    (h₁ : (flip bind Sstep)^[n₁] A = B) (h₂ : (flip bind Sstep)^[n₂] B = C)
    (h₃ : (flip bind Sstep)^[n₃] C = D) :
    (flip bind Sstep)^[n₃ + (n₂ + n₁)] A = D := by
  rw [Function.iterate_add_apply]
  rw [step_comp n₁ n₂ h₁ h₂]
  rw [h₃]

/-- Compose a single step followed by `n₂` steps. -/
lemma step_comp_single {A : Option (mach).Cfg} {B C : (mach).Cfg} (n₂ : Nat)
    (h₁ : Sstep B = some C) (h₂ : (flip bind Sstep)^[n₂] (some C) = A) :
    (flip bind Sstep)^[n₂ + 1] (some B) = A := by
  rw [Function.iterate_add_apply]
  rw [show (flip bind Sstep)^[1] (some B) = Sstep B by simp [flip]]
  rw [h₁]
  exact h₂

/-- Compose `n₁` steps followed by a single step. -/
lemma step_single_comp {A C : Option (mach).Cfg} {B : (mach).Cfg} (n₁ : Nat)
    (h₁ : (flip bind Sstep)^[n₁] A = some B) (h₂ : Sstep B = some C) :
    (flip bind Sstep)^[1 + n₁] A = some C := by
  rw [show 1 + n₁ = Nat.succ n₁ by omega]
  rw [Function.iterate_succ_apply']
  rw [h₁]
  change Sstep B = some C
  exact h₂

/-- `decodeAux` never lengthens the continuation. -/
lemma decodeAux_suffix_le (n : Nat) (l : List FormulaSym) :
    (decodeAux n l).2.length ≤ l.length := by
  revert n
  let P : List FormulaSym → Prop := fun l => ∀ n : Nat, (decodeAux n l).2.length ≤ l.length
  change P l
  refine WellFounded.induction (measure (fun l : List FormulaSym => l.length)).wf l ?_
  intro l ih
  dsimp [P] at ih ⊢
  intro n
  cases h : l with
  | nil => cases n <;> simp [decodeAux]
  | cons s l' =>
      cases n with
      | zero => simp [decodeAux]
      | succ n' =>
          cases s with
          | lit bl => rw [decodeAux_lit bl n' l']; change l'.length ≤ l'.length + 1; omega
          | varMark =>
              have h := decodeVar_suffix_le l'
              rw [decodeAux_varMark n' l']
              change (decodeVar l').2.length ≤ l'.length + 1
              omega
          | endMark => rw [decodeAux_endMark n' l']; change l'.length ≤ l'.length + 1; omega
          | notMark =>
              have h1 := ih l' (by rw [h]; change l'.length < l'.length + 1; omega) n'
              rw [decodeAux_notMark n' l']
              change (decodeAux n' l').2.length ≤ l'.length + 1
              omega
          | andMark =>
              have h1 := ih l' (by rw [h]; change l'.length < l'.length + 1; omega) n'
              let X : List FormulaSym := (decodeAux n' l').2
              have hXlen : X.length ≤ l'.length := by simpa [X] using h1
              have h2 := ih X (by rw [h]; change (decodeAux n' l').2.length < l'.length + 1; omega) n'
              rw [decodeAux_andMark n' l']
              change (decodeAux n' X).2.length ≤ l'.length + 1
              omega
          | orMark =>
              have h1 := ih l' (by rw [h]; change l'.length < l'.length + 1; omega) n'
              let X : List FormulaSym := (decodeAux n' l').2
              have hXlen : X.length ≤ l'.length := by simpa [X] using h1
              have h2 := ih X (by rw [h]; change (decodeAux n' l').2.length < l'.length + 1; omega) n'
              rw [decodeAux_orMark n' l']
              change (decodeAux n' X).2.length ≤ l'.length + 1
              omega
          | iffMark =>
              have h1 := ih l' (by rw [h]; change l'.length < l'.length + 1; omega) n'
              let X : List FormulaSym := (decodeAux n' l').2
              have hXlen : X.length ≤ l'.length := by simpa [X] using h1
              have h2 := ih X (by rw [h]; change (decodeAux n' l').2.length < l'.length + 1; omega) n'
              rw [decodeAux_iffMark n' l']
              change (decodeAux n' X).2.length ≤ l'.length + 1
              omega

/-- The parse statement: from `rd` with input `inp`, the machine parses the
first formula `f = decodeAux b inp .1`, emits its reversed Tseitin clauses onto
`o`, pushes its value variable, advances the counter past the auxiliary
variables allocated for `f`, and reaches `reduce` with the continuation `rest`
on `in`.  The budget `b` is passed down (`b - 1` per connective level) and
stays at least the remaining input length. -/
lemma parse_phase (f : Formula) (b : Nat) (inp rest : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (T : List FormulaSym) (O U : List CNFSym) (hV : V.head? ≠ some true)
    (hbudget : inp.length ≤ b) (hdec : decodeAux b inp = (f, rest)) :
    let (cls, y, next) := to3CNF' f c
    ∀ v₀ : St, ∃ v₁ : St, (flip bind Sstep)^[parseSteps f c]
      (some (⟨some Label.rd, v₀, stk inp T c V F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, v₁, stk rest T next
          (false :: List.replicate (y + 1) true ++ V) F []
          ((encCNF cls).reverse ++ O) U⟩ : (mach).Cfg) := by
  -- Induct on the formula, reverting the state parameters so the induction
  -- hypothesis lets the machine's counter, value stack, and frame stack
  -- evolve through the recursive descent.
  revert hV hbudget hdec b inp rest c V F T O U
  induction f with
  | var i =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hdec' : decodeVar l = (Formula.var i, rest) := by
                    simpa [decodeAux] using hdec
                  have hspec := decodeVar_eq_var l i rest hdec'
                  have hinp : FormulaSym.varMark :: l = varEnc i ++ rest := by
                    rw [hspec.1]
                    rfl
                  rw [hinp]
                  intro v₀
                  exact var_phase i v₀ rest T c V F O U hspec.2
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                      (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                        exact decodeAux_notMark b' l] at hdec
                  cases hdec
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                      (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                  cases hdec
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                      (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                  cases hdec
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                      (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                  cases hdec
  | const bt =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases bt with
      | true =>
          cases inp with
          | nil =>
              rw [decodeAux_nil b] at hdec
              cases hdec
          | cons s l =>
              have hb := budget_pos_of_cons s l b hbudget
              cases s with
              | lit bl =>
                  cases bl with
                  | true =>
                              cases b with
                      | zero => omega
                      | succ b' =>
                          have hrest : l = rest := by
                            simpa [decodeAux] using congrArg Prod.snd hdec
                          subst rest
                          intro v₀
                          refine ⟨St.done, ?_⟩
                          have h1' : (flip bind Sstep)^[1] (some (⟨some Label.rd, v₀, stk (FormulaSym.lit true :: l) T c V F [] O U⟩ : (mach).Cfg))
                              = some (⟨some Label.const, St.rd (FormulaSym.lit true), stk l T c V F [] O U⟩ : (mach).Cfg) := by
                            simpa [flip] using rd_lit_step v₀ true l T c V F [] O U
                          have h2 := const_phase_true c l T V F O U
                          have hc : parseSteps (Formula.const true) c = (2 * c + 3) + 1 := by
                            unfold parseSteps
                            simp
                          rw [hc]
                          simpa [encCNF, forceTrue] using step_comp 1 (2 * c + 3) h1' h2
                  | false =>
                              cases b with
                      | zero => omega
                      | succ b' =>
                          rw [show decodeAux (Nat.succ b') (FormulaSym.lit false :: l) =
                              (Formula.const false, l) by exact decodeAux_lit false b' l] at hdec
                          cases hdec
              | varMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                            exact decodeAux_varMark b' l] at hdec
                      have hne := decodeVar_fst_ne_const_true l
                      rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                            exact (Prod.eta (decodeVar l)).symm] at hdec
                      exact (hne (congrArg Prod.fst hdec)).elim
              | endMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                          (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                      cases hdec
              | notMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                          (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                            exact decodeAux_notMark b' l] at hdec
                      cases hdec
              | andMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                          (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                      cases hdec
              | orMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                          (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                      cases hdec
              | iffMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                          (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                      cases hdec
      | false =>
          cases inp with
          | nil =>
              rw [decodeAux_nil b] at hdec
              have hrest : rest = [] := congrArg Prod.snd hdec.symm
              subst rest
              intro v₀
              refine ⟨St.done, ?_⟩
              simpa [parseSteps, encCNF, forceFalse] using junkEmpty_phase v₀ T c V F O U
          | cons s l =>
              have hb := budget_pos_of_cons s l b hbudget
              cases s with
              | lit bl =>
                  cases bl with
                  | false =>
                              cases b with
                      | zero => omega
                      | succ b' =>
                          have hrest : l = rest := by
                            simpa [decodeAux] using congrArg Prod.snd hdec
                          subst rest
                          intro v₀
                          refine ⟨St.done, ?_⟩
                          have h1' : (flip bind Sstep)^[1] (some (⟨some Label.rd, v₀, stk (FormulaSym.lit false :: l) T c V F [] O U⟩ : (mach).Cfg))
                              = some (⟨some Label.const, St.rd (FormulaSym.lit false), stk l T c V F [] O U⟩ : (mach).Cfg) := by
                            simpa [flip] using rd_lit_step v₀ false l T c V F [] O U
                          have h2 := const_phase_false c l T V F O U
                          have hc : parseSteps (Formula.const false) c = (2 * c + 4) + 1 := by
                            unfold parseSteps
                            simp
                          rw [hc]
                          simpa [encCNF, forceFalse] using step_comp 1 (2 * c + 4) h1' h2
                  | true =>
                              cases b with
                      | zero => omega
                      | succ b' =>
                          rw [show decodeAux (Nat.succ b') (FormulaSym.lit true :: l) =
                              (Formula.const true, l) by exact decodeAux_lit true b' l] at hdec
                          cases hdec
              | varMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      have hdec' : decodeVar l = (Formula.const false, rest) := by
                        simpa [decodeAux] using hdec
                      have hl : l.head? ≠ some FormulaSym.endMark := by
                        by_contra hne
                        cases l with
                        | nil => simp at hne
                        | cons s' l' =>
                            have hs' : s' = FormulaSym.endMark := by simpa using hne
                            have hdecv : decodeVar (FormulaSym.endMark :: l') = (Formula.const false, rest) := by
                              simpa [hs'] using hdec'
                            rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl] at hdecv
                            rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
                            have hfst : (decodeVarIdx 0 l').1 = Formula.const false := congrArg Prod.fst hdecv
                            rw [hk] at hfst
                            cases hfst
                      have hrest : rest = l := by
                        have hdec'' : decodeVar l = (Formula.const false, l) := by
                          cases l with
                          | nil => simp [decodeVar]
                          | cons s' l' =>
                              have hs' : s' ≠ FormulaSym.endMark := by
                                intro hse
                                apply hl
                                simp [hse]
                              simp [decodeVar, hs']
                        exact (congrArg Prod.snd (hdec''.symm.trans hdec')).symm
                      subst rest
                      intro v₀
                      refine ⟨St.done, ?_⟩
                      simpa [parseSteps, encCNF, forceFalse] using junkVar_phase v₀ l T c V F O U hl
              | endMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      have hrest : l = rest := by
                        simpa [decodeAux] using congrArg Prod.snd hdec
                      subst rest
                      intro v₀
                      refine ⟨St.done, ?_⟩
                      simpa [parseSteps, encCNF, forceFalse] using junkEnd_phase v₀ l T c V F O U
              | notMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                          (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                            exact decodeAux_notMark b' l] at hdec
                      cases hdec
              | andMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                          (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                      cases hdec
              | orMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                          (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                      cases hdec
              | iffMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                          (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                      cases hdec
  | not f' ih =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hdec' : decodeAux b' l = (f', rest) := by
                    have hfst : (decodeAux b' l).1 = f' := by
                      simpa [decodeAux] using congrArg Prod.fst hdec
                    have hsnd : (decodeAux b' l).2 = rest := by
                      simpa [decodeAux] using congrArg Prod.snd hdec
                    exact Prod.ext hfst hsnd
                  have hbudget' : l.length ≤ b' := by
                    simp [List.length_cons] at hbudget
                    omega
                  have hparsec := ih b' l rest c V (Frame.not :: F) T O U hV hbudget' hdec'
                  intro v₀
                  rcases hparsec (St.rd FormulaSym.notMark) with ⟨v₁, hparsecv⟩
                  rcases hdec_f' : to3CNF' f' c with ⟨cls', y₁, c₁⟩
                  have h1 := rd_not_step v₀ l T c V F [] O U
                  have h2' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₁, stk rest T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.not :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.emitNot, St.emitNot, stk rest T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) F []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_not_step v₁ rest T c₁
                      (false :: List.replicate (y₁ + 1) true ++ V) F [] ((encCNF cls').reverse ++ O) U
                  have h3 := not_phase rest T c₁ y₁ V F ((encCNF cls').reverse ++ O) U hV
                  have hcomp1 := step_comp_single (parseSteps f' c) h1 hparsecv
                  have hcomp1' : (flip bind Sstep)^[parseSteps f' c + 1]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.notMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₁, stk rest T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.not :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f'] using hcomp1
                  have hcomp2 := step_comp (parseSteps f' c + 1) 1 hcomp1' h2'
                  have hcomp := step_comp (1 + (parseSteps f' c + 1)) (4 * c₁ + 3 * y₁ + 16) hcomp2 h3
                  have hc : parseSteps (Formula.not f') c = (4 * c₁ + 3 * y₁ + 16) + (1 + (parseSteps f' c + 1)) := by
                    conv_lhs =>
                      unfold parseSteps
                      rw [hdec_f']
                    simp
                    omega
                  rw [hc]
                  refine ⟨St.done, ?_⟩
                  simpa [encCNF, List.flatMap_append, List.reverse_append, List.append_assoc, to3CNF', hdec_f'] using hcomp
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                        exact decodeAux_varMark b' l] at hdec
                  -- decodeVar never yields a `not`
                  have hnot : (decodeVar l).1 ≠ Formula.not f' := by
                    cases l with
                    | nil => simp [decodeVar]
                    | cons s' l' =>
                        cases s' with
                        | endMark =>
                            rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
                            rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
                            rw [hk]
                            simp
                        | _ => simp [decodeVar]
                  rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                        exact (Prod.eta (decodeVar l)).symm] at hdec
                  exact (hnot (congrArg Prod.fst hdec)).elim
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                      (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                  cases hdec
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                      (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                  cases hdec
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                      (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                  cases hdec
  | and f' g' ihf ihg =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hf' : (decodeAux b' l).1 = f' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_andMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.and f _ => f | _ => Formula.const false) h
                  have hg' : (decodeAux b' (decodeAux b' l).2).1 = g' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_andMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.and _ g => g | _ => Formula.const false) h
                  have hrest : (decodeAux b' (decodeAux b' l).2).2 = rest := by
                    have h := congrArg Prod.snd hdec
                    rw [decodeAux_andMark b' l] at h
                    exact h
                  let rest₁ := (decodeAux b' l).2
                  have hdec1 : decodeAux b' l = (f', rest₁) := Prod.ext hf' rfl
                  have hdec2 : decodeAux b' rest₁ = (g', rest) := by
                    simpa [rest₁] using Prod.ext hg' hrest
                  have hbudget₁ : l.length ≤ b' := by
                    simp [List.length_cons] at hbudget
                    omega
                  have hbudget₂ : rest₁.length ≤ b' := by
                    have hsuf := decodeAux_suffix_le b' l
                    have : rest₁.length ≤ l.length := by
                      simpa [rest₁] using hsuf
                    omega
                  have hparsec1 := ihf b' l rest₁ c V (Frame.and₁ :: F) T O U hV hbudget₁ hdec1
                  rcases hdec_f' : to3CNF' f' c with ⟨cls', y₁, c₁⟩
                  rcases hdec_g' : to3CNF' g' c₁ with ⟨cls'', y₂, c₂⟩
                  have hV' : (false :: List.replicate (y₁ + 1) true ++ V).head? ≠ some true := by
                    simp
                  have hparsec2 := ihg b' rest₁ rest c₁ (false :: List.replicate (y₁ + 1) true ++ V)
                    (Frame.and₂ :: F) T ((encCNF cls').reverse ++ O) U hV' hbudget₂ hdec2
                  intro v₀
                  rcases hparsec1 (St.rd FormulaSym.andMark) with ⟨v₁, hparsec1v⟩
                  rcases hparsec2 (St.and₁Done) with ⟨v₂, hparsec2v⟩
                  have h1 := rd_and_step v₀ l T c V F [] O U
                  have h2' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.and₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.rd, St.and₁Done, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.and₂ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_and₁_step v₁ rest₁ T c₁
                      (false :: List.replicate (y₁ + 1) true ++ V) F [] ((encCNF cls').reverse ++ O) U
                  have h5' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.and₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.emitAnd, St.emitAnd, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_and₂_step v₂ rest T c₂
                      (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U
                  have h6 := emitAnd_phase rest T c₂ y₁ y₂ V F ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U hV
                  have hcomp1 := step_comp_single (parseSteps f' c) h1 hparsec1v
                  have hcomp1' : (flip bind Sstep)^[parseSteps f' c + 1]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.andMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.and₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f'] using hcomp1
                  have hcomp2 := step_comp (parseSteps f' c + 1) 1 hcomp1' h2'
                  have hcomp3 := step_comp (1 + (parseSteps f' c + 1)) (parseSteps g' c₁) hcomp2 hparsec2v
                  have hcomp3' : (flip bind Sstep)^[parseSteps g' c₁ + (1 + (parseSteps f' c + 1))]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.andMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.and₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f', hdec_g'] using hcomp3
                  have hcomp4 := step_comp (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))) 1 hcomp3' h5'
                  have hcomp := step_comp (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))))
                    (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) hcomp4 h6
                  have hc : parseSteps (Formula.and f' g') c =
                      (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) + (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1)))) := by
                    have hm1 : (match (cls', y₁, c₁) with | (fst, y₁, c₁) => match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) =
    (match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) := by rfl
                    have hm2 :
                        (match (cls'', y₂, c₂) with
                          | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) =
                        3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) := by rfl
                    conv_lhs =>
                      unfold parseSteps
                      rw [hdec_f']
                      rw [hm1]
                      rw [hdec_g']
                      rw [hm2]
                    omega
                  rw [hc]
                  refine ⟨St.done, ?_⟩
                  simpa [encCNF, List.flatMap_append, List.reverse_append, List.append_assoc, to3CNF', hdec_f', hdec_g'] using hcomp
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                        exact decodeAux_varMark b' l] at hdec
                  have hne := decodeVar_fst_ne_and l f' g'
                  rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                        exact (Prod.eta (decodeVar l)).symm] at hdec
                  exact (hne (congrArg Prod.fst hdec)).elim
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                      (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                        exact decodeAux_notMark b' l] at hdec
                  cases hdec
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                      (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                  cases hdec
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                      (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                  cases hdec
  | or f' g' ihf ihg =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hf' : (decodeAux b' l).1 = f' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_orMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.or f _ => f | _ => Formula.const false) h
                  have hg' : (decodeAux b' (decodeAux b' l).2).1 = g' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_orMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.or _ g => g | _ => Formula.const false) h
                  have hrest : (decodeAux b' (decodeAux b' l).2).2 = rest := by
                    have h := congrArg Prod.snd hdec
                    rw [decodeAux_orMark b' l] at h
                    exact h
                  let rest₁ := (decodeAux b' l).2
                  have hdec1 : decodeAux b' l = (f', rest₁) := Prod.ext hf' rfl
                  have hdec2 : decodeAux b' rest₁ = (g', rest) := by
                    simpa [rest₁] using Prod.ext hg' hrest
                  have hbudget₁ : l.length ≤ b' := by
                    simp [List.length_cons] at hbudget
                    omega
                  have hbudget₂ : rest₁.length ≤ b' := by
                    have hsuf := decodeAux_suffix_le b' l
                    have : rest₁.length ≤ l.length := by
                      simpa [rest₁] using hsuf
                    omega
                  have hparsec1 := ihf b' l rest₁ c V (Frame.or₁ :: F) T O U hV hbudget₁ hdec1
                  rcases hdec_f' : to3CNF' f' c with ⟨cls', y₁, c₁⟩
                  rcases hdec_g' : to3CNF' g' c₁ with ⟨cls'', y₂, c₂⟩
                  have hV' : (false :: List.replicate (y₁ + 1) true ++ V).head? ≠ some true := by
                    simp
                  have hparsec2 := ihg b' rest₁ rest c₁ (false :: List.replicate (y₁ + 1) true ++ V)
                    (Frame.or₂ :: F) T ((encCNF cls').reverse ++ O) U hV' hbudget₂ hdec2
                  intro v₀
                  rcases hparsec1 (St.rd FormulaSym.orMark) with ⟨v₁, hparsec1v⟩
                  rcases hparsec2 (St.or₁Done) with ⟨v₂, hparsec2v⟩
                  have h1 := rd_or_step v₀ l T c V F [] O U
                  have h2' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.or₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.rd, St.or₁Done, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.or₂ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_or₁_step v₁ rest₁ T c₁
                      (false :: List.replicate (y₁ + 1) true ++ V) F [] ((encCNF cls').reverse ++ O) U
                  have h5' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.or₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.emitOr, St.emitOr, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_or₂_step v₂ rest T c₂
                      (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U
                  have h6 := emitOr_phase rest T c₂ y₁ y₂ V F ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U hV
                  have hcomp1 := step_comp_single (parseSteps f' c) h1 hparsec1v
                  have hcomp1' : (flip bind Sstep)^[parseSteps f' c + 1]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.orMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.or₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f'] using hcomp1
                  have hcomp2 := step_comp (parseSteps f' c + 1) 1 hcomp1' h2'
                  have hcomp3 := step_comp (1 + (parseSteps f' c + 1)) (parseSteps g' c₁) hcomp2 hparsec2v
                  have hcomp3' : (flip bind Sstep)^[parseSteps g' c₁ + (1 + (parseSteps f' c + 1))]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.orMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.or₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f', hdec_g'] using hcomp3
                  have hcomp4 := step_comp (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))) 1 hcomp3' h5'
                  have hcomp := step_comp (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))))
                    (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) hcomp4 h6
                  have hc : parseSteps (Formula.or f' g') c =
                      (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) + (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1)))) := by
                    have hm1 : (match (cls', y₁, c₁) with | (fst, y₁, c₁) => match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) =
    (match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) := by rfl
                    have hm2 :
                        (match (cls'', y₂, c₂) with
                          | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) =
                        3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) := by rfl
                    conv_lhs =>
                      unfold parseSteps
                      rw [hdec_f']
                      rw [hm1]
                      rw [hdec_g']
                      rw [hm2]
                    omega
                  rw [hc]
                  refine ⟨St.done, ?_⟩
                  simpa [encCNF, List.flatMap_append, List.reverse_append, List.append_assoc, to3CNF', hdec_f', hdec_g'] using hcomp
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                        exact decodeAux_varMark b' l] at hdec
                  have hne := decodeVar_fst_ne_or l f' g'
                  rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                        exact (Prod.eta (decodeVar l)).symm] at hdec
                  exact (hne (congrArg Prod.fst hdec)).elim
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                      (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                        exact decodeAux_notMark b' l] at hdec
                  cases hdec
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                      (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                  cases hdec
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                      (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                  cases hdec
  | iff f' g' ihf ihg =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hf' : (decodeAux b' l).1 = f' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_iffMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.iff f _ => f | _ => Formula.const false) h
                  have hg' : (decodeAux b' (decodeAux b' l).2).1 = g' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_iffMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.iff _ g => g | _ => Formula.const false) h
                  have hrest : (decodeAux b' (decodeAux b' l).2).2 = rest := by
                    have h := congrArg Prod.snd hdec
                    rw [decodeAux_iffMark b' l] at h
                    exact h
                  let rest₁ := (decodeAux b' l).2
                  have hdec1 : decodeAux b' l = (f', rest₁) := Prod.ext hf' rfl
                  have hdec2 : decodeAux b' rest₁ = (g', rest) := by
                    simpa [rest₁] using Prod.ext hg' hrest
                  have hbudget₁ : l.length ≤ b' := by
                    simp [List.length_cons] at hbudget
                    omega
                  have hbudget₂ : rest₁.length ≤ b' := by
                    have hsuf := decodeAux_suffix_le b' l
                    have : rest₁.length ≤ l.length := by
                      simpa [rest₁] using hsuf
                    omega
                  have hparsec1 := ihf b' l rest₁ c V (Frame.iff₁ :: F) T O U hV hbudget₁ hdec1
                  rcases hdec_f' : to3CNF' f' c with ⟨cls', y₁, c₁⟩
                  rcases hdec_g' : to3CNF' g' c₁ with ⟨cls'', y₂, c₂⟩
                  have hV' : (false :: List.replicate (y₁ + 1) true ++ V).head? ≠ some true := by
                    simp
                  have hparsec2 := ihg b' rest₁ rest c₁ (false :: List.replicate (y₁ + 1) true ++ V)
                    (Frame.iff₂ :: F) T ((encCNF cls').reverse ++ O) U hV' hbudget₂ hdec2
                  intro v₀
                  rcases hparsec1 (St.rd FormulaSym.iffMark) with ⟨v₁, hparsec1v⟩
                  rcases hparsec2 (St.iff₁Done) with ⟨v₂, hparsec2v⟩
                  have h1 := rd_iff_step v₀ l T c V F [] O U
                  have h2' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.iff₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.rd, St.iff₁Done, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.iff₂ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_iff₁_step v₁ rest₁ T c₁
                      (false :: List.replicate (y₁ + 1) true ++ V) F [] ((encCNF cls').reverse ++ O) U
                  have h5' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.iff₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.emitIff, St.emitIff, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_iff₂_step v₂ rest T c₂
                      (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U
                  have h6 := emitIff_phase rest T c₂ y₁ y₂ V F ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U hV
                  have hcomp1 := step_comp_single (parseSteps f' c) h1 hparsec1v
                  have hcomp1' : (flip bind Sstep)^[parseSteps f' c + 1]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.iffMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.iff₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f'] using hcomp1
                  have hcomp2 := step_comp (parseSteps f' c + 1) 1 hcomp1' h2'
                  have hcomp3 := step_comp (1 + (parseSteps f' c + 1)) (parseSteps g' c₁) hcomp2 hparsec2v
                  have hcomp3' : (flip bind Sstep)^[parseSteps g' c₁ + (1 + (parseSteps f' c + 1))]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.iffMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.iff₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f', hdec_g'] using hcomp3
                  have hcomp4 := step_comp (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))) 1 hcomp3' h5'
                  have hcomp := step_comp (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))))
                    (8 * c₂ + 7 * y₁ + 15 * y₂ + 86) hcomp4 h6
                  have hc : parseSteps (Formula.iff f' g') c =
                      (8 * c₂ + 7 * y₁ + 15 * y₂ + 86) + (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1)))) := by
                    have hm1 : (match (cls', y₁, c₁) with | (fst, y₁, c₁) => match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86)) =
    (match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86)) := by rfl
                    have hm2 :
                        (match (cls'', y₂, c₂) with
                          | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86)) =
                        3 + parseSteps f' c + parseSteps g' c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86) := by rfl
                    conv_lhs =>
                      unfold parseSteps
                      rw [hdec_f']
                      rw [hm1]
                      rw [hdec_g']
                      rw [hm2]
                    omega
                  rw [hc]
                  refine ⟨St.done, ?_⟩
                  simpa [encCNF, List.flatMap_append, List.reverse_append, List.append_assoc, to3CNF', hdec_f', hdec_g'] using hcomp
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                        exact decodeAux_varMark b' l] at hdec
                  have hne := decodeVar_fst_ne_iff l f' g'
                  rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                        exact (Prod.eta (decodeVar l)).symm] at hdec
                  exact (hne (congrArg Prod.fst hdec)).elim
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                      (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                        exact decodeAux_notMark b' l] at hdec
                  cases hdec
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                      (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                  cases hdec
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                      (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                  cases hdec
-- ============================================================
-- copyOut: transfer `o` to `out` (reversing it back), then halt
-- ============================================================

/-- `copyOut` pops one symbol from `o` and pushes it onto `out`. -/
lemma copyOut_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (s : CNFSym) (O U : List CNFSym) :
    Sstep (⟨some Label.copyOut, v, stk inp T c V F S (s :: O) U⟩ : (mach).Cfg)
      = some (⟨some Label.copyOut, St.copySym s, stk inp T c V F S O (s :: U)⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `copyOut` with `o` empty goes to `clearIn`, resetting the state to `init`. -/
lemma copyOut_done (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (U : List CNFSym) :
    Sstep (⟨some Label.copyOut, v, stk inp T c V F S [] U⟩ : (mach).Cfg)
      = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `copyOut` phase: transfer `o` to `out` (reversing it back), then reach
`clearIn` with the state reset to `init`. -/
lemma copyOut_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[O.length + 1]
      (some (⟨some Label.copyOut, v, stk inp T c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] (O.reverse ++ U)⟩ : (mach).Cfg) := by
  induction O generalizing v U with
  | nil =>
      have h := copyOut_done v inp T c V F S U
      change (flip bind Sstep) (some (⟨some Label.copyOut, v, stk inp T c V F S [] U⟩ : (mach).Cfg))
        = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] U⟩ : (mach).Cfg)
      simpa [flip] using h
  | cons s rest ih =>
      have h := copyOut_step v inp T c V F S s rest U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.copyOut, v, stk inp T c V F S (s :: rest) U⟩ : (mach).Cfg))
        = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] ((s :: rest).reverse ++ U)⟩ : (mach).Cfg)
      rw [h]
      have hih := ih (St.copySym s) (s :: U)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.copyOut, St.copySym s, stk inp T c V F S rest (s :: U)⟩ : (mach).Cfg))
          = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] (rest.reverse ++ (s :: U))⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.clearIn, St.init, stk inp T c V F S [] ((s :: rest).reverse ++ U)⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.append_assoc]

/-- The `done` label halts, leaving the state at `init`. -/
lemma done_step (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (U : List CNFSym) :
    Sstep (⟨some Label.done, St.init, stk inp T c V F S [] U⟩ : (mach).Cfg)
      = some (⟨none, St.init, stk inp T c V F S [] U⟩ : (mach).Cfg) := by
  simp [Sstep, prog]

/-- `clearIn` pops one junk symbol from `in` and discards it.  The pre-state is
irrelevant (the `clearIn` pop overwrites it). -/
lemma clearIn_step (v : St) (s : FormulaSym) (inp T : List FormulaSym) (c : Nat)
    (V : List Bool) (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.clearIn, v, stk (s :: inp) T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.clearIn, St.rd s, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- `clearIn` with `in` empty goes to `clearCnt`, setting the state to `done`.
The pre-state is irrelevant (the `clearIn` pop overwrites it). -/
lemma clearIn_done (v : St) (T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.clearIn, v, stk [] T c V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.clearCnt, St.done, stk [] T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `clearIn` phase: discard the junk left on `in`, then reach `clearCnt`. -/
lemma clearIn_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[inp.length + 1]
      (some (⟨some Label.clearIn, v, stk inp T c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.clearCnt, St.done, stk [] T c V F S O U⟩ : (mach).Cfg) := by
  induction inp generalizing v with
  | nil =>
      have h := clearIn_done v T c V F S O U
      change (flip bind Sstep) (some (⟨some Label.clearIn, v, stk [] T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.clearCnt, St.done, stk [] T c V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | cons s rest ih =>
      have h := clearIn_step v s rest T c V F S O U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.clearIn, v, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.clearCnt, St.done, stk [] T c V F S O U⟩ : (mach).Cfg)
      rw [h]
      exact ih (v := St.rd s)

/-- `clearCnt` pops one counter unit and discards it.  The pre-state is
irrelevant (the `clearCnt` pop overwrites it). -/
lemma clearCnt_step (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.clearCnt, v, stk inp T (c + 1) V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.clearCnt, St.done, stk inp T c V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep, List.replicate_succ]

/-- `clearCnt` with the counter empty goes to `done`, resetting the state to
`init`.  The pre-state is irrelevant (the `clearCnt` pop overwrites it). -/
lemma clearCnt_done (v : St) (inp T : List FormulaSym) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    Sstep (⟨some Label.clearCnt, v, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      = some (⟨some Label.done, St.init, stk inp T 0 V F S O U⟩ : (mach).Cfg) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [stk, Function.update, prog, Sstep]

/-- The `clearCnt` phase: discard the remaining counter units, then reach `done`
with the counter empty. -/
lemma clearCnt_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[c + 1]
      (some (⟨some Label.clearCnt, v, stk inp T c V F S O U⟩ : (mach).Cfg))
    = some (⟨some Label.done, St.init, stk inp T 0 V F S O U⟩ : (mach).Cfg) := by
  induction c generalizing v with
  | zero =>
      have h := clearCnt_done v inp T V F S O U
      change (flip bind Sstep) (some (⟨some Label.clearCnt, v, stk inp T 0 V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      simpa [flip] using h
  | succ c ih =>
      have h := clearCnt_step v inp T c V F S O U
      rw [show Nat.succ c + 1 = (c + 1) + 1 by rfl]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[c + 1]
          (Sstep (⟨some Label.clearCnt, v, stk inp T (Nat.succ c) V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stk inp T 0 V F S O U⟩ : (mach).Cfg)
      rw [show Nat.succ c = c + 1 by rfl]
      rw [h]
      exact ih (v := St.done)

-- ============================================================
-- polynomial time: bounds and the full run (`outputsFun`)
-- ============================================================

/-- Both the value variable and the next auxiliary index of a formula are
bounded by `c` plus the encoding length. -/
lemma to3CNF'_bounds (f : Formula) (c : Nat) :
    (to3CNF' f c).2.1 ≤ c + (enc f).length ∧
    (to3CNF' f c).2.2 ≤ c + (enc f).length := by
  induction f generalizing c with
  | var i =>
      constructor <;> simp [to3CNF', enc, varEnc] <;> omega
  | const b =>
      by_cases hb : b
      · constructor <;> simp [to3CNF', hb, forceTrue, forceFalse, enc] <;> omega
      · constructor <;> simp [to3CNF', hb, forceTrue, forceFalse, enc] <;> omega
  | not f' ih =>
      constructor
      · simp [to3CNF', enc, List.length_cons]
        have h := (ih c).2
        nlinarith
      · simp [to3CNF', enc, List.length_cons]
        have h := (ih c).2
        nlinarith
  | and f' g' ihf ihg =>
      constructor
      · simp [to3CNF', enc, List.length_cons]
        have hf := (ihf c).2
        have hg := (ihg (to3CNF' f' c).2.2).2
        nlinarith
      · simp [to3CNF', enc, List.length_cons]
        have hf := (ihf c).2
        have hg := (ihg (to3CNF' f' c).2.2).2
        nlinarith
  | or f' g' ihf ihg =>
      constructor
      · simp [to3CNF', enc, List.length_cons]
        have hf := (ihf c).2
        have hg := (ihg (to3CNF' f' c).2.2).2
        nlinarith
      · simp [to3CNF', enc, List.length_cons]
        have hf := (ihf c).2
        have hg := (ihg (to3CNF' f' c).2.2).2
        nlinarith
  | iff f' g' ihf ihg =>
      constructor
      · simp [to3CNF', enc, List.length_cons]
        have hf := (ihf c).2
        have hg := (ihg (to3CNF' f' c).2.2).2
        nlinarith
      · simp [to3CNF', enc, List.length_cons]
        have hf := (ihf c).2
        have hg := (ihg (to3CNF' f' c).2.2).2
        nlinarith

/-- The number of clauses in the Tseitin encoding is bounded by four times the
encoding length: each `not` adds two clauses and one symbol, each `and`/`or`
adds three clauses and one symbol (beyond the children), and each `iff` adds
four clauses and one symbol. -/
lemma to3CNF'_clauses_num_le (f : Formula) (c : Nat) :
    (to3CNF' f c).1.length ≤ 4 * (enc f).length := by
  induction f generalizing c with
  | var i => simp [to3CNF', enc, varEnc]
  | const b => by_cases hb : b <;> simp [to3CNF', hb, enc, forceTrue, forceFalse]
  | not f' ih =>
      have hc : (to3CNF' f' c).1.length ≤ 4 * (enc f').length := ih c
      simp [to3CNF', enc, notClauses, List.length_cons]
      nlinarith
  | and f' g' ihf ihg =>
      have hc1 : (to3CNF' f' c).1.length ≤ 4 * (enc f').length := ihf c
      have hc2 : (to3CNF' g' (to3CNF' f' c).2.2).1.length ≤ 4 * (enc g').length :=
        ihg (to3CNF' f' c).2.2
      simp [to3CNF', enc, andClauses, List.length_cons]
      nlinarith
  | or f' g' ihf ihg =>
      have hc1 : (to3CNF' f' c).1.length ≤ 4 * (enc f').length := ihf c
      have hc2 : (to3CNF' g' (to3CNF' f' c).2.2).1.length ≤ 4 * (enc g').length :=
        ihg (to3CNF' f' c).2.2
      simp [to3CNF', enc, orClauses, List.length_cons]
      nlinarith
  | iff f' g' ihf ihg =>
      have hc1 : (to3CNF' f' c).1.length ≤ 4 * (enc f').length := ihf c
      have hc2 : (to3CNF' g' (to3CNF' f' c).2.2).1.length ≤ 4 * (enc g').length :=
        ihg (to3CNF' f' c).2.2
      simp [to3CNF', enc, iffClauses, List.length_cons]
      nlinarith

/-- The parse step count is bounded by a quadratic in the encoding length. -/
lemma parseSteps_le (f : Formula) (c : Nat) :
    parseSteps f c ≤ 40 * (enc f).length * (c + (enc f).length + 1) := by
  induction f generalizing c with
  | var i =>
      simp [parseSteps, enc, varEnc]
      nlinarith
  | const b =>
      by_cases hb : b <;> simp [parseSteps, enc, hb] <;> omega
  | not f' ih =>
      have hn : (enc f').length ≥ 1 := by
        cases f' <;> simp [enc, varEnc]
      have hb := to3CNF'_bounds f' c
      rcases to3CNF' f' c with ⟨cl, y1, c1⟩
      rcases hb with ⟨hy, hc1⟩
      have hsteps : parseSteps f' c ≤ 40 * (enc f').length * (c + (enc f').length + 1) := ih c
      simp [parseSteps, enc]
      nlinarith
  | and f' g' ihf ihg =>
      have hn : (enc f').length ≥ 1 := by
        cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by
        cases g' <;> simp [enc, varEnc]
      have hb1 := to3CNF'_bounds f' c
      rcases hb1 with ⟨hy1, hc1⟩
      have hb2 := to3CNF'_bounds g' (to3CNF' f' c).2.2
      rcases hb2 with ⟨hy2, hc2⟩
      have hf : parseSteps f' c ≤ 40 * (enc f').length * (c + (enc f').length + 1) := ihf c
      have hg : parseSteps g' (to3CNF' f' c).2.2 ≤
          40 * (enc g').length * ((to3CNF' f' c).2.2 + (enc g').length + 1) :=
        ihg (to3CNF' f' c).2.2
      simp [parseSteps, enc]
      nlinarith
  | or f' g' ihf ihg =>
      have hn : (enc f').length ≥ 1 := by
        cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by
        cases g' <;> simp [enc, varEnc]
      have hb1 := to3CNF'_bounds f' c
      rcases hb1 with ⟨hy1, hc1⟩
      have hb2 := to3CNF'_bounds g' (to3CNF' f' c).2.2
      rcases hb2 with ⟨hy2, hc2⟩
      have hf : parseSteps f' c ≤ 40 * (enc f').length * (c + (enc f').length + 1) := ihf c
      have hg : parseSteps g' (to3CNF' f' c).2.2 ≤
          40 * (enc g').length * ((to3CNF' f' c).2.2 + (enc g').length + 1) :=
        ihg (to3CNF' f' c).2.2
      simp [parseSteps, enc]
      nlinarith
  | iff f' g' ihf ihg =>
      have hn : (enc f').length ≥ 1 := by
        cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by
        cases g' <;> simp [enc, varEnc]
      have hb1 := to3CNF'_bounds f' c
      rcases hb1 with ⟨hy1, hc1⟩
      have hb2 := to3CNF'_bounds g' (to3CNF' f' c).2.2
      rcases hb2 with ⟨hy2, hc2⟩
      have hf : parseSteps f' c ≤ 40 * (enc f').length * (c + (enc f').length + 1) := ihf c
      have hg : parseSteps g' (to3CNF' f' c).2.2 ≤
          40 * (enc g').length * ((to3CNF' f' c).2.2 + (enc g').length + 1) :=
        ihg (to3CNF' f' c).2.2
      simp [parseSteps, enc]
      nlinarith

/-- `decodeAux` decodes a formula whose encoding is bounded by twice the number
of consumed symbols plus one.  The constant is forced to `1`: composing the
`2·consumed + 1` bounds of two subformulas under a binary node gives
`2·(consumed₁ + consumed₂ + 1) + 1`, exactly the bound for the combined
consumption. -/
lemma decodeAux_enc_consumed_le (n : Nat) (l : List FormulaSym) :
    (enc (decodeAux n l).1).length ≤ 2 * (l.length - (decodeAux n l).2.length) + 1 := by
  revert n
  refine WellFounded.induction (measure List.length).wf l
    (C := fun l' => ∀ (n : Nat),
      (enc (decodeAux n l').1).length ≤ 2 * (l'.length - (decodeAux n l').2.length) + 1) ?_
  intro l ih n
  cases l with
  | nil => cases n <;> simp [decodeAux, enc]
  | cons s rest =>
      have hlt_rest : rest.length < (s :: rest).length := by
        simp [List.length_cons]
      cases n with
      | zero => simp [decodeAux, enc]
      | succ n' =>
          cases s with
          | lit _ => simp [decodeAux, enc]
          | varMark =>
              by_cases h : rest.head? = some FormulaSym.endMark
              · rcases hrun : endMarkRun rest with ⟨k, suf⟩
                have hspec := endMarkRun_spec rest
                rw [hrun] at hspec
                have hrep : rest = List.replicate k FormulaSym.endMark ++ suf := hspec.1
                have hk : 1 ≤ k := by
                  by_contra hk0
                  have hk0' : k = 0 := by omega
                  have : rest = suf := by
                    rw [hk0'] at hrep
                    simpa using hrep
                  rw [this] at h
                  exact hspec.2 h
                have hdec := decodeVar_endMarkRun rest k suf hk hrun
                have hlen : rest.length = k + suf.length := by
                  rw [hrep]
                  simp [List.length_replicate, List.length_append]
                have hk1 : k ≤ rest.length := by omega
                simp [decodeAux, hdec, enc, varEnc]
                omega
              · cases rest with
                | nil => simp [decodeAux, decodeVar, enc]
                | cons s0 t =>
                    have hsne : s0 ≠ FormulaSym.endMark := by
                      intro hse
                      simp [hse] at h
                    simp [decodeAux, decodeVar, enc, hsne]
          | endMark => simp [decodeAux, enc]
          | notMark =>
              have h1 : (enc (decodeAux n' rest).1).length ≤
                  2 * (rest.length - (decodeAux n' rest).2.length) + 1 :=
                ih rest hlt_rest n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              simp [decodeAux, enc, List.length_cons]
              omega
          | andMark =>
              have h1 : (enc (decodeAux n' rest).1).length ≤
                  2 * (rest.length - (decodeAux n' rest).2.length) + 1 :=
                ih rest hlt_rest n'
              have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                  2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 1 :=
                ih (decodeAux n' rest).2
                  (Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) hlt_rest) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                decodeAux_suffix_le n' (decodeAux n' rest).2
              simp [decodeAux, enc, List.length_cons]
              omega
          | orMark =>
              have h1 : (enc (decodeAux n' rest).1).length ≤
                  2 * (rest.length - (decodeAux n' rest).2.length) + 1 :=
                ih rest hlt_rest n'
              have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                  2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 1 :=
                ih (decodeAux n' rest).2
                  (Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) hlt_rest) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                decodeAux_suffix_le n' (decodeAux n' rest).2
              simp [decodeAux, enc, List.length_cons]
              omega
          | iffMark =>
              have h1 : (enc (decodeAux n' rest).1).length ≤
                  2 * (rest.length - (decodeAux n' rest).2.length) + 1 :=
                ih rest hlt_rest n'
              have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                  2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 1 :=
                ih (decodeAux n' rest).2
                  (Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) hlt_rest) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                decodeAux_suffix_le n' (decodeAux n' rest).2
              simp [decodeAux, enc, List.length_cons]
              omega

/-- The encoding of the decoded formula is at most double the input plus three. -/
lemma enc_decode_le (x : List FormulaSym) :
    (enc (decode x)).length ≤ 2 * x.length + 3 := by
  have h := decodeAux_enc_consumed_le x.length x
  have hle : x.length - (decodeAux x.length x).2.length ≤ x.length := by omega
  simpa [decode] using (by omega : (enc (decodeAux x.length x).1).length ≤ 2 * x.length + 3)

/-- The number of original variables of a decoded formula is at most the input
length. -/
lemma numVars_decode_le (x : List FormulaSym) : numVars (decode x) ≤ x.length := by
  let P : List FormulaSym → Prop := fun l => ∀ n, numVars (decodeAux n l).1 ≤ l.length
  have hP : P x := by
    dsimp [P]
    refine WellFounded.induction (measure (fun l : List FormulaSym => l.length)).wf x
        (C := fun l => ∀ n, numVars (decodeAux n l).1 ≤ l.length) ?_
    intro l ih
    intro n
    cases l with
    | nil => cases n <;> simp [decodeAux, numVars]
    | cons s rest =>
        cases n with
        | zero => simp [decodeAux, numVars]
        | succ n' =>
            cases s with
            | lit _ => simp [decodeAux, numVars]
            | varMark =>
                by_cases h : rest.head? = some FormulaSym.endMark
                · rcases hrun : endMarkRun rest with ⟨k, suf⟩
                  have hspec := endMarkRun_spec rest
                  rw [hrun] at hspec
                  have hrep : rest = List.replicate k FormulaSym.endMark ++ suf := hspec.1
                  have hk : 1 ≤ k := by
                    by_contra hk0
                    have hk0' : k = 0 := by omega
                    have : rest = suf := by
                      rw [hk0'] at hrep
                      simpa using hrep
                    rw [this] at h
                    exact hspec.2 h
                  have hdec := decodeVar_endMarkRun rest k suf hk hrun
                  have hlen : rest.length = k + suf.length := by
                    rw [hrep]
                    simp [List.length_replicate, List.length_append]
                  simp [decodeAux, hdec, numVars]
                  omega
                · cases rest with
                  | nil => simp [decodeAux, decodeVar, numVars]
                  | cons s0 t =>
                      have hsne : s0 ≠ FormulaSym.endMark := by
                        intro hse
                        simp [hse] at h
                      simp [decodeAux, decodeVar, numVars, hsne]
            | endMark => simp [decodeAux, numVars]
            | notMark =>
                have h1 : numVars (decodeAux n' rest).1 ≤ rest.length :=
                  ih rest (by
                    change rest.length < (FormulaSym.notMark :: rest).length
                    simpa [List.length_cons] using Nat.lt_succ_self rest.length) n'
                simp [decodeAux, numVars]
                omega
            | andMark =>
                have h1 : numVars (decodeAux n' rest).1 ≤ rest.length :=
                  ih rest (by
                    change rest.length < (FormulaSym.andMark :: rest).length
                    simpa [List.length_cons] using Nat.lt_succ_self rest.length) n'
                have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                    (decodeAux n' rest).2.length := by
                  refine ih (decodeAux n' rest).2 ?_ n'
                  change (decodeAux n' rest).2.length < (FormulaSym.andMark :: rest).length
                  simpa [List.length_cons] using
                    Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) (Nat.lt_succ_self rest.length)
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                simp [decodeAux, numVars]
                omega
            | orMark =>
                have h1 : numVars (decodeAux n' rest).1 ≤ rest.length :=
                  ih rest (by
                    change rest.length < (FormulaSym.orMark :: rest).length
                    simpa [List.length_cons] using Nat.lt_succ_self rest.length) n'
                have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                    (decodeAux n' rest).2.length := by
                  refine ih (decodeAux n' rest).2 ?_ n'
                  change (decodeAux n' rest).2.length < (FormulaSym.orMark :: rest).length
                  simpa [List.length_cons] using
                    Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) (Nat.lt_succ_self rest.length)
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                simp [decodeAux, numVars]
                omega
            | iffMark =>
                have h1 : numVars (decodeAux n' rest).1 ≤ rest.length :=
                  ih rest (by
                    change rest.length < (FormulaSym.iffMark :: rest).length
                    simpa [List.length_cons] using Nat.lt_succ_self rest.length) n'
                have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                    (decodeAux n' rest).2.length := by
                  refine ih (decodeAux n' rest).2 ?_ n'
                  change (decodeAux n' rest).2.length < (FormulaSym.iffMark :: rest).length
                  simpa [List.length_cons] using
                    Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) (Nat.lt_succ_self rest.length)
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                simp [decodeAux, numVars]
                omega
  simpa [decode, P] using hP x.length
/-- The encoded Tseitin clauses are bounded by a quadratic in the encoding
length. -/
lemma encCNF_to3CNF'_le (f : Formula) (c : Nat) :
    (encCNF (to3CNF' f c).1).length ≤
      12 * (enc f).length * (c + (enc f).length + 1) + 6 * (enc f).length := by
  induction f generalizing c with
  | var i => simp [to3CNF', enc, varEnc, encCNF]
  | const b => by_cases hb : b <;> simp [to3CNF', hb, enc, encCNF, forceTrue, forceFalse, encClause, encLit, litSym, litIndex] <;> omega
  | not f' ih =>
      rcases h : to3CNF' f' c with ⟨cl, y1, c1⟩
      have hc : (encCNF cl).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa [h] using ih c
      have hn : (enc f').length ≥ 1 := by cases f' <;> simp [enc, varEnc]
      have hy1 : y1 ≤ c + (enc f').length := by simpa [h] using (to3CNF'_bounds f' c).1
      have hc1 : c1 ≤ c + (enc f').length := by simpa [h] using (to3CNF'_bounds f' c).2
      have hnext : c ≤ c1 := by
        have hg := to3CNF'_next_ge f' c
        rw [h] at hg
        exact hg
      have hcl : cl.length ≤ 4 * (enc f').length := by simpa [h] using to3CNF'_clauses_num_le f' c
      have hnotc : (encCNF (notClauses c1 y1)).length ≤ 12 * (c + (enc f').length + 1) + 30 := by
        simp [encCNF, notClauses, encClause, encLit, litSym, litIndex]
        nlinarith
      have hsplit : (encCNF (cl ++ notClauses c1 y1)).length =
          (encCNF cl).length + (encCNF (notClauses c1 y1)).length := by
        simp [encCNF, List.length_append, List.flatMap_append]
      simp [to3CNF', enc, h]
      nlinarith [hsplit]
  | and f' g' ihf ihg =>
      rcases h1 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases h2 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa [h1] using ihf c
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa [h2] using ihg c1
      have hn : (enc f').length ≥ 1 := by cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by cases g' <;> simp [enc, varEnc]
      have hy1 : y1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).1
      have hc1' : c1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).2
      have hy2 : y2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).1
      have hc2' : c2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).2
      have hnext : c ≤ c1 := by
        have hg := to3CNF'_next_ge f' c
        rw [h1] at hg
        exact hg
      have hcl1 : cl1.length ≤ 4 * (enc f').length := by simpa [h1] using to3CNF'_clauses_num_le f' c
      have hcl2 : cl2.length ≤ 4 * (enc g').length := by simpa [h2] using to3CNF'_clauses_num_le g' c1
      have hclc : (encCNF (andClauses c2 y1 y2)).length ≤ 12 * (c1 + (enc f').length + (enc g').length + 1) + 30 := by
        simp [encCNF, andClauses, encClause, encLit, litSym, litIndex]
        nlinarith
      have hsplit : (encCNF (cl1 ++ (cl2 ++ andClauses c2 y1 y2))).length =
          (encCNF cl1).length + (encCNF cl2).length + (encCNF (andClauses c2 y1 y2)).length := by
        simp [encCNF, List.length_append, List.flatMap_append, Nat.add_assoc]
      simp [to3CNF', enc, h1, h2]
      nlinarith [hsplit]
  | or f' g' ihf ihg =>
      rcases h1 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases h2 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa [h1] using ihf c
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa [h2] using ihg c1
      have hn : (enc f').length ≥ 1 := by cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by cases g' <;> simp [enc, varEnc]
      have hy1 : y1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).1
      have hc1' : c1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).2
      have hy2 : y2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).1
      have hc2' : c2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).2
      have hnext : c ≤ c1 := by
        have hg := to3CNF'_next_ge f' c
        rw [h1] at hg
        exact hg
      have hcl1 : cl1.length ≤ 4 * (enc f').length := by simpa [h1] using to3CNF'_clauses_num_le f' c
      have hcl2 : cl2.length ≤ 4 * (enc g').length := by simpa [h2] using to3CNF'_clauses_num_le g' c1
      have hclc : (encCNF (orClauses c2 y1 y2)).length ≤ 12 * (c1 + (enc f').length + (enc g').length + 1) + 30 := by
        simp [encCNF, orClauses, encClause, encLit, litSym, litIndex]
        nlinarith
      have hsplit : (encCNF (cl1 ++ (cl2 ++ orClauses c2 y1 y2))).length =
          (encCNF cl1).length + (encCNF cl2).length + (encCNF (orClauses c2 y1 y2)).length := by
        simp [encCNF, List.length_append, List.flatMap_append, Nat.add_assoc]
      simp [to3CNF', enc, h1, h2]
      nlinarith [hsplit]
  | iff f' g' ihf ihg =>
      rcases h1 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases h2 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa [h1] using ihf c
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa [h2] using ihg c1
      have hn : (enc f').length ≥ 1 := by cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by cases g' <;> simp [enc, varEnc]
      have hy1 : y1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).1
      have hc1' : c1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).2
      have hy2 : y2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).1
      have hc2' : c2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).2
      have hnext : c ≤ c1 := by
        have hg := to3CNF'_next_ge f' c
        rw [h1] at hg
        exact hg
      have hcl1 : cl1.length ≤ 4 * (enc f').length := by simpa [h1] using to3CNF'_clauses_num_le f' c
      have hcl2 : cl2.length ≤ 4 * (enc g').length := by simpa [h2] using to3CNF'_clauses_num_le g' c1
      have hclc : (encCNF (iffClauses c2 y1 y2)).length ≤ 12 * (c1 + (enc f').length + (enc g').length + 1) + 40 := by
        simp [encCNF, iffClauses, encClause, encLit, litSym, litIndex]
        nlinarith
      have hsplit : (encCNF (cl1 ++ (cl2 ++ iffClauses c2 y1 y2))).length =
          (encCNF cl1).length + (encCNF cl2).length + (encCNF (iffClauses c2 y1 y2)).length := by
        simp [encCNF, List.length_append, List.flatMap_append, Nat.add_assoc]
      simp [to3CNF', enc, h1, h2]
      nlinarith [hsplit]
/-- The input alphabet of the machine is `FormulaSym`. -/
def satInputAlphabet : (mach).Γ (mach).k₀ ≃ FormulaSym := Equiv.refl _

/-- The output alphabet of the machine is `CNFSym`. -/
def satOutputAlphabet : (mach).Γ (mach).k₁ ≃ CNFSym := Equiv.refl _

/-- The polynomial time bound. -/
noncomputable def satTo3CNFTime : Polynomial ℕ :=
  800 * Polynomial.X ^ 2 + 3000 * Polynomial.X + 2000

/-- `count` from any pre-state: the count step pops from `in` and overwrites the
state, so `count_phase_aux` (stated from `St.rd default`) applies from the
machine's initial state `St.init` as well. -/
lemma count_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[inp.length + 1]
        (some (⟨some Label.count, v, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.reorder, St.done, stk [] (inp.reverse ++ T) (c + inp.length) V F S O U⟩ : (mach).Cfg) := by
  induction inp generalizing T c v with
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
      have hih := ih (v := St.rd s) (T := s :: T) (c := c + 1)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.count, St.rd s, stk rest (s :: T) (c + 1) V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.reorder, St.done, stk [] (rest.reverse ++ (s :: T)) ((c + 1) + rest.length) V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reorder, St.done, stk [] ((s :: rest).reverse ++ T) (c + (s :: rest).length) V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, List.length_cons, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- `reorder` from any pre-state: the reorder step pops from `temp` and
overwrites the state, so `reorder_phase_aux` (stated from `St.rd default`)
applies from the state `St.done` left by the count phase. -/
lemma reorder_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[T.length + 1]
        (some (⟨some Label.reorder, v, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.rd, St.done, stk (T.reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
  induction T generalizing inp v with
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
      have hih := ih (inp := s :: inp) (v := St.rd s)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.reorder, St.rd s, stk (s :: inp) rest c V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.rd, St.done, stk (rest.reverse ++ (s :: inp)) [] c V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.rd, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- The full machine run: count, reorder, the recursive descent, the root unit
clause, copying `o` to `out`, and clearing the junk.  The final `out` tape is
`encCNF (to3CNF_len (decode inp) inp.length)`. -/
noncomputable def satTo3CNFOutputsFun (inp : List FormulaSym) :
    TM2OutputsInTime mach inp (some (encCNF (to3CNF_len (decode inp) inp.length))) (satTo3CNFTime.eval inp.length) := by
  let n := inp.length
  let f0 := decode inp
  let rest := (decodeAux n inp).2
  let cls := (to3CNF' f0 n).1
  let y := (to3CNF' f0 n).2.1
  let next := (to3CNF' f0 n).2.2
  let outList := encCNF (to3CNF_len f0 n)
  let initC : (mach).Cfg := ⟨some Label.count, St.init, stk inp [] 0 [] [] [] [] []⟩
  let C1 : (mach).Cfg := ⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩
  let C2 : (mach).Cfg := ⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩
  have hdec : decodeAux n inp = (f0, rest) := by
    change decodeAux inp.length inp = (f0, rest)
    rfl
  have hV : ([] : List Bool).head? ≠ some true := by simp
  have hparse0 : ∀ v₀ : St, ∃ v₁ : St,
      (flip bind Sstep)^[parseSteps f0 n]
        (some (⟨some Label.rd, v₀, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, v₁, stk rest [] next
            (false :: List.replicate (y + 1) true) [] []
            ((encCNF cls).reverse) []⟩ : (mach).Cfg) := by
    intro v₀
    simpa using parse_phase f0 n inp rest n [] [] [] [] [] hV le_rfl hdec v₀
  have hparse_done : ∃ v₁ : St,
      (flip bind Sstep)^[parseSteps f0 n]
        (some (⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, v₁, stk rest [] next
            (false :: List.replicate (y + 1) true) [] []
            ((encCNF cls).reverse) []⟩ : (mach).Cfg) := hparse0 St.done
  let v₁ : St := Classical.choose hparse_done
  have hparse : (flip bind Sstep)^[parseSteps f0 n]
      (some (⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, v₁, stk rest [] next
          (false :: List.replicate (y + 1) true) [] []
          ((encCNF cls).reverse) []⟩ : (mach).Cfg) := by
    simpa [v₁] using Classical.choose_spec hparse_done
  let C3 : (mach).Cfg := ⟨some Label.reduce, v₁, stk rest [] next
      (false :: List.replicate (y + 1) true) [] [] ((encCNF cls).reverse) []⟩
  let C4 : (mach).Cfg := ⟨some Label.emitTrue, St.emitTrue, stk rest [] next
      (false :: List.replicate (y + 1) true) [] [] ((encCNF cls).reverse) []⟩
  let C5 : (mach).Cfg := ⟨some Label.copyOut, St.done, stk rest [] next [] [] []
      ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse) []⟩
  let C6 : (mach).Cfg := ⟨some Label.clearIn, St.init, stk rest [] next [] [] [] [] (C5.stk K.o).reverse⟩
  let C7 : (mach).Cfg := ⟨some Label.clearCnt, St.done, stk [] [] next [] [] [] [] (C5.stk K.o).reverse⟩
  let C8 : (mach).Cfg := ⟨some Label.done, St.init, stk [] [] 0 [] [] [] [] (C5.stk K.o).reverse⟩
  let C9 : (mach).Cfg := ⟨none, St.init, stk [] [] 0 [] [] [] [] (C5.stk K.o).reverse⟩
  have hcount : EvalsToInTime Sstep initC (some C1) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some initC) = some C1
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.count, St.init, stk inp [] 0 [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩ : (mach).Cfg)
    rw [count_phase St.init inp [] 0 [] [] [] [] []]
    simp [n, List.append_nil, Nat.zero_add]
  have hreorder : EvalsToInTime Sstep C1 (some C2) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some C1) = some C2
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg)
    rw [show n + 1 = inp.reverse.length + 1 by simp [n, List.length_reverse]]
    rw [reorder_phase St.done [] inp.reverse n [] [] [] [] []]
    simp [n, List.reverse_reverse]
  have hparseE : EvalsToInTime Sstep C2 (some C3) (parseSteps f0 n) := by
    refine ⟨⟨parseSteps f0 n, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[parseSteps f0 n] (some C2) = some C3
    exact hparse
  have hreduce : EvalsToInTime Sstep C3 (some C4) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some C3) = some C4
    exact reduce_top_step v₁ rest [] next (false :: List.replicate (y + 1) true) [] ((encCNF cls).reverse) []
  have hemTrue : EvalsToInTime Sstep C4 (some C5) ((y + 1) + 2) := by
    refine ⟨⟨(y + 1) + 2, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[(y + 1) + 2] (some C4) = some C5
    exact emitTrue_phase y St.emitTrue rest [] next [] [] ((encCNF cls).reverse) []
  have hcopyOut : EvalsToInTime Sstep C5 (some C6) ((C5.stk K.o).length + 1) := by
    refine ⟨⟨(C5.stk K.o).length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse).length + 1]
        (some (⟨some Label.copyOut, St.done, stk rest [] next [] [] []
            ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse) []⟩ : (mach).Cfg))
        = some (⟨some Label.clearIn, St.init, stk rest [] next [] [] [] []
            ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse).reverse⟩ : (mach).Cfg)
    rw [copyOut_phase St.done rest [] next [] [] []
        ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse) []]
    simp [List.append_nil]
  have hclearIn : EvalsToInTime Sstep C6 (some C7) (rest.length + 1) := by
    refine ⟨⟨rest.length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[rest.length + 1]
        (some (⟨some Label.clearIn, St.init, stk rest [] next [] [] [] [] (C5.stk K.o).reverse⟩ : (mach).Cfg))
        = some (⟨some Label.clearCnt, St.done, stk [] [] next [] [] [] [] (C5.stk K.o).reverse⟩ : (mach).Cfg)
    rw [clearIn_phase St.init rest [] next [] [] [] [] (C5.stk K.o).reverse]
  have hclearCnt : EvalsToInTime Sstep C7 (some C8) (next + 1) := by
    refine ⟨⟨next + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[next + 1]
        (some (⟨some Label.clearCnt, St.done, stk [] [] next [] [] [] [] (C5.stk K.o).reverse⟩ : (mach).Cfg))
        = some (⟨some Label.done, St.init, stk [] [] 0 [] [] [] [] (C5.stk K.o).reverse⟩ : (mach).Cfg)
    rw [clearCnt_phase St.done [] [] next [] [] [] [] (C5.stk K.o).reverse]
  have hdone : EvalsToInTime Sstep C8 (some C9) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some C8) = some C9
    exact done_step [] [] 0 [] [] [] (C5.stk K.o).reverse
  have h12 : EvalsToInTime Sstep initC (some C2) ((n + 1) + (n + 1)) :=
    EvalsToInTime.trans Sstep (n + 1) (n + 1) initC C1 (some C2) hcount hreorder
  have h123 : EvalsToInTime Sstep initC (some C3) (parseSteps f0 n + ((n + 1) + (n + 1))) :=
    EvalsToInTime.trans Sstep ((n + 1) + (n + 1)) (parseSteps f0 n) initC C2 (some C3) h12 hparseE
  have h1234 : EvalsToInTime Sstep initC (some C4) (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))) :=
    EvalsToInTime.trans Sstep (parseSteps f0 n + ((n + 1) + (n + 1))) 1 initC C3 (some C4) h123 hreduce
  have h12345 : EvalsToInTime Sstep initC (some C5) (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))) :=
    EvalsToInTime.trans Sstep (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))) ((y + 1) + 2) initC C4 (some C5) h1234 hemTrue
  have h123456 : EvalsToInTime Sstep initC (some C6) ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))))) :=
    EvalsToInTime.trans Sstep (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))) ((C5.stk K.o).length + 1) initC C5 (some C6) h12345 hcopyOut
  have h1234567 : EvalsToInTime Sstep initC (some C7) (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))) :=
    EvalsToInTime.trans Sstep ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))))) (rest.length + 1) initC C6 (some C7) h123456 hclearIn
  have h12345678 : EvalsToInTime Sstep initC (some C8) (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))))))) :=
    EvalsToInTime.trans Sstep (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))) (next + 1) initC C7 (some C8) h1234567 hclearCnt
  have h123456789 : EvalsToInTime Sstep initC (some C9) (1 + (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))))) :=
    EvalsToInTime.trans Sstep (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))))))) 1 initC C8 (some C9) h12345678 hdone
  have hout : (C5.stk K.o).reverse = encCNF (to3CNF_len f0 n) := by
    have hrev : (C5.stk K.o).reverse = encCNF cls ++ encCNF [[Literal.pos y]] := by
      simp [C5, List.reverse_append, List.reverse_reverse]
    have htl : to3CNF_len f0 n = cls ++ [[Literal.pos y]] := by
      simp [to3CNF_len, cls, y, forceTrue]
    rw [hrev, htl]
    simp [encCNF]
  have hfinalCfg : C9 = haltList mach outList := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [C9, haltList, outList, hout]
  have hinit : initList mach inp = initC := by
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k <;> simp [initC, initList, stk]
  have hparse_le : parseSteps f0 n ≤ 240 * n * n + 680 * n + 480 := by
    have h := parseSteps_le f0 n
    have hf0 : (enc f0).length ≤ 2 * n + 3 := by
      simpa [f0, n] using enc_decode_le inp
    have helen0 : 0 ≤ (enc f0).length := by simp
    nlinarith [h, hf0, helen0]
  have hbounds := to3CNF'_bounds f0 n
  have hy_le : y ≤ 3 * n + 3 := by
    have hy0 : y ≤ n + (enc f0).length := by simpa [y] using hbounds.1
    have hf0 : (enc f0).length ≤ 2 * n + 3 := by simpa [f0, n] using enc_decode_le inp
    nlinarith [hy0, hf0]
  have hnext_le : next ≤ 3 * n + 3 := by
    have hn0 : next ≤ n + (enc f0).length := by simpa [next] using hbounds.2
    have hf0 : (enc f0).length ≤ 2 * n + 3 := by simpa [f0, n] using enc_decode_le inp
    nlinarith [hn0, hf0]
  have henc : (encCNF cls).length ≤ 72 * n * n + 216 * n + 162 := by
    have h := encCNF_to3CNF'_le f0 n
    have hcl : (encCNF cls).length ≤ 12 * (enc f0).length * (n + (enc f0).length + 1) + 6 * (enc f0).length := by
      simpa [cls] using h
    have hf0 : (enc f0).length ≤ 2 * n + 3 := by simpa [f0, n] using enc_decode_le inp
    have helen0 : 0 ≤ (enc f0).length := by simp
    nlinarith [hcl, hf0, helen0]
  have hoLen : (C5.stk K.o).length ≤ 72 * n * n + 219 * n + 169 := by
    have hlen : (C5.stk K.o).length = (encCNF [[Literal.pos y]]).length + (encCNF cls).length := by
      simp [C5, List.length_append]
    have hyenc : (encCNF [[Literal.pos y]]).length = y + 4 := by
      simp [encCNF, encClause, encLit, litSym, litIndex]
    rw [hlen, hyenc]
    nlinarith [hy_le, henc]
  have hrest_le : rest.length ≤ n := by
    have h := decodeAux_suffix_le n inp
    simpa [rest, n] using h
  have hct : satTo3CNFTime.eval n = 800 * n * n + 3000 * n + 2000 := by
    simp [satTo3CNFTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_natCast]
    ring
  have htotal_le :
      1 + (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))))
        ≤ satTo3CNFTime.eval n := by
    rw [hct]
    nlinarith [hparse_le, hy_le, hnext_le, hoLen, hrest_le]
  have hfull : EvalsToInTime Sstep initC (some (haltList mach outList))
      (1 + (next + 1 + (rest.length + 1 + ((C5.stk K.o).length + 1 + (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))))))) := by
    simpa [hfinalCfg] using h123456789
  change EvalsToInTime Sstep (initList mach inp) (some (haltList mach outList))
      (satTo3CNFTime.eval inp.length)
  rw [hinit]
  exact ⟨hfull.toEvalsTo, le_trans hfull.steps_le_m htotal_le⟩

/-- The reduction machine computes the 3-CNF encoding in polynomial time. -/
noncomputable def satTo3CNFComputableInPolyTime :
    TM2ComputableInPolyTime (id : List FormulaSym → List FormulaSym) (id : List CNFSym → List CNFSym)
      (fun inp => encCNF (to3CNF_len (decode inp) inp.length)) where
  tm := mach
  inputAlphabet := satInputAlphabet
  outputAlphabet := satOutputAlphabet
  time := satTo3CNFTime
  outputsFun := fun inp => by
    simpa [satInputAlphabet, satOutputAlphabet] using satTo3CNFOutputsFun inp

end TM3CNF

end Turing

end Chapter34

end CLRS
