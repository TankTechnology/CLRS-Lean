import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B1_Machine

/-!
# Dev B1: the machine program `prog`

Development split of `SatTo3CNFMachine`: the TM2 program `prog` for the
labels declared in `Dev.B1_Machine`.  The step relation `Sstep` and the step
lemmas are in `Dev.B1_Steps`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

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

end TM3CNF

end Turing

end Chapter34

end CLRS
