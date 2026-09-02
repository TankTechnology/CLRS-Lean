import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Affine copies of one marked-cell row: core machine

The source contains `(step, count)` followed by one numeric row in which each
cell additionally carries a `frameEnd`.  The controller removes those inner
markers, emits the first row, and then emits `count - 1` further rows after
adding `step` unary ticks to every numeric cell.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Runtime input of the affine marked-cell row copier. -/
structure UnaryFrameMarkedCellAffineRows where
  step : Nat
  count : Nat
  cells : List Nat
deriving DecidableEq, Repr

/-- Canonical source: two controller parameters followed by one marked row
per numeric cell. -/
def encodeUnaryFrameMarkedCellAffineRows
    (family : UnaryFrameMarkedCellAffineRows) : List UnaryFrameSym :=
  encodeUnaryFrame [family.step, family.count] ++
    family.cells.flatMap fun value =>
      encodeUnaryFrame [value] ++ [.frameEnd]

/-- Numeric contents of every output arm row. -/
def unaryFrameMarkedCellAffineRowValues
    (family : UnaryFrameMarkedCellAffineRows) : List (List Nat) :=
  List.ofFn fun row : Fin family.count =>
    family.cells.map fun value => value + family.step * row.val

/-- Public output: one complete unary cell list per outer marked row. -/
def unaryFrameMarkedCellAffineRowsStream
    (family : UnaryFrameMarkedCellAffineRows) : List UnaryFrameSym :=
  (unaryFrameMarkedCellAffineRowValues family).flatMap fun row =>
    encodeUnaryFrame row ++ [.frameEnd]

/-- Finite control of the prepend-order implementation. -/
inductive UnaryFrameMarkedCellAffineRowsLabel
  | loadStep | incStep | loadCount | incCount | beginRows
  | copyFirst
  | emitFirst (symbol : UnaryFrameSym)
  | saveFirst (symbol : UnaryFrameSym)
  | finishFirst | nextRow
  | transfer | scan
  | emitExisting | saveExisting
  | addStep | emitAdded | saveAdded | rememberAdded
  | restoreStep | restoreStepInc
  | emitSeparator | saveSeparator
  | finishRow
  | clearInput | clearWork₁ | clearWork₂
  | clearTemp | clearStep | clearCount
  | halt | invalid
deriving DecidableEq, Fintype

/-- One fixed controller.  Work stack one retains the latest row in reverse;
work stack two exposes it in forward order for the next affine copy. -/
def unaryFrameMarkedCellAffineRowsRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedCellAffineRowsLabel
  main := .loadStep
  op
    | .loadStep => .popInput .invalid fun
        | .tick => .incStep
        | .separator => .loadCount
        | .frameEnd => .invalid
    | .incStep => .inc₂ .loadStep
    | .loadCount => .popInput .invalid fun
        | .tick => .incCount
        | .separator => .beginRows
        | .frameEnd => .invalid
    | .incCount => .inc₃ .loadCount
    | .beginRows => .dec₃ .clearInput .copyFirst
    | .copyFirst => .popInput .finishFirst fun
        | .frameEnd => .copyFirst
        | symbol => .emitFirst symbol
    | .emitFirst symbol => .pushOutput symbol (.saveFirst symbol)
    | .saveFirst symbol => .pushWork₁ symbol .copyFirst
    | .finishFirst => .pushOutput .frameEnd .nextRow
    | .nextRow => .dec₃ .clearInput .transfer
    | .transfer => .moveWork₁Work₂ .scan fun _ => .transfer
    | .scan => .popWork₂ .finishRow fun
        | .tick => .emitExisting
        | .separator => .addStep
        | .frameEnd => .scan
    | .emitExisting => .pushOutput .tick .saveExisting
    | .saveExisting => .pushWork₁ .tick .scan
    | .addStep => .dec₂ .restoreStep .emitAdded
    | .emitAdded => .pushOutput .tick .saveAdded
    | .saveAdded => .pushWork₁ .tick .rememberAdded
    | .rememberAdded => .inc₁ .addStep
    | .restoreStep => .dec₁ .emitSeparator .restoreStepInc
    | .restoreStepInc => .inc₂ .restoreStep
    | .emitSeparator => .pushOutput .separator .saveSeparator
    | .saveSeparator => .pushWork₁ .separator .scan
    | .finishRow => .pushOutput .frameEnd .nextRow
    | .clearInput => .popInput .clearWork₁ fun _ => .clearInput
    | .clearWork₁ => .popWork₁ .clearWork₂ fun _ => .clearWork₁
    | .clearWork₂ => .popWork₂ .clearTemp fun _ => .clearWork₂
    | .clearTemp => .dec₁ .clearStep .clearTemp
    | .clearStep => .dec₂ .clearCount .clearStep
    | .clearCount => .dec₃ .halt .clearCount
    | .halt => .halt
    | .invalid => .halt

end CLRS.Chapter34.Turing.PolyBuilder
