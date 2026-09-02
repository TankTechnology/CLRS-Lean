import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame

/-!
# Growing affine-prefix rows: core machine

For runtime values `(base, count)`, row `i` contains the unary frames
`base, ..., base + i - 1` and ends in `frameEnd`.  Thus row zero is empty and
each subsequent row extends the preceding row by one affine value.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Runtime parameters of one growing affine-prefix family. -/
structure UnaryFrameAffinePrefixRows where
  base : Nat
  count : Nat
deriving DecidableEq, Repr

/-- Canonical two-field source. -/
def encodeUnaryFrameAffinePrefixRows
    (family : UnaryFrameAffinePrefixRows) : List UnaryFrameSym :=
  encodeUnaryFrame [family.base, family.count]

/-- Mathematical rows generated from the two runtime parameters. -/
def unaryFrameAffinePrefixRowValues
    (family : UnaryFrameAffinePrefixRows) : List (List Nat) :=
  List.ofFn fun row : Fin family.count =>
    List.ofFn fun index : Fin row.val => family.base + index.val

/-- Public marked-row byte stream. -/
def unaryFrameAffinePrefixRowsStream
    (family : UnaryFrameAffinePrefixRows) : List UnaryFrameSym :=
  (unaryFrameAffinePrefixRowValues family).flatMap fun row =>
    encodeUnaryFrame row ++ [.frameEnd]

/-- Proof-facing recursive stream, parameterized by the already accumulated
row payload. -/
def unaryFrameAffinePrefixRowsStreamFrom :
    Nat → List UnaryFrameSym → Nat → List UnaryFrameSym
  | _, _, 0 => []
  | current, payload, count + 1 =>
      payload ++ [.frameEnd] ++
        unaryFrameAffinePrefixRowsStreamFrom (current + 1)
          (payload ++ encodeUnaryFrameBlock current) count

/-- Finite control of the reverse-output growing-prefix machine. -/
inductive UnaryFrameAffinePrefixRowsLabel
  | loadBase | incBase
  | rows
  | transfer
  | emitRestore
  | emitSymbol (symbol : UnaryFrameSym)
  | restoreSymbol (symbol : UnaryFrameSym)
  | pushRowEnd
  | appendCurrent | saveCurrent | pushCurrentTick | pushCurrentSeparator
  | restoreCurrent | restoreCurrentInc | advance
  | clearCurrent | clearPersistent
  | halt | invalid
deriving DecidableEq, Fintype

/-- A fixed controller retains the preceding row in reverse order on work
stack one.  Each outer tick copies that row to the output, restores it, and
prepends the reverse of the next unary block to the persistent stack. -/
def unaryFrameAffinePrefixRowsRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameAffinePrefixRowsLabel
  main := .loadBase
  op
    | .loadBase => .popInput .invalid fun
        | .tick => .incBase
        | .separator => .rows
        | .frameEnd => .invalid
    | .incBase => .inc₁ .loadBase
    | .rows => .popInput .invalid fun
        | .tick => .transfer
        | .separator => .clearCurrent
        | .frameEnd => .invalid
    | .transfer => .moveWork₁Work₂ .emitRestore fun _ => .transfer
    | .emitRestore => .popWork₂ .pushRowEnd .emitSymbol
    | .emitSymbol symbol => .pushOutput symbol (.restoreSymbol symbol)
    | .restoreSymbol symbol => .pushWork₁ symbol .emitRestore
    | .pushRowEnd => .pushOutput .frameEnd .appendCurrent
    | .appendCurrent => .dec₁ .pushCurrentSeparator .saveCurrent
    | .saveCurrent => .inc₂ .pushCurrentTick
    | .pushCurrentTick => .pushWork₁ .tick .appendCurrent
    | .pushCurrentSeparator => .pushWork₁ .separator .restoreCurrent
    | .restoreCurrent => .dec₂ .advance .restoreCurrentInc
    | .restoreCurrentInc => .inc₁ .restoreCurrent
    | .advance => .inc₁ .rows
    | .clearCurrent => .dec₁ .clearPersistent .clearCurrent
    | .clearPersistent => .popWork₁ .halt fun _ => .clearPersistent
    | .halt => .halt
    | .invalid => .halt

/-- Proof-facing configurations. -/
def unaryFrameAffinePrefixRowsCfg
    (label : UnaryFrameAffinePrefixRowsLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    BuilderCfg unaryFrameAffinePrefixRowsRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := current
  counter₂ := saved
  counter₃ := []

end CLRS.Chapter34.Turing.PolyBuilder
