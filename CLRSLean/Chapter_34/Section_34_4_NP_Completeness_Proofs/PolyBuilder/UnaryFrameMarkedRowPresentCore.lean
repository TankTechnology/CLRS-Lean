import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate

/-!
# Marking every delimited row as present: core definitions

The optional-conjunction controller expects `tick` before every present row
and one additional `frameEnd` after the complete family.  This fixed
transducer supplies exactly that framing for an arbitrary marked-row family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Encoding obtained by selecting the present branch for every marked row. -/
def encodeUnaryFramePresentMarkedRowFamily
    (family : UnaryFrameMarkedRowFamily) : List UnaryFrameSym :=
  family.rows.flatMap (fun row => .tick :: row ++ [.frameEnd]) ++
    [.frameEnd]

inductive UnaryFrameMarkedRowPresentLabel
  | beginRow
  | emitPresent (symbol : UnaryFrameSym)
  | emitSymbol (symbol : UnaryFrameSym)
  | scan
  | emitFinal
  | finish
deriving DecidableEq, Fintype

/-- Prepend-output implementation of the all-present row framing pass. -/
def unaryFrameMarkedRowPresentRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedRowPresentLabel
  main := .beginRow
  op
    | .beginRow => .popInput .emitFinal .emitPresent
    | .emitPresent symbol => .pushOutput .tick (.emitSymbol symbol)
    | .emitSymbol .frameEnd => .pushOutput .frameEnd .beginRow
    | .emitSymbol .tick => .pushOutput .tick .scan
    | .emitSymbol .separator => .pushOutput .separator .scan
    | .scan => .popInput .emitFinal .emitSymbol
    | .emitFinal => .pushOutput .frameEnd .finish
    | .finish => .halt

def unaryFrameMarkedRowPresentCfg
    (label : UnaryFrameMarkedRowPresentLabel)
    (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowPresentRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := false
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

def unaryFrameMarkedRowPresentLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowPresentRevProgram :=
  unaryFrameMarkedRowPresentCfg .beginRow none input output

end CLRS.Chapter34.Turing.PolyBuilder
