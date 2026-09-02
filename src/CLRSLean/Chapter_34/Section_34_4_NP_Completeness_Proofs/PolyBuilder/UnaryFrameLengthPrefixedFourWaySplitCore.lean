import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import Mathlib.Tactic

/-!
# Streaming split of length-prefixed four-channel unary packets

One input packet has the layout

`width / selector / 3*width coordinate fields / width true fields /
 width false fields / frameEnd`.

The fixed controller copies the payload while inserting ordinary row markers
after selector, coordinates, true, and false.  The three runtime counters are
loaded from the unary width; no packet width enters finite control.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The three variable-width sections of a four-channel packet. -/
inductive UnaryFrameLengthPrefixedFourWaySplitSection
  | coordinates | trueArm | falseArm
deriving DecidableEq, Fintype

/-- Finite control of the dynamic four-way splitter. -/
inductive UnaryFrameLengthPrefixedFourWaySplitLabel
  | loadWidth
  | incCoordinate₁ | incCoordinate₂ | incCoordinate₃
  | incTrue | incFalse
  | selectorScan | selectorTick | selectorSeparator | selectorBoundary
  | sectionCheck (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
  | sectionScan (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
  | sectionTick (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
  | sectionSeparator (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
  | sectionBoundary (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
  | consumeBoundary
  | finish | invalid
deriving DecidableEq, Fintype

abbrev UnaryFrameLengthPrefixedFourWaySplitProgram :=
  Program UnaryFrameSym UnaryFrameSym

/-- The next section after one completed channel. -/
def unaryFrameLengthPrefixedFourWaySplitNext
    (channel : UnaryFrameLengthPrefixedFourWaySplitSection) :
    UnaryFrameLengthPrefixedFourWaySplitLabel :=
  match channel with
  | .coordinates => .sectionCheck .trueArm
  | .trueArm => .sectionCheck .falseArm
  | .falseArm => .consumeBoundary

/-- Decrement the runtime field counter belonging to one section. -/
def unaryFrameLengthPrefixedFourWaySplitCheckOp
    (channel : UnaryFrameLengthPrefixedFourWaySplitSection) :
    Op UnaryFrameSym UnaryFrameSym
      UnaryFrameLengthPrefixedFourWaySplitLabel :=
  match channel with
  | .coordinates => .dec₁ (.sectionBoundary channel) (.sectionScan channel)
  | .trueArm => .dec₂ (.sectionBoundary channel) (.sectionScan channel)
  | .falseArm => .dec₃ (.sectionBoundary channel) (.sectionScan channel)

/-- Reversed-output streaming program.  Each width tick loads three
coordinate-field tokens and one token for each arm. -/
def unaryFrameLengthPrefixedFourWaySplitRevProgram :
    UnaryFrameLengthPrefixedFourWaySplitProgram where
  Label := UnaryFrameLengthPrefixedFourWaySplitLabel
  main := .loadWidth
  op
    | .loadWidth => .popInput .finish fun
        | .tick => .incCoordinate₁
        | .separator => .selectorScan
        | .frameEnd => .invalid
    | .incCoordinate₁ => .inc₁ .incCoordinate₂
    | .incCoordinate₂ => .inc₁ .incCoordinate₃
    | .incCoordinate₃ => .inc₁ .incTrue
    | .incTrue => .inc₂ .incFalse
    | .incFalse => .inc₃ .loadWidth
    | .selectorScan => .popInput .invalid fun
        | .tick => .selectorTick
        | .separator => .selectorSeparator
        | .frameEnd => .invalid
    | .selectorTick => .pushOutput .tick .selectorScan
    | .selectorSeparator => .pushOutput .separator .selectorBoundary
    | .selectorBoundary =>
        .pushOutput .frameEnd (.sectionCheck .coordinates)
    | .sectionCheck channel =>
        unaryFrameLengthPrefixedFourWaySplitCheckOp channel
    | .sectionScan channel => .popInput .invalid fun
        | .tick => .sectionTick channel
        | .separator => .sectionSeparator channel
        | .frameEnd => .invalid
    | .sectionTick channel => .pushOutput .tick (.sectionScan channel)
    | .sectionSeparator channel =>
        .pushOutput .separator (.sectionCheck channel)
    | .sectionBoundary channel =>
        .pushOutput .frameEnd
          (unaryFrameLengthPrefixedFourWaySplitNext channel)
    | .consumeBoundary => .popInput .invalid fun
        | .frameEnd => .loadWidth
        | _ => .invalid
    | .finish => .halt
    | .invalid => .halt

/-- Uniform explicit configuration surface used by the simulation proof. -/
def unaryFrameLengthPrefixedFourWaySplitCfg
    (label : UnaryFrameLengthPrefixedFourWaySplitLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (coordinateFields trueFields falseFields : Nat) :
    BuilderCfg unaryFrameLengthPrefixedFourWaySplitRevProgram :=
  { label := some label
    buffer₁ := buffer₁
    buffer₂ := buffer₂
    test := test
    input := input
    output := output
    work₁ := []
    work₂ := []
    counter₁ := List.replicate coordinateFields ()
    counter₂ := List.replicate trueFields ()
    counter₃ := List.replicate falseFields () }

/-- Clean packet-loop boundary. -/
def unaryFrameLengthPrefixedFourWaySplitLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameLengthPrefixedFourWaySplitRevProgram :=
  unaryFrameLengthPrefixedFourWaySplitCfg .loadWidth none none false input
    output 0 0 0

/-- Exact marked four-row output for one numeric packet. -/
def encodeUnaryFrameLengthPrefixedFourWaySplitOutput
    (selector : Nat) (coordinates whenTrue whenFalse : List Nat) :
    List UnaryFrameSym :=
  encodeUnaryFrame [selector] ++ [.frameEnd] ++
    encodeUnaryFrame coordinates ++ [.frameEnd] ++
    encodeUnaryFrame whenTrue ++ [.frameEnd] ++
    encodeUnaryFrame whenFalse ++ [.frameEnd]

/-- Exact length-prefixed input for one numeric packet. -/
def encodeUnaryFrameLengthPrefixedFourWaySplitInput
    (width selector : Nat)
    (coordinates whenTrue whenFalse : List Nat) : List UnaryFrameSym :=
  encodeUnaryFrame [width, selector] ++ encodeUnaryFrame coordinates ++
    encodeUnaryFrame whenTrue ++ encodeUnaryFrame whenFalse ++ [.frameEnd]

end CLRS.Chapter34.Turing.PolyBuilder
