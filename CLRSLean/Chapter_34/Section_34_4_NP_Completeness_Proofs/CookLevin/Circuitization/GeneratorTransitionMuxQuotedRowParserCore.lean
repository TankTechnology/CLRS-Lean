import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameQuoteCore

/-!
# A delimiter-safe parser for consecutive transition mux invocations

The existing arithmetic mux controller emits the exact textbook byte stream,
but concatenates consecutive transition seeds without retaining an outer row
delimiter.  This fixed parser follows the public mux grammar, quotes every
payload byte, and emits one literal `frameEnd` after each complete invocation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The four delimiter-terminated triples of a coordinate are parsed in
finite control.  `header` parses the shared-selector header. -/
inductive TransitionMuxQuotedRowPhase
  | header
  | coordinate (index : Fin 3)
deriving DecidableEq, Fintype

/-- Stable scan states.  A complete invocation returns to
`afterInvocation`, where either another coordinate, another header, or end of
input is distinguished by the next symbol. -/
inductive TransitionMuxQuotedRowState
  | triple (phase : TransitionMuxQuotedRowPhase) (separators : Fin 4)
  | afterInvocation
deriving DecidableEq, Fintype

/-- Finite labels of the prepend-output parser. -/
inductive TransitionMuxQuotedRowParserLabel
  | scan (state : TransitionMuxQuotedRowState)
  | emitFirst (state : TransitionMuxQuotedRowState)
      (symbol : UnaryFrameSym)
  | emitSecond (state : TransitionMuxQuotedRowState)
      (symbol : UnaryFrameSym)
  | emitBoundaryThenFirst (state : TransitionMuxQuotedRowState)
      (symbol : UnaryFrameSym)
  | emitFinalBoundary
  | halt
  | invalid
deriving DecidableEq, Fintype

def transitionMuxQuotedRowInitialState : TransitionMuxQuotedRowState :=
  .triple .header ⟨0, by omega⟩

def transitionMuxQuotedRowFirstHeaderState : TransitionMuxQuotedRowState :=
  .triple .header ⟨1, by omega⟩

def transitionMuxQuotedRowFirstCoordinateState :
    TransitionMuxQuotedRowState :=
  .triple (.coordinate ⟨0, by omega⟩) ⟨0, by omega⟩

/-- State reached after the closing delimiter of one parsed triple. -/
def transitionMuxQuotedRowAfterTriple :
    TransitionMuxQuotedRowPhase → TransitionMuxQuotedRowState
  | .header => .afterInvocation
  | .coordinate index =>
      if hnext : index.val + 1 < 3 then
        .triple (.coordinate ⟨index.val + 1, hnext⟩) ⟨0, by omega⟩
      else
        .afterInvocation

def transitionMuxQuotedRowIncrement
    (separators : Fin 4) (hroom : separators.val < 3) : Fin 4 :=
  ⟨separators.val + 1, by omega⟩

/-- One fixed parser works for every selector, coordinate count, wire value,
and input length. -/
def transitionMuxQuotedRowParserRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := TransitionMuxQuotedRowParserLabel
  main := .scan transitionMuxQuotedRowInitialState
  op
    | .scan (.triple phase separators) =>
        .popInput .halt fun
          | .tick => .emitFirst (.triple phase separators) .tick
          | .separator =>
              if hroom : separators.val < 3 then
                .emitFirst
                  (.triple phase
                    (transitionMuxQuotedRowIncrement separators hroom))
                  .separator
              else
                .invalid
          | .frameEnd =>
              if separators.val = 3 then
                .emitFirst (transitionMuxQuotedRowAfterTriple phase) .frameEnd
              else
                .invalid
    | .scan .afterInvocation =>
        .popInput .emitFinalBoundary fun
          | .frameEnd =>
              .emitFirst transitionMuxQuotedRowFirstCoordinateState .frameEnd
          | .separator =>
              .emitBoundaryThenFirst transitionMuxQuotedRowFirstHeaderState
                .separator
          | .tick => .invalid
    | .emitBoundaryThenFirst state symbol =>
        .pushOutput .frameEnd (.emitFirst state symbol)
    | .emitFirst state symbol =>
        .pushOutput (quoteUnaryFrameFirst symbol) (.emitSecond state symbol)
    | .emitSecond state symbol =>
        .pushOutput (quoteUnaryFrameSecond symbol) (.scan state)
    | .emitFinalBoundary => .pushOutput .frameEnd .halt
    | .halt => .halt
    | .invalid => .halt

def transitionMuxQuotedRowParserCfg
    (label : TransitionMuxQuotedRowParserLabel)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg transitionMuxQuotedRowParserRevProgram :=
  { label := some label
    buffer₁ := buffer
    buffer₂ := none
    test := false
    input := input
    output := output
    work₁ := []
    work₂ := []
    counter₁ := []
    counter₂ := []
    counter₃ := [] }

def transitionMuxQuotedRowParserScanCfg
    (state : TransitionMuxQuotedRowState)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg transitionMuxQuotedRowParserRevProgram :=
  transitionMuxQuotedRowParserCfg (.scan state) buffer input output

/-- The typed source consumed by the parser. -/
def transitionMuxInvocationViewFamilyFrames
    (views : List TransitionDispatchMuxInvocationView) :
    List UnaryFrameSym :=
  views.flatMap TransitionDispatchMuxInvocationView.encode

/-- Desired delimiter-safe output, one row per mux invocation. -/
def transitionMuxInvocationQuotedRowFamily
    (views : List TransitionDispatchMuxInvocationView) :
    UnaryFrameMarkedRowFamily where
  rows := views.map fun view => quoteUnaryFrameStream view.encode
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rw [List.mem_map] at hrow
    rcases hrow with ⟨view, hview, rfl⟩
    exact quoteUnaryFrameStream_frameEnd_free view.encode symbol hsymbol

@[simp] theorem transitionMuxInvocationQuotedRowFamily_rows
    (views : List TransitionDispatchMuxInvocationView) :
    (transitionMuxInvocationQuotedRowFamily views).rows =
      views.map fun view => quoteUnaryFrameStream view.encode := rfl

theorem transitionMuxInvocationQuotedRowFamily_encoding
    (views : List TransitionDispatchMuxInvocationView) :
    encodeUnaryFrameMarkedRowFamily
        (transitionMuxInvocationQuotedRowFamily views) =
      views.flatMap fun view =>
        quoteUnaryFrameStream view.encode ++ [.frameEnd] := by
  simp [encodeUnaryFrameMarkedRowFamily,
    transitionMuxInvocationQuotedRowFamily, List.flatMap_map]

end CLRS.Chapter34.Turing.CookLevin
