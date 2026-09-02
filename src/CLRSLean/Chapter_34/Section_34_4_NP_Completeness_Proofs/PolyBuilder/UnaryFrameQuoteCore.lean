import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate

/-!
# Quoting arbitrary unary-frame streams as one marked row

The two-symbol code below turns every `UnaryFrameSym` into a payload over
`tick/separator`.  Appending one real `frameEnd` therefore gives an
unambiguous outer row boundary, even when the original stream contains many
gate-frame boundaries.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Frame-end-free two-symbol code for one unary-frame symbol. -/
def quoteUnaryFrameSym : UnaryFrameSym → List UnaryFrameSym
  | .tick => [.tick, .tick]
  | .separator => [.tick, .separator]
  | .frameEnd => [.separator, .tick]

/-- Concatenate the fixed codewords of an arbitrary stream. -/
def quoteUnaryFrameStream (input : List UnaryFrameSym) : List UnaryFrameSym :=
  input.flatMap quoteUnaryFrameSym

@[simp] theorem quoteUnaryFrameStream_nil :
    quoteUnaryFrameStream [] = [] := rfl

@[simp] theorem quoteUnaryFrameStream_cons
    (symbol : UnaryFrameSym) (rest : List UnaryFrameSym) :
    quoteUnaryFrameStream (symbol :: rest) =
      quoteUnaryFrameSym symbol ++ quoteUnaryFrameStream rest := rfl

/-- No quoted payload can contain the reserved outer boundary. -/
theorem quoteUnaryFrameStream_frameEnd_free
    (input : List UnaryFrameSym) (symbol : UnaryFrameSym)
    (hsymbol : symbol ∈ quoteUnaryFrameStream input) :
    symbol ≠ UnaryFrameSym.frameEnd := by
  induction input with
  | nil => simp at hsymbol
  | cons head rest ih =>
      simp only [quoteUnaryFrameStream_cons, List.mem_append] at hsymbol
      rcases hsymbol with hhead | hrest
      · cases head with
        | tick =>
            simp [quoteUnaryFrameSym] at hhead
            subst symbol
            decide
        | separator =>
            simp [quoteUnaryFrameSym] at hhead
            rcases hhead with rfl | rfl <;> decide
        | frameEnd =>
            simp [quoteUnaryFrameSym] at hhead
            rcases hhead with rfl | rfl <;> decide
      · exact ih hrest

@[simp] theorem quoteUnaryFrameSym_length (symbol : UnaryFrameSym) :
    (quoteUnaryFrameSym symbol).length = 2 := by
  cases symbol <;> rfl

@[simp] theorem quoteUnaryFrameStream_length (input : List UnaryFrameSym) :
    (quoteUnaryFrameStream input).length = 2 * input.length := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      simp [quoteUnaryFrameStream_cons, ih]
      omega

/-- One quoted stream packaged as a delimiter-safe singleton family. -/
def quotedUnaryFrameSingleton (input : List UnaryFrameSym) :
    UnaryFrameMarkedRowFamily where
  rows := [quoteUnaryFrameStream input]
  frameEnd_free := by
    intro row hrow symbol hsymbol
    simp only [List.mem_singleton] at hrow
    subst row
    exact quoteUnaryFrameStream_frameEnd_free input symbol hsymbol

@[simp] theorem encode_quotedUnaryFrameSingleton
    (input : List UnaryFrameSym) :
    encodeUnaryFrameMarkedRowFamily (quotedUnaryFrameSingleton input) =
      quoteUnaryFrameStream input ++ [.frameEnd] := by
  simp [encodeUnaryFrameMarkedRowFamily, quotedUnaryFrameSingleton]

/-- Finite control of the reverse-output quoting transducer. -/
inductive UnaryFrameQuoteLabel
  | scan
  | emitFirst (symbol : UnaryFrameSym)
  | emitSecond (symbol : UnaryFrameSym)
  | emitBoundary
  | finish
deriving DecidableEq, Fintype

/-- First code symbol. -/
def quoteUnaryFrameFirst : UnaryFrameSym → UnaryFrameSym
  | .tick => .tick
  | .separator => .tick
  | .frameEnd => .separator

/-- Second code symbol. -/
def quoteUnaryFrameSecond : UnaryFrameSym → UnaryFrameSym
  | .tick => .tick
  | .separator => .separator
  | .frameEnd => .tick

@[simp] theorem quoteUnaryFrameSym_eq_pair (symbol : UnaryFrameSym) :
    quoteUnaryFrameSym symbol =
      [quoteUnaryFrameFirst symbol, quoteUnaryFrameSecond symbol] := by
  cases symbol <;> rfl

/-- The prepend-only pass emits the reverse of the quoted singleton row. -/
def unaryFrameQuoteMarkedRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameQuoteLabel
  main := .scan
  op
    | .scan => .popInput .emitBoundary .emitFirst
    | .emitFirst symbol =>
        .pushOutput (quoteUnaryFrameFirst symbol) (.emitSecond symbol)
    | .emitSecond symbol =>
        .pushOutput (quoteUnaryFrameSecond symbol) .scan
    | .emitBoundary => .pushOutput .frameEnd .finish
    | .finish => .halt

/-- Uniform configuration surface for the exact simulation. -/
def unaryFrameQuoteCfg (label : UnaryFrameQuoteLabel)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameQuoteMarkedRevProgram :=
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

end CLRS.Chapter34.Turing.PolyBuilder
