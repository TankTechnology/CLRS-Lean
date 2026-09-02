import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Certificate.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap
import Mathlib.Data.Fintype.Sum

/-!
# General CLIQUE verifier: finite-state parsing front end

The verifier receives `pairEncoding certificate input`.  This first, reusable
stage tags the two halves and checks their complete concrete grammars.  Unary
field values are deliberately left untouched: the later verifier stages use
them for cardinality, range, duplicate, and adjacency checks.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier

open _root_.Turing
open PolyBuilder

/-- Which half of the paired verifier input is currently being scanned. -/
inductive ParseSide
  | certificate
  | instance
deriving DecidableEq, Fintype, Inhabited

/-- Regular-language states for the two complete CLIQUE encodings. -/
inductive ParseGrammar
  | certificateStart
  | certificateVertices
  | certificateVertex
  | instanceStart
  | instanceVertexCount
  | instanceTargetSize
  | instanceEdges
  | instanceEdgeLeft
  | instanceEdgeRight
deriving DecidableEq, Fintype, Inhabited

/-- Finite parser state.  Once `valid` becomes false it remains false. -/
structure ParseMode where
  side : ParseSide
  grammar : ParseGrammar
  valid : Bool
deriving DecidableEq, Inhabited

private def parseModeEquiv :
    (ParseSide × ParseGrammar × Bool) ≃ ParseMode where
  toFun mode := ⟨mode.1, mode.2.1, mode.2.2⟩
  invFun mode := (mode.side, mode.grammar, mode.valid)
  left_inv mode := by rcases mode with ⟨side, grammar, valid⟩; rfl
  right_inv mode := by rcases mode with ⟨side, grammar, valid⟩; rfl

instance : Fintype ParseMode :=
  Fintype.ofEquiv (ParseSide × ParseGrammar × Bool) parseModeEquiv

/-- Tagged stream consumed by the arithmetic part of the verifier. -/
inductive TaggedSym
  | certificate (symbol : CliqueSym)
  | instance (symbol : CliqueSym)
  | syntaxOK
  | syntaxError
deriving DecidableEq

private def taggedSymEquiv :
    (CliqueSym ⊕ (CliqueSym ⊕ (Unit ⊕ Unit))) ≃ TaggedSym where
  toFun
    | .inl symbol => .certificate symbol
    | .inr (.inl symbol) => .instance symbol
    | .inr (.inr (.inl _)) => .syntaxOK
    | .inr (.inr (.inr _)) => .syntaxError
  invFun
    | .certificate symbol => .inl symbol
    | .instance symbol => .inr (.inl symbol)
    | .syntaxOK => .inr (.inr (.inl ()))
    | .syntaxError => .inr (.inr (.inr ()))
  left_inv encoded := by rcases encoded with (_ | (_ | (_ | _))) <;> rfl
  right_inv symbol := by cases symbol <;> rfl

instance : Fintype TaggedSym :=
  Fintype.ofEquiv (CliqueSym ⊕ (CliqueSym ⊕ (Unit ⊕ Unit))) taggedSymEquiv

/-- Initial state: no certificate symbol has yet been read. -/
def initialParseMode : ParseMode :=
  { side := .certificate, grammar := .certificateStart, valid := true }

/-- One grammar transition on an ordinary (non-separator) symbol. -/
def grammarStep (grammar : ParseGrammar) (symbol : CliqueSym) :
    ParseGrammar × Bool :=
  if grammar = .certificateStart && symbol = .certificateMark then
    (.certificateVertices, true)
  else if grammar = .certificateVertices && symbol = .vertexMark then
    (.certificateVertex, true)
  else if grammar = .certificateVertex && symbol = .tick then
    (.certificateVertex, true)
  else if grammar = .certificateVertex && symbol = .recordEnd then
    (.certificateVertices, true)
  else if grammar = .instanceStart && symbol = .instanceMark then
    (.instanceVertexCount, true)
  else if grammar = .instanceVertexCount && symbol = .tick then
    (.instanceVertexCount, true)
  else if grammar = .instanceVertexCount && symbol = .fieldSep then
    (.instanceTargetSize, true)
  else if grammar = .instanceTargetSize && symbol = .tick then
    (.instanceTargetSize, true)
  else if grammar = .instanceTargetSize && symbol = .fieldSep then
    (.instanceEdges, true)
  else if grammar = .instanceEdges && symbol = .edgeMark then
    (.instanceEdgeLeft, true)
  else if grammar = .instanceEdgeLeft && symbol = .tick then
    (.instanceEdgeLeft, true)
  else if grammar = .instanceEdgeLeft && symbol = .pairSep then
    (.instanceEdgeRight, true)
  else if grammar = .instanceEdgeRight && symbol = .tick then
    (.instanceEdgeRight, true)
  else if grammar = .instanceEdgeRight && symbol = .recordEnd then
    (.instanceEdges, true)
  else
    (grammar, false)

/-- Ordinary symbols preserve the paired-input side and update only grammar
state and validity. -/
def stepSymbol (mode : ParseMode) (symbol : CliqueSym) : ParseMode :=
  if mode.valid then
    let result := grammarStep mode.grammar symbol
    if result.2 then { mode with grammar := result.1 }
    else { mode with valid := false }
  else mode

@[simp] theorem stepSymbol_side (mode : ParseMode) (symbol : CliqueSym) :
    (stepSymbol mode symbol).side = mode.side := by
  by_cases hvalid : mode.valid = true
  · by_cases hstep : (grammarStep mode.grammar symbol).2 = true
    · simp [stepSymbol, hvalid, hstep]
    · simp [stepSymbol, hvalid, hstep]
  · simp [stepSymbol, hvalid]

/-- The unique `none` separator closes the certificate grammar and starts the
instance grammar.  Any later separator makes the stream invalid. -/
def stepSeparator (mode : ParseMode) : ParseMode :=
  match mode.side with
  | .certificate =>
      { side := .instance
        grammar := .instanceStart
        valid := mode.valid && decide (mode.grammar = .certificateVertices) }
  | .instance => { mode with valid := false }

@[simp] theorem stepSeparator_side (mode : ParseMode) :
    (stepSeparator mode).side = .instance := by
  rcases mode with ⟨side, grammar, valid⟩
  cases side <;> rfl

/-- Preserve every raw symbol while recording which half supplied it. -/
def tagSymbol (side : ParseSide) (symbol : CliqueSym) : TaggedSym :=
  match side with
  | .certificate => .certificate symbol
  | .instance => .instance symbol

/-- One streaming parser action.  The pair separator itself is not retained. -/
def parseAction (mode : ParseMode) (symbol : Option CliqueSym) :
    List TaggedSym × ParseMode :=
  match symbol with
  | some token => ([tagSymbol mode.side token], stepSymbol mode token)
  | none => ([], stepSeparator mode)

/-- Only a completely parsed instance edge stream is accepting. -/
def parseFinish (mode : ParseMode) : List TaggedSym :=
  if mode.side = .instance && mode.valid && mode.grammar = .instanceEdges then
    [.syntaxOK]
  else
    [.syntaxError]

/-- Fixed finite-state specification of the paired-input parser. -/
def parsePairSpec : StatefulFlatMapSpec ParseMode (Option CliqueSym) TaggedSym where
  initial := initialParseMode
  action := parseAction
  finish := parseFinish

/-- Pure output stream of the parsing front end. -/
def parsePairStream : List (Option CliqueSym) → List TaggedSym :=
  rewriteStatefulFlatMap parsePairSpec

/-- State after scanning a list of ordinary symbols. -/
def scanSymbols (mode : ParseMode) (input : List CliqueSym) : ParseMode :=
  input.foldl stepSymbol mode

/-- Status marker produced for a paired certificate and instance. -/
def parsePairStatus (certificate input : List CliqueSym) : TaggedSym :=
  let afterCertificate := scanSymbols initialParseMode certificate
  let afterSeparator := stepSeparator afterCertificate
  let afterInstance := scanSymbols afterSeparator input
  if afterInstance.side = .instance && afterInstance.valid &&
      afterInstance.grammar = .instanceEdges then
    .syntaxOK
  else
    .syntaxError

end CLRS.Chapter34.Turing.GeneralCliqueVerifier
