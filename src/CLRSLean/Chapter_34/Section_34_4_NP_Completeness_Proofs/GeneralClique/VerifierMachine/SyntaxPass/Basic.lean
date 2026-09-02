import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.ParseSemantics

/-!
# General CLIQUE verifier: Boolean syntax pass

The existing parser preserves a tagged copy of its input.  The final verifier
also needs a small reusable component that emits only the grammar verdict.
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.SyntaxPass

open PolyBuilder

/-- One syntax-only transition: update the parser mode without emitting a
tagged copy of the current symbol. -/
def syntaxAction (mode : ParseMode) (symbol : Option CliqueSym) :
    List Bool × ParseMode :=
  ([], (parseAction mode symbol).2)

/-- Emit the complete-grammar verdict as a singleton Boolean string. -/
def syntaxFinish (mode : ParseMode) : List Bool :=
  if mode.side = .instance && mode.valid && mode.grammar = .instanceEdges then
    [true]
  else
    [false]

/-- Fixed finite-state Boolean syntax checker. -/
def syntaxSpec : StatefulFlatMapSpec ParseMode (Option CliqueSym) Bool where
  initial := initialParseMode
  action := syntaxAction
  finish := syntaxFinish

/-- Raw list function computed by the concrete syntax checker. -/
def syntaxPassStream (input : List (Option CliqueSym)) : List Bool :=
  rewriteStatefulFlatMap syntaxSpec input

/-- Public Boolean specification for a raw certificate/instance pair. -/
def syntaxPass (certificate input : List CliqueSym) : Bool :=
  decide (parsePairStatus certificate input = .syntaxOK)

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.SyntaxPass
