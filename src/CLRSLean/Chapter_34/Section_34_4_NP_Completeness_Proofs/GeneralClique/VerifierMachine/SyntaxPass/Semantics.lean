import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.SyntaxPass.Basic

/-!
# General CLIQUE verifier: syntax-pass semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.SyntaxPass

open PolyBuilder

private def syntaxStep (mode : ParseMode) (symbol : Option CliqueSym) :
    ParseMode :=
  (parseAction mode symbol).2

private theorem rewrite_syntax_from (mode : ParseMode)
    (input : List (Option CliqueSym)) :
    rewriteStatefulFlatMapFrom syntaxSpec mode input =
      syntaxFinish (input.foldl syntaxStep mode) := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol input ih =>
      simp only [rewriteStatefulFlatMapFrom, syntaxSpec, syntaxAction,
        List.nil_append, List.foldl_cons, syntaxStep]
      exact ih _

private theorem fold_some_symbols (mode : ParseMode)
    (input : List CliqueSym) :
    (input.map some).foldl syntaxStep mode = scanSymbols mode input := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol input ih =>
      simp [syntaxStep, parseAction, scanSymbols, ih]

/-- Exact singleton output on the public separator-based pair encoding. -/
theorem syntaxPassStream_pairEncoding (certificate input : List CliqueSym) :
    syntaxPassStream (pairEncoding certificate input) =
      boolEncoding (syntaxPass certificate input) := by
  unfold syntaxPassStream rewriteStatefulFlatMap pairEncoding
  rw [rewrite_syntax_from]
  simp only [List.foldl_append, fold_some_symbols, List.foldl_cons,
    List.foldl_nil]
  change syntaxFinish
      (scanSymbols (stepSeparator (scanSymbols initialParseMode certificate))
        input) = _
  unfold syntaxFinish syntaxPass parsePairStatus
  split <;> simp_all [boolEncoding, _root_.Turing.TM2Comp.boolEncoding]

/-- The Boolean syntax component accepts exactly when both complete decoders
succeed on the raw strings. -/
theorem syntaxPass_eq_true_iff (certificate input : List CliqueSym) :
    syntaxPass certificate input = true ↔
      (∃ vertices, decodeCliqueCertificate certificate = some vertices) ∧
      ∃ I, decodeCliqueInstance input = some I := by
  simp only [syntaxPass, decide_eq_true_eq]
  exact parsePairStatus_eq_syntaxOK_iff certificate input

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.SyntaxPass
