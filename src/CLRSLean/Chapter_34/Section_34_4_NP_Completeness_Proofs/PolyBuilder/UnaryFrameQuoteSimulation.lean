import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameQuoteCore
import Mathlib.Tactic

/-!
# Exact simulation of unary-frame quoting
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev quoteStep := step unaryFrameQuoteMarkedRevProgram

/-- Exact cost through the input scan, stopping before the outer boundary is
emitted. -/
def unaryFrameQuoteScanSteps (input : List UnaryFrameSym) : Nat :=
  3 * input.length + 1

/-- The scan emits the reverse of every two-symbol codeword. -/
private theorem unaryFrameQuote_scan_eval
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    (flip Option.bind quoteStep)^[unaryFrameQuoteScanSteps input]
        (some (unaryFrameQuoteCfg .scan buffer input output)) =
      some (unaryFrameQuoteCfg .emitBoundary none []
        ((quoteUnaryFrameStream input).reverse ++ output)) := by
  induction input generalizing buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show unaryFrameQuoteScanSteps (symbol :: rest) =
          unaryFrameQuoteScanSteps rest + 1 + 1 + 1 by
            simp [unaryFrameQuoteScanSteps]
            omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind quoteStep)^[unaryFrameQuoteScanSteps rest]
            (some (unaryFrameQuoteCfg .scan (some symbol) rest
              (quoteUnaryFrameSecond symbol ::
                quoteUnaryFrameFirst symbol :: output))) = _
      simpa [quoteUnaryFrameStream_cons, quoteUnaryFrameSym_eq_pair,
        List.reverse_append, List.append_assoc] using
        ih (some symbol)
          (quoteUnaryFrameSecond symbol ::
            quoteUnaryFrameFirst symbol :: output)

/-- Total cost including the outer boundary and the final halt. -/
def unaryFrameQuoteMarkedSteps (input : List UnaryFrameSym) : Nat :=
  3 * input.length + 3

/-- The concrete prepend-only controller outputs the reversed encoding of one
quoted singleton marked row. -/
def unaryFrameQuoteMarkedRev_run (input : List UnaryFrameSym) :
    EvalsToInTime quoteStep
      (initialCfg unaryFrameQuoteMarkedRevProgram input)
      (some (haltCfg unaryFrameQuoteMarkedRevProgram
        (encodeUnaryFrameMarkedRowFamily
          (quotedUnaryFrameSingleton input)).reverse))
      (unaryFrameQuoteMarkedSteps input) := by
  let afterScan := unaryFrameQuoteCfg .emitBoundary none []
    (quoteUnaryFrameStream input).reverse
  let afterBoundary := unaryFrameQuoteCfg .finish none []
    (.frameEnd :: (quoteUnaryFrameStream input).reverse)
  have hscan : EvalsToInTime quoteStep
      (initialCfg unaryFrameQuoteMarkedRevProgram input)
      (some afterScan) (unaryFrameQuoteScanSteps input) := by
    change EvalsToInTime quoteStep
      (unaryFrameQuoteCfg .scan none input [])
      (some afterScan) (unaryFrameQuoteScanSteps input)
    refine ⟨⟨unaryFrameQuoteScanSteps input, ?_⟩, le_rfl⟩
    simpa [afterScan] using
      unaryFrameQuote_scan_eval none input []
  have hboundary : EvalsToInTime quoteStep afterScan
      (some afterBoundary) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hhalt : EvalsToInTime quoteStep afterBoundary
      (some (haltCfg unaryFrameQuoteMarkedRevProgram
        (.frameEnd :: (quoteUnaryFrameStream input).reverse))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let throughBoundary := EvalsToInTime.trans quoteStep
    (unaryFrameQuoteScanSteps input) 1 _ afterScan _ hscan hboundary
  let full := EvalsToInTime.trans quoteStep
    (1 + unaryFrameQuoteScanSteps input) 1 _ afterBoundary _
      throughBoundary hhalt
  convert full using 1
  · rw [encode_quotedUnaryFrameSingleton]
    simp [List.reverse_append]
  · simp [unaryFrameQuoteMarkedSteps, unaryFrameQuoteScanSteps]
    omega

end CLRS.Chapter34.Turing.PolyBuilder
