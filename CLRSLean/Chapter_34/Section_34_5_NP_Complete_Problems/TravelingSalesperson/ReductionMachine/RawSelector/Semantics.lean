import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawSelector.Core

/-! # Guarded TSP output selector: exact semantics -/

namespace CLRS.Chapter34.Turing.TSPReduction.RawSelector

open PolyBuilder

private theorem payload_true (candidate : List TSPSym) :
    rewriteStatefulFlatMapFrom spec (.payload true) (candidate.map some) =
      candidate := by
  induction candidate with
  | nil => rfl
  | cons symbol rest ih =>
      change symbol :: rewriteStatefulFlatMapFrom spec (.payload true)
        (rest.map some) = symbol :: rest
      rw [ih]

private theorem payload_false (candidate : List TSPSym) :
    rewriteStatefulFlatMapFrom spec (.payload false) (candidate.map some) =
      [] := by
  induction candidate with
  | nil => rfl
  | cons symbol rest ih =>
      change rewriteStatefulFlatMapFrom spec (.payload false)
        (rest.map some) = []
      exact ih

/-- Exact behavior on every canonically tagged selector input. -/
theorem stream_inputEncoding (input : Bool × List TSPSym) :
    stream (inputEncoding input) = selectedOutput input := by
  rcases input with ⟨accept, candidate⟩
  cases accept with
  | false =>
      change rewriteStatefulFlatMapFrom spec .start
        (some .certificateMark :: none :: candidate.map some) = []
      rw [show rewriteStatefulFlatMapFrom spec .start
          (some .certificateMark :: none :: candidate.map some) =
        rewriteStatefulFlatMapFrom spec (.payload false)
          (candidate.map some) by rfl]
      exact payload_false candidate
  | true =>
      change rewriteStatefulFlatMapFrom spec .start
        (some .instanceMark :: none :: candidate.map some) = candidate
      rw [show rewriteStatefulFlatMapFrom spec .start
          (some .instanceMark :: none :: candidate.map some) =
        rewriteStatefulFlatMapFrom spec (.payload true)
          (candidate.map some) by rfl]
      exact payload_true candidate

end CLRS.Chapter34.Turing.TSPReduction.RawSelector
