import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchSelector.Core

/-!
# VERTEX-COVER to HAM-CYCLE output-selector semantics
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchSelector

open PolyBuilder

private theorem payload_ordinary (candidate : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec (.payload .ordinary)
        (candidate.map some) = candidate := by
  induction candidate with
  | nil => rfl
  | cons symbol rest ih =>
      change symbol :: rewriteStatefulFlatMapFrom spec (.payload .ordinary)
        (rest.map some) = symbol :: rest
      rw [ih]

private theorem payload_yes (candidate : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec (.payload .yes)
        (candidate.map some) =
      encodeHamiltonianCycleInstance
        HamiltonianCycleReduction.canonicalHamiltonianYesInstance := by
  induction candidate with
  | nil => rfl
  | cons symbol rest ih =>
      change rewriteStatefulFlatMapFrom spec (.payload .yes)
        (rest.map some) = _
      exact ih

private theorem payload_no (candidate : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec (.payload .no)
        (candidate.map some) =
      encodeHamiltonianCycleInstance
        HamiltonianCycleReduction.canonicalHamiltonianNoInstance := by
  induction candidate with
  | nil => rfl
  | cons symbol rest ih =>
      change rewriteStatefulFlatMapFrom spec (.payload .no)
        (rest.map some) = _
      exact ih

/-- Exact behavior on the tagged pair encoding. -/
theorem stream_inputEncoding (input : Branch × List CliqueSym) :
    stream (inputEncoding input) = selectedOutput input := by
  rcases input with ⟨branch, candidate⟩
  cases branch with
  | ordinary =>
      change rewriteStatefulFlatMapFrom spec .start
        (some .instanceMark :: none :: candidate.map some) = candidate
      rw [show rewriteStatefulFlatMapFrom spec .start
          (some .instanceMark :: none :: candidate.map some) =
        rewriteStatefulFlatMapFrom spec (.payload .ordinary)
          (candidate.map some) by rfl]
      exact payload_ordinary candidate
  | yes =>
      change rewriteStatefulFlatMapFrom spec .start
        (some .certificateMark :: none :: candidate.map some) = _
      rw [show rewriteStatefulFlatMapFrom spec .start
          (some .certificateMark :: none :: candidate.map some) =
        rewriteStatefulFlatMapFrom spec (.payload .yes)
          (candidate.map some) by rfl]
      exact payload_yes candidate
  | no =>
      change rewriteStatefulFlatMapFrom spec .start
        (some .tick :: none :: candidate.map some) = _
      rw [show rewriteStatefulFlatMapFrom spec .start
          (some .tick :: none :: candidate.map some) =
        rewriteStatefulFlatMapFrom spec (.payload .no)
          (candidate.map some) by rfl]
      exact payload_no candidate

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchSelector
