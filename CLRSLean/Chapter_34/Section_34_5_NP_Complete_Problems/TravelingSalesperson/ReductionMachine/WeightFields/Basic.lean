import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding.Fields
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros

/-!
# HAM-CYCLE to TSP machine: formatting adjacency answers

The reusable graph lookup machine emits one Boolean per queried edge.  This
module gives the fixed local translation from those answers to the textbook
TSP weights: an edge becomes the compact field for `1`, and a nonedge becomes
the compact field for `2`.
-/

namespace CLRS.Chapter34.Turing.TSPReduction.WeightFields

open PolyBuilder

/-- Textbook weight selected by one graph-adjacency answer. -/
def answerWeight : Bool → Nat
  | true => 1
  | false => 2

/-- Canonical TSP fields corresponding to a stream of adjacency answers. -/
def stream (answers : List Bool) : List TSPSym :=
  answers.flatMap fun answer => encodeTSPField (answerWeight answer)

/-- Symbol-local body used by the verified bounded-loop compiler. -/
def body : LoopBody Bool TSPSym where
  emit := fun answer => encodeTSPField (answerWeight answer)
  cost := fun _ => 5
  emit_length_le_cost := by
    intro answer
    cases answer <;> decide

@[simp] theorem stream_nil : stream [] = [] := rfl

@[simp] theorem stream_cons (answer : Bool) (answers : List Bool) :
    stream (answer :: answers) =
      encodeTSPField (answerWeight answer) ++ stream answers := by
  rfl

theorem stream_eq_body (answers : List Bool) :
    stream answers = answers.flatMap body.emit := by
  rfl

end CLRS.Chapter34.Turing.TSPReduction.WeightFields
