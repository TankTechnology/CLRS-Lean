import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.WeightFields.Basic
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding

/-! # Formatting the diagonal of the HAM-CYCLE to TSP matrix -/

namespace CLRS.Chapter34.Turing.TSPReduction.DiagonalFields

open PolyBuilder

/-- Emit one weight-two field at every vertex-record marker. -/
def stream (input : List CliqueSym) : List TSPSym :=
  input.flatMap fun symbol =>
    match symbol with
    | .vertexMark => encodeTSPField 2
    | _ => []

def body : LoopBody CliqueSym TSPSym where
  emit := fun symbol =>
    match symbol with
    | .vertexMark => encodeTSPField 2
    | _ => []
  cost := fun _ => 5
  emit_length_le_cost := by
    intro symbol
    cases symbol <;> decide

/-- Semantic output for a typed vertex list. -/
def fields (vertices : List Nat) : List TSPSym :=
  encodeTSPFields (List.replicate vertices.length 2)

@[simp] theorem stream_nil : stream [] = [] := rfl

theorem stream_cons (symbol : CliqueSym) (input : List CliqueSym) :
    stream (symbol :: input) =
      (match symbol with
       | .vertexMark => encodeTSPField 2
       | _ => []) ++ stream input := by
  rfl

theorem stream_append (left right : List CliqueSym) :
    stream (left ++ right) = stream left ++ stream right := by
  exact List.flatMap_append

private theorem stream_prependCliqueTicks (count : Nat)
    (suffix : List CliqueSym) :
    stream (prependCliqueTicks count suffix) = stream suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [prependCliqueTicks, stream_cons, ih, List.nil_append]

@[simp] theorem stream_encodeCliqueVertex (vertex : Nat) :
    stream (encodeCliqueVertex vertex) = encodeTSPField 2 := by
  rw [encodeCliqueVertex, stream_cons, stream_prependCliqueTicks]
  rfl

private theorem stream_flatMap_encodeCliqueVertex (vertices : List Nat) :
    stream (vertices.flatMap encodeCliqueVertex) = fields vertices := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices ih =>
      rw [List.flatMap_cons, stream_append, stream_encodeCliqueVertex, ih]
      simp [fields, List.replicate_succ, encodeTSPFields]

theorem stream_encodeCliqueCertificate (vertices : List Nat) :
    stream (encodeCliqueCertificate vertices) = fields vertices := by
  rw [encodeCliqueCertificate, stream_cons]
  exact stream_flatMap_encodeCliqueVertex vertices

end CLRS.Chapter34.Turing.TSPReduction.DiagonalFields
