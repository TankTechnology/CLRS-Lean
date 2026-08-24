import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros

/-! # One Boolean count token per encoded graph vertex -/

namespace CLRS.Chapter34.Turing.TSPReduction.VertexTokens

open PolyBuilder

def stream (input : List CliqueSym) : List Bool :=
  input.flatMap fun symbol =>
    match symbol with
    | .vertexMark => [false]
    | _ => []

def body : LoopBody CliqueSym Bool where
  emit := fun symbol =>
    match symbol with
    | .vertexMark => [false]
    | _ => []
  cost := fun _ => 1
  emit_length_le_cost := by
    intro symbol
    cases symbol <;> decide

def tokens (vertices : List Nat) : List Bool :=
  List.replicate vertices.length false

theorem stream_cons (symbol : CliqueSym) (input : List CliqueSym) :
    stream (symbol :: input) =
      (match symbol with
       | .vertexMark => [false]
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
    stream (encodeCliqueVertex vertex) = [false] := by
  rw [encodeCliqueVertex, stream_cons, stream_prependCliqueTicks]
  rfl

private theorem stream_flatMap_encodeCliqueVertex (vertices : List Nat) :
    stream (vertices.flatMap encodeCliqueVertex) = tokens vertices := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices ih =>
      rw [List.flatMap_cons, stream_append, stream_encodeCliqueVertex, ih]
      simp [tokens, List.replicate_succ]

theorem stream_encodeCliqueCertificate (vertices : List Nat) :
    stream (encodeCliqueCertificate vertices) = tokens vertices := by
  rw [encodeCliqueCertificate, stream_cons]
  exact stream_flatMap_encodeCliqueVertex vertices

end CLRS.Chapter34.Turing.TSPReduction.VertexTokens
