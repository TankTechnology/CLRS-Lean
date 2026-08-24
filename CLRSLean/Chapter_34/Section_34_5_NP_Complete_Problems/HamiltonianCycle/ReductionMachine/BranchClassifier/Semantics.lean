import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchClassifier.Core

/-!
# VERTEX-COVER to HAM-CYCLE branch-classifier semantics
-/

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchClassifier

open PolyBuilder

private theorem vertices_ticks (count : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec .vertices
        (prependCliqueTicks count (.fieldSep :: tail)) =
      rewriteStatefulFlatMapFrom spec (.target false) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [prependCliqueTicks, rewriteStatefulFlatMapFrom, spec] using ih

private theorem target_true_ticks (count : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec (.target true)
        (prependCliqueTicks count (.fieldSep :: tail)) =
      rewriteStatefulFlatMapFrom spec (.edges true false) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [prependCliqueTicks, rewriteStatefulFlatMapFrom, spec] using ih

private theorem target_ticks (count : Nat) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec (.target false)
        (prependCliqueTicks count (.fieldSep :: tail)) =
      rewriteStatefulFlatMapFrom spec (.edges (count != 0) false) tail := by
  cases count with
  | zero => rfl
  | succ count =>
      simpa [prependCliqueTicks, rewriteStatefulFlatMapFrom, spec] using
        target_true_ticks count tail

private theorem edges_seen (targetPositive : Bool) (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec (.edges targetPositive true) tail =
      [((if targetPositive then Branch.ordinary else Branch.no)).symbol] := by
  induction tail with
  | nil => cases targetPositive <;>
      simp [rewriteStatefulFlatMapFrom, spec, finishBranch]
  | cons symbol tail ih =>
      simpa [rewriteStatefulFlatMapFrom, spec] using ih

private theorem edges_nonempty (targetPositive : Bool) (symbol : CliqueSym)
    (tail : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec (.edges targetPositive false)
        (symbol :: tail) =
      [((if targetPositive then Branch.ordinary else Branch.no)).symbol] := by
  simp only [rewriteStatefulFlatMapFrom, spec, List.nil_append]
  exact edges_seen targetPositive tail

/-- On a canonical typed source, the classifier emits exactly one branch tag. -/
theorem stream_encode (I : VertexCoverInstance) :
    stream (encodeVertexCoverInstance I) = [(branch I).symbol] := by
  change rewriteStatefulFlatMapFrom spec .start
      (.instanceMark :: prependCliqueTicks I.vertexCount
        (.fieldSep :: prependCliqueTicks I.targetSize
          (.fieldSep :: I.edges.flatMap encodeCliqueEdge))) = _
  rw [show rewriteStatefulFlatMapFrom spec .start
      (.instanceMark :: prependCliqueTicks I.vertexCount
        (.fieldSep :: prependCliqueTicks I.targetSize
          (.fieldSep :: I.edges.flatMap encodeCliqueEdge))) =
      rewriteStatefulFlatMapFrom spec .vertices
        (prependCliqueTicks I.vertexCount
          (.fieldSep :: prependCliqueTicks I.targetSize
            (.fieldSep :: I.edges.flatMap encodeCliqueEdge))) by rfl]
  rw [vertices_ticks, target_ticks]
  cases hedges : I.edges with
  | nil =>
      simp [rewriteStatefulFlatMapFrom, spec, finishBranch, branch, hedges]
  | cons edge rest =>
      rw [List.flatMap_cons]
      have hrecord : encodeCliqueEdge edge ≠ [] := by
        simp [encodeCliqueEdge]
      cases hencoded : encodeCliqueEdge edge with
      | nil => exact (hrecord hencoded).elim
      | cons symbol tail =>
          rw [List.cons_append, edges_nonempty]
          cases htarget : I.targetSize with
          | zero => simp [branch, hedges, htarget]
          | succ target => simp [branch, hedges, htarget]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.BranchClassifier
