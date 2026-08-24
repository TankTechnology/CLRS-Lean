import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorEndpoints.Source
import Mathlib.Data.List.Permutation

/-!
# HAM-CYCLE selector endpoints: fixed polynomial-time edge generator
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- Selector-outer endpoint stream produced by the fixed formatter. -/
def selectorEndpointStream (I : VertexCoverInstance) : List CliqueSym :=
  offsetRowsEdgeStream (offsetFamily I)

/-- A fixed polynomial-time TM2 computes all selector-to-chain endpoint edges
from the original typed VERTEX-COVER encoding. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id
      selectorEndpointStream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    formatInputComputableInPolyTime
    offsetRowsFormatComputableInPolyTime
  change TM2ComputableInPolyTime encodeVertexCoverInstance id
    (fun I => offsetRowsEdgeStream (offsetFamily I))
  simpa only [Function.comp_def] using Classical.choice composed

theorem markedRowValues_eq_replicate (I : VertexCoverInstance) :
    unaryFrameMarkedCellAffineRowValues (markedFamily I) =
      List.replicate I.targetSize (endpointCells I) := by
  simp [unaryFrameMarkedCellAffineRowValues, markedFamily,
    List.ofFn_const]

private theorem offsetRowsEdgeStreamFrom_replicate
    (base row count : Nat) (values : List Nat) :
    offsetRowsEdgeStreamFrom base row (List.replicate count values) =
      (List.range' row count).flatMap fun selector =>
        values.flatMap fun lower =>
          encodeCliqueEdge (lower, base + selector) := by
  induction count generalizing row with
  | zero => rfl
  | succ count ih =>
      simp [List.replicate_succ, offsetRowsEdgeStreamFrom,
        List.range'_succ, ih]

theorem selectorEndpointStream_eq_selectorOuter
    (I : VertexCoverInstance) :
    selectorEndpointStream I =
      (List.range I.targetSize).flatMap fun selector =>
        (endpointCells I).flatMap fun endpoint =>
          encodeCliqueEdge
            (endpoint, selectorVertex I.edges.length selector) := by
  rw [selectorEndpointStream, offsetRowsEdgeStream, offsetFamily,
    markedRowValues_eq_replicate,
    offsetRowsEdgeStreamFrom_replicate]
  simp [selectorVertex, List.range_eq_range']

private theorem flatMap_swap_perm (xs : List α) (ys : List β)
    (emit : α → β → List γ) :
    List.Perm
      (xs.flatMap fun x => ys.flatMap fun y => emit x y)
      (ys.flatMap fun y => xs.flatMap fun x => emit x y) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      exact (ih.append_left _).trans
        (List.flatMap_append_perm ys (emit x)
          (fun y => xs.flatMap fun x => emit x y))

private theorem selectorEndpointEdgesFor_stream
    (I : VertexCoverInstance) (u : Nat) :
    (selectorEndpointEdgesFor I.edges.length I.targetSize
        (incidentOccurrences I u)).flatMap encodeCliqueEdge =
      (List.range I.targetSize).flatMap fun selector =>
        (Incidence.Endpoints.endpointValues
          (incidentOccurrences I u)).flatMap fun endpoint =>
            encodeCliqueEdge
              (endpoint, selectorVertex I.edges.length selector) := by
  cases hrefs : incidentOccurrences I u with
  | nil => simp [selectorEndpointEdgesFor,
      Incidence.Endpoints.endpointValues]
  | cons first rest =>
      have hfirstMem : first ∈ incidentOccurrences I u := by
        rw [hrefs]
        simp
      have hlastMem : (first :: rest).getLast (by simp) ∈
          incidentOccurrences I u := by
        rw [hrefs]
        exact List.getLast_mem _
      have hfirst := incidentVertex_lt_selectorBase
        (position := 0) hfirstMem (by omega)
      have hlast := incidentVertex_lt_selectorBase
        (position := 5) hlastMem (by omega)
      simp only [selectorEndpointEdgesFor, Incidence.Endpoints.endpointValues]
      rw [List.flatMap_assoc]
      apply congrArg (fun emit => (List.range I.targetSize).flatMap emit)
      funext selector
      have hfirstSelector : incidentVertex first 0 <
          selectorVertex I.edges.length selector := by
        simp [selectorVertex]
        omega
      have hlastSelector :
          incidentVertex ((first :: rest).getLast (by simp)) 5 <
            selectorVertex I.edges.length selector := by
        simp [selectorVertex]
        omega
      simp [normalizeUndirectedEdge, hfirstSelector, hlastSelector]

private theorem canonicalSelectorEndpointStream_eq_vertexOuter
    (I : VertexCoverInstance) :
    (allSelectorEndpointEdges I).flatMap encodeCliqueEdge =
      (List.range I.vertexCount).flatMap fun u =>
        (List.range I.targetSize).flatMap fun selector =>
          (Incidence.Endpoints.endpointValues
            (incidentOccurrences I u)).flatMap fun endpoint =>
              encodeCliqueEdge
                (endpoint, selectorVertex I.edges.length selector) := by
  rw [allSelectorEndpointEdges, List.flatMap_assoc]
  apply congrArg (fun emit => (List.range I.vertexCount).flatMap emit)
  funext u
  exact selectorEndpointEdgesFor_stream I u

/-- The generated stream is the textbook selector-endpoint edge family up to
record order.  `List.Perm` deliberately records preservation of duplicates,
not merely set membership. -/
theorem selectorEndpointStream_edges (I : VertexCoverInstance) :
    List.Perm (selectorEndpointStream I)
      ((allSelectorEndpointEdges I).flatMap encodeCliqueEdge) := by
  rw [selectorEndpointStream_eq_selectorOuter]
  have hswap := flatMap_swap_perm
    (List.range I.targetSize) (List.range I.vertexCount)
    (fun selector u =>
      (Incidence.Endpoints.endpointValues
        (incidentOccurrences I u)).flatMap fun endpoint =>
          encodeCliqueEdge
            (endpoint, selectorVertex I.edges.length selector))
  have hselector :
      (List.range I.targetSize).flatMap (fun selector =>
        (endpointCells I).flatMap fun endpoint =>
          encodeCliqueEdge
            (endpoint, selectorVertex I.edges.length selector)) =
      (List.range I.targetSize).flatMap fun selector =>
        (List.range I.vertexCount).flatMap fun u =>
          (Incidence.Endpoints.endpointValues
            (incidentOccurrences I u)).flatMap fun endpoint =>
              encodeCliqueEdge
                (endpoint, selectorVertex I.edges.length selector) := by
    simp [endpointCells, List.flatMap_assoc]
  rw [hselector]
  exact hswap.trans (List.Perm.of_eq
    (canonicalSelectorEndpointStream_eq_vertexOuter I).symm)

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints
