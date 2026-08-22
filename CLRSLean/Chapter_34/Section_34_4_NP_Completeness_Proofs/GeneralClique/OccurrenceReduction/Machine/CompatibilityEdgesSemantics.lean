import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesIterations
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: canonical semantics

This file identifies the edge order accumulated by the compatibility
controller with the textbook `normalizedPairs` enumeration used by the
general CLIQUE instance.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private def occurrenceCliqueEdgesFor
    (occurrences : List IndexedOccurrence) : List (Nat × Nat) :=
  (normalizedPairs occurrences.length).filter fun edge =>
    match occurrences[edge.1]?, occurrences[edge.2]? with
    | some left, some right => decide (left.Compatible right)
    | _, _ => false

private def encodeOccurrenceCliqueEdgesFor
    (occurrences : List IndexedOccurrence) : List CliqueSym :=
  (occurrenceCliqueEdgesFor occurrences).flatMap encodeCliqueEdge

/-- The controller's executable comparison bit is exactly the semantic
compatibility predicate on the two indexed occurrences. -/
theorem indexedOccurrencesCompatibleCode_eq_decide
    (current prior : IndexedOccurrence × Nat) :
    indexedOccurrencesCompatibleCode current prior =
      decide (prior.1.Compatible current.1) := by
  rcases current with ⟨⟨cc, cp, cl⟩, cv⟩
  rcases prior with ⟨⟨pc, pp, pl⟩, pv⟩
  cases cl <;> cases pl <;>
    simp [indexedOccurrencesCompatibleCode, occurrenceRowsCompatibleCode,
      IndexedOccurrence.Compatible, occurrencePolarityFlag,
      occurrenceVariableCode, complement]

private theorem zipIdx_map_snd (occurrences : List IndexedOccurrence) :
    occurrences.zipIdx.map Prod.snd = List.range occurrences.length := by
  rw [List.zipIdx_eq_zip_range', List.range_eq_range']
  apply List.map_snd_zip
  rw [List.length_range']

private theorem oldFilter_eq (occurrences : List IndexedOccurrence)
    (right : IndexedOccurrence) :
    List.filter
      (fun edge =>
        match (occurrences ++ [right])[edge.1]?,
            (occurrences ++ [right])[edge.2]? with
        | some left, some right => decide (left.Compatible right)
        | _, _ => false)
      (normalizedPairs occurrences.length) =
    List.filter
      (fun edge =>
        match occurrences[edge.1]?, occurrences[edge.2]? with
        | some left, some right => decide (left.Compatible right)
        | _, _ => false)
      (normalizedPairs occurrences.length) := by
  apply List.filter_congr
  intro edge hedge
  have hbounds := normalizedPairs_mem_iff.mp hedge
  have hleft : edge.1 < occurrences.length :=
    lt_trans hbounds.1 hbounds.2
  simp [List.getElem?_append, hleft, hbounds.2]

private theorem flatMap_filter_bool {α β : Type} (p : α → Bool)
    (f : α → List β) (xs : List α) :
    (xs.filter p).flatMap f =
      xs.flatMap fun x => if p x then f x else [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases h : p x <;> simp [h, ih]

private theorem newFilterEncoding_eq
    (occurrences : List IndexedOccurrence) (right : IndexedOccurrence) :
    List.flatMap encodeCliqueEdge
      (List.filter
        (fun edge =>
          match (occurrences ++ [right])[edge.1]?,
              (occurrences ++ [right])[edge.2]? with
          | some left, some right => decide (left.Compatible right)
          | _, _ => false)
        ((List.range occurrences.length).map fun u =>
          (u, occurrences.length))) =
      encodeCompatibleOccurrenceEdges (right, occurrences.length)
        occurrences.zipIdx := by
  have hindices :
      (List.range occurrences.length).map
          (fun u => (u, occurrences.length)) =
        occurrences.zipIdx.map fun prior =>
          (prior.2, occurrences.length) := by
    calc
      _ = (occurrences.zipIdx.map Prod.snd).map
          (fun u => (u, occurrences.length)) := by
            rw [zipIdx_map_snd]
      _ = _ := by
        simp only [List.map_map]
        rfl
  rw [hindices, List.filter_map, List.flatMap_map]
  have hpredicate : ∀ prior ∈ occurrences.zipIdx,
      (match (occurrences ++ [right])[prior.2]?,
          (occurrences ++ [right])[occurrences.length]? with
        | some left, some right => decide (left.Compatible right)
        | _, _ => false) =
      decide (prior.1.Compatible right) := by
    intro prior hprior
    have hfields := List.mem_zipIdx hprior
    have hbound : prior.2 < occurrences.length := by omega
    have hvalue : prior.1 = occurrences[prior.2] := by
      simpa using hfields.2.2
    simp [List.getElem?_append, hbound, hvalue]
  rw [List.filter_congr (fun prior hprior => by
    simpa only [Function.comp_apply] using hpredicate prior hprior)]
  rw [flatMap_filter_bool]
  unfold encodeCompatibleOccurrenceEdges
  apply List.flatMap_congr
  intro prior hprior
  simp [encodeCompatibleOccurrenceEdge,
    indexedOccurrencesCompatibleCode_eq_decide]

private theorem occurrenceCliqueEdgesFor_append_singleton
    (occurrences : List IndexedOccurrence) (right : IndexedOccurrence) :
    encodeOccurrenceCliqueEdgesFor (occurrences ++ [right]) =
      encodeOccurrenceCliqueEdgesFor occurrences ++
        encodeCompatibleOccurrenceEdges (right, occurrences.length)
          occurrences.zipIdx := by
  unfold encodeOccurrenceCliqueEdgesFor occurrenceCliqueEdgesFor
  simp only [List.length_append, List.length_singleton,
    normalizedPairs, List.filter_append, List.flatMap_append]
  rw [oldFilter_eq, newFilterEncoding_eq]

private theorem encodeCompatibleOccurrenceIterations_reverse_zipIdx
    (occurrences : List IndexedOccurrence) :
    encodeCompatibleOccurrenceIterations occurrences.zipIdx.reverse =
      encodeOccurrenceCliqueEdgesFor occurrences := by
  induction occurrences using List.reverseRecOn with
  | nil =>
      simp [encodeCompatibleOccurrenceIterations,
        encodeOccurrenceCliqueEdgesFor, occurrenceCliqueEdgesFor,
        normalizedPairs]
  | append_singleton occurrences right ih =>
      rw [List.zipIdx_append]
      simp only [List.zipIdx_singleton, Nat.zero_add, List.reverse_append,
        List.reverse_singleton]
      change encodeCompatibleOccurrenceIterations
          ((right, occurrences.length) :: occurrences.zipIdx.reverse) = _
      rw [encodeCompatibleOccurrenceIterations, List.reverse_reverse, ih,
        occurrenceCliqueEdgesFor_append_singleton]

/-- Exhausting the loaded canonical occurrence rows emits precisely the
serialized edge suffix of the textbook occurrence graph, in its canonical
normalized-pair order. -/
theorem encodeCompatibleOccurrenceIterations_canonical (formula : CNF) :
    encodeCompatibleOccurrenceIterations
        (indexedOccurrences formula).zipIdx.reverse =
      encodeOccurrenceCliqueEdges formula := by
  rw [encodeCompatibleOccurrenceIterations_reverse_zipIdx]
  rfl

end TMClique
end Turing
end Chapter34
end CLRS
