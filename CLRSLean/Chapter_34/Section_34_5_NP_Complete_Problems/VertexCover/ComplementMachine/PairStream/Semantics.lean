import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.Semantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement

/-!
# VERTEX-COVER complement machine: canonical pair-stream semantics

The general CLIQUE verifier already contains a fixed polynomial-time machine
that turns a certificate into all positional vertex pairs.  Feeding it the
canonical certificate `[0, ..., n - 1]` produces exactly the normalized-pair
order shared by the occurrence graph and the VERTEX-COVER complement map.
-/

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream

open GeneralCliqueVerifier
open GeneralCliqueVerifier.PairGenerator

private theorem entriesFrom_append (position : Nat)
    (left right : List Nat) :
    certificatePairEntriesFrom position (left ++ right) =
      certificatePairEntriesFrom position left ++
        certificatePairEntriesFrom (position + left.length) right := by
  induction left generalizing position with
  | nil => simp
  | cons vertex left ih =>
      simp only [List.cons_append, certificatePairEntriesFrom_cons,
        List.length_cons, List.cons_append]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (position + 1)

private theorem entries_append_singleton (vertices : List Nat) (vertex : Nat) :
    certificatePairEntries (vertices ++ [vertex]) =
      certificatePairEntries vertices ++
        [(certificatePairOccurrence vertices.length, vertex)] := by
  simp only [certificatePairEntries]
  rw [entriesFrom_append]
  simp

private theorem entriesFrom_map_snd (position : Nat) (vertices : List Nat) :
    (certificatePairEntriesFrom position vertices).map Prod.snd = vertices := by
  induction vertices generalizing position with
  | nil => rfl
  | cons vertex vertices ih =>
      simp [certificatePairEntriesFrom, ih]

private theorem entries_map_snd (vertices : List Nat) :
    (certificatePairEntries vertices).map Prod.snd = vertices := by
  exact entriesFrom_map_snd 0 vertices

private theorem entriesFrom_synthetic (position : Nat) (vertices : List Nat) :
    ∀ entry ∈ certificatePairEntriesFrom position vertices,
      GeneralCliqueVerifier.AdjacencyPipeline.SyntheticEntry entry := by
  intro entry hentry
  induction vertices generalizing position with
  | nil => simp at hentry
  | cons vertex vertices ih =>
      simp only [certificatePairEntriesFrom_cons, List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · simp [GeneralCliqueVerifier.AdjacencyPipeline.SyntheticEntry,
          certificatePairOccurrence]
      · exact ih (position + 1) hentry

private theorem entriesFrom_clause_lt (position : Nat) (vertices : List Nat) :
    ∀ entry ∈ certificatePairEntriesFrom position vertices,
      entry.1.clauseIndex < position + vertices.length := by
  intro entry hentry
  induction vertices generalizing position with
  | nil => simp at hentry
  | cons vertex vertices ih =>
      simp only [certificatePairEntriesFrom_cons, List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · simp [certificatePairOccurrence]
      · have hlt := ih (position + 1) hentry
        simp only [List.length_cons]
        omega

/-- Adding one final certificate vertex appends precisely the pairs from every
earlier vertex to the new vertex. -/
theorem certificateRawPairs_append_singleton (vertices : List Nat)
    (vertex : Nat) :
    certificateRawPairs (vertices ++ [vertex]) =
      certificateRawPairs vertices ++ vertices.map fun prior => (prior, vertex) := by
  let current := (certificatePairOccurrence vertices.length, vertex)
  have hcurrent :
      GeneralCliqueVerifier.AdjacencyPipeline.SyntheticEntry current := by
    simp [current, GeneralCliqueVerifier.AdjacencyPipeline.SyntheticEntry,
      certificatePairOccurrence]
  have hpriors : ∀ prior ∈ certificatePairEntries vertices,
      GeneralCliqueVerifier.AdjacencyPipeline.SyntheticEntry prior := by
    intro prior hprior
    exact entriesFrom_synthetic 0 vertices prior (by
      simpa [certificatePairEntries] using hprior)
  have hne : ∀ prior ∈ certificatePairEntries vertices,
      prior.1.clauseIndex ≠ current.1.clauseIndex := by
    intro prior hprior heq
    have hlt := entriesFrom_clause_lt 0 vertices prior (by
      simpa [certificatePairEntries] using hprior)
    simp only [current, certificatePairOccurrence] at heq
    omega
  have hpairs :=
    GeneralCliqueVerifier.AdjacencyPipeline.compatibleOccurrencePairs_synthetic
      current (certificatePairEntries vertices) hcurrent hpriors hne
  have hmap :
      (certificatePairEntries vertices).map
          (fun prior => (prior.2, current.2)) =
        vertices.map fun prior => (prior, vertex) := by
    rw [show (certificatePairEntries vertices).map
          (fun prior => (prior.2, current.2)) =
        ((certificatePairEntries vertices).map Prod.snd).map
          (fun prior => (prior, vertex)) by
      simp [current, List.map_map]]
    rw [entries_map_snd]
  rw [hmap] at hpairs
  simp only [certificateRawPairs, entries_append_singleton,
    List.reverse_append, List.reverse_singleton, List.singleton_append,
    compatibleOccurrencePairIterations, List.reverse_reverse]
  exact congrArg (certificateRawPairs vertices ++ ·) hpairs

/-- The reused certificate pair generator on `[0, ..., n - 1]` emits exactly
the chapter-wide canonical normalized pairs. -/
theorem certificateRangeRawPairs_eq_normalizedPairs (n : Nat) :
    certificateRawPairs (List.range n) = normalizedPairs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, certificateRawPairs_append_singleton,
        normalizedPairs, ih]

/-- The machine-facing pair family is exactly the pair family used by the
VERTEX-COVER complement map. -/
theorem certificateRangeRawPairs_eq_vertexCoverNormalizedPairs (n : Nat) :
    certificateRawPairs (List.range n) = vertexCoverNormalizedPairs n := by
  rw [certificateRangeRawPairs_eq_normalizedPairs]
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [normalizedPairs, vertexCoverNormalizedPairs, ih]

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream
