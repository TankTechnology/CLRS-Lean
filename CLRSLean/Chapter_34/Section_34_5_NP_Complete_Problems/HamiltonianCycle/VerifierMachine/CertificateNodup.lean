import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.RawStreams
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeOrder.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.Semantics
import Mathlib.Tactic

/-!
# HAM-CYCLE verifier certificate distinctness

The existing CLIQUE machinery enumerates every positional pair in a
certificate and normalizes its endpoints.  Distinct values become strictly
ordered edges, while a repeated value becomes a self-pair.  Packing that edge
stream into a dummy graph therefore lets the existing fixed edge-order
machine decide certificate `Nodup` without a new quadratic controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CertificateNodup

open _root_.Turing
open PolyBuilder
open GeneralCliqueVerifier

abbrev RawInput := AdjacencyPipeline.RawInput

/-- Physical input encoding shared with the other raw verifier passes. -/
def rawEncoding : RawInput → List (Option CliqueSym) :=
  AdjacencyPipeline.rawEncoding

/-- Empty-header graph whose edge suffix is the normalized positional-pair
family generated from the certificate. -/
def queryGraph (edges : List (Nat × Nat)) : CliqueInstance :=
  { vertexCount := 0, targetSize := 0, edges := edges }

/-- Typed input expected by the reused edge-order pass. -/
def packedInput (edges : List (Nat × Nat)) :
    List CliqueSym × List CliqueSym :=
  ([], encodeCliqueInstance (queryGraph edges))

/-- Fixed prefix of the packed empty-certificate/dummy-graph stream. -/
def packedPrefix : List (Option CliqueSym) :=
  [none, some .instanceMark, some .fieldSep, some .fieldSep]

/-- Two streaming modes suffice to emit the fixed prefix once. -/
inductive PackMode
  | start
  | copy
deriving DecidableEq, Fintype

/-- Prefix each canonical edge stream by an empty certificate and a dummy
zero-field graph header. -/
def packSpec : StatefulFlatMapSpec PackMode CliqueSym (Option CliqueSym) where
  initial := .start
  action mode symbol :=
    match mode with
    | .start => (packedPrefix ++ [some symbol], .copy)
    | .copy => ([some symbol], .copy)
  finish
    | .start => packedPrefix
    | .copy => []

private theorem rewrite_pack_copy (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom packSpec .copy input = input.map some := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change some symbol :: rewriteStatefulFlatMapFrom packSpec .copy input =
        some symbol :: input.map some
      exact congrArg (List.cons (some symbol)) ih

/-- Exact byte-level effect of the fixed packer. -/
theorem rewrite_pack (input : List CliqueSym) :
    rewriteStatefulFlatMap packSpec input = packedPrefix ++ input.map some := by
  cases input with
  | nil => rfl
  | cons symbol input =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom.eq_def]
      change packedPrefix ++ [some symbol] ++
          rewriteStatefulFlatMapFrom packSpec .copy input =
        packedPrefix ++ (some symbol :: input.map some)
      rw [rewrite_pack_copy]
      simp

/-- The packer's physical stream is the standard pair encoding of the dummy
graph consumed by `EdgeOrder`. -/
theorem packed_encoding (edges : List (Nat × Nat)) :
    packedPrefix ++ (edges.flatMap encodeCliqueEdge).map some =
      pairEncoding (packedInput edges).1 (packedInput edges).2 := by
  simp [packedPrefix, packedInput, queryGraph, pairEncoding,
    encodeCliqueInstance, prependCliqueTicks]

/-- A fixed polynomial-time machine packages a normalized query family as a
dummy graph for the existing edge-order checker. -/
noncomputable def packComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      (fun input : List CliqueSym × List CliqueSym =>
        pairEncoding input.1 input.2)
      packedInput := by
  let machine := statefulFlatMap_computableInPolyTime packSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun edges => by
        have output := machine.outputsFun (edges.flatMap encodeCliqueEdge)
        rw [rewrite_pack, packed_encoding] at output
        simpa using output }

/-- Total raw Boolean used by the HAM-CYCLE verifier. -/
def nodupCheck (input : RawInput) : Bool :=
  GeneralCliqueVerifier.EdgeOrder.edgeOrderPass
    (packedInput (AdjacencyPipeline.rawQueries input)).1
    (packedInput (AdjacencyPipeline.rawQueries input)).2

/-- The certificate-pair generator, packer, and edge-order pass compose into
one fixed polynomial-time TM2. -/
noncomputable def nodupCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding nodupCheck := by
  let packed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    AdjacencyPipeline.rawQueriesComputableInPolyTime
    packComputableInPolyTime
  let checked := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (Classical.choice packed)
    GeneralCliqueVerifier.EdgeOrder.edgeOrderPassComputableInPolyTime
  change TM2ComputableInPolyTime AdjacencyPipeline.rawEncoding
    TM2Comp.boolEncoding
    (fun input => GeneralCliqueVerifier.EdgeOrder.edgeOrderPass
      (packedInput (AdjacencyPipeline.rawQueries input)).1
      (packedInput (AdjacencyPipeline.rawQueries input)).2)
  simpa only [Function.comp_def] using Classical.choice checked

/-- Normalization is strict exactly when the original endpoints differ. -/
private theorem normalizeQuery_strict_iff_ne (left right : Nat) :
    (QueryNormalizer.normalizeQuery (left, right)).1 <
        (QueryNormalizer.normalizeQuery (left, right)).2 ↔
      left ≠ right := by
  by_cases hle : left ≤ right
  · simp [QueryNormalizer.normalizeQuery, hle]
    omega
  · have hright : right < left := by omega
    simp [QueryNormalizer.normalizeQuery, hle]
    omega

/-- Every normalized positional query is strict exactly when the certificate
values are duplicate-free. -/
private theorem normalizedQueries_strict_iff_nodup (vertices : List Nat) :
    (∀ edge ∈ QueryNormalizer.normalizedCertificatePairs vertices,
        edge.1 < edge.2) ↔ vertices.Nodup := by
  induction vertices using List.reverseRecOn with
  | nil =>
      simp [QueryNormalizer.normalizedCertificatePairs,
        PairGenerator.certificateRawPairs,
        PairGenerator.certificatePairEntries,
        PairGenerator.certificatePairEntriesFrom,
        PairGenerator.compatibleOccurrencePairIterations]
  | append_singleton vertices vertex ih =>
      rw [QueryNormalizer.normalizedCertificatePairs,
        VertexCover.ComplementMachine.PairStream.certificateRawPairs_append_singleton]
      simp only [List.map_append, List.mem_append]
      constructor
      · intro hstrict
        have hleft : ∀ edge ∈
            (PairGenerator.certificateRawPairs vertices).map
              QueryNormalizer.normalizeQuery,
            edge.1 < edge.2 := by
          intro edge hedge
          exact hstrict edge (Or.inl hedge)
        have hvertices : vertices.Nodup := ih.mp hleft
        have hnotmem : vertex ∉ vertices := by
          intro hmem
          have hpresent : (vertex, vertex) ∈
              (vertices.map fun prior => (prior, vertex)).map
                QueryNormalizer.normalizeQuery := by
            rw [List.mem_map]
            refine ⟨(vertex, vertex), ?_, ?_⟩
            exact List.mem_map.mpr ⟨vertex, hmem, rfl⟩
            simp [QueryNormalizer.normalizeQuery]
          have := hstrict (vertex, vertex) (Or.inr hpresent)
          omega
        exact List.nodup_append.mpr
          ⟨hvertices, List.nodup_singleton vertex, by
            intro prior hprior only honly
            simp only [List.mem_singleton] at honly
            subst only
            intro heq
            subst prior
            exact hnotmem hprior⟩
      · intro hnodup edge hedge
        rcases (List.nodup_append.mp hnodup) with
          ⟨hvertices, _, hdisjoint⟩
        rcases hedge with hedge | hedge
        · exact ih.mpr hvertices edge hedge
        · rcases List.mem_map.mp hedge with ⟨pair, hpair, rfl⟩
          rcases List.mem_map.mp hpair with ⟨prior, hprior, rfl⟩
          rw [normalizeQuery_strict_iff_ne]
          intro heq
          subst prior
          exact hdisjoint vertex hprior vertex (by simp) rfl

/-- On any canonically decodable certificate, the concrete fixed-machine
Boolean accepts exactly duplicate-free vertex lists. -/
theorem nodupCheck_eq_true_iff
    (certificate input : List CliqueSym) (vertices : List Nat)
    (hcertificate : decodeCliqueCertificate certificate = some vertices) :
    nodupCheck (certificate, input) = true ↔ vertices.Nodup := by
  have hvalue :
      GeneralCliqueVerifier.Canonicalizer.certificateValue certificate =
        vertices := by
    simp [GeneralCliqueVerifier.Canonicalizer.certificateValue, hcertificate]
  rw [nodupCheck]
  change GeneralCliqueVerifier.EdgeOrder.edgeOrderPass []
      (encodeCliqueInstance
        (queryGraph (AdjacencyPipeline.rawQueries (certificate, input)))) =
      true ↔ vertices.Nodup
  rw [GeneralCliqueVerifier.EdgeOrder.edgeOrderPass_encode_iff]
  simp only [queryGraph]
  change (∀ edge ∈ QueryNormalizer.normalizedCertificatePairs
      (GeneralCliqueVerifier.Canonicalizer.certificateValue certificate),
      edge.1 < edge.2) ↔ vertices.Nodup
  rw [hvalue]
  exact normalizedQueries_strict_iff_nodup vertices

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CertificateNodup
