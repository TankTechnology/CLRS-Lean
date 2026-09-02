import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Canonicalizer.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Composition
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Header
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_2_Polynomial_Time_Verification.PairProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# General CLIQUE verifier: raw pair to canonical adjacency streams

This module connects the total raw canonicalizers to the already verified
certificate-pair generator.  Both branches still share the original paired
certificate/instance input, and their outputs are prepared for the batch edge
lookup controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.AdjacencyPipeline

open PolyBuilder
open _root_.Turing

local instance : Inhabited CliqueSym := ⟨.tick⟩

/-- Semantic domain of the public verifier before its final Boolean pass. -/
abbrev RawInput := List CliqueSym × List CliqueSym

/-- Physical separator encoding used by every raw verifier component. -/
def rawEncoding (input : RawInput) : List (Option CliqueSym) :=
  pairEncoding input.1 input.2

/-- Total decoded certificate associated with a raw verifier input. -/
def rawVertices (input : RawInput) : List Nat :=
  Canonicalizer.certificateValue input.1

/-- Total decoded graph associated with a raw verifier input. -/
def rawInstance (input : RawInput) : CliqueInstance :=
  Canonicalizer.instanceValue input.2

/-- Canonically oriented positional queries generated from the total decoded
certificate. -/
def rawQueries (input : RawInput) : List (Nat × Nat) :=
  QueryNormalizer.normalizedCertificatePairs (rawVertices input)

/-- Physical query stream passed to the batch lookup controller. -/
def rawQueryStream (input : RawInput) : List CliqueSym :=
  (rawQueries input).flatMap encodeCliqueEdge

/-- Physical canonical graph stream passed to the batch lookup controller. -/
def rawGraphStream (input : RawInput) : List CliqueSym :=
  encodeCliqueInstance (rawInstance input)

/-- Project and totalize the certificate half of an arbitrary raw pair. -/
noncomputable def rawVerticesComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding encodeCliqueCertificate rawVertices := by
  let projected := PairFirstProjection.computableInPolyTime CliqueSym
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch projected
    Canonicalizer.certificateComputableInPolyTime
  change TM2ComputableInPolyTime
    (fun input : RawInput => pairEncoding input.1 input.2)
    encodeCliqueCertificate
    (fun input => Canonicalizer.certificateValue input.1)
  exact Classical.choice composed

/-- Project and totalize the graph half of an arbitrary raw pair. -/
noncomputable def rawInstanceComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding encodeCliqueInstance rawInstance := by
  let projected := Turing.Prj.prjComputableInPolyTime
    (Γ := CliqueSym)
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch projected
    Canonicalizer.instanceComputableInPolyTime
  change TM2ComputableInPolyTime
    (fun input : RawInput => pairEncoding input.1 input.2)
    encodeCliqueInstance
    (fun input => Canonicalizer.instanceValue input.2)
  exact Classical.choice composed

/-- Generate every normalized certificate query from an arbitrary raw pair. -/
noncomputable def rawQueriesComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      rawQueries := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawVerticesComputableInPolyTime
    QueryNormalizer.normalizedCertificatePairs_computableInPolyTime
  change TM2ComputableInPolyTime rawEncoding
    (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
    (fun input => QueryNormalizer.normalizedCertificatePairs
      (rawVertices input))
  exact Classical.choice composed

/-- The query generator exposed at its literal output-stream boundary. -/
noncomputable def rawQueryStreamComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id rawQueryStream := by
  let queries := rawQueriesComputableInPolyTime
  exact
    { tm := queries.tm
      inputAlphabet := queries.inputAlphabet
      outputAlphabet := queries.outputAlphabet
      time := queries.time
      outputsFun := fun input => by
        simpa [rawQueryStream] using queries.outputsFun input }

/-- The graph canonicalizer exposed at its literal output-stream boundary. -/
noncomputable def rawGraphStreamComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id rawGraphStream := by
  let graph := rawInstanceComputableInPolyTime
  exact
    { tm := graph.tm
      inputAlphabet := graph.inputAlphabet
      outputAlphabet := graph.outputAlphabet
      time := graph.time
      outputsFun := fun input => by
        simpa [rawGraphStream] using graph.outputsFun input }

/-- Stateless map from an ordinary stream to its `some`-tagged copy. -/
def someMapSpec (Γ : Type) :
    StatefulFlatMapSpec Unit Γ (Option Γ) where
  initial := ()
  action := fun _ symbol => ([some symbol], ())
  finish := fun _ => []

private theorem rewrite_someMapSpec_from {Γ : Type} (input : List Γ) :
    rewriteStatefulFlatMapFrom (someMapSpec Γ) () input = input.map some := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      change some symbol ::
          rewriteStatefulFlatMapFrom (someMapSpec Γ) () input =
        some symbol :: input.map some
      exact congrArg (some symbol :: ·) ih

@[simp] theorem rewrite_someMapSpec {Γ : Type} (input : List Γ) :
    rewriteStatefulFlatMap (someMapSpec Γ) input = input.map some := by
  exact rewrite_someMapSpec_from input

/-- Fixed linear-time mapper adding an `Option.some` tag to each symbol. -/
noncomputable def someMapComputableInPolyTime (Γ : Type) [Fintype Γ] :
    TM2ComputableInPolyTime id id (List.map (@some Γ)) := by
  let machine := statefulFlatMap_computableInPolyTime (someMapSpec Γ)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        simpa using machine.outputsFun input }

/-- Query branch with the unique pair separator already appended. -/
def queryPairLeft (input : RawInput) : List (Option CliqueSym) :=
  OptionPairLeft.format (rawQueryStream input)

/-- Graph branch tagged for the right half of a pair encoding. -/
def graphPairRight (input : RawInput) : List (Option CliqueSym) :=
  (rawGraphStream input).map some

/-- Concrete query branch, including its trailing separator. -/
noncomputable def queryPairLeftComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id queryPairLeft := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawQueryStreamComputableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => OptionPairLeft.format (rawQueryStream input))
  exact Classical.choice composed

/-- Concrete tagged graph branch. -/
noncomputable def graphPairRightComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id graphPairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawGraphStreamComputableInPolyTime
    (someMapComputableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime rawEncoding id
    (fun input => (rawGraphStream input).map some)
  exact Classical.choice composed

/-- Nine-symbol fixed pair code for `Option CliqueSym`. -/
def encodeOptionCliqueSymPair :
    Option CliqueSym → UnaryFrameSym × UnaryFrameSym
  | some symbol => TMClique.encodeCliqueSymPair symbol
  | none => (.frameEnd, .frameEnd)

/-- Decoder for the exhaustive nine-symbol pair code. -/
def decodeOptionCliqueSymPair :
    UnaryFrameSym → UnaryFrameSym → Option CliqueSym
  | .frameEnd, .frameEnd => none
  | left, right => some (TMClique.decodeCliqueSymPair left right)

@[simp] theorem decode_encodeOptionCliqueSymPair
    (symbol : Option CliqueSym) :
    decodeOptionCliqueSymPair (encodeOptionCliqueSymPair symbol).1
      (encodeOptionCliqueSymPair symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some symbol =>
      cases symbol <;> rfl

/-- Literal batch input assembled from the two same-input branches. -/
def batchInputStream (input : RawInput) : List (Option CliqueSym) :=
  pairEncoding (rawQueryStream input) (rawGraphStream input)

/-- A fixed polynomial-time TM2 constructs the exact paired input expected by
the batch edge lookup controller from arbitrary raw verifier input. -/
noncomputable def batchInputStreamComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id batchInputStream := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeOptionCliqueSymPair decodeOptionCliqueSymPair
    decode_encodeOptionCliqueSymPair
    queryPairLeftComputableInPolyTime graphPairRightComputableInPolyTime
  have machine : TM2ComputableInPolyTime rawEncoding id
      (fun input => queryPairLeft input ++ graphPairRight input) := joined
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        have heq : queryPairLeft input ++ graphPairRight input =
            batchInputStream input := by
          simp [queryPairLeft, graphPairRight, batchInputStream,
            OptionPairLeft.format, pairEncoding, List.append_assoc]
        rw [heq] at output
        simpa using output }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.AdjacencyPipeline
