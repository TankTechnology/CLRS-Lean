import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# HAM-CYCLE verifier target-field increment

A three-state streaming transducer copies a separator-encoded
certificate/graph pair and inserts one unary tick immediately after the first
graph field separator.  On canonical graph encodings this changes target
`k` to `k + 1` and nothing else.  Reusing the existing target-bound machine on
the original and transformed streams distinguishes `k = n` from `k < n`.

Main results:

- Theorem `incrementTargetField_encode`: exact action on canonical instances.
- Definition `computableInPolyTime`: a fixed linear-time TM2 for the paired
  transformation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.TargetIncrement

open _root_.Turing
open PolyBuilder

/-- Paired raw verifier input. -/
abbrev RawInput := List CliqueSym × List CliqueSym

/-- Standard separator encoding of a certificate/instance pair. -/
def rawEncoding (input : RawInput) : List (Option CliqueSym) :=
  pairEncoding input.1 input.2

/-- Insert one tick after the first field separator of a raw graph word. -/
def incrementTargetField : List CliqueSym → List CliqueSym
  | [] => []
  | .fieldSep :: rest => .fieldSep :: .tick :: rest
  | symbol :: rest => symbol :: incrementTargetField rest

/-- Semantic transformation on paired verifier inputs. -/
def incrementedInput (input : RawInput) : RawInput :=
  (input.1, incrementTargetField input.2)

/-- Incrementing below a unary prefix preserves that prefix. -/
theorem incrementTargetField_prependCliqueTicks
    (count : Nat) (rest : List CliqueSym) :
    incrementTargetField
        (prependCliqueTicks count (.fieldSep :: rest)) =
      prependCliqueTicks count (.fieldSep :: .tick :: rest) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, incrementTargetField, ih]

/-- On a canonical graph encoding, the transducer increments only the target
field. -/
theorem incrementTargetField_encode (I : CliqueInstance) :
    incrementTargetField (encodeCliqueInstance I) =
      encodeCliqueInstance { I with targetSize := I.targetSize + 1 } := by
  simp only [encodeCliqueInstance, incrementTargetField]
  rw [incrementTargetField_prependCliqueTicks]
  simp [prependCliqueTicks]

/-- Finite streaming modes: copy the certificate, seek the first graph field
separator, then copy the remaining graph suffix. -/
inductive Mode
  | certificate
  | graphHeader
  | copied
deriving DecidableEq, Fintype

/-- Fixed finite-state specification of target-field increment on paired raw
streams. -/
def spec : StatefulFlatMapSpec Mode (Option CliqueSym) (Option CliqueSym) where
  initial := .certificate
  action mode symbol :=
    match mode with
    | .certificate =>
        match symbol with
        | none => ([none], .graphHeader)
        | some token => ([some token], .certificate)
    | .graphHeader =>
        match symbol with
        | some .fieldSep => ([some .fieldSep, some .tick], .copied)
        | token => ([token], .graphHeader)
    | .copied => ([symbol], .copied)
  finish _ := []

private theorem rewrite_copied (input : List (Option CliqueSym)) :
    rewriteStatefulFlatMapFrom spec .copied input = input := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change symbol :: rewriteStatefulFlatMapFrom spec .copied input =
        symbol :: input
      exact congrArg (List.cons symbol) ih

private theorem rewrite_graphHeader (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
      (incrementTargetField input).map some := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      cases symbol with
      | fieldSep =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.fieldSep :: some CliqueSym.tick ::
              rewriteStatefulFlatMapFrom spec .copied (input.map some) =
            some CliqueSym.fieldSep :: some CliqueSym.tick :: input.map some
          exact congrArg (List.cons (some CliqueSym.fieldSep))
            (congrArg (List.cons (some CliqueSym.tick))
              (rewrite_copied (input.map some)))
      | instanceMark =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.instanceMark ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.instanceMark ::
              (incrementTargetField input).map some
          exact congrArg (List.cons (some CliqueSym.instanceMark)) ih
      | certificateMark =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.certificateMark ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.certificateMark ::
              (incrementTargetField input).map some
          exact congrArg (List.cons (some CliqueSym.certificateMark)) ih
      | tick =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.tick ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.tick :: (incrementTargetField input).map some
          exact congrArg (List.cons (some CliqueSym.tick)) ih
      | edgeMark =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.edgeMark ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.edgeMark :: (incrementTargetField input).map some
          exact congrArg (List.cons (some CliqueSym.edgeMark)) ih
      | vertexMark =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.vertexMark ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.vertexMark ::
              (incrementTargetField input).map some
          exact congrArg (List.cons (some CliqueSym.vertexMark)) ih
      | pairSep =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.pairSep ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.pairSep :: (incrementTargetField input).map some
          exact congrArg (List.cons (some CliqueSym.pairSep)) ih
      | recordEnd =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.recordEnd ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.recordEnd ::
              (incrementTargetField input).map some
          exact congrArg (List.cons (some CliqueSym.recordEnd)) ih

private theorem rewrite_certificate
    (certificate input : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec .certificate
        (pairEncoding certificate input) =
      pairEncoding certificate (incrementTargetField input) := by
  induction certificate with
  | nil =>
      simp only [pairEncoding, List.map_nil, List.nil_append]
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change none :: rewriteStatefulFlatMapFrom spec .graphHeader
          (input.map some) =
        none :: (incrementTargetField input).map some
      exact congrArg (List.cons none) (rewrite_graphHeader input)
  | cons symbol certificate ih =>
      simp only [pairEncoding, List.map_cons, List.cons_append]
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change some symbol :: rewriteStatefulFlatMapFrom spec .certificate
          (pairEncoding certificate input) =
        some symbol :: pairEncoding certificate (incrementTargetField input)
      exact congrArg (List.cons (some symbol)) ih

/-- The finite-state semantics is exactly target increment on the graph half
of a paired verifier input. -/
theorem rewrite_eq_pair (input : RawInput) :
    rewriteStatefulFlatMap spec (rawEncoding input) =
      rawEncoding (incrementedInput input) := by
  rcases input with ⟨certificate, graph⟩
  exact rewrite_certificate certificate graph

/-- A fixed polynomial-time TM2 increments the graph target field while
preserving the certificate and the rest of the graph word exactly. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime rawEncoding rawEncoding incrementedInput := by
  let machine := statefulFlatMap_computableInPolyTime spec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun (rawEncoding input)
        rw [rewrite_eq_pair input] at output
        simpa using output }

/-- On canonical input, running the existing target-bound Boolean after the
increment is exactly the strict inequality test `targetSize < vertexCount`. -/
theorem targetBound_incremented_encode_iff
    (certificate : List CliqueSym) (I : CliqueInstance) :
    GeneralCliqueVerifier.TargetBound.targetBoundPass certificate
        (incrementTargetField (encodeCliqueInstance I)) = true ↔
      I.targetSize < I.vertexCount := by
  rw [incrementTargetField_encode]
  rw [GeneralCliqueVerifier.TargetBound.targetBoundPass_encode_iff]
  change I.targetSize + 1 ≤ I.vertexCount ↔
    I.targetSize < I.vertexCount
  omega

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.TargetIncrement
