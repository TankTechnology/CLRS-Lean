import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.TargetBound.Canonical
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# HAM-CYCLE verifier minimum vertex count

A fixed streaming transducer replaces the target field by the unary constant
three.  Running the existing target-bound machine on the result decides the
textbook simple-cycle side condition `3 ≤ vertexCount`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.MinimumVertexCount

open _root_.Turing
open PolyBuilder

abbrev RawInput := List CliqueSym × List CliqueSym

def rawEncoding (input : RawInput) : List (Option CliqueSym) :=
  pairEncoding input.1 input.2

/-- Drop the current target field, retaining its terminating separator and
the complete edge suffix. -/
def dropTargetField : List CliqueSym → List CliqueSym
  | [] => []
  | .fieldSep :: rest => .fieldSep :: rest
  | _ :: rest => dropTargetField rest

/-- Replace the first graph target field by exactly three ticks. -/
def replaceTargetWithThree : List CliqueSym → List CliqueSym
  | [] => []
  | .fieldSep :: rest =>
      .fieldSep :: .tick :: .tick :: .tick :: dropTargetField rest
  | symbol :: rest => symbol :: replaceTargetWithThree rest

def replacedInput (input : RawInput) : RawInput :=
  (input.1, replaceTargetWithThree input.2)

private theorem dropTargetField_prepend (count : Nat)
    (rest : List CliqueSym) :
    dropTargetField (prependCliqueTicks count (.fieldSep :: rest)) =
      .fieldSep :: rest := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, dropTargetField, ih]

private theorem replaceTargetWithThree_prepend (count : Nat)
    (rest : List CliqueSym) :
    replaceTargetWithThree
        (prependCliqueTicks count (.fieldSep :: rest)) =
      prependCliqueTicks count
        (.fieldSep :: .tick :: .tick :: .tick :: dropTargetField rest) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [prependCliqueTicks, replaceTargetWithThree, ih]

/-- Exact typed effect on canonical graph encodings. -/
theorem replaceTargetWithThree_encode (I : CliqueInstance) :
    replaceTargetWithThree (encodeCliqueInstance I) =
      encodeCliqueInstance { I with targetSize := 3 } := by
  simp only [encodeCliqueInstance, replaceTargetWithThree]
  rw [replaceTargetWithThree_prepend, dropTargetField_prepend]
  rfl

inductive Mode
  | certificate
  | graphHeader
  | target
  | copied
deriving DecidableEq, Fintype

/-- Fixed paired-stream implementation of `replaceTargetWithThree`. -/
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
        | some .fieldSep =>
            ([some .fieldSep, some .tick, some .tick, some .tick], .target)
        | token => ([token], .graphHeader)
    | .target =>
        match symbol with
        | some .fieldSep => ([some .fieldSep], .copied)
        | _ => ([], .target)
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

private theorem rewrite_target (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec .target (input.map some) =
      (dropTargetField input).map some := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      cases symbol with
      | fieldSep =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.fieldSep ::
              rewriteStatefulFlatMapFrom spec .copied (input.map some) =
            some CliqueSym.fieldSep :: input.map some
          exact congrArg (List.cons (some CliqueSym.fieldSep))
            (rewrite_copied (input.map some))
      | instanceMark | certificateMark | tick | edgeMark | vertexMark |
          pairSep | recordEnd =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change rewriteStatefulFlatMapFrom spec .target (input.map some) =
            (dropTargetField input).map some
          exact ih

private theorem rewrite_graphHeader (input : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
      (replaceTargetWithThree input).map some := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      cases symbol with
      | fieldSep =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.fieldSep :: some CliqueSym.tick ::
              some CliqueSym.tick :: some CliqueSym.tick ::
                rewriteStatefulFlatMapFrom spec .target (input.map some) =
            some CliqueSym.fieldSep :: some CliqueSym.tick ::
              some CliqueSym.tick :: some CliqueSym.tick ::
                (dropTargetField input).map some
          exact congrArg (List.cons (some CliqueSym.fieldSep))
            (congrArg (List.cons (some CliqueSym.tick))
              (congrArg (List.cons (some CliqueSym.tick))
                (congrArg (List.cons (some CliqueSym.tick))
                  (rewrite_target input))))
      | instanceMark =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.instanceMark ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.instanceMark ::
              (replaceTargetWithThree input).map some
          exact congrArg (List.cons (some CliqueSym.instanceMark)) ih
      | certificateMark =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.certificateMark ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.certificateMark ::
              (replaceTargetWithThree input).map some
          exact congrArg (List.cons (some CliqueSym.certificateMark)) ih
      | tick =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.tick ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.tick :: (replaceTargetWithThree input).map some
          exact congrArg (List.cons (some CliqueSym.tick)) ih
      | edgeMark =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.edgeMark ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.edgeMark ::
              (replaceTargetWithThree input).map some
          exact congrArg (List.cons (some CliqueSym.edgeMark)) ih
      | vertexMark =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.vertexMark ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.vertexMark ::
              (replaceTargetWithThree input).map some
          exact congrArg (List.cons (some CliqueSym.vertexMark)) ih
      | pairSep =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.pairSep ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.pairSep ::
              (replaceTargetWithThree input).map some
          exact congrArg (List.cons (some CliqueSym.pairSep)) ih
      | recordEnd =>
          rw [rewriteStatefulFlatMapFrom.eq_def]
          change some CliqueSym.recordEnd ::
              rewriteStatefulFlatMapFrom spec .graphHeader (input.map some) =
            some CliqueSym.recordEnd ::
              (replaceTargetWithThree input).map some
          exact congrArg (List.cons (some CliqueSym.recordEnd)) ih

private theorem rewrite_certificate (certificate input : List CliqueSym) :
    rewriteStatefulFlatMapFrom spec .certificate
        (pairEncoding certificate input) =
      pairEncoding certificate (replaceTargetWithThree input) := by
  induction certificate with
  | nil =>
      simp only [pairEncoding, List.map_nil, List.nil_append]
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change none :: rewriteStatefulFlatMapFrom spec .graphHeader
          (input.map some) =
        none :: (replaceTargetWithThree input).map some
      exact congrArg (List.cons none) (rewrite_graphHeader input)
  | cons symbol certificate ih =>
      simp only [pairEncoding, List.map_cons, List.cons_append]
      rw [rewriteStatefulFlatMapFrom.eq_def]
      change some symbol :: rewriteStatefulFlatMapFrom spec .certificate
          (pairEncoding certificate input) =
        some symbol :: pairEncoding certificate (replaceTargetWithThree input)
      exact congrArg (List.cons (some symbol)) ih

theorem rewrite_eq_pair (input : RawInput) :
    rewriteStatefulFlatMap spec (rawEncoding input) =
      rawEncoding (replacedInput input) := by
  rcases input with ⟨certificate, graph⟩
  exact rewrite_certificate certificate graph

/-- Fixed polynomial-time paired-stream target replacement. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime rawEncoding rawEncoding replacedInput := by
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

/-- On canonical inputs, the reused target-bound pass is exactly the minimum
three-vertex condition. -/
theorem targetBound_replaced_encode_iff
    (certificate : List CliqueSym) (I : CliqueInstance) :
    GeneralCliqueVerifier.TargetBound.targetBoundPass certificate
        (replaceTargetWithThree (encodeCliqueInstance I)) = true ↔
      3 ≤ I.vertexCount := by
  rw [replaceTargetWithThree_encode]
  rw [GeneralCliqueVerifier.TargetBound.targetBoundPass_encode_iff]

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.MinimumVertexCount
