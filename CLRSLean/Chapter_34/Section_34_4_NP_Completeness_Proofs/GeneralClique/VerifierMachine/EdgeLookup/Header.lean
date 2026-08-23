import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Query

/-!
# General CLIQUE verifier: canonical lookup header

This module connects query loading to the graph edge suffix.  The instance's
vertex-count and target-size fields are skipped without disturbing the two
persistent query counters.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder

private theorem map_prependCliqueTicks (count : Nat)
    (suffix : List CliqueSym) :
    (prependCliqueTicks count suffix).map some =
      List.replicate count (some .tick) ++ suffix.map some := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

/-- Skip a canonical vertex-count field. -/
def vertexField_run (remaining left right : Nat)
    (rest : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .vertexField buffer₁ buffer₂ test
        (List.replicate remaining (some .tick) ++ some .fieldSep :: rest) []
        (List.replicate left ()) (List.replicate right ()) [])
      (some (cfg .targetField (some (some .fieldSep)) buffer₂ test rest []
        (List.replicate left ()) (List.replicate right ()) []))
      (remaining + 1) := by
  induction remaining generalizing buffer₁ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let after := cfg .vertexField (some (some .tick)) buffer₂ test
        (List.replicate remaining (some .tick) ++ some .fieldSep :: rest) []
        (List.replicate left ()) (List.replicate right ()) []
      have first : EvalsToInTime (step program)
          (cfg .vertexField buffer₁ buffer₂ test
            (List.replicate (remaining + 1) (some .tick) ++
              some .fieldSep :: rest) []
            (List.replicate left ()) (List.replicate right ()) [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, List.replicate_succ, step, program, cfg,
            stepOp]⟩, le_rfl⟩
      have restRun := ih (some (some .tick))
      let full := EvalsToInTime.trans (step program)
        1 (remaining + 1) _ after _ first restRun
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Skip a canonical target-size field and enter the edge scanner. -/
def targetField_run (remaining left right : Nat)
    (rest : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .targetField buffer₁ buffer₂ test
        (List.replicate remaining (some .tick) ++ some .fieldSep :: rest) []
        (List.replicate left ()) (List.replicate right ()) [])
      (some (cfg .edges (some (some .fieldSep)) buffer₂ test rest []
        (List.replicate left ()) (List.replicate right ()) []))
      (remaining + 1) := by
  induction remaining generalizing buffer₁ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let after := cfg .targetField (some (some .tick)) buffer₂ test
        (List.replicate remaining (some .tick) ++ some .fieldSep :: rest) []
        (List.replicate left ()) (List.replicate right ()) []
      have first : EvalsToInTime (step program)
          (cfg .targetField buffer₁ buffer₂ test
            (List.replicate (remaining + 1) (some .tick) ++
              some .fieldSep :: rest) []
            (List.replicate left ()) (List.replicate right ()) [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, List.replicate_succ, step, program, cfg,
            stepOp]⟩, le_rfl⟩
      have restRun := ih (some (some .tick))
      let full := EvalsToInTime.trans (step program)
        1 (remaining + 1) _ after _ first restRun
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact cost of loading a canonical query and skipping the instance header. -/
def headerSteps (query : Nat × Nat) (I : CliqueInstance) : Nat :=
  1 + (2 * query.1 + 1) + (2 * query.2 + 1) + 1 + 1 +
    (I.vertexCount + 1) + (I.targetSize + 1)

/-- A canonical query-instance pair reaches the edge suffix with both query
endpoints resident in counters one and two. -/
def header_run (query : Nat × Nat) (I : CliqueInstance) :
    EvalsToInTime (step program)
      (cfg .queryMark none none false
        (pairEncoding (encodeCliqueEdge query) (encodeCliqueInstance I)) []
        [] [] [])
      (some (cfg .edges (some (some .fieldSep)) none false
        ((I.edges.flatMap encodeCliqueEdge).map some) []
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (headerSteps query I) := by
  let instanceStream := (encodeCliqueInstance I).map some
  let edgeStream := (I.edges.flatMap encodeCliqueEdge).map some
  let targetStream :=
    List.replicate I.targetSize (some CliqueSym.tick) ++
      some .fieldSep :: edgeStream
  let queryRightStream :=
    List.replicate query.2 (some CliqueSym.tick) ++
      some .recordEnd :: none :: instanceStream
  let afterMark := cfg .queryLeft (some (some .edgeMark)) none false
    (List.replicate query.1 (some .tick) ++
      some .pairSep :: queryRightStream) [] [] [] []
  have first : EvalsToInTime (step program)
      (cfg .queryMark none none false
        (pairEncoding (encodeCliqueEdge query) (encodeCliqueInstance I)) []
        [] [] [])
      (some afterMark) 1 := by
    exact ⟨⟨1, by
      simp [flip, afterMark, queryRightStream, instanceStream, pairEncoding,
        encodeCliqueEdge, map_prependCliqueTicks, step, program, cfg,
        stepOp, List.append_assoc]⟩, le_rfl⟩
  have loadLeft := queryLeft_run query.1 0 0 queryRightStream
    (some (some .edgeMark)) none false
  have loadLeft' : EvalsToInTime (step program) afterMark
      (some (cfg .queryRight (some (some .pairSep)) none false
        queryRightStream [] (List.replicate query.1 ()) [] []))
      (2 * query.1 + 1) := by
    simpa [afterMark] using loadLeft
  let throughLeft := EvalsToInTime.trans (step program)
    1 (2 * query.1 + 1) _ afterMark _ first loadLeft'
  have loadRight := queryRight_run query.1 query.2 0
    (none :: instanceStream) (some (some .pairSep)) none false
  have loadRight' : EvalsToInTime (step program)
      (cfg .queryRight (some (some .pairSep)) none false queryRightStream []
        (List.replicate query.1 ()) [] [])
      (some (cfg .pairSeparator (some (some .recordEnd)) none false
        (none :: instanceStream) [] (List.replicate query.1 ())
        (List.replicate query.2 ()) []))
      (2 * query.2 + 1) := by
    simpa [queryRightStream] using loadRight
  let throughRight := EvalsToInTime.trans (step program)
    (1 + (2 * query.1 + 1)) (2 * query.2 + 1) _ _ _
    (by simpa [Nat.add_comm] using throughLeft) loadRight'
  let afterPair := cfg .instanceMark (some none) none false instanceStream []
    (List.replicate query.1 ()) (List.replicate query.2 ()) []
  have pairStep : EvalsToInTime (step program)
      (cfg .pairSeparator (some (some .recordEnd)) none false
        (none :: instanceStream) [] (List.replicate query.1 ())
        (List.replicate query.2 ()) [])
      (some afterPair) 1 := by
    exact ⟨⟨1, by
      simp [flip, afterPair, step, program, cfg, stepOp]⟩, le_rfl⟩
  let throughPair := EvalsToInTime.trans (step program)
    (1 + (2 * query.1 + 1) + (2 * query.2 + 1)) 1 _ _ _
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using throughRight) pairStep
  let afterInstance := cfg .vertexField (some (some .instanceMark)) none false
    (List.replicate I.vertexCount (some .tick) ++
      some .fieldSep :: targetStream) []
    (List.replicate query.1 ()) (List.replicate query.2 ()) []
  have instanceStep : EvalsToInTime (step program) afterPair
      (some afterInstance) 1 := by
    exact ⟨⟨1, by
      simp [flip, afterPair, afterInstance, instanceStream, targetStream,
        edgeStream, encodeCliqueInstance, map_prependCliqueTicks, step, program, cfg,
        stepOp]⟩, le_rfl⟩
  let throughInstance := EvalsToInTime.trans (step program)
    (1 + (2 * query.1 + 1) + (2 * query.2 + 1) + 1) 1 _ _ _
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using throughPair) instanceStep
  have skipVertices := vertexField_run I.vertexCount query.1 query.2
    targetStream (some (some .instanceMark)) none false
  have skipVertices' : EvalsToInTime (step program) afterInstance
      (some (cfg .targetField (some (some .fieldSep)) none false
        targetStream [] (List.replicate query.1 ())
        (List.replicate query.2 ()) []))
      (I.vertexCount + 1) := by
    simpa [afterInstance] using skipVertices
  let throughVertices := EvalsToInTime.trans (step program)
    (1 + (2 * query.1 + 1) + (2 * query.2 + 1) + 1 + 1)
    (I.vertexCount + 1) _ _ _
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using throughInstance) skipVertices'
  have skipTarget := targetField_run I.targetSize query.1 query.2 edgeStream
    (some (some .fieldSep)) none false
  have skipTarget' : EvalsToInTime (step program)
      (cfg .targetField (some (some .fieldSep)) none false targetStream []
        (List.replicate query.1 ()) (List.replicate query.2 ()) [])
      (some (cfg .edges (some (some .fieldSep)) none false edgeStream []
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (I.targetSize + 1) := by
    simpa [targetStream] using skipTarget
  let full := EvalsToInTime.trans (step program)
    (1 + (2 * query.1 + 1) + (2 * query.2 + 1) + 1 + 1 +
      (I.vertexCount + 1))
    (I.targetSize + 1) _ _ _
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using throughVertices) skipTarget'
  simpa [headerSteps, edgeStream, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup
