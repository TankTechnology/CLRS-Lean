import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Header

/-!
# Batch edge lookup: reversed query parsing
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem encodeCliqueEdge_reverse_map (edge : Nat × Nat) :
    ((encodeCliqueEdge edge).map some).reverse =
      some CliqueSym.recordEnd ::
        List.replicate edge.2 (some CliqueSym.tick) ++
        some CliqueSym.pairSep ::
          List.replicate edge.1 (some CliqueSym.tick) ++
          [some CliqueSym.edgeMark] := by
  rcases edge with ⟨left, right⟩
  simp [encodeCliqueEdge, prependCliqueTicks_eq_replicate,
    List.reverse_append, List.append_assoc]

/-- Parse the right endpoint from a reversed query record. -/
def queryRight_run (aggregate : Bool) (remaining saved : Nat)
    (tail input : List (Option CliqueSym)) (output : List Bool)
    (work₂ : List (Option CliqueSym)) (left : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.queryRight aggregate) buffer₁ buffer₂ test input output
        (List.replicate remaining (some CliqueSym.tick) ++
          some CliqueSym.pairSep :: tail)
        work₂ (List.replicate left ()) (List.replicate saved ()) [])
      (some (cfg (.queryLeft aggregate) (some (some .pairSep)) buffer₂ test
        input output tail work₂ (List.replicate left ())
        (List.replicate (saved + remaining) ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing saved buffer₁ with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg (.incQueryRight aggregate) (some (some .tick))
        buffer₂ test input output
        (List.replicate remaining (some CliqueSym.tick) ++
          some CliqueSym.pairSep :: tail)
        work₂ (List.replicate left ()) (List.replicate saved ()) []
      let afterInc := cfg (.queryRight aggregate) (some (some .tick)) buffer₂
        test input output
        (List.replicate remaining (some CliqueSym.tick) ++
          some CliqueSym.pairSep :: tail)
        work₂ (List.replicate left ()) (List.replicate (saved + 1) ()) []
      have first : EvalsToInTime (step program)
          (cfg (.queryRight aggregate) buffer₁ buffer₂ test input output
            (List.replicate (remaining + 1) (some CliqueSym.tick) ++
              some CliqueSym.pairSep :: tail)
            work₂ (List.replicate left ()) (List.replicate saved ()) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (buffer₁ := some (some .tick))
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Parse the left endpoint and enter the graph scan. -/
def queryLeft_run (aggregate : Bool) (remaining saved : Nat)
    (tail input : List (Option CliqueSym)) (output : List Bool)
    (work₂ : List (Option CliqueSym)) (right : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.queryLeft aggregate) buffer₁ buffer₂ test input output
        (List.replicate remaining (some CliqueSym.tick) ++
          some CliqueSym.edgeMark :: tail)
        work₂ (List.replicate saved ()) (List.replicate right ()) [])
      (some (cfg (.instanceMark aggregate) (some (some .edgeMark)) buffer₂
        test input output tail work₂ (List.replicate (saved + remaining) ())
        (List.replicate right ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing saved buffer₁ with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg (.incQueryLeft aggregate) (some (some .tick))
        buffer₂ test input output
        (List.replicate remaining (some CliqueSym.tick) ++
          some CliqueSym.edgeMark :: tail)
        work₂ (List.replicate saved ()) (List.replicate right ()) []
      let afterInc := cfg (.queryLeft aggregate) (some (some .tick)) buffer₂
        test input output
        (List.replicate remaining (some CliqueSym.tick) ++
          some CliqueSym.edgeMark :: tail)
        work₂ (List.replicate (saved + 1) ()) (List.replicate right ()) []
      have first : EvalsToInTime (step program)
          (cfg (.queryLeft aggregate) buffer₁ buffer₂ test input output
            (List.replicate (remaining + 1) (some CliqueSym.tick) ++
              some CliqueSym.edgeMark :: tail)
            work₂ (List.replicate saved ()) (List.replicate right ()) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (saved := saved + 1) (buffer₁ := some (some .tick))
      let firstTwo := EvalsToInTime.trans (step program) 1 1
        _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Exact reverse-record query parsing cost. -/
def querySteps (query : Nat × Nat) : Nat :=
  2 * (query.1 + query.2) + 3

/-- Pop and parse one complete reversed canonical query record. -/
def query_run (aggregate : Bool) (query : Nat × Nat)
    (tail input : List (Option CliqueSym)) (output : List Bool)
    (work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.nextQuery aggregate) buffer₁ buffer₂ test input output
        (((encodeCliqueEdge query).map some).reverse ++ tail) work₂ [] [] [])
      (some (cfg (.instanceMark aggregate) (some (some .edgeMark)) buffer₂
        test input output tail work₂ (List.replicate query.1 ())
        (List.replicate query.2 ()) []))
      (querySteps query) := by
  rw [encodeCliqueEdge_reverse_map]
  let rightTail := List.replicate query.1 (some CliqueSym.tick) ++
    some CliqueSym.edgeMark :: tail
  let afterEnd := cfg (.queryRight aggregate) (some (some .recordEnd)) buffer₂
    test input output
    (List.replicate query.2 (some CliqueSym.tick) ++
      some CliqueSym.pairSep :: rightTail)
    work₂ [] [] []
  have first : EvalsToInTime (step program)
      (cfg (.nextQuery aggregate) buffer₁ buffer₂ test input output
        (some CliqueSym.recordEnd ::
          List.replicate query.2 (some CliqueSym.tick) ++
          some CliqueSym.pairSep ::
          List.replicate query.1 (some CliqueSym.tick) ++
          [some CliqueSym.edgeMark] ++ tail)
        work₂ [] [] [])
      (some afterEnd) 1 :=
    ⟨⟨1, by simp [flip, afterEnd, rightTail, step, program, cfg,
      stepOp, List.append_assoc]⟩, le_rfl⟩
  have rightRun := queryRight_run aggregate query.2 0 rightTail input output
    work₂ 0 (some (some .recordEnd)) buffer₂ test
  let afterRight := cfg (.queryLeft aggregate) (some (some .pairSep)) buffer₂
    test input output rightTail work₂ [] (List.replicate query.2 ()) []
  have rightRun' : EvalsToInTime (step program) afterEnd (some afterRight)
      (2 * query.2 + 1) := by
    simpa [afterEnd, afterRight] using rightRun
  have leftRun := queryLeft_run aggregate query.1 0 tail input output work₂
    query.2 (some (some .pairSep)) buffer₂ test
  have leftRun' : EvalsToInTime (step program) afterRight
      (some (cfg (.instanceMark aggregate) (some (some .edgeMark)) buffer₂
        test input output tail work₂ (List.replicate query.1 ())
        (List.replicate query.2 ()) []))
      (2 * query.1 + 1) := by
    simpa [afterRight] using leftRun
  let throughRight := EvalsToInTime.trans (step program)
    1 (2 * query.2 + 1) _ afterEnd _ first rightRun'
  let full := EvalsToInTime.trans (step program)
    (1 + (2 * query.2 + 1)) (2 * query.1 + 1)
    _ afterRight _ (by simpa [Nat.add_comm] using throughRight) leftRun'
  convert full using 1
  all_goals
    simp [querySteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup
