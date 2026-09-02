import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Candidate

/-!
# General CLIQUE verifier: canonical edge-list scan

The candidate comparison is lifted to an arbitrary canonical edge list.  A
successful comparison clears the unread suffix and accepts; a failed one
returns with both query counters restored and continues recursively.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder

/-- Boolean tested after both endpoint fields have been compared. -/
def edgeMatches (query edge : Nat × Nat) : Bool :=
  decide (edge.1 = query.1) && decide (edge.2 = query.2)

theorem edgeMatches_eq_decide (query edge : Nat × Nat) :
    edgeMatches query edge = decide (query = edge) := by
  calc
    edgeMatches query edge = decide (edge = query) := by
      rcases query with ⟨queryLeft, queryRight⟩
      rcases edge with ⟨left, right⟩
      simp [edgeMatches, Prod.ext_iff]
    _ = decide (query = edge) := by
      by_cases h : edge = query
      · subst query
        rfl
      · have h' : query ≠ edge := fun hqe => h hqe.symm
        simp [h, h']

/-- Exact cost of scanning a canonical list of edge records. -/
def edgesSteps (query : Nat × Nat) : List (Nat × Nat) → Nat
  | [] => 1 + (query.1 + query.2 + 6)
  | edge :: edges =>
      1 + leftFieldSteps query.1 0 edge.1 +
        rightFieldSteps query.2 0 edge.2 +
        if edgeMatches query edge then
          (edges.flatMap encodeCliqueEdge).length + query.1 + query.2 + 6
        else edgesSteps query edges

private theorem encodeCliqueEdge_append (edge : Nat × Nat)
    (rest : List CliqueSym) :
    encodeCliqueEdge edge ++ rest =
      .edgeMark :: prependCliqueTicks edge.1
        (.pairSep :: prependCliqueTicks edge.2 (.recordEnd :: rest)) := by
  simp [encodeCliqueEdge, prependCliqueTicks_append]

/-- The reusable edge scanner computes membership in an arbitrary canonical
edge list while preserving exact execution time. -/
def edges_run (query : Nat × Nat) (edges : List (Nat × Nat))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .edges buffer₁ buffer₂ test
        ((edges.flatMap encodeCliqueEdge).map some) []
        (List.replicate query.1 ()) (List.replicate query.2 ()) [])
      (some (haltCfg program [decide (query ∈ edges)]))
      (edgesSteps query edges) := by
  induction edges generalizing buffer₁ test with
  | nil =>
      let afterPop := cfg (.clearInput false) none buffer₂ test [] []
        (List.replicate query.1 ()) (List.replicate query.2 ()) []
      have first : EvalsToInTime (step program)
          (cfg .edges buffer₁ buffer₂ test
            (([].flatMap encodeCliqueEdge).map some) []
            (List.replicate query.1 ()) (List.replicate query.2 ()) [])
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have restRun := clearInput_run false [] query.1 query.2 0 none buffer₂
        test
      have restRun' : EvalsToInTime (step program) afterPop
          (some (haltCfg program [false]))
          (query.1 + query.2 + 6) := by
        simpa [afterPop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using restRun
      let full := EvalsToInTime.trans (step program)
        1 (query.1 + query.2 + 6) _ afterPop _ first restRun'
      simpa [edgesSteps, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using full
  | cons edge edges ih =>
      let tail := edges.flatMap encodeCliqueEdge
      let rightInput := prependCliqueTicks edge.2 (.recordEnd :: tail)
      let afterPop := cfg (.left true) (some (some .edgeMark)) buffer₂ test
        ((prependCliqueTicks edge.1 (.pairSep :: rightInput)).map some) []
        (List.replicate query.1 ()) (List.replicate query.2 ()) []
      have first : EvalsToInTime (step program)
          (cfg .edges buffer₁ buffer₂ test
            (((edge :: edges).flatMap encodeCliqueEdge).map some) []
            (List.replicate query.1 ()) (List.replicate query.2 ()) [])
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, tail, rightInput, List.flatMap_cons,
            encodeCliqueEdge_append, step, program, cfg, stepOp]⟩, le_rfl⟩
      have leftRun := leftField_run query.1 query.2 edge.1 true rightInput
        (some (some .edgeMark)) buffer₂ test
      have leftRun' : EvalsToInTime (step program) afterPop
          (some (cfg (.right (decide (edge.1 = query.1)))
            (some (some .pairSep)) buffer₂ false (rightInput.map some) []
            (List.replicate query.1 ()) (List.replicate query.2 ()) []))
          (leftFieldSteps query.1 0 edge.1) := by
        simpa [afterPop] using leftRun
      have rightRun := rightField_run query.1 query.2 edge.2
        (decide (edge.1 = query.1)) tail
        (some (some .pairSep)) buffer₂ false
      have rightRun' : EvalsToInTime (step program)
          (cfg (.right (decide (edge.1 = query.1)))
            (some (some .pairSep)) buffer₂ false (rightInput.map some) []
            (List.replicate query.1 ()) (List.replicate query.2 ()) [])
          (some (cfg
            (if edgeMatches query edge then .clearInput true else .edges)
            (some (some .recordEnd)) buffer₂ false (tail.map some) []
            (List.replicate query.1 ()) (List.replicate query.2 ()) []))
          (rightFieldSteps query.2 0 edge.2) := by
        simpa [rightInput, edgeMatches] using rightRun
      let throughLeft := EvalsToInTime.trans (step program)
        1 (leftFieldSteps query.1 0 edge.1) _ afterPop _ first leftRun'
      have throughLeft' : EvalsToInTime (step program)
          (cfg .edges buffer₁ buffer₂ test
            (((edge :: edges).flatMap encodeCliqueEdge).map some) []
            (List.replicate query.1 ()) (List.replicate query.2 ()) [])
          (some (cfg (.right (decide (edge.1 = query.1)))
            (some (some .pairSep)) buffer₂ false (rightInput.map some) []
            (List.replicate query.1 ()) (List.replicate query.2 ()) []))
          (1 + leftFieldSteps query.1 0 edge.1) := by
        simpa [Nat.add_comm] using throughLeft
      let throughRight := EvalsToInTime.trans (step program)
        (1 + leftFieldSteps query.1 0 edge.1)
        (rightFieldSteps query.2 0 edge.2) _ _ _ throughLeft' rightRun'
      cases hmatch : edgeMatches query edge with
      | false =>
          have recurse := ih (some (some .recordEnd)) false
          have throughRight' : EvalsToInTime (step program)
              (cfg .edges buffer₁ buffer₂ test
                (((edge :: edges).flatMap encodeCliqueEdge).map some) []
                (List.replicate query.1 ())
                (List.replicate query.2 ()) [])
              (some (cfg .edges (some (some .recordEnd)) buffer₂ false
                (tail.map some) [] (List.replicate query.1 ())
                (List.replicate query.2 ()) []))
              (1 + leftFieldSteps query.1 0 edge.1 +
                rightFieldSteps query.2 0 edge.2) := by
            simpa [hmatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using throughRight
          have recurse' : EvalsToInTime (step program)
              (cfg .edges (some (some .recordEnd)) buffer₂ false
                (tail.map some) [] (List.replicate query.1 ())
                (List.replicate query.2 ()) [])
              (some (haltCfg program [decide (query ∈ edges)]))
              (edgesSteps query edges) := by
            simpa [tail] using recurse
          let full := EvalsToInTime.trans (step program)
            (1 + leftFieldSteps query.1 0 edge.1 +
              rightFieldSteps query.2 0 edge.2)
            (edgesSteps query edges) _ _ _ throughRight' recurse'
          have hne : query ≠ edge := by
            simpa [edgeMatches_eq_decide] using hmatch
          simpa [edgesSteps, hmatch, hne, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | true =>
          have cleanup := clearInput_run true (tail.map some) query.1
            query.2 0 (some (some .recordEnd)) buffer₂ false
          have throughRight' : EvalsToInTime (step program)
              (cfg .edges buffer₁ buffer₂ test
                (((edge :: edges).flatMap encodeCliqueEdge).map some) []
                (List.replicate query.1 ())
                (List.replicate query.2 ()) [])
              (some (cfg (.clearInput true) (some (some .recordEnd))
                buffer₂ false (tail.map some) []
                (List.replicate query.1 ())
                (List.replicate query.2 ()) []))
              (1 + leftFieldSteps query.1 0 edge.1 +
                rightFieldSteps query.2 0 edge.2) := by
            simpa [hmatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using throughRight
          have cleanup' : EvalsToInTime (step program)
              (cfg (.clearInput true) (some (some .recordEnd)) buffer₂ false
                (tail.map some) [] (List.replicate query.1 ())
                (List.replicate query.2 ()) [])
              (some (haltCfg program [true]))
              (tail.length + query.1 + query.2 + 6) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using cleanup
          let full := EvalsToInTime.trans (step program)
            (1 + leftFieldSteps query.1 0 edge.1 +
              rightFieldSteps query.2 0 edge.2)
            (tail.length + query.1 + query.2 + 6)
            _ _ _ throughRight' cleanup'
          have heq : query = edge := by
            simpa [edgeMatches_eq_decide] using hmatch
          simpa [edgesSteps, edgeMatches, hmatch, heq, tail, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup
