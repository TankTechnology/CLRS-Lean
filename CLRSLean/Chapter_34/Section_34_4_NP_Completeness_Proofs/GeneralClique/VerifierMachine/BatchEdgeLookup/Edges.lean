import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.CandidateRight

/-!
# Batch edge lookup: canonical edge-list scan
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Exact cost of scanning one canonical graph edge list, stopping comparison
after the first match but still preserving the unread graph suffix. -/
def edgesSteps (query : Nat × Nat) : List (Nat × Nat) → Nat
  | [] => 1
  | edge :: edges =>
      1 + EdgeLookup.leftFieldSteps query.1 0 edge.1 +
        EdgeLookup.rightFieldSteps query.2 0 edge.2 +
        if EdgeLookup.edgeMatches query edge then
          (edges.flatMap encodeCliqueEdge).length + 1
        else edgesSteps query edges

/-- Empty scans preserve the incoming test bit; every nonempty canonical edge
record leaves it false after counter restoration. -/
def edgesFinalTest (initial : Bool) : List (Nat × Nat) → Bool
  | [] => initial
  | _ :: _ => false

private theorem encodeCliqueEdge_append (edge : Nat × Nat)
    (rest : List CliqueSym) :
    encodeCliqueEdge edge ++ rest =
      .edgeMark :: prependCliqueTicks edge.1
        (.pairSep :: prependCliqueTicks edge.2 (.recordEnd :: rest)) := by
  simp [encodeCliqueEdge, prependCliqueTicks_append]

/-- The edge scanner computes membership while preserving the entire graph
edge suffix, in reverse order, on work two. -/
def edges_run (aggregate : Bool) (query : Nat × Nat)
    (edges : List (Nat × Nat)) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.edges aggregate) buffer₁ buffer₂ test
        ((edges.flatMap encodeCliqueEdge).map some) output work₁ work₂
        (List.replicate query.1 ()) (List.replicate query.2 ()) [])
      (some (cfg (.clearLeft aggregate (decide (query ∈ edges))) buffer₁ none
        (edgesFinalTest test edges) [] output work₁
        (((edges.flatMap encodeCliqueEdge).map some).reverse ++ work₂)
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (edgesSteps query edges) := by
  induction edges generalizing buffer₂ test work₂ with
  | nil =>
      exact ⟨⟨1, by simp [flip, edgesFinalTest, step, program, cfg, stepOp]⟩,
        le_rfl⟩
  | cons edge edges ih =>
      let tail := edges.flatMap encodeCliqueEdge
      let rightInput := prependCliqueTicks edge.2 (.recordEnd :: tail)
      let afterPop := cfg (.left aggregate true) buffer₁
        (some (some .edgeMark)) test
        ((prependCliqueTicks edge.1 (.pairSep :: rightInput)).map some)
        output work₁ (some CliqueSym.edgeMark :: work₂)
        (List.replicate query.1 ()) (List.replicate query.2 ()) []
      have first : EvalsToInTime (step program)
          (cfg (.edges aggregate) buffer₁ buffer₂ test
            (((edge :: edges).flatMap encodeCliqueEdge).map some) output
            work₁ work₂ (List.replicate query.1 ())
            (List.replicate query.2 ()) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, tail, rightInput,
          List.flatMap_cons, encodeCliqueEdge_append, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have leftRun := leftField_run aggregate query.1 query.2 edge.1 true
        rightInput output work₁ (some CliqueSym.edgeMark :: work₂) buffer₁
        (some (some .edgeMark)) test
      let leftStored :=
        ((prependCliqueTicks edge.1 [.pairSep]).map some).reverse ++
          some CliqueSym.edgeMark :: work₂
      have leftRun' : EvalsToInTime (step program) afterPop
          (some (cfg (.right aggregate (decide (edge.1 = query.1)))
            buffer₁ (some (some .pairSep)) false (rightInput.map some) output
            work₁ leftStored (List.replicate query.1 ())
            (List.replicate query.2 ()) []))
          (EdgeLookup.leftFieldSteps query.1 0 edge.1) := by
        simpa [afterPop, leftStored] using leftRun
      have rightRun := rightField_run aggregate query.1 query.2 edge.2
        (decide (edge.1 = query.1)) tail output work₁ leftStored buffer₁
        (some (some .pairSep)) false
      let edgeStored := ((encodeCliqueEdge edge).map some).reverse ++ work₂
      have hstored :
          ((prependCliqueTicks edge.2 [.recordEnd]).map some).reverse ++
              leftStored = edgeStored := by
        unfold leftStored edgeStored
        simp only [encodeCliqueEdge, List.map_cons, List.reverse_cons]
        have hsplit :
            prependCliqueTicks edge.1
                (.pairSep :: prependCliqueTicks edge.2 [.recordEnd]) =
              prependCliqueTicks edge.1 [.pairSep] ++
                prependCliqueTicks edge.2 [.recordEnd] := by
          symm
          exact prependCliqueTicks_append _ _ _
        rw [hsplit]
        simp [List.map_append, List.reverse_append, List.append_assoc]
      rw [hstored] at rightRun
      have rightRun' : EvalsToInTime (step program)
          (cfg (.right aggregate (decide (edge.1 = query.1)))
            buffer₁ (some (some .pairSep)) false (rightInput.map some) output
            work₁ leftStored (List.replicate query.1 ())
            (List.replicate query.2 ()) [])
          (some (cfg
            (if EdgeLookup.edgeMatches query edge then .drainGraph aggregate
              else .edges aggregate)
            buffer₁ (some (some .recordEnd)) false (tail.map some) output
            work₁ edgeStored (List.replicate query.1 ())
            (List.replicate query.2 ()) []))
          (EdgeLookup.rightFieldSteps query.2 0 edge.2) := by
        simpa [rightInput, EdgeLookup.edgeMatches] using rightRun
      let throughLeft := EvalsToInTime.trans (step program)
        1 (EdgeLookup.leftFieldSteps query.1 0 edge.1)
        _ afterPop _ first leftRun'
      have throughLeft' : EvalsToInTime (step program)
          (cfg (.edges aggregate) buffer₁ buffer₂ test
            (((edge :: edges).flatMap encodeCliqueEdge).map some) output
            work₁ work₂ (List.replicate query.1 ())
            (List.replicate query.2 ()) [])
          (some (cfg (.right aggregate (decide (edge.1 = query.1)))
            buffer₁ (some (some .pairSep)) false (rightInput.map some) output
            work₁ leftStored (List.replicate query.1 ())
            (List.replicate query.2 ()) []))
          (1 + EdgeLookup.leftFieldSteps query.1 0 edge.1) := by
        simpa [Nat.add_comm] using throughLeft
      let throughRight := EvalsToInTime.trans (step program)
        (1 + EdgeLookup.leftFieldSteps query.1 0 edge.1)
        (EdgeLookup.rightFieldSteps query.2 0 edge.2)
        _ _ _ throughLeft' rightRun'
      cases hmatch : EdgeLookup.edgeMatches query edge with
      | false =>
          have recurse := ih (buffer₂ := some (some CliqueSym.recordEnd))
            (test := false) (work₂ := edgeStored)
          have hfinal : edgesFinalTest false edges = false := by
            cases edges <;> rfl
          rw [hfinal] at recurse
          have throughRight' : EvalsToInTime (step program)
              (cfg (.edges aggregate) buffer₁ buffer₂ test
                (((edge :: edges).flatMap encodeCliqueEdge).map some) output
                work₁ work₂ (List.replicate query.1 ())
                (List.replicate query.2 ()) [])
              (some (cfg (.edges aggregate) buffer₁
                (some (some .recordEnd)) false (tail.map some) output work₁
                edgeStored (List.replicate query.1 ())
                (List.replicate query.2 ()) []))
              (1 + EdgeLookup.leftFieldSteps query.1 0 edge.1 +
                EdgeLookup.rightFieldSteps query.2 0 edge.2) := by
            simpa [hmatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using throughRight
          let full := EvalsToInTime.trans (step program)
            (1 + EdgeLookup.leftFieldSteps query.1 0 edge.1 +
              EdgeLookup.rightFieldSteps query.2 0 edge.2)
            (edgesSteps query edges) _ _ _ throughRight' (by
              simpa [tail] using recurse)
          have hne : query ≠ edge := by
            simpa [EdgeLookup.edgeMatches_eq_decide] using hmatch
          simpa [edgesSteps, edgesFinalTest, hmatch, hne, hfinal, tail,
            edgeStored,
            List.flatMap_cons, List.reverse_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
      | true =>
          have drain := drainGraph_run aggregate (tail.map some) output work₁
            edgeStored query.1 query.2 0 buffer₁
            (some (some CliqueSym.recordEnd)) false
          have drain' : EvalsToInTime (step program)
              (cfg (.drainGraph aggregate) buffer₁
                (some (some CliqueSym.recordEnd)) false (tail.map some) output
                work₁ edgeStored (List.replicate query.1 ())
                (List.replicate query.2 ()) [])
              (some (cfg (.clearLeft aggregate true) buffer₁ none false []
                output work₁ ((tail.map some).reverse ++ edgeStored)
                (List.replicate query.1 ()) (List.replicate query.2 ()) []))
              (tail.length + 1) := by
            simpa using drain
          have throughRight' : EvalsToInTime (step program)
              (cfg (.edges aggregate) buffer₁ buffer₂ test
                (((edge :: edges).flatMap encodeCliqueEdge).map some) output
                work₁ work₂ (List.replicate query.1 ())
                (List.replicate query.2 ()) [])
              (some (cfg (.drainGraph aggregate) buffer₁
                (some (some .recordEnd)) false (tail.map some) output work₁
                edgeStored (List.replicate query.1 ())
                (List.replicate query.2 ()) []))
              (1 + EdgeLookup.leftFieldSteps query.1 0 edge.1 +
                EdgeLookup.rightFieldSteps query.2 0 edge.2) := by
            simpa [hmatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using throughRight
          let full := EvalsToInTime.trans (step program)
            (1 + EdgeLookup.leftFieldSteps query.1 0 edge.1 +
              EdgeLookup.rightFieldSteps query.2 0 edge.2)
            (tail.length + 1) _ _ _ throughRight' drain'
          have heq : query = edge := by
            simpa [EdgeLookup.edgeMatches_eq_decide] using hmatch
          have hself : EdgeLookup.edgeMatches edge edge = true := by
            simpa [heq] using hmatch
          simpa [edgesSteps, edgesFinalTest, hmatch, hself, heq, tail,
            edgeStored,
            List.flatMap_cons, List.reverse_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup
