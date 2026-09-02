import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Load

/-!
# HAM-CYCLE incidence scanner: reversed vertex query parsing
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder

/-- Exact cost of loading one reversed unary vertex query. -/
def querySteps (vertex : Nat) : Nat := 2 * vertex + 2

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail =
      List.replicate count CliqueSym.tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [prependCliqueTicks, ih, List.replicate_succ]
      rfl

private def queryTicks_run (remaining loaded : Nat)
    (tail input : List (Option CliqueSym)) (output : List UnaryFrameSym)
    (work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .queryTicks buffer₁ buffer₂ test
        input output
        ((List.replicate remaining (some CliqueSym.tick)) ++
          some CliqueSym.vertexMark :: tail)
        work₂ (List.replicate loaded ()) [] [])
      (some (cfg .instanceMark (some (some .vertexMark)) buffer₂ test
        input output tail work₂ (List.replicate (remaining + loaded) ()) [] []))
      (2 * remaining + 1) := by
  induction remaining generalizing loaded buffer₁ with
  | zero =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg .incQuery (some (some .tick)) buffer₂ test
        input output
        (List.replicate remaining (some CliqueSym.tick) ++
          some CliqueSym.vertexMark :: tail)
        work₂ (List.replicate loaded ()) [] []
      let afterInc := cfg .queryTicks (some (some .tick)) buffer₂ test
        input output
        (List.replicate remaining (some CliqueSym.tick) ++
          some CliqueSym.vertexMark :: tail)
        work₂ (List.replicate (loaded + 1) ()) [] []
      have first : EvalsToInTime (step program)
          (cfg .queryTicks buffer₁ buffer₂ test input output
            (List.replicate (remaining + 1) (some CliqueSym.tick) ++
              some CliqueSym.vertexMark :: tail)
            work₂ (List.replicate loaded ()) [] [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterInc) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterInc, step, program, cfg, stepOp,
          List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (loaded := loaded + 1)
        (buffer₁ := some (some CliqueSym.tick))
      let firstTwo := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ firstTwo rest
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

/-- Pop the record terminator, load the unary query into counter one, and
enter the graph scan with the other two counters empty. -/
def query_run (vertex : Nat) (tail input : List (Option CliqueSym))
    (output : List UnaryFrameSym) (work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .nextQuery buffer₁ buffer₂ test input output
        (((encodeCliqueVertex vertex).map some).reverse ++ tail)
        work₂ [] [] [])
      (some (cfg .instanceMark (some (some .vertexMark)) buffer₂ test
        input output tail work₂ (List.replicate vertex ()) [] []))
      (querySteps vertex) := by
  let afterPop := cfg .queryTicks (some (some .recordEnd)) buffer₂ test
    input output
    (List.replicate vertex (some CliqueSym.tick) ++
      some CliqueSym.vertexMark :: tail)
    work₂ [] [] []
  have first : EvalsToInTime (step program)
      (cfg .nextQuery buffer₁ buffer₂ test input output
        (((encodeCliqueVertex vertex).map some).reverse ++ tail)
        work₂ [] [] [])
      (some afterPop) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    simp [flip, afterPop, encodeCliqueVertex,
      prependCliqueTicks_eq_replicate, step, program, cfg, stepOp,
      List.reverse_append, List.reverse_replicate, List.append_assoc]
  have rest := queryTicks_run vertex 0 tail input output work₂
    (some (some CliqueSym.recordEnd)) buffer₂ test
  let full := EvalsToInTime.trans (step program)
    1 (2 * vertex + 1) _ afterPop _ first rest
  convert full using 1
  all_goals
    simp [querySteps, Nat.add_comm]
  omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner
