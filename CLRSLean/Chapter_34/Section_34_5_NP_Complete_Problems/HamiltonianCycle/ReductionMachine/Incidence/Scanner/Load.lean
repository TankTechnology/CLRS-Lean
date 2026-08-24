import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Scanner.Core

/-!
# HAM-CYCLE incidence scanner: query loading
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner

open PolyBuilder

/-- Reversed physical query records stored on work stack one. -/
def encodeVertexQueryWork (vertices : List Nat) :
    List (Option CliqueSym) :=
  vertices.flatMap fun vertex => ((encodeCliqueVertex vertex).map some).reverse

theorem encodeVertexQueryWork_append (left right : List Nat) :
    encodeVertexQueryWork (left ++ right) =
      encodeVertexQueryWork left ++ encodeVertexQueryWork right := by
  simp [encodeVertexQueryWork, List.flatMap_append]

theorem encodeVertexQueryWork_reverse (vertices : List Nat) :
    encodeVertexQueryWork vertices.reverse =
      ((vertices.flatMap encodeCliqueVertex).map some).reverse := by
  induction vertices with
  | nil => rfl
  | cons vertex vertices ih =>
      rw [List.reverse_cons, encodeVertexQueryWork_append, ih]
      simp [encodeVertexQueryWork, List.map_append, List.reverse_append]

private def loadSymbols_run (symbols graph : List CliqueSym)
    (work₁ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .loadQueries buffer₁ buffer₂ test
        (symbols.map some ++ none :: graph.map some) [] work₁ [] [] [] [])
      (some (cfg .beginQueries (some none) buffer₂ test (graph.map some) []
        (none :: (symbols.map some).reverse ++ work₁) [] [] [] []))
      (symbols.length + 1) := by
  induction symbols generalizing work₁ buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol symbols ih =>
      let after := cfg .loadQueries (some (some symbol)) buffer₂ test
        (symbols.map some ++ none :: graph.map some) []
        (some symbol :: work₁) [] [] [] []
      have first : EvalsToInTime (step program)
          (cfg .loadQueries buffer₁ buffer₂ test
            ((symbol :: symbols).map some ++ none :: graph.map some) []
            work₁ [] [] [] [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (work₁ := some symbol :: work₁)
        (buffer₁ := some (some symbol))
      let full := EvalsToInTime.trans (step program)
        1 (symbols.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Exact cost of loading the vertex-query half. -/
def loadSteps (I : VertexCoverInstance) : Nat :=
  (vertexQueryStream I).length + 2

/-- Move all vertex records onto work stack one, discard the pair separator,
and enter the repeated-query loop. -/
def load_run (I : VertexCoverInstance) :
    EvalsToInTime (step program)
      (initialCfg program (Incidence.inputStream I))
      (some (cfg .nextQuery (some none) none false
        ((encodeVertexCoverInstance I).map some) []
        ((vertexQueryStream I).map some).reverse [] [] [] []))
      (loadSteps I) := by
  let symbols := vertexQueryStream I
  have loaded := loadSymbols_run symbols (encodeVertexCoverInstance I)
    [] none none false
  let afterLoad := cfg .beginQueries (some none) none false
    ((encodeVertexCoverInstance I).map some) []
    (none :: (symbols.map some).reverse) [] [] [] []
  have loaded' : EvalsToInTime (step program)
      (initialCfg program (Incidence.inputStream I))
      (some afterLoad) (symbols.length + 1) := by
    simpa [symbols, afterLoad, Incidence.inputStream, pairEncoding,
      initialCfg, cfg, program, List.append_assoc] using loaded
  have separator : EvalsToInTime (step program) afterLoad
      (some (cfg .nextQuery (some none) none false
        ((encodeVertexCoverInstance I).map some) []
        (symbols.map some).reverse [] [] [] [])) 1 :=
    ⟨⟨1, by simp [flip, afterLoad, step, program, cfg, stepOp]⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step program)
    (symbols.length + 1) 1 _ afterLoad _ loaded' separator
  convert full using 1
  all_goals
    simp [loadSteps, symbols, Nat.add_comm]
  omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Scanner
