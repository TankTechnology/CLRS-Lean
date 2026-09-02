import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.GuardSelector.Basic
import Mathlib.Tactic

/-!
# VERTEX-COVER guarded selector: exact simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GuardSelector

open PolyBuilder
open NonedgeFilter

def steps (input : Bool × List CliqueSym) : Nat :=
  if input.1 then 3 * input.2.length + 5 else input.2.length + 13

private def fallback_run (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .fallbackRecordEnd buffer test [] [] [])
      (some (haltCfg program
        (encodeCliqueInstance canonicalVertexCoverNoInstance))) 10 := by
  exact ⟨⟨10, by
    simp [flip, step, program, cfg, haltCfg, stepOp,
      canonicalVertexCoverNoInstance, encodeCliqueInstance,
      encodeCliqueEdge, prependCliqueTicks]⟩, le_rfl⟩

private def clear_run (candidate : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .clear buffer test (candidate.map some) [] [])
      (some (haltCfg program
        (encodeCliqueInstance canonicalVertexCoverNoInstance)))
      (candidate.length + 11) := by
  induction candidate generalizing buffer test with
  | nil =>
      let after := cfg .fallbackRecordEnd none test [] [] []
      have first : EvalsToInTime (step program)
          (cfg .clear buffer test [] [] []) (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := fallback_run none test
      let full := EvalsToInTime.trans (step program)
        1 10 _ after _ first rest
      simpa using full
  | cons symbol candidate ih =>
      let after := cfg .clear (some (some symbol)) test
        (candidate.map some) [] []
      have first : EvalsToInTime (step program)
          (cfg .clear buffer test ((symbol :: candidate).map some) [] [])
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (some (some symbol)) test
      let full := EvalsToInTime.trans (step program)
        1 (candidate.length + 11) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def copy_run (symbols : List CliqueSym) (output : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .copy buffer test [] output (symbols.map some))
      (some (haltCfg program (symbols.reverse ++ output)))
      (2 * symbols.length + 2) := by
  induction symbols generalizing output buffer test with
  | nil =>
      exact ⟨⟨2, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | cons symbol symbols ih =>
      let afterPop := cfg (.copyPush symbol) (some (some symbol)) test []
        output (symbols.map some)
      let afterPush := cfg .copy (some (some symbol)) test []
        (symbol :: output) (symbols.map some)
      have first : EvalsToInTime (step program)
          (cfg .copy buffer test [] output ((symbol :: symbols).map some))
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterPush) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, afterPush, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have rest := ih (symbol :: output) (some (some symbol)) test
      let through := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * symbols.length + 2) _ afterPush _ through rest
      simpa [List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def load_run (candidate : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool)
    (work : List (Option CliqueSym)) :
    EvalsToInTime (step program)
      (cfg .load buffer test (candidate.map some) [] work)
      (some (cfg .copy none test [] []
        ((candidate.map some).reverse ++ work)))
      (candidate.length + 1) := by
  induction candidate generalizing buffer work with
  | nil =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol candidate ih =>
      let after := cfg .load (some (some symbol)) test
        (candidate.map some) [] (some symbol :: work)
      have first : EvalsToInTime (step program)
          (cfg .load buffer test ((symbol :: candidate).map some) [] work)
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (some (some symbol)) (some symbol :: work)
      let full := EvalsToInTime.trans (step program)
        1 (candidate.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

private def accepted_run (candidate : List CliqueSym)
    (buffer : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .load buffer test (candidate.map some) [] [])
      (some (haltCfg program candidate)) (3 * candidate.length + 3) := by
  have loaded := load_run candidate buffer test []
  have copied := copy_run candidate.reverse [] none test
  have hwork : (candidate.map some).reverse =
      candidate.reverse.map some := by simp
  rw [hwork] at loaded
  have loaded' : EvalsToInTime (step program)
      (cfg .load buffer test (candidate.map some) [] [])
      (some (cfg .copy none test [] [] (candidate.reverse.map some)))
      (candidate.length + 1) := by
    simpa using loaded
  have copied' : EvalsToInTime (step program)
      (cfg .copy none test [] [] (candidate.reverse.map some))
      (some (haltCfg program candidate))
      (2 * candidate.reverse.length + 2) := by
    simpa using copied
  let full := EvalsToInTime.trans (step program)
    (candidate.length + 1) (2 * candidate.reverse.length + 2)
      _ _ _ loaded' copied'
  have hsteps : (2 * candidate.reverse.length + 2) +
      (candidate.length + 1) =
        3 * candidate.length + 3 := by
    simp
    omega
  rw [hsteps] at full
  exact full

/-- Exact successful run on every tagged candidate word. -/
def run (input : Bool × List CliqueSym) :
    EvalsToInTime (step program)
      (initialCfg program (inputEncoding input))
      (some (haltCfg program (selectedOutput input)))
      (steps input) := by
  rcases input with ⟨accept, candidate⟩
  cases accept with
  | false =>
      let afterStart := cfg (.dropSeparator false)
        (some (some .certificateMark)) false
        (none :: candidate.map some) [] []
      let afterSeparator := cfg .clear (some none) false
        (candidate.map some) [] []
      have first : EvalsToInTime (step program)
          (initialCfg program (inputEncoding (false, candidate)))
          (some afterStart) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterStart, inputEncoding, pairEncoding, bitSymbol,
            initialCfg, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterStart
          (some afterSeparator) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterStart, afterSeparator, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have rest := clear_run candidate (some none) false
      let through := EvalsToInTime.trans (step program)
        1 1 _ afterStart _ first second
      let full := EvalsToInTime.trans (step program)
        2 (candidate.length + 11) _ afterSeparator _ through rest
      simpa [steps, selectedOutput, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full
  | true =>
      let afterStart := cfg (.dropSeparator true)
        (some (some .instanceMark)) false
        (none :: candidate.map some) [] []
      let afterSeparator := cfg .load (some none) false
        (candidate.map some) [] []
      have first : EvalsToInTime (step program)
          (initialCfg program (inputEncoding (true, candidate)))
          (some afterStart) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterStart, inputEncoding, pairEncoding, bitSymbol,
            initialCfg, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterStart
          (some afterSeparator) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterStart, afterSeparator, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have rest := accepted_run candidate (some none) false
      let through := EvalsToInTime.trans (step program)
        1 1 _ afterStart _ first second
      let full := EvalsToInTime.trans (step program)
        2 (3 * candidate.length + 3) _ afterSeparator _ through rest
      have hsteps : 2 + (3 * candidate.length + 3) =
          3 * candidate.length + 5 := by omega
      simpa [steps, selectedOutput, hsteps] using full

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GuardSelector
