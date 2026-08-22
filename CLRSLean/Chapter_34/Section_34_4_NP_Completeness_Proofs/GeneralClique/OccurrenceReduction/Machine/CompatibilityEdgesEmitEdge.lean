import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesEmitRow
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: emit one edge

The compatible branch copies both endpoint counters into one canonical edge
record while restoring the counters exactly for the surrounding row loop.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private theorem replicate_tick_append_tick (count : Nat)
    (tail : List CliqueSym) :
    List.replicate count .tick ++ .tick :: tail =
      List.replicate (count + 1) .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, ih]

private theorem prependCliqueTicks_eq (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

private inductive CompatibilityEdgeCounter
  | upper | lower
  deriving DecidableEq

private def compatibilityEdgeCopyLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .copyUpper
  | .lower => .copyLower

private def compatibilityEdgeSaveLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .saveUpper
  | .lower => .saveLower

private def compatibilityEdgePushTickLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .pushUpperTick
  | .lower => .pushLowerTick

private def compatibilityEdgeRestoreLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .restoreUpper
  | .lower => .restoreLower

private def compatibilityEdgeRestoreIncLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .restoreUpperInc
  | .lower => .restoreLowerInc

private def compatibilityEdgeAfterRestoreLabel :
    CompatibilityEdgeCounter → CompatibilityEdgesLabel
  | .upper => .pushPairSeparator
  | .lower => .pushEdgeMark

private def compatibilityEdgeCounterCfg
    (counter : CompatibilityEdgeCounter) (label : CompatibilityEdgesLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (work₁ work₂ : List UnaryFrameSym)
    (primary other saved : Nat) : BuilderCfg compatibilityEdgesProgram :=
  match counter with
  | .upper => compatibilityEdgesCfg label buffer₁ buffer₂ test input output
      work₁ work₂ primary other saved
  | .lower => compatibilityEdgesCfg label buffer₁ buffer₂ test input output
      work₁ work₂ other primary saved

private def compatibilityEdges_copyCounterRun
    (counter : CompatibilityEdgeCounter) (remaining saved : Nat)
    (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (other : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter (compatibilityEdgeCopyLabel counter)
        buffer₁ buffer₂ test input output work₁ work₂
        remaining other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ false
        input (List.replicate remaining .tick ++ output) work₁ work₂
        0 other (saved + remaining))) (3 * remaining + 1) := by
  induction remaining generalizing saved test output with
  | zero =>
      cases counter <;>
        exact ⟨⟨1, by
          simp [flip, compatibilityEdgeCounterCfg, compatibilityEdgeCopyLabel,
            compatibilityEdgeRestoreLabel, step, compatibilityEdgesProgram,
            compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterTick := compatibilityEdgeCounterCfg counter
        (compatibilityEdgeCopyLabel counter) buffer₁ buffer₂ true input
        (.tick :: output) work₁ work₂ remaining other (saved + 1)
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgeCounterCfg counter
            (compatibilityEdgeCopyLabel counter) buffer₁ buffer₂ test input
            output work₁ work₂ (remaining + 1) other saved)
          (some afterTick) 3 := by
        cases counter <;>
          exact ⟨⟨3, by
            simp [Function.iterate_succ_apply, flip, afterTick,
              compatibilityEdgeCounterCfg, compatibilityEdgeCopyLabel,
              List.replicate_succ, step,
              compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
            le_rfl⟩
      have rest := ih (saved := saved + 1) (test := true)
        (output := .tick :: output)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        3 (3 * remaining + 1) _ afterTick _ first rest
      convert full using 1 <;> try omega
      simp only [replicate_tick_append_tick, Nat.add_comm,
        Nat.add_left_comm]

private def compatibilityEdges_restoreCounterRun
    (counter : CompatibilityEdgeCounter) (saved restored : Nat)
    (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (other : Nat) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ test input
        output work₁ work₂ restored other saved)
      (some (compatibilityEdgeCounterCfg counter
        (compatibilityEdgeAfterRestoreLabel counter) buffer₁ buffer₂ false
        input output work₁ work₂ (restored + saved) other 0))
      (2 * saved + 1) := by
  induction saved generalizing restored test with
  | zero =>
      cases counter <;>
        exact ⟨⟨1, by
          simp [flip, compatibilityEdgeCounterCfg,
            compatibilityEdgeRestoreLabel, compatibilityEdgeAfterRestoreLabel,
            step, compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]⟩,
          le_rfl⟩
  | succ saved ih =>
      let afterIncrement := compatibilityEdgeCounterCfg counter
        (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ true input
        output work₁ work₂ (restored + 1) other saved
      have first : EvalsToInTime (step compatibilityEdgesProgram)
          (compatibilityEdgeCounterCfg counter
            (compatibilityEdgeRestoreLabel counter) buffer₁ buffer₂ test input
            output work₁ work₂ restored other (saved + 1))
          (some afterIncrement) 2 := by
        cases counter <;>
          exact ⟨⟨2, by
            simp [Function.iterate_succ_apply, flip, afterIncrement,
              compatibilityEdgeCounterCfg, compatibilityEdgeRestoreLabel,
              List.replicate_succ, step, compatibilityEdgesProgram,
              compatibilityEdgesCfg, stepOp]⟩, le_rfl⟩
      have rest := ih (restored := restored + 1) (test := true)
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        2 (2 * saved + 1) _ afterIncrement _ first rest
      convert full using 1 <;> try omega
      simp only [Nat.add_comm, Nat.add_left_comm]

/-- Exact budget for writing one compatible normalized edge. -/
def compatibilityEdgesEmitCompatibleEdgeSteps (upper lower : Nat) : Nat :=
  5 * upper + 5 * lower + 7

/-- The compatible branch writes exactly the canonical normalized edge record
and restores both endpoint counters before entering lower cleanup. -/
def compatibilityEdges_emitCompatibleEdgeRun
    (upper lower : Nat) (input work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) :
    EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .pushEdgeEnd buffer₁ buffer₂ test input output
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .clearLower buffer₁ buffer₂ false input
        (encodeCliqueEdge (lower, upper) ++ output) work₁ work₂
        upper lower 0))
      (compatibilityEdgesEmitCompatibleEdgeSteps upper lower) := by
  have endRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .pushEdgeEnd buffer₁ buffer₂ test input output
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .copyUpper buffer₁ buffer₂ test input
        (.recordEnd :: output) work₁ work₂ upper lower 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  have upperCopy := compatibilityEdges_copyCounterRun .upper upper 0 input
    work₁ work₂ (.recordEnd :: output) buffer₁ buffer₂ test lower
  have upperRestore := compatibilityEdges_restoreCounterRun .upper upper 0 input
    work₁ work₂
    (List.replicate upper .tick ++ .recordEnd :: output)
    buffer₁ buffer₂ false lower
  have pairRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .pushPairSeparator buffer₁ buffer₂ false input
        (List.replicate upper .tick ++ .recordEnd :: output)
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .copyLower buffer₁ buffer₂ false input
        (.pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
        work₁ work₂ upper lower 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  have lowerCopy := compatibilityEdges_copyCounterRun .lower lower 0 input
    work₁ work₂
    (.pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
    buffer₁ buffer₂ false upper
  have lowerRestore := compatibilityEdges_restoreCounterRun .lower lower 0 input
    work₁ work₂
    (List.replicate lower .tick ++
      .pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
    buffer₁ buffer₂ false upper
  have markRun : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .pushEdgeMark buffer₁ buffer₂ false input
        (List.replicate lower .tick ++
          .pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
        work₁ work₂ upper lower 0)
      (some (compatibilityEdgesCfg .clearLower buffer₁ buffer₂ false input
        (.edgeMark :: List.replicate lower .tick ++
          .pairSep :: List.replicate upper .tick ++ .recordEnd :: output)
        work₁ work₂ upper lower 0)) 1 := by
    exact ⟨⟨1, by
      simp [flip, step, compatibilityEdgesProgram, compatibilityEdgesCfg,
        stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step compatibilityEdgesProgram)
    1 (3 * upper + 1) _ _ _ endRun (by
      simpa [compatibilityEdgeCounterCfg, compatibilityEdgeCopyLabel,
        compatibilityEdgeRestoreLabel] using upperCopy)
  let second := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * upper + 1) _ _ _ first (by
      simpa [compatibilityEdgeCounterCfg, compatibilityEdgeRestoreLabel,
        compatibilityEdgeAfterRestoreLabel] using upperRestore)
  let third := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ second pairRun
  let fourth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (3 * lower + 1) _ _ _ third (by
      simpa [compatibilityEdgeCounterCfg, compatibilityEdgeCopyLabel,
        compatibilityEdgeRestoreLabel, List.append_assoc] using lowerCopy)
  let fifth := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ (2 * lower + 1) _ _ _ fourth (by
      simpa [compatibilityEdgeCounterCfg, compatibilityEdgeRestoreLabel,
        compatibilityEdgeAfterRestoreLabel, List.append_assoc] using lowerRestore)
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    _ 1 _ _ _ fifth (by simpa [List.append_assoc] using markRun)
  convert full using 1 <;>
    simp [encodeCliqueEdge, prependCliqueTicks_eq,
      compatibilityEdgesEmitCompatibleEdgeSteps, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  all_goals try omega

end TMClique
end Turing
end Chapter34
end CLRS
