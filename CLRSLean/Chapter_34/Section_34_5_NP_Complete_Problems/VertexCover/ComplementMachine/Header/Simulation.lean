import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.Header.Basic
import Mathlib.Tactic

/-!
# VERTEX-COVER complement header: phase simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Header

open PolyBuilder

def emitSteps (remaining original : Nat) : Nat :=
  2 * remaining + 2 * original + 6

def clearSteps (edges : List CliqueSym) (remaining original : Nat) : Nat :=
  edges.length + 1 + emitSteps remaining original

def targetSteps : Nat → Nat → Nat → List CliqueSym → Nat
  | remaining, original, 0, edges =>
      1 + clearSteps edges remaining original
  | remaining, original, target + 1, edges =>
      2 + targetSteps (remaining - 1) original target edges

def vertexSteps : Nat → Nat → Nat → Nat → List CliqueSym → Nat
  | remaining, original, 0, target, edges =>
      1 + targetSteps remaining original target edges
  | remaining, original, vertices + 1, target, edges =>
      3 + vertexSteps (remaining + 1) (original + 1) vertices target edges

def headerSteps (I : CliqueInstance) : Nat :=
  1 + vertexSteps 0 0 I.vertexCount I.targetSize
    (I.edges.flatMap encodeCliqueEdge)

private theorem replicate_append_same {α : Type} (symbol : α)
    (count : Nat) (tail : List α) :
    List.replicate count symbol ++ symbol :: tail =
      symbol :: List.replicate count symbol ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

private def emitOriginal_run (original : Nat) (output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .emitOriginal buffer test [] output []
        (List.replicate original ()))
      (some (haltCfg program
        (.instanceMark :: List.replicate original .tick ++ output)))
      (2 * original + 3) := by
  induction original generalizing output buffer test with
  | zero =>
      exact ⟨⟨3, by
        simp [flip, step, program, cfg, haltCfg, stepOp]⟩, le_rfl⟩
  | succ original ih =>
      let afterDec := cfg .pushOriginalTick buffer true [] output []
        (List.replicate original ())
      let afterPush := cfg .emitOriginal buffer true []
        (.tick :: output) [] (List.replicate original ())
      have first : EvalsToInTime (step program)
          (cfg .emitOriginal buffer test [] output []
            (List.replicate (original + 1) ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterPush) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterPush, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have rest := ih (.tick :: output) buffer true
      let through := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * original + 3) _ afterPush _ through rest
      simpa [List.replicate_succ, replicate_append_same, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def emitRemaining_run (remaining original : Nat)
    (output : List CliqueSym) (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .emitRemaining buffer test [] output
        (List.replicate remaining ()) (List.replicate original ()))
      (some (haltCfg program
        (.instanceMark :: List.replicate original .tick ++
          .fieldSep :: List.replicate remaining .tick ++ output)))
      (2 * remaining + 2 * original + 5) := by
  induction remaining generalizing output buffer test with
  | zero =>
      let afterDec := cfg .emitMiddleSeparator buffer false [] output []
        (List.replicate original ())
      let afterSep := cfg .emitOriginal buffer false []
        (.fieldSep :: output) [] (List.replicate original ())
      have first : EvalsToInTime (step program)
          (cfg .emitRemaining buffer test [] output []
            (List.replicate original ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterSep) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterSep, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have rest := emitOriginal_run original (.fieldSep :: output)
        buffer false
      let through := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * original + 3) _ afterSep _ through rest
      have hsteps : (2 * original + 3) + 2 = 2 * original + 5 := by
        omega
      simpa only [List.replicate_zero, List.nil_append, Nat.mul_zero,
        Nat.zero_add, List.append_assoc, List.singleton_append, hsteps]
        using full
  | succ remaining ih =>
      let afterDec := cfg .pushRemainingTick buffer true [] output
        (List.replicate remaining ()) (List.replicate original ())
      let afterPush := cfg .emitRemaining buffer true [] (.tick :: output)
        (List.replicate remaining ()) (List.replicate original ())
      have first : EvalsToInTime (step program)
          (cfg .emitRemaining buffer test [] output
            (List.replicate (remaining + 1) ())
            (List.replicate original ()))
          (some afterDec) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterDec
          (some afterPush) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterDec, afterPush, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have rest := ih (.tick :: output) buffer true
      let through := EvalsToInTime.trans (step program)
        1 1 _ afterDec _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 2 * original + 5) _ afterPush _ through rest
      simpa [List.replicate_succ, replicate_append_same, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def emit_run (remaining original : Nat)
    (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .emitRightSeparator buffer test [] []
        (List.replicate remaining ()) (List.replicate original ()))
      (some (haltCfg program
        (.instanceMark :: List.replicate original .tick ++
          .fieldSep :: List.replicate remaining .tick ++ [.fieldSep])))
      (emitSteps remaining original) := by
  let after := cfg .emitRemaining buffer test [] [.fieldSep]
    (List.replicate remaining ()) (List.replicate original ())
  have first : EvalsToInTime (step program)
      (cfg .emitRightSeparator buffer test [] []
        (List.replicate remaining ()) (List.replicate original ()))
      (some after) 1 := by
    exact ⟨⟨1, by
      simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
  have rest := emitRemaining_run remaining original [.fieldSep] buffer test
  let full := EvalsToInTime.trans (step program)
    1 (2 * remaining + 2 * original + 5) _ after _ first rest
  simpa [emitSteps, Nat.add_assoc] using full

private def clear_run (edges : List CliqueSym) (remaining original : Nat)
    (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .clearEdges buffer test edges []
        (List.replicate remaining ()) (List.replicate original ()))
      (some (haltCfg program
        (.instanceMark :: List.replicate original .tick ++
          .fieldSep :: List.replicate remaining .tick ++ [.fieldSep])))
      (clearSteps edges remaining original) := by
  induction edges generalizing buffer test with
  | nil =>
      let after := cfg .emitRightSeparator none test [] []
        (List.replicate remaining ()) (List.replicate original ())
      have first : EvalsToInTime (step program)
          (cfg .clearEdges buffer test [] []
            (List.replicate remaining ()) (List.replicate original ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := emit_run remaining original none test
      let full := EvalsToInTime.trans (step program)
        1 (emitSteps remaining original) _ after _ first rest
      simpa [clearSteps, Nat.add_comm] using full
  | cons symbol edges ih =>
      let after := cfg .clearEdges (some symbol) test edges []
        (List.replicate remaining ()) (List.replicate original ())
      have first : EvalsToInTime (step program)
          (cfg .clearEdges buffer test (symbol :: edges) []
            (List.replicate remaining ()) (List.replicate original ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (some symbol) test
      let full := EvalsToInTime.trans (step program)
        1 (clearSteps edges remaining original) _ after _ first rest
      have hsteps : clearSteps edges remaining original + 1 =
          clearSteps (symbol :: edges) remaining original := by
        simp [clearSteps]
        omega
      rw [← hsteps]
      exact full

private def targets_run (remaining original target : Nat)
    (edges : List CliqueSym) (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .targets buffer test
        (List.replicate target .tick ++ .fieldSep :: edges) []
        (List.replicate remaining ()) (List.replicate original ()))
      (some (haltCfg program
        (.instanceMark :: List.replicate original .tick ++
          .fieldSep :: List.replicate (remaining - target) .tick ++
            [.fieldSep])))
      (targetSteps remaining original target edges) := by
  induction target generalizing remaining buffer test with
  | zero =>
      let after := cfg .clearEdges (some .fieldSep) test edges []
        (List.replicate remaining ()) (List.replicate original ())
      have first : EvalsToInTime (step program)
          (cfg .targets buffer test (.fieldSep :: edges) []
            (List.replicate remaining ()) (List.replicate original ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := clear_run edges remaining original (some .fieldSep) test
      let full := EvalsToInTime.trans (step program)
        1 (clearSteps edges remaining original) _ after _ first rest
      simpa [targetSteps, Nat.add_comm] using full
  | succ target ih =>
      let afterPop := cfg .decrementRemaining (some .tick) test
        (List.replicate target .tick ++ .fieldSep :: edges) []
        (List.replicate remaining ()) (List.replicate original ())
      let afterDec := cfg .targets (some .tick) (remaining != 0)
        (List.replicate target .tick ++ .fieldSep :: edges) []
        (List.replicate (remaining - 1) ()) (List.replicate original ())
      have first : EvalsToInTime (step program)
          (cfg .targets buffer test
            (List.replicate (target + 1) .tick ++ .fieldSep :: edges) []
            (List.replicate remaining ()) (List.replicate original ()))
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterDec) 1 := by
        cases remaining <;>
          exact ⟨⟨1, by
            simp [flip, afterPop, afterDec, step, program, cfg, stepOp,
              List.replicate_succ]⟩, le_rfl⟩
      have rest := ih (remaining - 1) (some .tick) (remaining != 0)
      let through := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (targetSteps (remaining - 1) original target edges)
          _ afterDec _ through rest
      simpa [targetSteps, Nat.sub_sub, Nat.add_comm, Nat.add_assoc] using full

private def vertices_run (remaining original vertices target : Nat)
    (edges : List CliqueSym) (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .vertices buffer test
        (List.replicate vertices .tick ++ .fieldSep ::
          List.replicate target .tick ++ .fieldSep :: edges) []
        (List.replicate remaining ()) (List.replicate original ()))
      (some (haltCfg program
        (.instanceMark :: List.replicate (original + vertices) .tick ++
          .fieldSep ::
            List.replicate ((remaining + vertices) - target) .tick ++
              [.fieldSep])))
      (vertexSteps remaining original vertices target edges) := by
  induction vertices generalizing remaining original buffer test with
  | zero =>
      let after := cfg .targets (some .fieldSep) test
        (List.replicate target .tick ++ .fieldSep :: edges) []
        (List.replicate remaining ()) (List.replicate original ())
      have first : EvalsToInTime (step program)
          (cfg .vertices buffer test
            (.fieldSep :: List.replicate target .tick ++
              .fieldSep :: edges) []
            (List.replicate remaining ()) (List.replicate original ()))
          (some after) 1 := by
        exact ⟨⟨1, by
          simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := targets_run remaining original target edges
        (some .fieldSep) test
      let full := EvalsToInTime.trans (step program)
        1 (targetSteps remaining original target edges) _ after _ first rest
      simpa [vertexSteps, Nat.add_comm] using full
  | succ vertices ih =>
      let tail := List.replicate vertices .tick ++ .fieldSep ::
        List.replicate target .tick ++ .fieldSep :: edges
      let afterPop := cfg .incrementRemaining (some .tick) test tail []
        (List.replicate remaining ()) (List.replicate original ())
      let afterFirst := cfg .incrementOriginal (some .tick) test tail []
        (List.replicate (remaining + 1) ()) (List.replicate original ())
      let afterSecond := cfg .vertices (some .tick) test tail []
        (List.replicate (remaining + 1) ())
        (List.replicate (original + 1) ())
      have first : EvalsToInTime (step program)
          (cfg .vertices buffer test
            (List.replicate (vertices + 1) .tick ++ .fieldSep ::
              List.replicate target .tick ++ .fieldSep :: edges) []
            (List.replicate remaining ()) (List.replicate original ()))
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, tail, afterPop, step, program, cfg, stepOp,
            List.replicate_succ]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterFirst) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, afterFirst, step, program, cfg, stepOp,
            List.replicate_succ]⟩,
          le_rfl⟩
      have third : EvalsToInTime (step program) afterFirst
          (some afterSecond) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterFirst, afterSecond, step, program, cfg, stepOp,
            List.replicate_succ]⟩,
          le_rfl⟩
      have rest := ih (remaining + 1) (original + 1) (some .tick) test
      let throughFirst := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let through := EvalsToInTime.trans (step program)
        2 1 _ afterFirst _ throughFirst third
      let full := EvalsToInTime.trans (step program)
        3 (vertexSteps (remaining + 1) (original + 1) vertices target edges)
          _ afterSecond _ through rest
      simpa [tail, vertexSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

private theorem replicate_eq_prepend (count : Nat)
    (suffix : List CliqueSym) :
    List.replicate count CliqueSym.tick ++ suffix =
      prependCliqueTicks count suffix := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, prependCliqueTicks, ih]

/-- Exact successful run of the fixed controller on every canonical graph
encoding. -/
def run (I : CliqueInstance) :
    EvalsToInTime (step program)
      (initialCfg program (encodeCliqueInstance I))
      (some (haltCfg program (complementHeader I)))
      (headerSteps I) := by
  let edges := I.edges.flatMap encodeCliqueEdge
  let tail := prependCliqueTicks I.vertexCount
    (.fieldSep :: prependCliqueTicks I.targetSize (.fieldSep :: edges))
  let after := cfg .vertices (some .instanceMark) false tail [] [] []
  have first : EvalsToInTime (step program)
      (initialCfg program (encodeCliqueInstance I)) (some after) 1 := by
    exact ⟨⟨1, by
      simp [flip, after, tail, edges, step, program, cfg, initialCfg,
        encodeCliqueInstance, stepOp]⟩, le_rfl⟩
  have rest := vertices_run 0 0 I.vertexCount I.targetSize edges
    (some .instanceMark) false
  have htail : tail =
      List.replicate I.vertexCount .tick ++ .fieldSep ::
        List.replicate I.targetSize .tick ++ .fieldSep :: edges := by
    simp only [tail]
    rw [← replicate_eq_prepend I.vertexCount]
    rw [← replicate_eq_prepend I.targetSize]
    simp only [List.append_assoc, List.cons_append]
  have rest' : EvalsToInTime (step program) after
      (some (haltCfg program
        (.instanceMark :: List.replicate I.vertexCount .tick ++
          .fieldSep ::
            List.replicate (I.vertexCount - I.targetSize) .tick ++
              [.fieldSep])))
      (vertexSteps 0 0 I.vertexCount I.targetSize edges) := by
    simpa [after, htail] using rest
  let full := EvalsToInTime.trans (step program)
    1 (vertexSteps 0 0 I.vertexCount I.targetSize edges)
      _ after _ first rest'
  have hout : complementHeader I =
      .instanceMark :: List.replicate I.vertexCount .tick ++
        .fieldSep ::
          List.replicate (I.vertexCount - I.targetSize) .tick ++
            [.fieldSep] := by
    unfold complementHeader
    rw [← replicate_eq_prepend I.vertexCount]
    rw [← replicate_eq_prepend (I.vertexCount - I.targetSize)]
    simp only [List.append_assoc, List.cons_append]
  rw [hout]
  change EvalsToInTime (step program)
    (initialCfg program (encodeCliqueInstance I)) _
    (1 + vertexSteps 0 0 I.vertexCount I.targetSize edges)
  have hsteps : vertexSteps 0 0 I.vertexCount I.targetSize edges + 1 =
      1 + vertexSteps 0 0 I.vertexCount I.targetSize edges := by
    omega
  rw [← hsteps]
  exact full

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Header
