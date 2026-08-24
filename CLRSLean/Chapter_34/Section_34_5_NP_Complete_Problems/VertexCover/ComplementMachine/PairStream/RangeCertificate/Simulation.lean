import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.RangeCertificate.Basic
import Mathlib.Tactic

/-!
# Range-certificate controller: local simulations
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream.RangeCertificate

open PolyBuilder

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

/-- Consume the current index, save it in counter three, and prepend its unary
ticks to the output. -/
private theorem copyIndex_eval (index : Nat)
    (buffer : Option CliqueSym) (test : Bool) (input output : List CliqueSym)
    (remaining saved : List Unit) :
    (flip Option.bind (step program))^[3 * index + 1]
      (some (cfg .copyIndex buffer test input output remaining
        (List.replicate index ()) saved)) =
      some (cfg .pushRecordEnd buffer false input
        (List.replicate index .tick ++ output) remaining []
        (List.replicate index () ++ saved)) := by
  induction index generalizing output saved test with
  | zero => rfl
  | succ index ih =>
      rw [show 3 * (index + 1) + 1 = (3 * index + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step program))^[3 * index + 1]
          (some (cfg .copyIndex buffer true input (.tick :: output) remaining
            (List.replicate index ()) (() :: saved))) = _
      simpa only [List.replicate_succ, List.cons_append,
        List.append_assoc, replicate_append_cons] using
        ih (output := .tick :: output) (saved := () :: saved) (test := true)

/-- Restore a saved current index from counter three to counter two. -/
private theorem restoreIndex_eval (index : Nat)
    (buffer : Option CliqueSym) (test : Bool) (input output : List CliqueSym)
    (remaining restored : List Unit) :
    (flip Option.bind (step program))^[2 * index + 1]
      (some (cfg .restoreIndex buffer test input output remaining restored
        (List.replicate index ()))) =
      some (cfg .advance buffer false input output remaining
        (List.replicate index () ++ restored) []) := by
  induction index generalizing restored test with
  | zero => rfl
  | succ index ih =>
      rw [show 2 * (index + 1) + 1 = (2 * index + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step program))^[2 * index + 1]
          (some (cfg .restoreIndex buffer true input output remaining
            (() :: restored) (List.replicate index ()))) = _
      simpa only [List.replicate_succ, List.cons_append,
        List.append_assoc, replicate_append_cons] using
        ih (restored := () :: restored) (test := true)

/-- Serialize one current range vertex and advance the index counter. -/
def onePhase (index : Nat) (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) (remaining : List Unit) :
    EvalsToInTime (step program)
      (cfg .next buffer test input output (() :: remaining)
        (List.replicate index ()) [])
      (some (cfg .next buffer false input
        ((encodeCliqueVertex index).reverse ++ output) remaining
        (List.replicate (index + 1) ()) []))
      (5 * index + 6) := by
  let afterDec := cfg .pushVertex buffer true input output remaining
    (List.replicate index ()) []
  let afterVertex := cfg .copyIndex buffer true input
    (.vertexMark :: output) remaining (List.replicate index ()) []
  let afterCopy := cfg .pushRecordEnd buffer false input
    (List.replicate index .tick ++ .vertexMark :: output) remaining []
    (List.replicate index ())
  let afterEnd := cfg .restoreIndex buffer false input
    (.recordEnd :: (List.replicate index .tick ++ .vertexMark :: output))
    remaining [] (List.replicate index ())
  let afterRestore := cfg .advance buffer false input
    (.recordEnd :: (List.replicate index .tick ++ .vertexMark :: output))
    remaining (List.replicate index ()) []
  have hdec : EvalsToInTime (step program)
      (cfg .next buffer test input output (() :: remaining)
        (List.replicate index ()) []) (some afterDec) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hvertex : EvalsToInTime (step program) afterDec
      (some afterVertex) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hcopy : EvalsToInTime (step program) afterVertex
      (some afterCopy) (3 * index + 1) := by
    exact ⟨⟨3 * index + 1, by
      simpa [afterVertex, afterCopy] using
        copyIndex_eval index buffer true input (.vertexMark :: output)
          remaining []⟩, le_rfl⟩
  have hend : EvalsToInTime (step program) afterCopy
      (some afterEnd) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step program) afterEnd
      (some afterRestore) (2 * index + 1) := by
    exact ⟨⟨2 * index + 1, by
      simpa [afterEnd, afterRestore] using
        restoreIndex_eval index buffer false input
          (.recordEnd :: (List.replicate index .tick ++
            .vertexMark :: output)) remaining []⟩, le_rfl⟩
  have hadvance : EvalsToInTime (step program) afterRestore
      (some (cfg .next buffer false input
        (.recordEnd :: (List.replicate index .tick ++ .vertexMark :: output))
        remaining (List.replicate (index + 1) ()) [])) 1 := by
    exact ⟨⟨1, by simp [afterRestore, List.replicate_succ, flip,
      step, program, cfg, stepOp]⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step program) 1 1 _ afterDec _ hdec hvertex
  let second := EvalsToInTime.trans (step program) 2 (3 * index + 1)
    _ afterVertex _ first hcopy
  let third := EvalsToInTime.trans (step program) _ 1 _ afterCopy _ second hend
  let fourth := EvalsToInTime.trans (step program) _ (2 * index + 1)
    _ afterEnd _ third hrestore
  let full := EvalsToInTime.trans (step program) _ 1 _ afterRestore _ fourth
    hadvance
  convert full using 1
  · simp [encodeCliqueVertex, prependCliqueTicks_eq_replicate,
      List.reverse_append, List.append_assoc]
  · omega

/-- Exact recursive cost of a range-row family. -/
def phaseSteps : Nat → Nat → Nat
  | _, 0 => 0
  | start, count + 1 =>
      (5 * start + 6) + phaseSteps (start + 1) count

/-- Serialize every row in one consecutive range. -/
def phases (start count : Nat) (buffer : Option CliqueSym)
    (input output : List CliqueSym) :
    EvalsToInTime (step program)
      (cfg .next buffer false input output (List.replicate count ())
        (List.replicate start ()) [])
      (some (cfg .next buffer false input
        ((rangeRowsFrom start count).reverse ++ output) []
        (List.replicate (start + count) ()) []))
      (phaseSteps start count) := by
  induction count generalizing start output with
  | zero =>
      exact ⟨⟨0, by simp [rangeRowsFrom, cfg]⟩, le_rfl⟩
  | succ count ih =>
      have first := onePhase start buffer false input output
        (List.replicate count ())
      have rest := ih (start + 1)
        ((encodeCliqueVertex start).reverse ++ output)
      let full := EvalsToInTime.trans (step program)
        (5 * start + 6) (phaseSteps (start + 1) count)
        _ _ _ first rest
      simpa [phaseSteps, rangeRowsFrom, List.range'_succ,
        List.replicate_succ,
        List.reverse_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Load the unary vertex-count header into counter one. -/
def scanVertexCount (count : Nat) (suffix output : List CliqueSym)
    (loaded : List Unit) (buffer : Option CliqueSym) :
    EvalsToInTime (step program)
      (cfg .scanVertexCount buffer false
        (prependCliqueTicks count (.fieldSep :: suffix)) output loaded [] [])
      (some (cfg .next (some .fieldSep) false suffix output
        (List.replicate count () ++ loaded) [] []))
      (2 * count + 1) := by
  induction count generalizing loaded buffer with
  | zero => exact ⟨⟨1, by
      simp [prependCliqueTicks, flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ count ih =>
      have first : EvalsToInTime (step program)
          (cfg .scanVertexCount buffer false
            (prependCliqueTicks (count + 1) (.fieldSep :: suffix))
            output loaded [] [])
          (some (cfg .scanVertexCount (some .tick) false
            (prependCliqueTicks count (.fieldSep :: suffix)) output
            (() :: loaded) [] [])) 2 :=
        ⟨⟨2, by
          simp [prependCliqueTicks, Function.iterate_succ_apply, flip,
            step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (() :: loaded) (some .tick)
      let full := EvalsToInTime.trans (step program)
        2 (2 * count + 1) _ _ _ first rest
      convert full using 1
      · simp [List.replicate_succ, replicate_append_cons]
      · omega

private def clearIndex (count : Nat) (suffix output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .clearIndex buffer test suffix output []
        (List.replicate count ()) [])
      (some (cfg .drain buffer false suffix output [] [] []))
      (count + 1) := by
  induction count generalizing buffer test with
  | zero => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | succ count ih =>
      have first : EvalsToInTime (step program)
          (cfg .clearIndex buffer test suffix output []
            (List.replicate (count + 1) ()) [])
          (some (cfg .clearIndex buffer true suffix output []
            (List.replicate count ()) [])) 1 :=
        ⟨⟨1, by simp [List.replicate_succ, flip, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih buffer true
      let full := EvalsToInTime.trans (step program) 1 (count + 1)
        _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def drain (suffix output : List CliqueSym)
    (buffer : Option CliqueSym) :
    EvalsToInTime (step program)
      (cfg .drain buffer false suffix output [] [] [])
      (some (cfg .halt none false [] output [] [] []))
      (suffix.length + 1) := by
  induction suffix generalizing buffer with
  | nil => exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩,
      le_rfl⟩
  | cons symbol suffix ih =>
      have first : EvalsToInTime (step program)
          (cfg .drain buffer false (symbol :: suffix) output [] [] [])
          (some (cfg .drain (some symbol) false suffix output [] [] [])) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (some symbol)
      let full := EvalsToInTime.trans (step program) 1 (suffix.length + 1)
        _ _ _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Empty remaining counter, index cleanup, suffix draining, and halt. -/
def finish (count : Nat) (suffix output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .next buffer test suffix output [] (List.replicate count ()) [])
      (some (haltCfg program output))
      (count + suffix.length + 4) := by
  have hnext : EvalsToInTime (step program)
      (cfg .next buffer test suffix output [] (List.replicate count ()) [])
      (some (cfg .clearIndex buffer false suffix output []
        (List.replicate count ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear := clearIndex count suffix output buffer false
  have hdrain := drain suffix output buffer
  have hhalt : EvalsToInTime (step program)
      (cfg .halt none false [] output [] [] [])
      (some (haltCfg program output)) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let first := EvalsToInTime.trans (step program) 1 (count + 1)
    _ _ _ hnext hclear
  let second := EvalsToInTime.trans (step program) _ (suffix.length + 1)
    _ _ _ first hdrain
  let full := EvalsToInTime.trans (step program) _ 1 _ _ _ second hhalt
  convert full using 1
  all_goals omega

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream.RangeCertificate
