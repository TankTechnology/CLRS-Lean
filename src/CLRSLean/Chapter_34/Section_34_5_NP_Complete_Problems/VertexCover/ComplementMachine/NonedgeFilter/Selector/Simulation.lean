import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Selector.Basic
import Mathlib.Tactic

/-!
# VERTEX-COVER complement machine: selector phases
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter.Selector

open PolyBuilder
open NonedgeFilter

private def loadSymbols_run (symbols : List CliqueSym)
    (rest : List (Option CliqueSym)) (output : List CliqueSym)
    (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .load buffer₁ buffer₂ test
        (symbols.map some ++ none :: rest) output work₁ work₂)
      (some (cfg .dropSeparator (some none) buffer₂ test rest output
        (none :: (symbols.map some).reverse ++ work₁) work₂))
      (symbols.length + 1) := by
  induction symbols generalizing work₁ buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol symbols ih =>
      let after := cfg .load (some (some symbol)) buffer₂ test
        (symbols.map some ++ none :: rest) output
        (some symbol :: work₁) work₂
      have first : EvalsToInTime (step program)
          (cfg .load buffer₁ buffer₂ test
            ((symbol :: symbols).map some ++ none :: rest) output
            work₁ work₂)
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have remaining := ih (work₁ := some symbol :: work₁)
        (buffer₁ := some (some symbol))
      let full := EvalsToInTime.trans (step program)
        1 (symbols.length + 1) _ after _ first remaining
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Load the reversed candidate half and remove its pair separator. -/
def load_run (edges : List (Nat × Nat)) (bits : List Bool) :
    EvalsToInTime (step program)
      (initialCfg program (inputEncoding (edges, bits)))
      (some (cfg .nextBit (some none) none false
        ((bits.map bitSymbol).map some) []
        ((edges.flatMap encodeCliqueEdge).map some) []))
      ((edges.flatMap encodeCliqueEdge).length + 2) := by
  let symbols := (edges.flatMap encodeCliqueEdge).reverse
  let rest := (bits.map bitSymbol).map some
  have loaded := loadSymbols_run symbols rest [] [] [] none none false
  let afterLoad := cfg .dropSeparator (some none) none false rest []
    (none :: (symbols.map some).reverse) []
  have loaded' : EvalsToInTime (step program)
      (initialCfg program (inputEncoding (edges, bits)))
      (some afterLoad) (symbols.length + 1) := by
    simpa [symbols, rest, afterLoad, inputEncoding, pairEncoding, initialCfg,
      cfg, program, List.append_assoc] using loaded
  have separator : EvalsToInTime (step program) afterLoad
      (some (cfg .nextBit (some none) none false rest []
        ((symbols.map some).reverse) [])) 1 :=
    ⟨⟨1, by simp [flip, afterLoad, step, program, cfg, stepOp]⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step program)
    (symbols.length + 1) 1 _ afterLoad _ loaded' separator
  convert full using 1
  all_goals
    simp [symbols, rest, List.map_reverse, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  omega

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

def edgePrefix (edge : Nat × Nat) : List CliqueSym :=
  .edgeMark :: List.replicate edge.1 .tick ++
    .pairSep :: List.replicate edge.2 .tick

theorem encodeCliqueEdge_eq_prefix (edge : Nat × Nat) :
    encodeCliqueEdge edge = edgePrefix edge ++ [CliqueSym.recordEnd] := by
  simp [encodeCliqueEdge, edgePrefix, prependCliqueTicks_eq_replicate,
    List.append_assoc]

theorem recordEnd_not_mem_edgePrefix (edge : Nat × Nat) :
    CliqueSym.recordEnd ∉ edgePrefix edge := by
  simp [edgePrefix]

private def discardPrefix_run (body : List CliqueSym)
    (hrecord : CliqueSym.recordEnd ∉ body)
    (input : List (Option CliqueSym)) (output : List CliqueSym)
    (tail work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .discard buffer₁ buffer₂ test input output
        ((body ++ [CliqueSym.recordEnd]).map some ++ tail) work₂)
      (some (cfg .nextBit (some (some CliqueSym.recordEnd)) buffer₂ test
        input output tail work₂))
      (body.length + 1) := by
  induction body generalizing buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol body ih =>
      have hsymbol : symbol ≠ CliqueSym.recordEnd := by
        intro h
        apply hrecord
        simp [h]
      have htail : CliqueSym.recordEnd ∉ body := by
        intro h
        exact hrecord (by simp [h])
      let after := cfg .discard (some (some symbol)) buffer₂ test input
        output ((body ++ [CliqueSym.recordEnd]).map some ++ tail) work₂
      have first : EvalsToInTime (step program)
          (cfg .discard buffer₁ buffer₂ test input output
            (((symbol :: body) ++ [CliqueSym.recordEnd]).map some ++ tail) work₂)
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩,
          le_rfl⟩
      have remaining := ih htail (buffer₁ := some (some symbol))
      let full := EvalsToInTime.trans (step program)
        1 (body.length + 1) _ after _ first remaining
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def copyPrefix_run (body : List CliqueSym)
    (hrecord : CliqueSym.recordEnd ∉ body)
    (input : List (Option CliqueSym)) (output : List CliqueSym)
    (tail work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .copy buffer₁ buffer₂ test input output
        ((body ++ [CliqueSym.recordEnd]).map some ++ tail) work₂)
      (some (cfg .nextBit (some (some CliqueSym.recordEnd)) buffer₂ test input
        ((body ++ [CliqueSym.recordEnd]).reverse ++ output) tail work₂))
      (2 * (body.length + 1)) := by
  induction body generalizing output buffer₁ with
  | nil =>
      exact ⟨⟨2, by
        simp [Function.iterate_succ_apply, flip, step, program, cfg,
          stepOp]⟩, le_rfl⟩
  | cons symbol body ih =>
      have hsymbol : symbol ≠ CliqueSym.recordEnd := by
        intro h
        apply hrecord
        simp [h]
      have htail : CliqueSym.recordEnd ∉ body := by
        intro h
        exact hrecord (by simp [h])
      let afterPop := cfg (.copyPush symbol) (some (some symbol)) buffer₂
        test input output ((body ++ [CliqueSym.recordEnd]).map some ++ tail) work₂
      let afterPush := cfg .copy (some (some symbol)) buffer₂ test input
        (symbol :: output) ((body ++ [CliqueSym.recordEnd]).map some ++ tail) work₂
      have pop : EvalsToInTime (step program)
          (cfg .copy buffer₁ buffer₂ test input output
            (((symbol :: body) ++ [CliqueSym.recordEnd]).map some ++ tail) work₂)
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have push : EvalsToInTime (step program) afterPop
          (some afterPush) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterPush, step, program, cfg,
          stepOp, hsymbol]⟩, le_rfl⟩
      have remaining := ih htail (output := symbol :: output)
        (buffer₁ := some (some symbol))
      let firstTwo := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ pop push
      let full := EvalsToInTime.trans (step program)
        2 (2 * (body.length + 1)) _ afterPush _ firstTwo remaining
      convert full using 1
      all_goals
        simp [List.reverse_cons, List.append_assoc, Nat.add_comm,
          Nat.add_left_comm]
      omega

def selectSteps (bit : Bool) (edge : Nat × Nat) : Nat :=
  1 + if bit then (encodeCliqueEdge edge).length
      else 2 * (encodeCliqueEdge edge).length

/-- One answer bit consumes exactly one candidate edge record. -/
def select_run (bit : Bool) (edge : Nat × Nat)
    (input : List (Option CliqueSym)) (output : List CliqueSym)
    (tail work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.select bit) buffer₁ buffer₂ test input output
        ((encodeCliqueEdge edge).map some ++ tail) work₂)
      (some (cfg .nextBit (some (some CliqueSym.recordEnd)) buffer₂ test input
        (if bit then output else (encodeCliqueEdge edge).reverse ++ output)
        tail work₂))
      (selectSteps bit edge) := by
  have hprefix := recordEnd_not_mem_edgePrefix edge
  cases bit with
  | false =>
      have copied := copyPrefix_run (edgePrefix edge) hprefix input output
        tail work₂ buffer₁ buffer₂ test
      rw [← encodeCliqueEdge_eq_prefix edge] at copied
      let first : EvalsToInTime (step program)
          (cfg (.select false) buffer₁ buffer₂ test input output
            ((encodeCliqueEdge edge).map some ++ tail) work₂)
          (some (cfg .copy buffer₁ buffer₂ test input output
            ((encodeCliqueEdge edge).map some ++ tail) work₂)) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step program)
        1 (2 * (edgePrefix edge).length.succ) _ _ _ first copied
      simpa [selectSteps, encodeCliqueEdge_eq_prefix, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full
  | true =>
      have discarded := discardPrefix_run (edgePrefix edge) hprefix input
        output tail work₂ buffer₁ buffer₂ test
      rw [← encodeCliqueEdge_eq_prefix edge] at discarded
      let first : EvalsToInTime (step program)
          (cfg (.select true) buffer₁ buffer₂ test input output
            ((encodeCliqueEdge edge).map some ++ tail) work₂)
          (some (cfg .discard buffer₁ buffer₂ test input output
            ((encodeCliqueEdge edge).map some ++ tail) work₂)) 1 :=
        ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step program)
        1 (edgePrefix edge).length.succ _ _ _ first discarded
      simpa [selectSteps, encodeCliqueEdge_eq_prefix, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter.Selector
