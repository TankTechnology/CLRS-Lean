import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Streaming unary indices

General-circuit encodings store every wire reference in unary.  This module
provides a concrete counter machine that turns a unit clock of length `n` into
the concatenated encodings of `0, ..., n - 1`.  The builder first produces the
reverse stream (the natural orientation of a prepend-only output stack), then
the verified reversal machine supplies the public forward stream.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Boolean presentation of the circuit wire format `encNat`: `true` is an
argument mark and `false` is the terminating mark. -/
def unaryIndexCode (index : Nat) : List Bool :=
  List.replicate index true ++ [false]

/-- Forward concatenation of unary indices `0, ..., count - 1`. -/
def unaryIndexStream (count : Nat) : List Bool :=
  (List.range count).flatMap unaryIndexCode

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

/-- The same stream starting at an arbitrary index, used by the phase proof. -/
private def unaryIndexStreamFrom : Nat → Nat → List Bool
  | _, 0 => []
  | start, count + 1 =>
      unaryIndexCode start ++ unaryIndexStreamFrom (start + 1) count

private theorem unaryIndexStreamFrom_zero (count : Nat) :
    unaryIndexStreamFrom 0 count = unaryIndexStream count := by
  have aux : ∀ start count,
      unaryIndexStreamFrom start count =
        (List.range' start count).flatMap unaryIndexCode := by
    intro start count
    induction count generalizing start with
    | zero => rfl
    | succ count ih =>
        change unaryIndexCode start ++
            unaryIndexStreamFrom (start + 1) count = _
        rw [ih]
        rfl
  rw [unaryIndexStream, List.range_eq_range']
  exact aux 0 count

/-- Finite control of the reversed unary-index streamer. -/
inductive UnaryIndexLabel
  | next
  | decIndex
  | saveIndex
  | pushArg
  | pushEnd
  | restore
  | restoreIndex
  | advance
  | clear
  | halt
deriving DecidableEq, Fintype

/-- Counter machine that emits `(unaryIndexStream input.length).reverse`. -/
def unaryIndexRevProgram : Program Unit Bool where
  Label := UnaryIndexLabel
  main := .next
  op
    | .next => .popInput .clear (fun _ => .decIndex)
    | .decIndex => .dec₁ .pushEnd .saveIndex
    | .saveIndex => .inc₂ .pushArg
    | .pushArg => .pushOutput true .decIndex
    | .pushEnd => .pushOutput false .restore
    | .restore => .dec₂ .advance .restoreIndex
    | .restoreIndex => .inc₁ .restore
    | .advance => .inc₁ .next
    | .clear => .dec₁ .halt .clear
    | .halt => .halt

private def unaryIndexCfg (label : UnaryIndexLabel)
    (buffer : Option Unit) (test : Bool) (input : List Unit)
    (output : List Bool) (counter₁ counter₂ : List Unit) :
    BuilderCfg unaryIndexRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := counter₁
  counter₂ := counter₂
  counter₃ := []

/-- Consume the current index counter, save it in counter two, and prepend its
argument marks. -/
private theorem unaryIndex_emitArgs_eval (index : Nat)
    (buffer : Option Unit) (test : Bool) (input : List Unit)
    (output : List Bool) (saved : List Unit) :
    (flip Option.bind (step unaryIndexRevProgram))^[3 * index + 1]
      (some (unaryIndexCfg .decIndex buffer test input output
        (List.replicate index ()) saved)) =
      some (unaryIndexCfg .pushEnd buffer false input
        (List.replicate index true ++ output) []
        (List.replicate index () ++ saved)) := by
  induction index generalizing test output saved with
  | zero => rfl
  | succ index ih =>
      rw [show 3 * (index + 1) + 1 = (3 * index + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryIndexRevProgram))^[3 * index + 1]
          (some (unaryIndexCfg .decIndex buffer true input (true :: output)
            (List.replicate index ()) (() :: saved))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using
        ih true (true :: output) (() :: saved)

/-- Restore a saved index from counter two to counter one. -/
private theorem unaryIndex_restore_eval (index : Nat)
    (buffer : Option Unit) (test : Bool) (input : List Unit)
    (output : List Bool) (restored : List Unit) :
    (flip Option.bind (step unaryIndexRevProgram))^[2 * index + 1]
      (some (unaryIndexCfg .restore buffer test input output restored
        (List.replicate index ()))) =
      some (unaryIndexCfg .advance buffer false input output
        (List.replicate index () ++ restored) []) := by
  induction index generalizing test restored with
  | zero => rfl
  | succ index ih =>
      rw [show 2 * (index + 1) + 1 = (2 * index + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryIndexRevProgram))^[2 * index + 1]
          (some (unaryIndexCfg .restore buffer true input output
            (() :: restored) (List.replicate index ()))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using
        ih true (() :: restored)

/-- Process one clock token at current index `index`. -/
private def unaryIndex_onePhase (index : Nat) (buffer : Option Unit)
    (rest : List Unit) (output : List Bool) :
    EvalsToInTime (step unaryIndexRevProgram)
      (unaryIndexCfg .next buffer false (() :: rest) output
        (List.replicate index ()) [])
      (some (unaryIndexCfg .next (some ()) false rest
        ((unaryIndexCode index).reverse ++ output)
        (List.replicate (index + 1) ()) []))
      (5 * index + 5) := by
  let afterPop := unaryIndexCfg .decIndex (some ()) false rest output
    (List.replicate index ()) []
  let afterArgs := unaryIndexCfg .pushEnd (some ()) false rest
    (List.replicate index true ++ output) [] (List.replicate index ())
  let afterEnd := unaryIndexCfg .restore (some ()) false rest
    (false :: List.replicate index true ++ output) []
    (List.replicate index ())
  let afterRestore := unaryIndexCfg .advance (some ()) false rest
    (false :: List.replicate index true ++ output)
    (List.replicate index ()) []
  have hpop : EvalsToInTime (step unaryIndexRevProgram)
      (unaryIndexCfg .next buffer false (() :: rest) output
        (List.replicate index ()) []) (some afterPop) 1 := by
    refine ⟨⟨1, rfl⟩, le_rfl⟩
  have hargs : EvalsToInTime (step unaryIndexRevProgram)
      afterPop (some afterArgs) (3 * index + 1) := by
    refine ⟨⟨3 * index + 1, ?_⟩, le_rfl⟩
    simpa [afterPop, afterArgs] using
      unaryIndex_emitArgs_eval index (some ()) false rest output []
  have hend : EvalsToInTime (step unaryIndexRevProgram)
      afterArgs (some afterEnd) 1 := by
    refine ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step unaryIndexRevProgram)
      afterEnd (some afterRestore) (2 * index + 1) := by
    refine ⟨⟨2 * index + 1, ?_⟩, le_rfl⟩
    simpa [afterEnd, afterRestore] using
      unaryIndex_restore_eval index (some ()) false rest
        (false :: List.replicate index true ++ output) []
  have hadvance : EvalsToInTime (step unaryIndexRevProgram)
      afterRestore
      (some (unaryIndexCfg .next (some ()) false rest
        ((unaryIndexCode index).reverse ++ output)
        (List.replicate (index + 1) ()) [])) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (unaryIndexCfg .next (some ()) false rest
      (false :: List.replicate index true ++ output)
      (() :: List.replicate index ()) []) = _
    simp [unaryIndexCode, List.reverse_append, List.replicate_succ]
  let h₁ := EvalsToInTime.trans (step unaryIndexRevProgram)
    1 (3 * index + 1) _ afterPop _ hpop hargs
  let h₂ := EvalsToInTime.trans (step unaryIndexRevProgram)
    ((3 * index + 1) + 1) 1 _ afterArgs _ h₁ hend
  let h₃ := EvalsToInTime.trans (step unaryIndexRevProgram)
    (1 + ((3 * index + 1) + 1)) (2 * index + 1)
    _ afterEnd _ h₂ hrestore
  let h₄ := EvalsToInTime.trans (step unaryIndexRevProgram)
    ((2 * index + 1) + (1 + ((3 * index + 1) + 1))) 1
    _ afterRestore _ h₃ hadvance
  have hbound :
      1 + ((2 * index + 1) + (1 + ((3 * index + 1) + 1))) =
        5 * index + 5 := by omega
  rw [← hbound]
  exact h₄

private def unaryIndexPhaseSteps : Nat → Nat → Nat
  | _, 0 => 0
  | start, count + 1 =>
      (5 * start + 5) + unaryIndexPhaseSteps (start + 1) count

private theorem unaryIndexPhaseSteps_le (start count : Nat) :
    unaryIndexPhaseSteps start count ≤
      5 * count * start + 5 * count ^ 2 := by
  induction count generalizing start with
  | zero => simp [unaryIndexPhaseSteps]
  | succ count ih =>
      simp only [unaryIndexPhaseSteps]
      have h := ih (start + 1)
      nlinarith

/-- Process every remaining clock token, starting at an arbitrary index.  The
final pop buffer is existential because it is irrelevant to the following
empty-input cleanup transition. -/
private def unaryIndex_inputPhases (start : Nat) (buffer : Option Unit)
    (input : List Unit) (output : List Bool) :
    Σ finalBuffer,
      EvalsToInTime (step unaryIndexRevProgram)
        (unaryIndexCfg .next buffer false input output
          (List.replicate start ()) [])
        (some (unaryIndexCfg .next finalBuffer false []
          ((unaryIndexStreamFrom start input.length).reverse ++ output)
          (List.replicate (start + input.length) ()) []))
        (unaryIndexPhaseSteps start input.length) := by
  induction input generalizing start buffer output with
  | nil =>
      exact ⟨buffer, ⟨⟨0, rfl⟩, le_rfl⟩⟩
  | cons head rest ih =>
      cases head
      let first := unaryIndex_onePhase start buffer rest output
      rcases ih (start + 1) (some ())
          ((unaryIndexCode start).reverse ++ output) with
        ⟨finalBuffer, remaining⟩
      let full := EvalsToInTime.trans (step unaryIndexRevProgram)
        (5 * start + 5) (unaryIndexPhaseSteps (start + 1) rest.length)
        _
        (unaryIndexCfg .next (some ()) false rest
          ((unaryIndexCode start).reverse ++ output)
          (List.replicate (start + 1) ()) [])
        _ first remaining
      have hstart : start + 1 + rest.length =
          start + (Unit.unit :: rest).length := by simp; omega
      have hout :
          (unaryIndexStreamFrom (start + 1) rest.length).reverse ++
              ((unaryIndexCode start).reverse ++ output) =
            (unaryIndexStreamFrom start (Unit.unit :: rest).length).reverse ++
              output := by
        simp [unaryIndexStreamFrom, List.reverse_append, List.append_assoc]
      have hbound :
          unaryIndexPhaseSteps (start + 1) rest.length +
              (5 * start + 5) =
            unaryIndexPhaseSteps start (Unit.unit :: rest).length := by
        simp [unaryIndexPhaseSteps, Nat.add_comm]
      rw [hstart, hout] at full
      refine ⟨finalBuffer, ?_⟩
      rw [← hbound]
      exact full

/-- Total bound used by the reversed streamer. -/
def unaryIndexRevSteps (input : List Unit) : Nat :=
  unaryIndexPhaseSteps 0 input.length + input.length + 3

/-- Clear the final index counter and halt after every clock token is
processed. -/
private def unaryIndex_finish (count : Nat) (buffer : Option Unit)
    (output : List Bool) :
    EvalsToInTime (step unaryIndexRevProgram)
      (unaryIndexCfg .next buffer false [] output
        (List.replicate count ()) [])
      (some (haltCfg unaryIndexRevProgram output))
      (count + 3) := by
  have hclearEval (test : Bool) :
      (flip Option.bind (step unaryIndexRevProgram))^[count + 1]
        (some (unaryIndexCfg .clear none test [] output
          (List.replicate count ()) [])) =
        some (unaryIndexCfg .halt none false [] output [] []) := by
    induction count generalizing test with
    | zero => rfl
    | succ count ih =>
        rw [show count + 1 + 1 = (count + 1) + 1 by omega,
          Function.iterate_succ_apply]
        change
          (flip Option.bind (step unaryIndexRevProgram))^[count + 1]
            (some (unaryIndexCfg .clear none true [] output
              (List.replicate count ()) [])) = _
        simpa using ih true
  have hnext : EvalsToInTime (step unaryIndexRevProgram)
      (unaryIndexCfg .next buffer false [] output
        (List.replicate count ()) [])
      (some (unaryIndexCfg .clear none false [] output
        (List.replicate count ()) [])) 1 := by
    refine ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step unaryIndexRevProgram)
      (unaryIndexCfg .clear none false [] output
        (List.replicate count ()) [])
      (some (unaryIndexCfg .halt none false [] output [] []))
      (count + 1) := by
    exact ⟨⟨count + 1, hclearEval false⟩, le_rfl⟩
  have hhalt : EvalsToInTime (step unaryIndexRevProgram)
      (unaryIndexCfg .halt none false [] output [] [])
      (some (haltCfg unaryIndexRevProgram output)) 1 := by
    refine ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step unaryIndexRevProgram)
    1 (count + 1) _ _ _ hnext hclear
  let full := EvalsToInTime.trans (step unaryIndexRevProgram)
    ((count + 1) + 1) 1 _ _ _ h₁ hhalt
  have hbound : 1 + ((count + 1) + 1) = count + 3 := by omega
  rw [← hbound]
  exact full

/-- Complete reversed-stream builder run. -/
def unaryIndexRev_run (input : List Unit) :
    EvalsToInTime (step unaryIndexRevProgram)
      (initialCfg unaryIndexRevProgram input)
      (some (haltCfg unaryIndexRevProgram
        (unaryIndexStream input.length).reverse))
      (unaryIndexRevSteps input) := by
  rcases unaryIndex_inputPhases 0 none input [] with
    ⟨finalBuffer, phases⟩
  let finish := unaryIndex_finish input.length finalBuffer
    (unaryIndexStream input.length).reverse
  have hstream := unaryIndexStreamFrom_zero input.length
  let full := EvalsToInTime.trans (step unaryIndexRevProgram)
    (unaryIndexPhaseSteps 0 input.length) (input.length + 3)
    (initialCfg unaryIndexRevProgram input)
    (unaryIndexCfg .next finalBuffer false []
      (unaryIndexStream input.length).reverse
      (List.replicate input.length ()) [])
    _ (by
      simpa [initialCfg, unaryIndexCfg, unaryIndexRevProgram, hstream] using
        phases) finish
  have hbound : input.length + 3 + unaryIndexPhaseSteps 0 input.length =
      unaryIndexRevSteps input := by
    simp only [unaryIndexRevSteps]
    omega
  rw [← hbound]
  exact full

/-- Reversed-stream builder output contract. -/
theorem unaryIndexRev_builderOutputs :
    BuilderOutputs unaryIndexRevProgram
      (fun input => (unaryIndexStream input.length).reverse)
      unaryIndexRevSteps := by
  intro input
  exact ⟨unaryIndexRev_run input⟩

/-- Reversed-stream compiled TM2 output contract. -/
theorem unaryIndexRev_outputs :
    Outputs unaryIndexRevProgram
      (fun input => (unaryIndexStream input.length).reverse)
      unaryIndexRevSteps :=
  Outputs.of_builder_run unaryIndexRev_builderOutputs

/-- Quadratic envelope for the reversed unary-index stream. -/
noncomputable def unaryIndexRev_polyBound :
    PolyBound unaryIndexRevSteps where
  polynomial := 5 * Polynomial.X ^ 2 + Polynomial.X + 3
  bound input := by
    have hphase := unaryIndexPhaseSteps_le 0 input.length
    simp only [unaryIndexRevSteps, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega

/-- Concrete polynomial-time TM2 producing the reversed index stream. -/
noncomputable def unaryIndexRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit => (unaryIndexStream input.length).reverse) :=
  ComputableInPolyTime unaryIndexRevProgram _ unaryIndexRevSteps
    unaryIndexRev_outputs unaryIndexRev_polyBound

/-- Concrete polynomial-time TM2 producing the forward unary-index stream. -/
noncomputable def unaryIndexStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit => unaryIndexStream input.length) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryIndexRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := Bool))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
