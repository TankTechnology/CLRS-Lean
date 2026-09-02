import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Fixed delimiter maps over unary-frame streams

Affine runtime sources naturally emit every unary value with an ordinary
`separator`.  Higher Cook--Levin controllers sometimes use `frameEnd` at a
fixed field position.  This module supplies the reusable finite-state bridge:
ordinary separators are replaced cyclically by a nonempty delimiter table,
while ticks and pre-existing frame ends are preserved.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Advance one position in a nonempty finite delimiter table. -/
def unaryFrameDelimiterNext (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (index : Fin delimiters.length) :
    Fin delimiters.length :=
  if hnext : index.val + 1 < delimiters.length then
    ⟨index.val + 1, hnext⟩
  else
    ⟨0, hnonempty⟩

/-- One transducer action.  Only ordinary separators advance the table. -/
def unaryFrameDelimiterStep (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (index : Fin delimiters.length)
    (symbol : UnaryFrameSym) : UnaryFrameSym × Fin delimiters.length :=
  match symbol with
  | .tick => (.tick, index)
  | .separator =>
      (delimiters.get index,
        unaryFrameDelimiterNext delimiters hnonempty index)
  | .frameEnd => (.frameEnd, index)

/-- Pure streaming semantics from an arbitrary current table position. -/
def rewriteUnaryFrameDelimitersFrom (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Fin delimiters.length → List UnaryFrameSym → List UnaryFrameSym
  | _, [] => []
  | index, symbol :: rest =>
      let action := unaryFrameDelimiterStep delimiters hnonempty index symbol
      action.1 ::
        rewriteUnaryFrameDelimitersFrom delimiters hnonempty action.2 rest

/-- Replace ordinary separators cyclically from the first table entry. -/
def rewriteUnaryFrameDelimiters (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (input : List UnaryFrameSym) :
    List UnaryFrameSym :=
  rewriteUnaryFrameDelimitersFrom delimiters hnonempty ⟨0, hnonempty⟩ input

/-- Value-level view of the same cyclic delimiter convention. -/
def encodeUnaryFrameWithDelimiterCycleFrom
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Fin delimiters.length → List Nat → List UnaryFrameSym
  | _, [] => []
  | index, value :: rest =>
      List.replicate value .tick ++ [delimiters.get index] ++
        encodeUnaryFrameWithDelimiterCycleFrom delimiters hnonempty
          (unaryFrameDelimiterNext delimiters hnonempty index) rest

/-- Unary values encoded with the delimiter table starting at position zero. -/
def encodeUnaryFrameWithDelimiterCycle
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (values : List Nat) :
    List UnaryFrameSym :=
  encodeUnaryFrameWithDelimiterCycleFrom delimiters hnonempty
    ⟨0, hnonempty⟩ values

private theorem rewriteUnaryFrameDelimitersFrom_ticks
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom delimiters hnonempty index
        (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameDelimitersFrom delimiters hnonempty index tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameDelimitersFrom, unaryFrameDelimiterStep]
      exact congrArg (List.cons .tick) ih

/-- The symbol transducer has the expected value-level semantics on every
well-formed ordinary unary frame. -/
theorem rewriteUnaryFrameDelimitersFrom_encodeUnaryFrame
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length) (values : List Nat) :
    rewriteUnaryFrameDelimitersFrom delimiters hnonempty index
        (encodeUnaryFrame values) =
      encodeUnaryFrameWithDelimiterCycleFrom delimiters hnonempty index
        values := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih =>
      rw [show encodeUnaryFrame (value :: rest) =
          List.replicate value .tick ++
            .separator :: encodeUnaryFrame rest by
          simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [show encodeUnaryFrameWithDelimiterCycleFrom delimiters hnonempty
          index (value :: rest) =
          List.replicate value .tick ++ [delimiters.get index] ++
            encodeUnaryFrameWithDelimiterCycleFrom delimiters hnonempty
              (unaryFrameDelimiterNext delimiters hnonempty index) rest by
          rfl]
      rw [rewriteUnaryFrameDelimitersFrom_ticks]
      simp only [rewriteUnaryFrameDelimitersFrom,
        unaryFrameDelimiterStep]
      rw [ih]
      simp only [List.append_assoc, List.singleton_append]

/-- Rewriting a complete ordinary unary frame is exactly cyclic encoding. -/
theorem rewriteUnaryFrameDelimiters_encodeUnaryFrame
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (values : List Nat) :
    rewriteUnaryFrameDelimiters delimiters hnonempty
        (encodeUnaryFrame values) =
      encodeUnaryFrameWithDelimiterCycle delimiters hnonempty values := by
  exact rewriteUnaryFrameDelimitersFrom_encodeUnaryFrame delimiters
    hnonempty ⟨0, hnonempty⟩ values

/-- Finite control records the current delimiter and a just-popped symbol. -/
inductive UnaryFrameDelimiterMapLabel (delimiters : List UnaryFrameSym)
  | scan (index : Fin delimiters.length)
  | emit (index : Fin delimiters.length) (symbol : UnaryFrameSym)
  | finish
deriving DecidableEq, Fintype

/-- The fixed prepend-output transducer. -/
def unaryFrameDelimiterMapRevProgram (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameDelimiterMapLabel delimiters
  main := .scan ⟨0, hnonempty⟩
  op
    | .scan index => .popInput .finish (.emit index)
    | .emit index symbol =>
        let action := unaryFrameDelimiterStep delimiters hnonempty index symbol
        .pushOutput action.1 (.scan action.2)
    | .finish => .halt

private def unaryFrameDelimiterMapCfg
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (label : UnaryFrameDelimiterMapLabel delimiters)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameDelimiterMapRevProgram delimiters hnonempty) :=
  { label := some label
    buffer₁ := buffer
    buffer₂ := none
    test := false
    input := input
    output := output
    work₁ := []
    work₂ := []
    counter₁ := []
    counter₂ := []
    counter₃ := [] }

private def unaryFrameDelimiterMapLoopCfg
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length) (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameDelimiterMapRevProgram delimiters hnonempty) :=
  unaryFrameDelimiterMapCfg delimiters hnonempty (.scan index) buffer
    input output

private theorem unaryFrameDelimiterMap_phase_eval
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length) (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    (flip Option.bind
      (step (unaryFrameDelimiterMapRevProgram delimiters hnonempty)))^[
        2 * input.length + 1]
      (some (unaryFrameDelimiterMapLoopCfg delimiters hnonempty index
        buffer input output)) =
      some (unaryFrameDelimiterMapCfg delimiters hnonempty .finish none []
        ((rewriteUnaryFrameDelimitersFrom delimiters hnonempty index input).reverse ++
          output)) := by
  induction input generalizing index buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      let action := unaryFrameDelimiterStep delimiters hnonempty index symbol
      change
        (flip Option.bind
          (step (unaryFrameDelimiterMapRevProgram delimiters hnonempty)))^[
            2 * rest.length + 1]
          (some (unaryFrameDelimiterMapLoopCfg delimiters hnonempty action.2
            (some symbol) rest (action.1 :: output))) = _
      simpa [rewriteUnaryFrameDelimitersFrom, action, List.reverse_cons,
        List.append_assoc] using
        ih action.2 (some symbol) (action.1 :: output)

/-- Exact runtime, including the final empty pop and halt instruction. -/
def unaryFrameDelimiterMapSteps (input : List UnaryFrameSym) : Nat :=
  2 * input.length + 2

/-- Exact reversed-output builder run. -/
def unaryFrameDelimiterMapRev_run (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (input : List UnaryFrameSym) :
    EvalsToInTime
      (step (unaryFrameDelimiterMapRevProgram delimiters hnonempty))
      (initialCfg (unaryFrameDelimiterMapRevProgram delimiters hnonempty) input)
      (some (haltCfg (unaryFrameDelimiterMapRevProgram delimiters hnonempty)
        (rewriteUnaryFrameDelimiters delimiters hnonempty input).reverse))
      (unaryFrameDelimiterMapSteps input) := by
  let beforeHalt := unaryFrameDelimiterMapCfg delimiters hnonempty .finish none []
    (rewriteUnaryFrameDelimiters delimiters hnonempty input).reverse
  have hphase := unaryFrameDelimiterMap_phase_eval delimiters hnonempty
    ⟨0, hnonempty⟩ none input []
  have hphaseRun : EvalsToInTime
      (step (unaryFrameDelimiterMapRevProgram delimiters hnonempty))
      (initialCfg (unaryFrameDelimiterMapRevProgram delimiters hnonempty) input)
      (some beforeHalt) (2 * input.length + 1) := by
    refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
    simpa [beforeHalt, initialCfg, unaryFrameDelimiterMapLoopCfg,
      unaryFrameDelimiterMapCfg, rewriteUnaryFrameDelimiters,
      unaryFrameDelimiterMapRevProgram] using hphase
  have hhalt : EvalsToInTime
      (step (unaryFrameDelimiterMapRevProgram delimiters hnonempty))
      beforeHalt
      (some (haltCfg (unaryFrameDelimiterMapRevProgram delimiters hnonempty)
        (rewriteUnaryFrameDelimiters delimiters hnonempty input).reverse)) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  let full := EvalsToInTime.trans
    (step (unaryFrameDelimiterMapRevProgram delimiters hnonempty))
    (2 * input.length + 1) 1 _ beforeHalt _ hphaseRun hhalt
  convert full using 1
  simp [unaryFrameDelimiterMapSteps]
  omega

/-- Exact compiled output contract for the reversed stream. -/
theorem unaryFrameDelimiterMapRev_outputs
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Outputs (unaryFrameDelimiterMapRevProgram delimiters hnonempty)
      (fun input =>
        (rewriteUnaryFrameDelimiters delimiters hnonempty input).reverse)
      unaryFrameDelimiterMapSteps :=
  Outputs.of_builder_run fun input =>
    ⟨unaryFrameDelimiterMapRev_run delimiters hnonempty input⟩

/-- Linear polynomial envelope for the finite-state transducer. -/
noncomputable def unaryFrameDelimiterMap_polyBound :
    PolyBound unaryFrameDelimiterMapSteps where
  polynomial := 2 * Polynomial.X + 2
  bound input := by
    simp [unaryFrameDelimiterMapSteps, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X]

/-- Concrete polynomial-time TM2 for the prepend-order result. -/
noncomputable def unaryFrameDelimiterMapRev_computableInPolyTime
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (rewriteUnaryFrameDelimiters delimiters hnonempty input).reverse) :=
  ComputableInPolyTime
    (unaryFrameDelimiterMapRevProgram delimiters hnonempty)
    _ unaryFrameDelimiterMapSteps
    (unaryFrameDelimiterMapRev_outputs delimiters hnonempty)
    unaryFrameDelimiterMap_polyBound

/-- Concrete polynomial-time TM2 for the forward rewritten stream. -/
noncomputable def unaryFrameDelimiterMap_computableInPolyTime
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameDelimiters delimiters hnonempty) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (unaryFrameDelimiterMapRev_computableInPolyTime delimiters hnonempty)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
