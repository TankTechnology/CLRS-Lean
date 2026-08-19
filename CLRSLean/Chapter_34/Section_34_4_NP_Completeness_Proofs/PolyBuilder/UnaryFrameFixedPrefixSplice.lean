import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Fixed-prefix delimiter splicing

A validity-tail row has a fixed-length affine prefix followed by a variable
one-hot invocation payload.  The prefix needs verifier-fixed `separator` /
`frameEnd` delimiters, while the payload must be preserved byte-for-byte.
This module implements that boundary with one finite-state TM2.

The input row is

`ordinaryPrefix ++ frameEnd ++ payload ++ frameEnd`.

The first `frameEnd` is an internal marker and is removed.  Prefix separators
are replaced by the fixed delimiter table; the payload and outer row end are
copied unchanged.  The controller then resets to the first prefix position.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Encode values against a fixed delimiter list.  Mismatched tails are
discarded; all correctness theorems state the required equal-length premise. -/
def encodeUnaryFrameWithFixedDelimiters :
    List Nat → List UnaryFrameSym → List UnaryFrameSym
  | value :: values, delimiter :: delimiters =>
      List.replicate value .tick ++ delimiter ::
        encodeUnaryFrameWithFixedDelimiters values delimiters
  | _, _ => []

/-- Source representation for rows whose fixed prefix is still ordinary
unary data and whose payload is protected by an internal `frameEnd`. -/
def encodeUnaryFrameFixedPrefixSpliceInputFamily {alpha : Type}
    (values : alpha → List Nat) (payload : alpha → List UnaryFrameSym) :
    List alpha → List UnaryFrameSym
  | [] => []
  | row :: rest =>
      encodeUnaryFrame (values row) ++ [.frameEnd] ++ payload row ++
        [.frameEnd] ++
          encodeUnaryFrameFixedPrefixSpliceInputFamily values payload rest

/-- Target representation: fixed delimiters are materialized, the internal
marker is gone, and the payload plus row boundary are unchanged. -/
def encodeUnaryFrameFixedPrefixSpliceOutputFamily {alpha : Type}
    (delimiters : List UnaryFrameSym)
    (values : alpha → List Nat) (payload : alpha → List UnaryFrameSym) :
    List alpha → List UnaryFrameSym
  | [] => []
  | row :: rest =>
      encodeUnaryFrameWithFixedDelimiters (values row) delimiters ++
        payload row ++ [.frameEnd] ++
          encodeUnaryFrameFixedPrefixSpliceOutputFamily
            delimiters values payload rest

/-- Finite streaming mode.  The extra terminal prefix position recognizes the
internal marker after exactly `delimiters.length` ordinary separators. -/
inductive UnaryFrameFixedPrefixSpliceMode
    (delimiters : List UnaryFrameSym)
  | fixed (position : Fin (delimiters.length + 1))
  | payload
deriving DecidableEq, Fintype

/-- One pure transducer action.  `none` means that the internal boundary is
dropped; every other action emits exactly one symbol. -/
def unaryFrameFixedPrefixSpliceAction
    (delimiters : List UnaryFrameSym)
    (mode : UnaryFrameFixedPrefixSpliceMode delimiters)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFrameFixedPrefixSpliceMode delimiters :=
  match mode with
  | .fixed position =>
      match symbol with
      | .tick => (some .tick, .fixed position)
      | .separator =>
          if hposition : position.val < delimiters.length then
            (some (delimiters.get ⟨position.val, hposition⟩),
              .fixed ⟨position.val + 1, by omega⟩)
          else
            (some .separator, .fixed position)
      | .frameEnd =>
          if hterminal : position.val = delimiters.length then
            (none, .payload)
          else
            (some .frameEnd, .fixed position)
  | .payload =>
      match symbol with
      | .frameEnd =>
          (some .frameEnd, .fixed ⟨0, by simp⟩)
      | other => (some other, .payload)

/-- Pure streaming semantics from an arbitrary mode. -/
def rewriteUnaryFrameFixedPrefixSpliceFrom
    (delimiters : List UnaryFrameSym) :
    UnaryFrameFixedPrefixSpliceMode delimiters →
      List UnaryFrameSym → List UnaryFrameSym
  | _, [] => []
  | mode, symbol :: rest =>
      let action := unaryFrameFixedPrefixSpliceAction delimiters mode symbol
      match action.1 with
      | none =>
          rewriteUnaryFrameFixedPrefixSpliceFrom delimiters action.2 rest
      | some emitted =>
          emitted ::
            rewriteUnaryFrameFixedPrefixSpliceFrom delimiters action.2 rest

/-- Rewrite from the first prefix position. -/
def rewriteUnaryFrameFixedPrefixSplice
    (delimiters : List UnaryFrameSym) (input : List UnaryFrameSym) :
    List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixSpliceFrom delimiters
    (.fixed ⟨0, by simp⟩) input

private theorem fixedPrefixSplice_fixed_ticks
    (delimiters : List UnaryFrameSym)
    (position : Fin (delimiters.length + 1)) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameFixedPrefixSpliceFrom delimiters (.fixed position)
        (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameFixedPrefixSpliceFrom delimiters (.fixed position)
          tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameFixedPrefixSpliceFrom,
        unaryFrameFixedPrefixSpliceAction]
      exact congrArg (List.cons .tick) ih

private theorem fixedPrefixSplice_fixed_separator
    (delimiters : List UnaryFrameSym)
    (position : Fin (delimiters.length + 1))
    (hposition : position.val < delimiters.length)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameFixedPrefixSpliceFrom delimiters (.fixed position)
        (.separator :: tail) =
      delimiters.get ⟨position.val, hposition⟩ ::
        rewriteUnaryFrameFixedPrefixSpliceFrom delimiters
          (.fixed ⟨position.val + 1, by omega⟩) tail := by
  simp [rewriteUnaryFrameFixedPrefixSpliceFrom,
    unaryFrameFixedPrefixSpliceAction, hposition]

private theorem fixedPrefixSplice_fixed_boundary
    (delimiters : List UnaryFrameSym) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameFixedPrefixSpliceFrom delimiters
        (.fixed ⟨delimiters.length, by omega⟩) (.frameEnd :: tail) =
      rewriteUnaryFrameFixedPrefixSpliceFrom delimiters .payload tail := by
  simp [rewriteUnaryFrameFixedPrefixSpliceFrom,
    unaryFrameFixedPrefixSpliceAction]

private theorem fixedPrefixSplice_payload_run
    (delimiters : List UnaryFrameSym) (payload tail : List UnaryFrameSym)
    (hpayload : ∀ symbol ∈ payload, symbol ≠ .frameEnd) :
    rewriteUnaryFrameFixedPrefixSpliceFrom delimiters .payload
        (payload ++ .frameEnd :: tail) =
      payload ++ .frameEnd ::
        rewriteUnaryFrameFixedPrefixSpliceFrom delimiters
          (.fixed ⟨0, by simp⟩) tail := by
  induction payload with
  | nil =>
      simp [rewriteUnaryFrameFixedPrefixSpliceFrom,
        unaryFrameFixedPrefixSpliceAction]
  | cons symbol rest ih =>
      have hsymbol := hpayload symbol (by simp)
      have hrest : ∀ item ∈ rest, item ≠ .frameEnd := by
        intro item hitem
        exact hpayload item (by simp [hitem])
      cases symbol <;>
        simp_all [rewriteUnaryFrameFixedPrefixSpliceFrom,
          unaryFrameFixedPrefixSpliceAction]

private theorem fixedPrefixSplice_fixed_values
    (delimiters : List UnaryFrameSym) (position : Nat)
    (values : List Nat) (tail : List UnaryFrameSym)
    (hfit : position + values.length = delimiters.length) :
    rewriteUnaryFrameFixedPrefixSpliceFrom delimiters
        (.fixed ⟨position, by omega⟩)
        (encodeUnaryFrame values ++ .frameEnd :: tail) =
      encodeUnaryFrameWithFixedDelimiters values
          (delimiters.drop position) ++
        rewriteUnaryFrameFixedPrefixSpliceFrom delimiters .payload tail := by
  induction values generalizing position with
  | nil =>
      have hposition : position = delimiters.length := by simpa using hfit
      subst position
      simpa [encodeUnaryFrame,
        encodeUnaryFrameWithFixedDelimiters] using
        fixedPrefixSplice_fixed_boundary delimiters tail
  | cons value values ih =>
      have hposition : position < delimiters.length := by
        simp only [List.length_cons] at hfit
        omega
      have htailFit : position + 1 + values.length = delimiters.length := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ .frameEnd :: tail =
          List.replicate value .tick ++
            (.separator ::
              (encodeUnaryFrame values ++ .frameEnd :: tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      have hticks := fixedPrefixSplice_fixed_ticks delimiters
        (⟨position, by omega⟩ : Fin (delimiters.length + 1)) value
        (.separator :: (encodeUnaryFrame values ++ .frameEnd :: tail))
      rw [hticks]
      rw [fixedPrefixSplice_fixed_separator delimiters
        ⟨position, by omega⟩ hposition]
      rw [ih (position + 1) htailFit]
      have hdrop : delimiters.drop position =
          delimiters.get ⟨position, hposition⟩ ::
            delimiters.drop (position + 1) := by
        simpa using List.drop_eq_getElem_cons hposition
      rw [hdrop]
      simp [encodeUnaryFrameWithFixedDelimiters, List.append_assoc]

/-- On well-formed row families, the pure transducer has the intended exact
splice semantics. -/
theorem rewriteUnaryFrameFixedPrefixSplice_family {alpha : Type}
    (delimiters : List UnaryFrameSym)
    (values : alpha → List Nat) (payload : alpha → List UnaryFrameSym)
    (rows : List alpha)
    (hlength : ∀ row, (values row).length = delimiters.length)
    (hpayload : ∀ row symbol, symbol ∈ payload row →
      symbol ≠ .frameEnd) :
    rewriteUnaryFrameFixedPrefixSplice delimiters
        (encodeUnaryFrameFixedPrefixSpliceInputFamily values payload rows) =
      encodeUnaryFrameFixedPrefixSpliceOutputFamily
        delimiters values payload rows := by
  unfold rewriteUnaryFrameFixedPrefixSplice
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [encodeUnaryFrameFixedPrefixSpliceInputFamily,
        encodeUnaryFrameFixedPrefixSpliceOutputFamily]
      rw [show encodeUnaryFrame (values row) ++ [.frameEnd] ++
            payload row ++ [.frameEnd] ++
              encodeUnaryFrameFixedPrefixSpliceInputFamily values payload rest =
          encodeUnaryFrame (values row) ++ .frameEnd ::
            (payload row ++ .frameEnd ::
              encodeUnaryFrameFixedPrefixSpliceInputFamily values payload rest) by
        simp [List.append_assoc]]
      rw [fixedPrefixSplice_fixed_values delimiters 0 (values row)
        (payload row ++ .frameEnd ::
          encodeUnaryFrameFixedPrefixSpliceInputFamily values payload rest)
        (by simpa using hlength row)]
      rw [fixedPrefixSplice_payload_run delimiters (payload row)
        (encodeUnaryFrameFixedPrefixSpliceInputFamily values payload rest)
        (hpayload row)]
      rw [ih]
      simp [List.append_assoc]

/-- Finite control for the prepend-output transducer. -/
inductive UnaryFrameFixedPrefixSpliceLabel
    (delimiters : List UnaryFrameSym)
  | scan (mode : UnaryFrameFixedPrefixSpliceMode delimiters)
  | emit (mode : UnaryFrameFixedPrefixSpliceMode delimiters)
      (symbol : UnaryFrameSym)
  | skip (mode : UnaryFrameFixedPrefixSpliceMode delimiters)
  | finish
deriving DecidableEq, Fintype

/-- Dispatch one consumed symbol without exposing projections from the paired
semantic action to the machine evaluator. -/
def unaryFrameFixedPrefixSpliceTarget
    (delimiters : List UnaryFrameSym)
    (mode : UnaryFrameFixedPrefixSpliceMode delimiters)
    (symbol : UnaryFrameSym) :
    UnaryFrameFixedPrefixSpliceLabel delimiters :=
  match unaryFrameFixedPrefixSpliceAction delimiters mode symbol with
  | (none, nextMode) => .skip nextMode
  | (some emitted, nextMode) => .emit nextMode emitted

/-- One fixed transducer for one fixed delimiter table. -/
def unaryFrameFixedPrefixSpliceRevProgram
    (delimiters : List UnaryFrameSym) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameFixedPrefixSpliceLabel delimiters
  main := .scan (.fixed ⟨0, by simp⟩)
  op
    | .scan mode => .popInput .finish fun symbol =>
        unaryFrameFixedPrefixSpliceTarget delimiters mode symbol
    | .emit mode symbol => .pushOutput symbol (.scan mode)
    | .skip mode => .jump (.scan mode)
    | .finish => .halt

private def unaryFrameFixedPrefixSpliceCfg
    (delimiters : List UnaryFrameSym)
    (label : UnaryFrameFixedPrefixSpliceLabel delimiters)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameFixedPrefixSpliceRevProgram delimiters) :=
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

private def unaryFrameFixedPrefixSpliceLoopCfg
    (delimiters : List UnaryFrameSym)
    (mode : UnaryFrameFixedPrefixSpliceMode delimiters)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameFixedPrefixSpliceRevProgram delimiters) :=
  unaryFrameFixedPrefixSpliceCfg delimiters (.scan mode) buffer input output

private theorem unaryFrameFixedPrefixSplice_phase_eval
    (delimiters : List UnaryFrameSym)
    (mode : UnaryFrameFixedPrefixSpliceMode delimiters)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    (flip Option.bind
      (step (unaryFrameFixedPrefixSpliceRevProgram delimiters)))^[
        2 * input.length + 1]
      (some (unaryFrameFixedPrefixSpliceLoopCfg
        delimiters mode buffer input output)) =
      some (unaryFrameFixedPrefixSpliceCfg delimiters .finish none []
        ((rewriteUnaryFrameFixedPrefixSpliceFrom
          delimiters mode input).reverse ++ output)) := by
  induction input generalizing mode buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      rcases haction : unaryFrameFixedPrefixSpliceAction
          delimiters mode symbol with ⟨emitted, nextMode⟩
      cases emitted with
      | none =>
          have htarget :
              unaryFrameFixedPrefixSpliceTarget delimiters mode symbol =
                .skip nextMode := by
            simp [unaryFrameFixedPrefixSpliceTarget, haction]
          have hfirst :
              step (unaryFrameFixedPrefixSpliceRevProgram delimiters)
                  (unaryFrameFixedPrefixSpliceLoopCfg delimiters mode buffer
                    (symbol :: rest) output) =
                some (unaryFrameFixedPrefixSpliceCfg delimiters
                  (.skip nextMode) (some symbol) rest output) := by
            change some (unaryFrameFixedPrefixSpliceCfg delimiters
              (unaryFrameFixedPrefixSpliceTarget delimiters mode symbol)
              (some symbol) rest output) = _
            rw [htarget]
          have hsecond :
              step (unaryFrameFixedPrefixSpliceRevProgram delimiters)
                  (unaryFrameFixedPrefixSpliceCfg delimiters
                    (.skip nextMode) (some symbol) rest output) =
                some (unaryFrameFixedPrefixSpliceLoopCfg delimiters nextMode
                  (some symbol) rest output) := by
            rfl
          have hinner :
              flip Option.bind
                  (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
                  (some (unaryFrameFixedPrefixSpliceLoopCfg delimiters mode
                    buffer (symbol :: rest) output)) =
                some (unaryFrameFixedPrefixSpliceCfg delimiters
                  (.skip nextMode) (some symbol) rest output) := by
            change step (unaryFrameFixedPrefixSpliceRevProgram delimiters)
              (unaryFrameFixedPrefixSpliceLoopCfg delimiters mode buffer
                (symbol :: rest) output) = _
            exact hfirst
          have htwo :
              flip Option.bind
                  (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
                (flip Option.bind
                  (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
                  (some (unaryFrameFixedPrefixSpliceLoopCfg
                    delimiters mode buffer (symbol :: rest) output))) =
                some (unaryFrameFixedPrefixSpliceLoopCfg delimiters nextMode
                  (some symbol) rest output) := by
            rw [hinner]
            change step (unaryFrameFixedPrefixSpliceRevProgram delimiters)
              (unaryFrameFixedPrefixSpliceCfg delimiters (.skip nextMode)
                (some symbol) rest output) = _
            exact hsecond
          rw [htwo]
          simpa [rewriteUnaryFrameFixedPrefixSpliceFrom, haction] using
            ih nextMode (some symbol) output
      | some emitted =>
          have htarget :
              unaryFrameFixedPrefixSpliceTarget delimiters mode symbol =
                .emit nextMode emitted := by
            simp [unaryFrameFixedPrefixSpliceTarget, haction]
          have hfirst :
              step (unaryFrameFixedPrefixSpliceRevProgram delimiters)
                  (unaryFrameFixedPrefixSpliceLoopCfg delimiters mode buffer
                    (symbol :: rest) output) =
                some (unaryFrameFixedPrefixSpliceCfg delimiters
                  (.emit nextMode emitted) (some symbol) rest output) := by
            change some (unaryFrameFixedPrefixSpliceCfg delimiters
              (unaryFrameFixedPrefixSpliceTarget delimiters mode symbol)
              (some symbol) rest output) = _
            rw [htarget]
          have hsecond :
              step (unaryFrameFixedPrefixSpliceRevProgram delimiters)
                  (unaryFrameFixedPrefixSpliceCfg delimiters
                    (.emit nextMode emitted) (some symbol) rest output) =
                some (unaryFrameFixedPrefixSpliceLoopCfg delimiters nextMode
                  (some symbol) rest (emitted :: output)) := by
            rfl
          have hinner :
              flip Option.bind
                  (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
                  (some (unaryFrameFixedPrefixSpliceLoopCfg delimiters mode
                    buffer (symbol :: rest) output)) =
                some (unaryFrameFixedPrefixSpliceCfg delimiters
                  (.emit nextMode emitted) (some symbol) rest output) := by
            change step (unaryFrameFixedPrefixSpliceRevProgram delimiters)
              (unaryFrameFixedPrefixSpliceLoopCfg delimiters mode buffer
                (symbol :: rest) output) = _
            exact hfirst
          have htwo :
              flip Option.bind
                  (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
                (flip Option.bind
                  (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
                  (some (unaryFrameFixedPrefixSpliceLoopCfg
                    delimiters mode buffer (symbol :: rest) output))) =
                some (unaryFrameFixedPrefixSpliceLoopCfg delimiters nextMode
                  (some symbol) rest (emitted :: output)) := by
            rw [hinner]
            change step (unaryFrameFixedPrefixSpliceRevProgram delimiters)
              (unaryFrameFixedPrefixSpliceCfg delimiters
                (.emit nextMode emitted) (some symbol) rest output) = _
            exact hsecond
          rw [htwo]
          simpa [rewriteUnaryFrameFixedPrefixSpliceFrom, haction,
            List.reverse_cons, List.append_assoc] using
            ih nextMode (some symbol) (emitted :: output)

/-- Exact runtime, including the final empty-input pop and halt. -/
def unaryFrameFixedPrefixSpliceSteps (input : List UnaryFrameSym) : Nat :=
  2 * input.length + 2

/-- Exact reverse-output builder run. -/
def unaryFrameFixedPrefixSpliceRev_run
    (delimiters input : List UnaryFrameSym) :
    EvalsToInTime
      (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
      (initialCfg (unaryFrameFixedPrefixSpliceRevProgram delimiters) input)
      (some (haltCfg (unaryFrameFixedPrefixSpliceRevProgram delimiters)
        (rewriteUnaryFrameFixedPrefixSplice delimiters input).reverse))
      (unaryFrameFixedPrefixSpliceSteps input) := by
  let beforeHalt := unaryFrameFixedPrefixSpliceCfg delimiters .finish none []
    (rewriteUnaryFrameFixedPrefixSplice delimiters input).reverse
  have hphase := unaryFrameFixedPrefixSplice_phase_eval delimiters
    (.fixed ⟨0, by simp⟩) none input []
  have hphaseRun : EvalsToInTime
      (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
      (initialCfg (unaryFrameFixedPrefixSpliceRevProgram delimiters) input)
      (some beforeHalt) (2 * input.length + 1) := by
    refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
    simpa [beforeHalt, initialCfg, unaryFrameFixedPrefixSpliceLoopCfg,
      unaryFrameFixedPrefixSpliceCfg, rewriteUnaryFrameFixedPrefixSplice,
      unaryFrameFixedPrefixSpliceRevProgram] using hphase
  have hhalt : EvalsToInTime
      (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
      beforeHalt
      (some (haltCfg (unaryFrameFixedPrefixSpliceRevProgram delimiters)
        (rewriteUnaryFrameFixedPrefixSplice delimiters input).reverse)) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step (unaryFrameFixedPrefixSpliceRevProgram delimiters))
    (2 * input.length + 1) 1 _ beforeHalt _ hphaseRun hhalt
  convert full using 1
  simp [unaryFrameFixedPrefixSpliceSteps]
  omega

/-- The exact runtime is bounded by the displayed linear polynomial. -/
theorem unaryFrameFixedPrefixSpliceSteps_le
    (input : List UnaryFrameSym) :
    unaryFrameFixedPrefixSpliceSteps input ≤ 2 * input.length + 2 := by
  rfl

/-- Concrete polynomial-time reverse-output transducer. -/
noncomputable def unaryFrameFixedPrefixSpliceRev_computableInPolyTime
    (delimiters : List UnaryFrameSym) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (rewriteUnaryFrameFixedPrefixSplice delimiters input).reverse) where
  tm := compile (unaryFrameFixedPrefixSpliceRevProgram delimiters)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun := fun input => by
    have builderRun := unaryFrameFixedPrefixSpliceRev_run delimiters input
    have compiledRun := compile_evalsToInTime
      (unaryFrameFixedPrefixSpliceRevProgram delimiters) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile (unaryFrameFixedPrefixSpliceRevProgram delimiters)).step
        (_root_.Turing.initList
          (compile (unaryFrameFixedPrefixSpliceRevProgram delimiters)) input)
        (some (_root_.Turing.haltList
          (compile (unaryFrameFixedPrefixSpliceRevProgram delimiters))
          (rewriteUnaryFrameFixedPrefixSplice delimiters input).reverse))
        (unaryFrameFixedPrefixSpliceSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameFixedPrefixSpliceSteps input ≤
        (2 * Polynomial.X + 2).eval input.length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameFixedPrefixSpliceSteps_le input
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile (unaryFrameFixedPrefixSpliceRevProgram delimiters)).step
        (_root_.Turing.initList
          (compile (unaryFrameFixedPrefixSpliceRevProgram delimiters)) input)
        (some (_root_.Turing.haltList
          (compile (unaryFrameFixedPrefixSpliceRevProgram delimiters))
          (rewriteUnaryFrameFixedPrefixSplice delimiters input).reverse))
        ((2 * Polynomial.X + 2).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward fixed-prefix splicer. -/
noncomputable def unaryFrameFixedPrefixSplice_computableInPolyTime
    (delimiters : List UnaryFrameSym) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameFixedPrefixSplice delimiters) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (unaryFrameFixedPrefixSpliceRev_computableInPolyTime delimiters)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
