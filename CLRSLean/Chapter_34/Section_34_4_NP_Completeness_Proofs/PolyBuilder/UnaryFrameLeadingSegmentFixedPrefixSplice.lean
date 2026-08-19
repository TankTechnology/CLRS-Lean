import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixSplice
import Mathlib.Tactic

/-!
# Fixed-prefix delimiter splicing behind a preserved leading segment

For a fixed nonempty delimiter table, this streaming TM2 maps every row

`leading ++ frameEnd ++ encodeUnaryFrame values ++ payload ++ frameEnd`

to

`leading ++ frameEnd ++ encodeWithFixedDelimiters values ++ payload ++ frameEnd`.

Both `leading` and `payload` are copied byte-for-byte.  Only the first fixed
number of ordinary separators after the first row boundary are rewritten.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- One semantic row for the leading-segment-preserving delimiter splice. -/
structure UnaryFrameLeadingSegmentFixedPrefixRow where
  leading : List UnaryFrameSym
  values : List Nat
  payload : List UnaryFrameSym
deriving DecidableEq, Repr

/-- Well-formed rows for one verifier-fixed delimiter table. -/
structure UnaryFrameLeadingSegmentFixedPrefixFamily
    (delimiters : List UnaryFrameSym) where
  rows : List UnaryFrameLeadingSegmentFixedPrefixRow
  values_lengths : ∀ row ∈ rows, row.values.length = delimiters.length
  leading_frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row.leading,
    symbol ≠ UnaryFrameSym.frameEnd
  payload_frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row.payload,
    symbol ≠ UnaryFrameSym.frameEnd

/-- Ordinary fixed fields behind a preserved leading segment. -/
def encodeUnaryFrameLeadingSegmentFixedPrefixInput
    {delimiters : List UnaryFrameSym}
    (family : UnaryFrameLeadingSegmentFixedPrefixFamily delimiters) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    row.leading ++ [.frameEnd] ++ encodeUnaryFrame row.values ++
      row.payload ++ [.frameEnd]

/-- Delimiter-materialized fixed fields behind the same leading segment. -/
def encodeUnaryFrameLeadingSegmentFixedPrefixOutput
    {delimiters : List UnaryFrameSym}
    (family : UnaryFrameLeadingSegmentFixedPrefixFamily delimiters) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    row.leading ++ [.frameEnd] ++
      encodeUnaryFrameWithFixedDelimiters row.values delimiters ++
      row.payload ++ [.frameEnd]

/-- Streaming phase. -/
inductive UnaryFrameLeadingSegmentFixedPrefixMode
    (delimiters : List UnaryFrameSym)
  | leading
  | fixed (position : Fin (delimiters.length + 1))
  | payload
deriving DecidableEq, Fintype

/-- Phase immediately after the preserved leading segment. -/
def unaryFrameLeadingSegmentFixedPrefixAfterLeading
    (delimiters : List UnaryFrameSym) :
    UnaryFrameLeadingSegmentFixedPrefixMode delimiters :=
  if h : 0 < delimiters.length then .fixed ⟨0, by omega⟩ else .payload

/-- Pure one-symbol action. -/
def unaryFrameLeadingSegmentFixedPrefixAction
    (delimiters : List UnaryFrameSym)
    (mode : UnaryFrameLeadingSegmentFixedPrefixMode delimiters)
    (symbol : UnaryFrameSym) :
    UnaryFrameSym × UnaryFrameLeadingSegmentFixedPrefixMode delimiters :=
  match mode with
  | .leading =>
      match symbol with
      | .frameEnd =>
          (.frameEnd,
            unaryFrameLeadingSegmentFixedPrefixAfterLeading delimiters)
      | other => (other, .leading)
  | .fixed position =>
      match symbol with
      | .tick => (.tick, .fixed position)
      | .separator =>
          if hposition : position.val < delimiters.length then
            let emitted := delimiters.get ⟨position.val, hposition⟩
            if hnext : position.val + 1 < delimiters.length then
              (emitted, .fixed ⟨position.val + 1, by omega⟩)
            else
              (emitted, .payload)
          else
            (.separator, .payload)
      | .frameEnd => (.frameEnd, .leading)
  | .payload =>
      match symbol with
      | .frameEnd => (.frameEnd, .leading)
      | other => (other, .payload)

/-- Pure streaming semantics from an arbitrary phase. -/
def rewriteUnaryFrameLeadingSegmentFixedPrefixFrom
    (delimiters : List UnaryFrameSym) :
    UnaryFrameLeadingSegmentFixedPrefixMode delimiters →
      List UnaryFrameSym → List UnaryFrameSym
  | _, [] => []
  | mode, symbol :: rest =>
      let action := unaryFrameLeadingSegmentFixedPrefixAction
        delimiters mode symbol
      action.1 :: rewriteUnaryFrameLeadingSegmentFixedPrefixFrom
        delimiters action.2 rest

/-- Rewrite from the preserved leading phase. -/
def rewriteUnaryFrameLeadingSegmentFixedPrefix
    (delimiters input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters .leading input

private theorem leadingSegmentSplice_leading_run
    (delimiters leading tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ leading, symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters .leading
        (leading ++ .frameEnd :: tail) =
      leading ++ .frameEnd ::
        rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
          (unaryFrameLeadingSegmentFixedPrefixAfterLeading delimiters)
          tail := by
  induction leading with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      cases symbol <;>
        simp_all [rewriteUnaryFrameLeadingSegmentFixedPrefixFrom,
          unaryFrameLeadingSegmentFixedPrefixAction]

private theorem leadingSegmentSplice_fixed_ticks
    (delimiters : List UnaryFrameSym)
    (position : Fin (delimiters.length + 1))
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
        (.fixed position) (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
          (.fixed position) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameLeadingSegmentFixedPrefixFrom,
        unaryFrameLeadingSegmentFixedPrefixAction]
      exact congrArg (List.cons .tick) ih

private theorem leadingSegmentSplice_fixed_separator
    (delimiters : List UnaryFrameSym) (position : Nat)
    (hposition : position < delimiters.length)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
        (.fixed ⟨position, by omega⟩) (.separator :: tail) =
      delimiters.get ⟨position, hposition⟩ ::
        if hnext : position + 1 < delimiters.length then
          rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
            (.fixed ⟨position + 1, by omega⟩) tail
        else
          rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
            .payload tail := by
  simp [rewriteUnaryFrameLeadingSegmentFixedPrefixFrom,
    unaryFrameLeadingSegmentFixedPrefixAction, hposition]
  split_ifs <;> simp

private theorem leadingSegmentSplice_fixed_values
    (delimiters : List UnaryFrameSym) (position : Nat)
    (values : List Nat) (tail : List UnaryFrameSym)
    (hfit : position + values.length = delimiters.length)
    (hposition : position < delimiters.length) :
    rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
        (.fixed ⟨position, by omega⟩) (encodeUnaryFrame values ++ tail) =
      encodeUnaryFrameWithFixedDelimiters values
          (delimiters.drop position) ++
        rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
          .payload tail := by
  induction values generalizing position with
  | nil =>
      simp only [List.length_nil, Nat.add_zero] at hfit
      omega
  | cons value values ih =>
      have hnextFit : position + 1 + values.length = delimiters.length := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [leadingSegmentSplice_fixed_ticks]
      rw [leadingSegmentSplice_fixed_separator delimiters position
        hposition]
      split_ifs with hnext
      · rw [ih (position + 1) hnextFit hnext]
        have hdrop : delimiters.drop position =
            delimiters.get ⟨position, hposition⟩ ::
              delimiters.drop (position + 1) := by
          simpa using List.drop_eq_getElem_cons hposition
        rw [hdrop]
        simp [encodeUnaryFrameWithFixedDelimiters, List.append_assoc]
      · cases values with
        | nil =>
            have hdrop : delimiters.drop position =
                [delimiters.get ⟨position, hposition⟩] := by
              have hlast : position + 1 = delimiters.length := by omega
              rw [show delimiters.drop position =
                  delimiters.get ⟨position, hposition⟩ ::
                    delimiters.drop (position + 1) by
                simpa using List.drop_eq_getElem_cons hposition,
                hlast]
              simp
            rw [hdrop]
            simp [encodeUnaryFrame, encodeUnaryFrameWithFixedDelimiters]
        | cons head rest =>
            simp only [List.length_cons] at hnextFit
            omega

private theorem leadingSegmentSplice_payload_run
    (delimiters payload tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ payload, symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters .payload
        (payload ++ .frameEnd :: tail) =
      payload ++ .frameEnd ::
        rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters
          .leading tail := by
  induction payload with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      cases symbol <;>
        simp_all [rewriteUnaryFrameLeadingSegmentFixedPrefixFrom,
          unaryFrameLeadingSegmentFixedPrefixAction]

/-- Exact pure action on every well-formed row family. -/
theorem rewriteUnaryFrameLeadingSegmentFixedPrefix_family
    (delimiters : List UnaryFrameSym)
    (family : UnaryFrameLeadingSegmentFixedPrefixFamily delimiters)
    (hnonempty : 0 < delimiters.length) :
    rewriteUnaryFrameLeadingSegmentFixedPrefix delimiters
        (encodeUnaryFrameLeadingSegmentFixedPrefixInput family) =
      encodeUnaryFrameLeadingSegmentFixedPrefixOutput family := by
  unfold rewriteUnaryFrameLeadingSegmentFixedPrefix
  let rowsRun : ∀ rows : List UnaryFrameLeadingSegmentFixedPrefixRow,
      (∀ row ∈ rows, row.values.length = delimiters.length) →
      (∀ row ∈ rows, ∀ symbol ∈ row.leading,
        symbol ≠ UnaryFrameSym.frameEnd) →
      (∀ row ∈ rows, ∀ symbol ∈ row.payload,
        symbol ≠ UnaryFrameSym.frameEnd) →
      rewriteUnaryFrameLeadingSegmentFixedPrefixFrom delimiters .leading
          (rows.flatMap fun row =>
            row.leading ++ [.frameEnd] ++ encodeUnaryFrame row.values ++
              row.payload ++ [.frameEnd]) =
        rows.flatMap fun row =>
          row.leading ++ [.frameEnd] ++
            encodeUnaryFrameWithFixedDelimiters row.values delimiters ++
            row.payload ++ [.frameEnd] := by
    intro rows hlength hleading hpayload
    induction rows with
    | nil => rfl
    | cons row rest ih =>
        let restInput := rest.flatMap fun item =>
          item.leading ++ [.frameEnd] ++ encodeUnaryFrame item.values ++
            item.payload ++ [.frameEnd]
        have hrowLength := hlength row (by simp)
        have hrowLeading := hleading row (by simp)
        have hrowPayload := hpayload row (by simp)
        have hrestLengths : ∀ item ∈ rest,
            item.values.length = delimiters.length := by
          intro item hitem
          exact hlength item (by simp [hitem])
        have hrestLeading : ∀ item ∈ rest, ∀ symbol ∈ item.leading,
            symbol ≠ UnaryFrameSym.frameEnd := by
          intro item hitem symbol hsymbol
          exact hleading item (by simp [hitem]) symbol hsymbol
        have hrestPayload : ∀ item ∈ rest, ∀ symbol ∈ item.payload,
            symbol ≠ UnaryFrameSym.frameEnd := by
          intro item hitem symbol hsymbol
          exact hpayload item (by simp [hitem]) symbol hsymbol
        have hafter :
            unaryFrameLeadingSegmentFixedPrefixAfterLeading delimiters =
              .fixed ⟨0, by omega⟩ := by
          simp [unaryFrameLeadingSegmentFixedPrefixAfterLeading, hnonempty]
        have hfixed := leadingSegmentSplice_fixed_values delimiters 0
          row.values (row.payload ++ .frameEnd :: restInput)
          (by simpa using hrowLength) hnonempty
        have ih' := ih hrestLengths hrestLeading hrestPayload
        simp only [List.flatMap_cons]
        rw [show
          (row.leading ++ [.frameEnd] ++ encodeUnaryFrame row.values ++
              row.payload ++ [.frameEnd]) ++ restInput =
            row.leading ++ .frameEnd ::
              (encodeUnaryFrame row.values ++
                (row.payload ++ .frameEnd :: restInput)) by
          simp [List.append_assoc]]
        rw [leadingSegmentSplice_leading_run delimiters row.leading
          (encodeUnaryFrame row.values ++
            (row.payload ++ .frameEnd :: restInput)) hrowLeading]
        rw [hafter, hfixed]
        rw [leadingSegmentSplice_payload_run delimiters row.payload
          restInput hrowPayload]
        rw [ih']
        simp [List.append_assoc]
  simpa [encodeUnaryFrameLeadingSegmentFixedPrefixInput,
    encodeUnaryFrameLeadingSegmentFixedPrefixOutput] using
    rowsRun family.rows family.values_lengths
      family.leading_frameEnd_free family.payload_frameEnd_free

/-! ## Concrete streaming machine -/

inductive UnaryFrameLeadingSegmentFixedPrefixLabel
    (delimiters : List UnaryFrameSym)
  | scan (mode : UnaryFrameLeadingSegmentFixedPrefixMode delimiters)
  | emit (mode : UnaryFrameLeadingSegmentFixedPrefixMode delimiters)
      (symbol : UnaryFrameSym)
  | finish
deriving DecidableEq, Fintype

def unaryFrameLeadingSegmentFixedPrefixRevProgram
    (delimiters : List UnaryFrameSym) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameLeadingSegmentFixedPrefixLabel delimiters
  main := .scan .leading
  op
    | .scan mode => .popInput .finish fun symbol =>
        let action := unaryFrameLeadingSegmentFixedPrefixAction
          delimiters mode symbol
        .emit action.2 action.1
    | .emit mode symbol => .pushOutput symbol (.scan mode)
    | .finish => .halt

private def unaryFrameLeadingSegmentFixedPrefixCfg
    (delimiters : List UnaryFrameSym)
    (label : UnaryFrameLeadingSegmentFixedPrefixLabel delimiters)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters) :=
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

private def unaryFrameLeadingSegmentFixedPrefixLoopCfg
    (delimiters : List UnaryFrameSym)
    (mode : UnaryFrameLeadingSegmentFixedPrefixMode delimiters)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters) :=
  unaryFrameLeadingSegmentFixedPrefixCfg delimiters (.scan mode)
    buffer input output

private theorem unaryFrameLeadingSegmentFixedPrefix_phase_eval
    (delimiters : List UnaryFrameSym)
    (mode : UnaryFrameLeadingSegmentFixedPrefixMode delimiters)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    (flip Option.bind
      (step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)))^[
        2 * input.length + 1]
      (some (unaryFrameLeadingSegmentFixedPrefixLoopCfg
        delimiters mode buffer input output)) =
      some (unaryFrameLeadingSegmentFixedPrefixCfg delimiters .finish none []
        ((rewriteUnaryFrameLeadingSegmentFixedPrefixFrom
          delimiters mode input).reverse ++ output)) := by
  induction input generalizing mode buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      rcases haction : unaryFrameLeadingSegmentFixedPrefixAction
          delimiters mode symbol with ⟨emitted, nextMode⟩
      have hfirst :
          step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)
              (unaryFrameLeadingSegmentFixedPrefixLoopCfg delimiters mode
                buffer (symbol :: rest) output) =
            some (unaryFrameLeadingSegmentFixedPrefixCfg delimiters
              (.emit nextMode emitted) (some symbol) rest output) := by
        change some (unaryFrameLeadingSegmentFixedPrefixCfg delimiters
          (.emit
            (unaryFrameLeadingSegmentFixedPrefixAction
              delimiters mode symbol).2
            (unaryFrameLeadingSegmentFixedPrefixAction
              delimiters mode symbol).1)
          (some symbol) rest output) = _
        rw [haction]
      have hsecond :
          step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)
              (unaryFrameLeadingSegmentFixedPrefixCfg delimiters
                (.emit nextMode emitted) (some symbol) rest output) =
            some (unaryFrameLeadingSegmentFixedPrefixLoopCfg delimiters
              nextMode (some symbol) rest (emitted :: output)) := by
        rfl
      have hinner :
          flip Option.bind
              (step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
              (some (unaryFrameLeadingSegmentFixedPrefixLoopCfg delimiters
                mode buffer (symbol :: rest) output)) =
            some (unaryFrameLeadingSegmentFixedPrefixCfg delimiters
              (.emit nextMode emitted) (some symbol) rest output) := by
        change step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)
          (unaryFrameLeadingSegmentFixedPrefixLoopCfg delimiters mode buffer
            (symbol :: rest) output) = _
        exact hfirst
      have htwo :
          flip Option.bind
              (step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
            (flip Option.bind
              (step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
              (some (unaryFrameLeadingSegmentFixedPrefixLoopCfg delimiters
                mode buffer (symbol :: rest) output))) =
            some (unaryFrameLeadingSegmentFixedPrefixLoopCfg delimiters
              nextMode (some symbol) rest (emitted :: output)) := by
        rw [hinner]
        change step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)
          (unaryFrameLeadingSegmentFixedPrefixCfg delimiters
            (.emit nextMode emitted) (some symbol) rest output) = _
        exact hsecond
      rw [htwo]
      simpa [rewriteUnaryFrameLeadingSegmentFixedPrefixFrom, haction,
        List.reverse_cons, List.append_assoc] using
        ih nextMode (some symbol) (emitted :: output)

def unaryFrameLeadingSegmentFixedPrefixSteps
    (input : List UnaryFrameSym) : Nat :=
  2 * input.length + 2

def unaryFrameLeadingSegmentFixedPrefixRev_run
    (delimiters input : List UnaryFrameSym) :
    EvalsToInTime
      (step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
      (initialCfg
        (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters) input)
      (some (haltCfg
        (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)
        (rewriteUnaryFrameLeadingSegmentFixedPrefix delimiters input).reverse))
      (unaryFrameLeadingSegmentFixedPrefixSteps input) := by
  let beforeHalt := unaryFrameLeadingSegmentFixedPrefixCfg delimiters
    .finish none []
    (rewriteUnaryFrameLeadingSegmentFixedPrefix delimiters input).reverse
  have hphase := unaryFrameLeadingSegmentFixedPrefix_phase_eval delimiters
    (.leading) none input []
  have hphaseRun : EvalsToInTime
      (step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
      (initialCfg
        (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters) input)
      (some beforeHalt) (2 * input.length + 1) := by
    refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
    simpa [beforeHalt, initialCfg,
      unaryFrameLeadingSegmentFixedPrefixLoopCfg,
      unaryFrameLeadingSegmentFixedPrefixCfg,
      rewriteUnaryFrameLeadingSegmentFixedPrefix,
      unaryFrameLeadingSegmentFixedPrefixRevProgram] using hphase
  have hhalt : EvalsToInTime
      (step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
      beforeHalt
      (some (haltCfg
        (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)
        (rewriteUnaryFrameLeadingSegmentFixedPrefix delimiters input).reverse))
      1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
    (2 * input.length + 1) 1 _ beforeHalt _ hphaseRun hhalt
  convert full using 1
  simp [unaryFrameLeadingSegmentFixedPrefixSteps]
  omega

theorem unaryFrameLeadingSegmentFixedPrefixSteps_le
    (input : List UnaryFrameSym) :
    unaryFrameLeadingSegmentFixedPrefixSteps input ≤
      2 * input.length + 2 := by
  rfl

noncomputable def
    unaryFrameLeadingSegmentFixedPrefixRev_computableInPolyTime
    (delimiters : List UnaryFrameSym) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (rewriteUnaryFrameLeadingSegmentFixedPrefix
          delimiters input).reverse) where
  tm := compile (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun := fun input => by
    have builderRun :=
      unaryFrameLeadingSegmentFixedPrefixRev_run delimiters input
    have compiledRun := compile_evalsToInTime
      (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile
          (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)).step
        (_root_.Turing.initList
          (compile (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
          input)
        (some (_root_.Turing.haltList
          (compile (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
          (rewriteUnaryFrameLeadingSegmentFixedPrefix
            delimiters input).reverse))
        (unaryFrameLeadingSegmentFixedPrefixSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameLeadingSegmentFixedPrefixSteps input ≤
        (2 * Polynomial.X + 2).eval input.length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameLeadingSegmentFixedPrefixSteps_le input
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile
          (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters)).step
        (_root_.Turing.initList
          (compile (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
          input)
        (some (_root_.Turing.haltList
          (compile (unaryFrameLeadingSegmentFixedPrefixRevProgram delimiters))
          (rewriteUnaryFrameLeadingSegmentFixedPrefix
            delimiters input).reverse))
        ((2 * Polynomial.X + 2).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

noncomputable def
    unaryFrameLeadingSegmentFixedPrefix_computableInPolyTime
    (delimiters : List UnaryFrameSym) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameLeadingSegmentFixedPrefix delimiters) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (unaryFrameLeadingSegmentFixedPrefixRev_computableInPolyTime delimiters)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
