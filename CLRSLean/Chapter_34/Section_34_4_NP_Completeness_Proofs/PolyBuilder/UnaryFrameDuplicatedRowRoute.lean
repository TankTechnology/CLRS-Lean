import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate
import Mathlib.Tactic

/-!
# Routing duplicated unary-frame rows

For a fixed positive number of ordinary unary prefix fields, this streaming
TM2 drops the prefix of the first copy of every duplicated row and retains its
payload, then retains the complete second copy.  Thus

`prefix ++ payload ++ frameEnd ++ prefix ++ payload ++ frameEnd`

becomes

`payload ++ frameEnd ++ prefix ++ payload ++ frameEnd`.

This is the reusable routing boundary needed by the Cook--Levin validity-row
assembler: the first payload feeds canonical one-hot expansion, while the
second complete row still owns the halted and tail operands.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Semantic source family for one fixed number of ordinary unary fields. -/
structure UnaryFrameDuplicatedRowRouteFamily (fieldCount : Nat) where
  rows : List (List Nat × List UnaryFrameSym)
  prefix_lengths : ∀ row ∈ rows, row.1.length = fieldCount
  payload_frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row.2,
    symbol ≠ UnaryFrameSym.frameEnd

/-- Two physical copies of every plain row. -/
def encodeUnaryFrameDuplicatedRowRouteInput {fieldCount : Nat}
    (family : UnaryFrameDuplicatedRowRouteFamily fieldCount) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    let packet := encodeUnaryFrame row.1 ++ row.2
    packet ++ [.frameEnd] ++ packet ++ [.frameEnd]

/-- Routed first payload followed by the untouched second row. -/
def encodeUnaryFrameDuplicatedRowRouteOutput {fieldCount : Nat}
    (family : UnaryFrameDuplicatedRowRouteFamily fieldCount) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    row.2 ++ [.frameEnd] ++ encodeUnaryFrame row.1 ++ row.2 ++ [.frameEnd]

/-- Streaming phase of the row router. -/
inductive UnaryFrameDuplicatedRowRouteMode (fieldCount : Nat)
  | firstPrefix (position : Fin (fieldCount + 1))
  | firstPayload
  | secondRow
deriving DecidableEq, Fintype

/-- Initial mode when the fixed prefix is known to be nonempty. -/
def unaryFrameDuplicatedRowRouteInitialMode (fieldCount : Nat) :
    UnaryFrameDuplicatedRowRouteMode fieldCount :=
  if hpositive : 0 < fieldCount then
    .firstPrefix ⟨0, by omega⟩
  else
    .firstPayload

/-- Pure symbol action.  `none` drops a first-copy prefix symbol. -/
def unaryFrameDuplicatedRowRouteAction (fieldCount : Nat)
    (mode : UnaryFrameDuplicatedRowRouteMode fieldCount)
    (symbol : UnaryFrameSym) :
    Option UnaryFrameSym × UnaryFrameDuplicatedRowRouteMode fieldCount :=
  match mode with
  | .firstPrefix position =>
      match symbol with
      | .tick => (none, .firstPrefix position)
      | .separator =>
          if hnext : position.val + 1 < fieldCount then
            (none, .firstPrefix ⟨position.val + 1, by omega⟩)
          else
            (none, .firstPayload)
      | .frameEnd => (none, .firstPayload)
  | .firstPayload =>
      match symbol with
      | .frameEnd => (some .frameEnd, .secondRow)
      | other => (some other, .firstPayload)
  | .secondRow =>
      match symbol with
      | .frameEnd =>
          (some .frameEnd,
            unaryFrameDuplicatedRowRouteInitialMode fieldCount)
      | other => (some other, .secondRow)

/-- Pure streaming semantics. -/
def rewriteUnaryFrameDuplicatedRowRouteFrom (fieldCount : Nat) :
    UnaryFrameDuplicatedRowRouteMode fieldCount →
      List UnaryFrameSym → List UnaryFrameSym
  | _, [] => []
  | mode, symbol :: rest =>
      let action := unaryFrameDuplicatedRowRouteAction fieldCount mode symbol
      match action.1 with
      | none => rewriteUnaryFrameDuplicatedRowRouteFrom
          fieldCount action.2 rest
      | some emitted => emitted ::
          rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount action.2 rest

/-- Route from the fixed initial phase. -/
def rewriteUnaryFrameDuplicatedRowRoute (fieldCount : Nat)
    (input : List UnaryFrameSym) : List UnaryFrameSym :=
  rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
    (unaryFrameDuplicatedRowRouteInitialMode fieldCount) input

private theorem duplicatedRowRoute_firstPrefix_ticks
    (fieldCount : Nat) (position : Fin (fieldCount + 1))
    (count : Nat) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
        (.firstPrefix position) (List.replicate count .tick ++ tail) =
      rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
        (.firstPrefix position) tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameDuplicatedRowRouteFrom,
        unaryFrameDuplicatedRowRouteAction]
      exact ih

private theorem duplicatedRowRoute_firstPrefix_separator
    (fieldCount : Nat) (position : Nat)
    (hposition : position < fieldCount) (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
        (.firstPrefix ⟨position, by omega⟩) (.separator :: tail) =
      if hnext : position + 1 < fieldCount then
        rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
          (.firstPrefix ⟨position + 1, by omega⟩) tail
      else
        rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
          .firstPayload tail := by
  simp [rewriteUnaryFrameDuplicatedRowRouteFrom,
    unaryFrameDuplicatedRowRouteAction]
  split_ifs <;> rfl

private theorem duplicatedRowRoute_dropPrefix
    (fieldCount position : Nat) (values : List Nat)
    (tail : List UnaryFrameSym)
    (hfit : position + values.length = fieldCount)
    (hposition : position < fieldCount) :
    rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
        (.firstPrefix ⟨position, by omega⟩)
        (encodeUnaryFrame values ++ tail) =
      rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
        .firstPayload tail := by
  induction values generalizing position with
  | nil =>
      simp only [List.length_nil, Nat.add_zero] at hfit
      omega
  | cons value values ih =>
      have hnextFit : position + 1 + values.length = fieldCount := by
        simp only [List.length_cons] at hfit
        omega
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            (.separator :: (encodeUnaryFrame values ++ tail)) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [duplicatedRowRoute_firstPrefix_ticks]
      rw [duplicatedRowRoute_firstPrefix_separator fieldCount position
        hposition]
      split_ifs with hnext
      · exact ih (position + 1) hnextFit hnext
      · cases values with
        | nil => rfl
        | cons head tail =>
            simp only [List.length_cons] at hnextFit
            omega

private theorem duplicatedRowRoute_firstPayload
    (fieldCount : Nat) (payload tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ payload,
      symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount .firstPayload
        (payload ++ .frameEnd :: tail) =
      payload ++ .frameEnd ::
        rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount .secondRow tail := by
  induction payload with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      cases symbol <;>
        simp_all [rewriteUnaryFrameDuplicatedRowRouteFrom,
          unaryFrameDuplicatedRowRouteAction]

private theorem duplicatedRowRoute_secondRow
    (fieldCount : Nat) (row tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount .secondRow
        (row ++ .frameEnd :: tail) =
      row ++ .frameEnd ::
        rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
          (unaryFrameDuplicatedRowRouteInitialMode fieldCount) tail := by
  induction row with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      cases symbol <;>
        simp_all [rewriteUnaryFrameDuplicatedRowRouteFrom,
          unaryFrameDuplicatedRowRouteAction]

private theorem duplicatedRowRoute_unaryFrame_no_frameEnd
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with (⟨hvalue, rfl⟩ | rfl) <;> simp

/-- Exact action on well-formed duplicated row families. -/
theorem rewriteUnaryFrameDuplicatedRowRoute_family
    {fieldCount : Nat} (family : UnaryFrameDuplicatedRowRouteFamily fieldCount)
    (hpositive : 0 < fieldCount) :
    rewriteUnaryFrameDuplicatedRowRoute fieldCount
        (encodeUnaryFrameDuplicatedRowRouteInput family) =
      encodeUnaryFrameDuplicatedRowRouteOutput family := by
  unfold rewriteUnaryFrameDuplicatedRowRoute
  rw [show unaryFrameDuplicatedRowRouteInitialMode fieldCount =
      .firstPrefix ⟨0, by omega⟩ by
    simp [unaryFrameDuplicatedRowRouteInitialMode, hpositive]]
  let rowsRun : ∀ (rows : List (List Nat × List UnaryFrameSym)),
      (∀ row ∈ rows, row.1.length = fieldCount) →
      (∀ row ∈ rows, ∀ symbol ∈ row.2,
        symbol ≠ UnaryFrameSym.frameEnd) →
      rewriteUnaryFrameDuplicatedRowRouteFrom fieldCount
          (.firstPrefix ⟨0, by omega⟩)
          (rows.flatMap fun row =>
            let packet := encodeUnaryFrame row.1 ++ row.2
            packet ++ [.frameEnd] ++ packet ++ [.frameEnd]) =
        rows.flatMap fun row =>
          row.2 ++ [.frameEnd] ++ encodeUnaryFrame row.1 ++ row.2 ++
            [.frameEnd] := by
    intro rows hlength hpayload
    induction rows with
    | nil => rfl
    | cons row rest ih =>
        let firstRowPrefix : List UnaryFrameSym := encodeUnaryFrame row.1
        let restInput : List UnaryFrameSym := rest.flatMap fun item =>
          let packet := encodeUnaryFrame item.1 ++ item.2
          packet ++ [.frameEnd] ++ packet ++ [.frameEnd]
        have hrowLength := hlength row (by simp)
        have hrowPayload := hpayload row (by simp)
        have hprefix := duplicatedRowRoute_dropPrefix fieldCount 0 row.1
          (row.2 ++ .frameEnd ::
            (firstRowPrefix ++ row.2 ++ .frameEnd :: restInput))
          (by simpa using hrowLength) hpositive
        have hsecondFree : ∀ symbol ∈ firstRowPrefix ++ row.2,
            symbol ≠ UnaryFrameSym.frameEnd := by
          intro symbol hsymbol
          rw [List.mem_append] at hsymbol
          rcases hsymbol with hprefixSymbol | hpayloadSymbol
          · exact duplicatedRowRoute_unaryFrame_no_frameEnd _ symbol
              hprefixSymbol
          · exact hrowPayload symbol hpayloadSymbol
        have hrestLengths : ∀ item ∈ rest,
            item.1.length = fieldCount := by
          intro item hitem
          exact hlength item (by simp [hitem])
        have hrestPayload : ∀ item ∈ rest, ∀ symbol ∈ item.2,
            symbol ≠ UnaryFrameSym.frameEnd := by
          intro item hitem symbol hsymbol
          exact hpayload item (by simp [hitem]) symbol hsymbol
        have ih' := ih hrestLengths hrestPayload
        simp only [List.flatMap_cons]
        rw [show
          (let packet := encodeUnaryFrame row.1 ++ row.2
           packet ++ [.frameEnd] ++ packet ++ [.frameEnd]) ++ restInput =
            firstRowPrefix ++ (row.2 ++ .frameEnd ::
              (firstRowPrefix ++ row.2 ++ .frameEnd :: restInput)) by
          simp [firstRowPrefix, List.append_assoc]]
        rw [hprefix]
        rw [duplicatedRowRoute_firstPayload fieldCount row.2
          (firstRowPrefix ++ row.2 ++ .frameEnd :: restInput) hrowPayload]
        rw [duplicatedRowRoute_secondRow fieldCount
          (firstRowPrefix ++ row.2)
          restInput hsecondFree]
        rw [show unaryFrameDuplicatedRowRouteInitialMode fieldCount =
            .firstPrefix ⟨0, by omega⟩ by
          simp [unaryFrameDuplicatedRowRouteInitialMode, hpositive]]
        rw [ih']
        simp [firstRowPrefix, List.append_assoc]
  simpa [encodeUnaryFrameDuplicatedRowRouteInput,
    encodeUnaryFrameDuplicatedRowRouteOutput] using
    rowsRun family.rows family.prefix_lengths family.payload_frameEnd_free

/-! ## Concrete streaming machine -/

inductive UnaryFrameDuplicatedRowRouteLabel (fieldCount : Nat)
  | scan (mode : UnaryFrameDuplicatedRowRouteMode fieldCount)
  | emit (mode : UnaryFrameDuplicatedRowRouteMode fieldCount)
      (symbol : UnaryFrameSym)
  | skip (mode : UnaryFrameDuplicatedRowRouteMode fieldCount)
  | finish
deriving DecidableEq, Fintype

def unaryFrameDuplicatedRowRouteTarget (fieldCount : Nat)
    (mode : UnaryFrameDuplicatedRowRouteMode fieldCount)
    (symbol : UnaryFrameSym) :
    UnaryFrameDuplicatedRowRouteLabel fieldCount :=
  match unaryFrameDuplicatedRowRouteAction fieldCount mode symbol with
  | (none, nextMode) => .skip nextMode
  | (some emitted, nextMode) => .emit nextMode emitted

def unaryFrameDuplicatedRowRouteRevProgram (fieldCount : Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameDuplicatedRowRouteLabel fieldCount
  main := .scan (unaryFrameDuplicatedRowRouteInitialMode fieldCount)
  op
    | .scan mode => .popInput .finish fun symbol =>
        unaryFrameDuplicatedRowRouteTarget fieldCount mode symbol
    | .emit mode symbol => .pushOutput symbol (.scan mode)
    | .skip mode => .jump (.scan mode)
    | .finish => .halt

private def unaryFrameDuplicatedRowRouteCfg (fieldCount : Nat)
    (label : UnaryFrameDuplicatedRowRouteLabel fieldCount)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameDuplicatedRowRouteRevProgram fieldCount) :=
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

private def unaryFrameDuplicatedRowRouteLoopCfg (fieldCount : Nat)
    (mode : UnaryFrameDuplicatedRowRouteMode fieldCount)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    BuilderCfg (unaryFrameDuplicatedRowRouteRevProgram fieldCount) :=
  unaryFrameDuplicatedRowRouteCfg fieldCount (.scan mode) buffer input output

private theorem unaryFrameDuplicatedRowRoute_phase_eval
    (fieldCount : Nat) (mode : UnaryFrameDuplicatedRowRouteMode fieldCount)
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    (flip Option.bind
      (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)))^[
        2 * input.length + 1]
      (some (unaryFrameDuplicatedRowRouteLoopCfg
        fieldCount mode buffer input output)) =
      some (unaryFrameDuplicatedRowRouteCfg fieldCount .finish none []
        ((rewriteUnaryFrameDuplicatedRowRouteFrom
          fieldCount mode input).reverse ++ output)) := by
  induction input generalizing mode buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      rcases haction : unaryFrameDuplicatedRowRouteAction
          fieldCount mode symbol with ⟨emitted, nextMode⟩
      cases emitted with
      | none =>
          have htarget : unaryFrameDuplicatedRowRouteTarget
              fieldCount mode symbol = .skip nextMode := by
            simp [unaryFrameDuplicatedRowRouteTarget, haction]
          have hfirst :
              step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
                  (unaryFrameDuplicatedRowRouteLoopCfg fieldCount mode buffer
                    (symbol :: rest) output) =
                some (unaryFrameDuplicatedRowRouteCfg fieldCount
                  (.skip nextMode) (some symbol) rest output) := by
            change some (unaryFrameDuplicatedRowRouteCfg fieldCount
              (unaryFrameDuplicatedRowRouteTarget fieldCount mode symbol)
              (some symbol) rest output) = _
            rw [htarget]
          have hsecond :
              step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
                  (unaryFrameDuplicatedRowRouteCfg fieldCount
                    (.skip nextMode) (some symbol) rest output) =
                some (unaryFrameDuplicatedRowRouteLoopCfg fieldCount nextMode
                  (some symbol) rest output) := by
            rfl
          have hinner :
              flip Option.bind
                  (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
                  (some (unaryFrameDuplicatedRowRouteLoopCfg
                    fieldCount mode buffer (symbol :: rest) output)) =
                some (unaryFrameDuplicatedRowRouteCfg fieldCount
                  (.skip nextMode) (some symbol) rest output) := by
            change step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
              (unaryFrameDuplicatedRowRouteLoopCfg fieldCount mode buffer
                (symbol :: rest) output) = _
            exact hfirst
          have htwo :
              flip Option.bind
                  (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
                (flip Option.bind
                  (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
                  (some (unaryFrameDuplicatedRowRouteLoopCfg
                    fieldCount mode buffer (symbol :: rest) output))) =
                some (unaryFrameDuplicatedRowRouteLoopCfg fieldCount nextMode
                  (some symbol) rest output) := by
            rw [hinner]
            change step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
              (unaryFrameDuplicatedRowRouteCfg fieldCount (.skip nextMode)
                (some symbol) rest output) = _
            exact hsecond
          rw [htwo]
          simpa [rewriteUnaryFrameDuplicatedRowRouteFrom, haction] using
            ih nextMode (some symbol) output
      | some emitted =>
          have htarget : unaryFrameDuplicatedRowRouteTarget
              fieldCount mode symbol = .emit nextMode emitted := by
            simp [unaryFrameDuplicatedRowRouteTarget, haction]
          have hfirst :
              step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
                  (unaryFrameDuplicatedRowRouteLoopCfg fieldCount mode buffer
                    (symbol :: rest) output) =
                some (unaryFrameDuplicatedRowRouteCfg fieldCount
                  (.emit nextMode emitted) (some symbol) rest output) := by
            change some (unaryFrameDuplicatedRowRouteCfg fieldCount
              (unaryFrameDuplicatedRowRouteTarget fieldCount mode symbol)
              (some symbol) rest output) = _
            rw [htarget]
          have hsecond :
              step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
                  (unaryFrameDuplicatedRowRouteCfg fieldCount
                    (.emit nextMode emitted) (some symbol) rest output) =
                some (unaryFrameDuplicatedRowRouteLoopCfg fieldCount nextMode
                  (some symbol) rest (emitted :: output)) := by
            rfl
          have hinner :
              flip Option.bind
                  (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
                  (some (unaryFrameDuplicatedRowRouteLoopCfg
                    fieldCount mode buffer (symbol :: rest) output)) =
                some (unaryFrameDuplicatedRowRouteCfg fieldCount
                  (.emit nextMode emitted) (some symbol) rest output) := by
            change step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
              (unaryFrameDuplicatedRowRouteLoopCfg fieldCount mode buffer
                (symbol :: rest) output) = _
            exact hfirst
          have htwo :
              flip Option.bind
                  (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
                (flip Option.bind
                  (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
                  (some (unaryFrameDuplicatedRowRouteLoopCfg
                    fieldCount mode buffer (symbol :: rest) output))) =
                some (unaryFrameDuplicatedRowRouteLoopCfg fieldCount nextMode
                  (some symbol) rest (emitted :: output)) := by
            rw [hinner]
            change step (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
              (unaryFrameDuplicatedRowRouteCfg fieldCount
                (.emit nextMode emitted) (some symbol) rest output) = _
            exact hsecond
          rw [htwo]
          simpa [rewriteUnaryFrameDuplicatedRowRouteFrom, haction,
            List.reverse_cons, List.append_assoc] using
            ih nextMode (some symbol) (emitted :: output)

def unaryFrameDuplicatedRowRouteSteps (input : List UnaryFrameSym) : Nat :=
  2 * input.length + 2

def unaryFrameDuplicatedRowRouteRev_run
    (fieldCount : Nat) (input : List UnaryFrameSym) :
    EvalsToInTime
      (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
      (initialCfg (unaryFrameDuplicatedRowRouteRevProgram fieldCount) input)
      (some (haltCfg (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
        (rewriteUnaryFrameDuplicatedRowRoute fieldCount input).reverse))
      (unaryFrameDuplicatedRowRouteSteps input) := by
  let beforeHalt := unaryFrameDuplicatedRowRouteCfg fieldCount .finish none []
    (rewriteUnaryFrameDuplicatedRowRoute fieldCount input).reverse
  have hphase := unaryFrameDuplicatedRowRoute_phase_eval fieldCount
    (unaryFrameDuplicatedRowRouteInitialMode fieldCount) none input []
  have hphaseRun : EvalsToInTime
      (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
      (initialCfg (unaryFrameDuplicatedRowRouteRevProgram fieldCount) input)
      (some beforeHalt) (2 * input.length + 1) := by
    refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
    simpa [beforeHalt, initialCfg, unaryFrameDuplicatedRowRouteLoopCfg,
      unaryFrameDuplicatedRowRouteCfg, rewriteUnaryFrameDuplicatedRowRoute,
      unaryFrameDuplicatedRowRouteRevProgram] using hphase
  have hhalt : EvalsToInTime
      (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
      beforeHalt
      (some (haltCfg (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
        (rewriteUnaryFrameDuplicatedRowRoute fieldCount input).reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
    (2 * input.length + 1) 1 _ beforeHalt _ hphaseRun hhalt
  convert full using 1
  simp [unaryFrameDuplicatedRowRouteSteps]
  omega

theorem unaryFrameDuplicatedRowRouteSteps_le
    (input : List UnaryFrameSym) :
    unaryFrameDuplicatedRowRouteSteps input ≤ 2 * input.length + 2 := by
  rfl

noncomputable def unaryFrameDuplicatedRowRouteRev_computableInPolyTime
    (fieldCount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        (rewriteUnaryFrameDuplicatedRowRoute fieldCount input).reverse) where
  tm := compile (unaryFrameDuplicatedRowRouteRevProgram fieldCount)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 2 * Polynomial.X + 2
  outputsFun := fun input => by
    have builderRun := unaryFrameDuplicatedRowRouteRev_run fieldCount input
    have compiledRun := compile_evalsToInTime
      (unaryFrameDuplicatedRowRouteRevProgram fieldCount) builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile (unaryFrameDuplicatedRowRouteRevProgram fieldCount)).step
        (_root_.Turing.initList
          (compile (unaryFrameDuplicatedRowRouteRevProgram fieldCount)) input)
        (some (_root_.Turing.haltList
          (compile (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
          (rewriteUnaryFrameDuplicatedRowRoute fieldCount input).reverse))
        (unaryFrameDuplicatedRowRouteSteps input) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameDuplicatedRowRouteSteps input ≤
        (2 * Polynomial.X + 2).eval input.length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameDuplicatedRowRouteSteps_le input
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile (unaryFrameDuplicatedRowRouteRevProgram fieldCount)).step
        (_root_.Turing.initList
          (compile (unaryFrameDuplicatedRowRouteRevProgram fieldCount)) input)
        (some (_root_.Turing.haltList
          (compile (unaryFrameDuplicatedRowRouteRevProgram fieldCount))
          (rewriteUnaryFrameDuplicatedRowRoute fieldCount input).reverse))
        ((2 * Polynomial.X + 2).eval input.length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

noncomputable def unaryFrameDuplicatedRowRoute_computableInPolyTime
    (fieldCount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameDuplicatedRowRoute fieldCount) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (unaryFrameDuplicatedRowRouteRev_computableInPolyTime fieldCount)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
