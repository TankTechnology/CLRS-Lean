import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowFieldReverseCore
import Mathlib.Tactic

/-!
# Reversing unary fields inside marked rows: exact simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev fieldReverseStep :=
  step unaryFrameMarkedRowFieldReverseRevProgram

private def fieldReverseLastTickBuffer
    (initial : Option UnaryFrameSym) : Nat → Option UnaryFrameSym
  | 0 => initial
  | _ + 1 => some .tick

private theorem fieldReverse_replicate_append_one
    (count : Nat) (symbol : UnaryFrameSym) :
    List.replicate count symbol ++ [symbol] =
      List.replicate (count + 1) symbol := by
  rw [← List.replicate_one, ← List.replicate_add]

private theorem fieldReverse_replicate_comm_cons
    (count : Nat) (symbol : UnaryFrameSym) (tail : List UnaryFrameSym) :
    List.replicate count symbol ++ symbol :: tail =
      symbol :: (List.replicate count symbol ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, ih]

@[simp] private theorem fieldReverseLastTickBuffer_tick (count : Nat) :
    fieldReverseLastTickBuffer (some .tick) count = some .tick := by
  cases count <;> rfl

@[simp] private theorem fieldReverseLastTickBuffer_succ
    (initial : Option UnaryFrameSym) (count : Nat) :
    fieldReverseLastTickBuffer initial (count + 1) = some .tick := by
  cases count <;> rfl

private def fieldReverseLastSeparatorBuffer
    (initial : Option UnaryFrameSym) : List Nat → Option UnaryFrameSym
  | [] => initial
  | _ :: _ => some .separator

private def fieldReverseFinalBuffer₂
    (initial : Option UnaryFrameSym) : List Nat → Option UnaryFrameSym
  | [] => initial
  | _ :: _ => none

@[simp] private theorem fieldReverseLastSeparatorBuffer_separator
    (values : List Nat) :
    fieldReverseLastSeparatorBuffer (some .separator) values =
      some .separator := by
  cases values <;> rfl

@[simp] private theorem fieldReverseFinalBuffer₂_none (values : List Nat) :
    fieldReverseFinalBuffer₂ none values = none := by
  cases values <;> rfl

/-- Scanning a unary tick prefix stores exactly that many pending ticks. -/
private def fieldReverse_scanTicks_run
    (value : Nat) (tail output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseCfg .scan buffer₁ buffer₂ test
        (List.replicate value .tick ++ tail) output work₁ work₂)
      (some (unaryFrameMarkedRowFieldReverseCfg .scan
        (fieldReverseLastTickBuffer buffer₁ value) buffer₂ test tail output
        work₁ (List.replicate value .tick ++ work₂)))
      (2 * value) := by
  induction value generalizing buffer₁ work₂ with
  | zero => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | succ value ih =>
      have hfirst : EvalsToInTime fieldReverseStep
          (unaryFrameMarkedRowFieldReverseCfg .scan buffer₁ buffer₂ test
            (List.replicate (value + 1) .tick ++ tail) output work₁ work₂)
          (some (unaryFrameMarkedRowFieldReverseCfg .scan
            (some .tick) buffer₂ test
            (List.replicate value .tick ++ tail) output work₁
            (.tick :: work₂))) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
      have hrest := ih (buffer₁ := some .tick)
        (work₂ := .tick :: work₂)
      let full := EvalsToInTime.trans fieldReverseStep 2 (2 * value) _ _ _
        hfirst hrest
      have hstack : List.replicate value UnaryFrameSym.tick ++
            .tick :: work₂ =
          List.replicate (value + 1) .tick ++ work₂ := by
        calc
          _ = UnaryFrameSym.tick ::
              (List.replicate value .tick ++ work₂) :=
            fieldReverse_replicate_comm_cons value .tick work₂
          _ = (UnaryFrameSym.tick :: List.replicate value .tick) ++
              work₂ := rfl
          _ = _ := by rw [List.replicate_succ]
      rw [hstack] at full
      rw [fieldReverseLastTickBuffer_tick] at full
      rw [show 2 * value + 2 = 2 * (value + 1) by omega] at full
      simpa [List.replicate_succ] using full

/-- Pending ticks are moved behind the saved separator, rebuilding one
ordinary unary block at the front of `work₁`. -/
private def fieldReverse_moveTicks_run
    (ticks input output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseCfg .moveTicks buffer₁ buffer₂ test
        input output work₁ ticks)
      (some (unaryFrameMarkedRowFieldReverseCfg .scan buffer₁ none test
        input output (List.replicate ticks.length .tick ++ work₁) []))
      (2 * ticks.length + 1) := by
  induction ticks generalizing buffer₂ work₁ with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons symbol ticks ih =>
      have hfirst : EvalsToInTime fieldReverseStep
          (unaryFrameMarkedRowFieldReverseCfg .moveTicks buffer₁ buffer₂ test
            input output work₁ (symbol :: ticks))
          (some (unaryFrameMarkedRowFieldReverseCfg .moveTicks buffer₁
            (some symbol) test input output (.tick :: work₁) ticks)) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      have hrest := ih (buffer₂ := some symbol) (work₁ := .tick :: work₁)
      let full := EvalsToInTime.trans fieldReverseStep 2
        (2 * ticks.length + 1) _ _ _ hfirst hrest
      have hstack : List.replicate ticks.length UnaryFrameSym.tick ++
            .tick :: work₁ =
          List.replicate (ticks.length + 1) .tick ++ work₁ := by
        calc
          _ = UnaryFrameSym.tick ::
              (List.replicate ticks.length .tick ++ work₁) :=
            fieldReverse_replicate_comm_cons ticks.length .tick work₁
          _ = (UnaryFrameSym.tick ::
              List.replicate ticks.length .tick) ++ work₁ := rfl
          _ = _ := by rw [List.replicate_succ]
      rw [hstack] at full
      rw [show 2 * ticks.length + 1 + 2 =
          2 * (ticks.length + 1) + 1 by omega] at full
      simpa using full

/-- One complete unary value is prepended as an intact block to the
partially reversed row. -/
private def fieldReverse_value_run
    (value : Nat) (tail output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseCfg .scan buffer₁ buffer₂ test
        (encodeUnaryFrameBlock value ++ tail) output work₁ [])
      (some (unaryFrameMarkedRowFieldReverseCfg .scan
        (some .separator) none test tail output
        (encodeUnaryFrameBlock value ++ work₁) []))
      (4 * value + 3) := by
  let ticks := List.replicate value UnaryFrameSym.tick
  have hscan := fieldReverse_scanTicks_run value
    (.separator :: tail) output work₁ [] buffer₁ buffer₂ test
  have hseparator : EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseCfg .scan
        (fieldReverseLastTickBuffer buffer₁ value) buffer₂ test
        (.separator :: tail) output work₁ ticks)
      (some (unaryFrameMarkedRowFieldReverseCfg .moveTicks
        (some .separator) buffer₂ test tail output
        (.separator :: work₁) ticks)) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hmove := fieldReverse_moveTicks_run ticks tail output
    (.separator :: work₁) (some .separator) buffer₂ test
  let first := EvalsToInTime.trans fieldReverseStep (2 * value) 2 _ _ _
    (by simpa [ticks] using hscan) hseparator
  let full := EvalsToInTime.trans fieldReverseStep (2 + 2 * value)
    (2 * ticks.length + 1) _ _ _ first hmove
  dsimp only [ticks] at full
  simp only [List.length_replicate] at full
  rw [show 2 * value + 1 + (2 + 2 * value) =
      4 * value + 3 by omega] at full
  simpa [encodeUnaryFrameBlock] using full

/-- Exact cost of building the reversed field list of one row. -/
def unaryFrameMarkedRowFieldReverseBuildSteps : List Nat → Nat
  | [] => 0
  | value :: values =>
      4 * value + 3 + unaryFrameMarkedRowFieldReverseBuildSteps values

/-- All source fields are accumulated in reverse field order on `work₁`. -/
private def fieldReverse_buildRow_run
    (values : List Nat) (tail output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseCfg .scan buffer₁ buffer₂ test
        (encodeUnaryFrame values ++ tail) output work₁ [])
      (some (unaryFrameMarkedRowFieldReverseCfg .scan
        (fieldReverseLastSeparatorBuffer buffer₁ values)
        (fieldReverseFinalBuffer₂ buffer₂ values)
        test tail output
        (encodeUnaryFrame values.reverse ++ work₁) []))
      (unaryFrameMarkedRowFieldReverseBuildSteps values) := by
  induction values generalizing buffer₁ buffer₂ work₁ with
  | nil =>
      change EvalsToInTime fieldReverseStep
        (unaryFrameMarkedRowFieldReverseCfg .scan buffer₁ buffer₂ test
          tail output work₁ [])
        (some (unaryFrameMarkedRowFieldReverseCfg .scan buffer₁ buffer₂ test
          tail output work₁ [])) 0
      exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons value values ih =>
      have hfirst := fieldReverse_value_run value
        (encodeUnaryFrame values ++ tail) output work₁ buffer₁ buffer₂ test
      have hrest := ih (buffer₁ := some .separator) (buffer₂ := none)
        (work₁ := encodeUnaryFrameBlock value ++ work₁)
      let full := EvalsToInTime.trans fieldReverseStep (4 * value + 3)
        (unaryFrameMarkedRowFieldReverseBuildSteps values) _ _ _
        (by simpa [encodeUnaryFrame] using hfirst) hrest
      rw [show unaryFrameMarkedRowFieldReverseBuildSteps values +
          (4 * value + 3) = 4 * value + 3 +
          unaryFrameMarkedRowFieldReverseBuildSteps values by omega] at full
      rw [fieldReverseLastSeparatorBuffer_separator,
        fieldReverseFinalBuffer₂_none] at full
      simpa [fieldReverseLastSeparatorBuffer, fieldReverseFinalBuffer₂,
        unaryFrameMarkedRowFieldReverseBuildSteps, encodeUnaryFrame,
        List.reverse_cons, List.flatMap_append, List.append_assoc] using full

/-- Draining a completed reversed row onto output reverses it once, as
required by the prepend-only first pass. -/
private def fieldReverse_transfer_run
    (source input output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseCfg .transfer buffer₁ buffer₂ test
        input output source [])
      (some (unaryFrameMarkedRowFieldReverseCfg .mark none buffer₂ test
        input (source.reverse ++ output) [] []))
      (2 * source.length + 1) := by
  induction source generalizing buffer₁ output with
  | nil => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons symbol source ih =>
      have hfirst : EvalsToInTime fieldReverseStep
          (unaryFrameMarkedRowFieldReverseCfg .transfer buffer₁ buffer₂ test
            input output (symbol :: source) [])
          (some (unaryFrameMarkedRowFieldReverseCfg .transfer
            (some symbol) buffer₂ test input (symbol :: output) source []))
          2 := ⟨⟨2, rfl⟩, le_rfl⟩
      have hrest := ih (buffer₁ := some symbol) (output := symbol :: output)
      let full := EvalsToInTime.trans fieldReverseStep 2
        (2 * source.length + 1) _ _ _ hfirst hrest
      convert full using 1 <;>
        simp [List.reverse_cons, List.append_assoc] <;> omega

/-- Exact cost of one complete marked value row. -/
def unaryFrameMarkedRowFieldReverseRowSteps (values : List Nat) : Nat :=
  unaryFrameMarkedRowFieldReverseBuildSteps values +
    2 * (encodeUnaryFrame values.reverse).length + 4

/-- One input row becomes the reverse of its field-reversed marked block on
the prepend-only output. -/
private def fieldReverse_oneRow_run
    (values : List Nat) (tail output : List UnaryFrameSym) :
    EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseLoopCfg
        (encodeUnaryFrame values ++ UnaryFrameSym.frameEnd :: tail) output)
      (some (unaryFrameMarkedRowFieldReverseLoopCfg tail
        ((encodeUnaryFrame values.reverse ++
          [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (unaryFrameMarkedRowFieldReverseRowSteps values) := by
  have hbuild := fieldReverse_buildRow_run values
    (UnaryFrameSym.frameEnd :: tail)
    output [] none none false
  let reversedRow := encodeUnaryFrame values.reverse
  have hboundary : EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseCfg .scan
        (fieldReverseLastSeparatorBuffer none values)
        none false (UnaryFrameSym.frameEnd :: tail) output reversedRow [])
      (some (unaryFrameMarkedRowFieldReverseCfg .transfer
        (some .frameEnd) none false tail output reversedRow [])) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  have htransfer := fieldReverse_transfer_run reversedRow tail output
    (some .frameEnd) none false
  have hmark : EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseCfg .mark none none false tail
        (reversedRow.reverse ++ output) [] [])
      (some (unaryFrameMarkedRowFieldReverseLoopCfg tail
        (UnaryFrameSym.frameEnd :: reversedRow.reverse ++ output))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hbuild' : EvalsToInTime fieldReverseStep
      (unaryFrameMarkedRowFieldReverseLoopCfg
        (encodeUnaryFrame values ++ UnaryFrameSym.frameEnd :: tail) output)
      (some (unaryFrameMarkedRowFieldReverseCfg .scan
        (fieldReverseLastSeparatorBuffer none values)
        none false (UnaryFrameSym.frameEnd :: tail) output reversedRow []))
      (unaryFrameMarkedRowFieldReverseBuildSteps values) := by
    rw [fieldReverseFinalBuffer₂_none] at hbuild
    simpa only [unaryFrameMarkedRowFieldReverseLoopCfg,
      List.append_nil] using hbuild
  let first := EvalsToInTime.trans fieldReverseStep
    (unaryFrameMarkedRowFieldReverseBuildSteps values) 2 _ _ _
    hbuild' hboundary
  let second := EvalsToInTime.trans fieldReverseStep
    (2 + unaryFrameMarkedRowFieldReverseBuildSteps values)
    (2 * reversedRow.length + 1) _ _ _ first htransfer
  let full := EvalsToInTime.trans fieldReverseStep
    ((2 * reversedRow.length + 1) +
      (2 + unaryFrameMarkedRowFieldReverseBuildSteps values)) 1 _ _ _
    second hmark
  have hsteps : 1 + ((2 * reversedRow.length + 1) +
        (2 + unaryFrameMarkedRowFieldReverseBuildSteps values)) =
      unaryFrameMarkedRowFieldReverseRowSteps values := by
    unfold unaryFrameMarkedRowFieldReverseRowSteps
    dsimp only [reversedRow]
    omega
  rw [hsteps] at full
  simpa [reversedRow, List.reverse_append, List.append_assoc] using full

/-- Total exact first-pass cost, including the empty-input probe and halt. -/
def unaryFrameMarkedRowFieldReverseSteps : List (List Nat) → Nat
  | [] => 2
  | row :: rows => unaryFrameMarkedRowFieldReverseRowSteps row +
      unaryFrameMarkedRowFieldReverseSteps rows

/-- Exact complete first-pass simulation. -/
def unaryFrameMarkedRowFieldReverseRev_run
    (family : UnaryFrameValueRowFamily) :
    EvalsToInTime fieldReverseStep
      (initialCfg unaryFrameMarkedRowFieldReverseRevProgram
        (encodeUnaryFrameValueRowFamily family))
      (some (haltCfg unaryFrameMarkedRowFieldReverseRevProgram
        (unaryFrameMarkedRowFieldReverseStream family).reverse))
      (unaryFrameMarkedRowFieldReverseSteps family.rows) := by
  let rowsRun : ∀ (rows : List (List Nat)) (output : List UnaryFrameSym),
      EvalsToInTime fieldReverseStep
        (unaryFrameMarkedRowFieldReverseLoopCfg
          ((rows.map encodeUnaryFrame).flatMap
            (fun row => row ++ [UnaryFrameSym.frameEnd])) output)
        (some (haltCfg unaryFrameMarkedRowFieldReverseRevProgram
          (((rows.map fun values => encodeUnaryFrame values.reverse).flatMap
            (fun row => row ++ [UnaryFrameSym.frameEnd])).reverse ++ output)))
        (unaryFrameMarkedRowFieldReverseSteps rows) := by
    intro rows output
    induction rows generalizing output with
    | nil => exact ⟨⟨2, rfl⟩, le_rfl⟩
    | cons row rows ih =>
        have hrow := fieldReverse_oneRow_run row
          ((rows.map encodeUnaryFrame).flatMap
            (fun item => item ++ [UnaryFrameSym.frameEnd])) output
        have hrest := ih
          ((encodeUnaryFrame row.reverse ++ [UnaryFrameSym.frameEnd]).reverse ++
            output)
        let full := EvalsToInTime.trans fieldReverseStep
          (unaryFrameMarkedRowFieldReverseRowSteps row)
          (unaryFrameMarkedRowFieldReverseSteps rows) _ _ _
          (by simpa using hrow) hrest
        rw [show unaryFrameMarkedRowFieldReverseSteps rows +
            unaryFrameMarkedRowFieldReverseRowSteps row =
          unaryFrameMarkedRowFieldReverseRowSteps row +
            unaryFrameMarkedRowFieldReverseSteps rows by omega] at full
        simpa [unaryFrameMarkedRowFieldReverseSteps, List.reverse_append,
          List.append_assoc] using full
  have run := rowsRun family.rows []
  simpa [encodeUnaryFrameValueRowFamily,
    unaryFrameMarkedRowFieldReverseStream,
    UnaryFrameValueRowFamily.marked,
    UnaryFrameValueRowFamily.fieldReversed,
    encodeUnaryFrameMarkedRowFamily,
    unaryFrameMarkedRowFieldReverseLoopCfg, initialCfg,
    unaryFrameMarkedRowFieldReverseCfg,
    unaryFrameMarkedRowFieldReverseRevProgram] using run

end CLRS.Chapter34.Turing.PolyBuilder
