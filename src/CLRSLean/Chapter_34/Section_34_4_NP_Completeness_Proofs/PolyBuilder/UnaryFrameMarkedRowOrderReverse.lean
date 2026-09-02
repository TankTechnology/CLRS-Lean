import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate
import Mathlib.Tactic

/-!
# Reversing marked-row order while preserving row contents

This linear concrete TM2 reads `frameEnd`-delimited rows from left to right,
buffers one row, and prepends that row unchanged to the output.  The result
reverses only the row order; symbols inside every row remain in their original
order.  This is the ordering primitive needed by the dispatch-mux label
assembler before it processes labels from last to first.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Marked-row encoding with only the row order reversed. -/
def encodeUnaryFrameMarkedRowOrderReverse
    (family : UnaryFrameMarkedRowFamily) : List UnaryFrameSym :=
  family.rows.reverse.flatMap fun row => row ++ [.frameEnd]

inductive UnaryFrameMarkedRowOrderReverseLabel
  | scan
  | save (symbol : UnaryFrameSym)
  | boundary
  | transfer
  | emit (symbol : UnaryFrameSym)
  | finish
deriving DecidableEq, Fintype

/-- One-row scratch program.  `work₁` receives the reversed current row;
transferring it onto the prepend-only output restores the row contents. -/
def unaryFrameMarkedRowOrderReverseProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedRowOrderReverseLabel
  main := .scan
  op
    | .scan => .popInput .finish fun symbol =>
        if symbol = .frameEnd then .boundary else .save symbol
    | .save symbol => .pushWork₁ symbol .scan
    | .boundary => .pushOutput .frameEnd .transfer
    | .transfer => .popWork₁ .scan .emit
    | .emit symbol => .pushOutput symbol .transfer
    | .finish => .halt

private def unaryFrameMarkedRowOrderReverseCfg
    (label : UnaryFrameMarkedRowOrderReverseLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowOrderReverseProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := []
  counter₂ := []
  counter₃ := []

private def unaryFrameMarkedRowOrderReverseLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowOrderReverseProgram :=
  unaryFrameMarkedRowOrderReverseCfg .scan none none false
    input output [] []

private def markedRowOrderReverseLastBuffer
    (initial : Option UnaryFrameSym) (symbols : List UnaryFrameSym) :
    Option UnaryFrameSym :=
  symbols.foldl (fun _ symbol => some symbol) initial

private theorem markedRowOrderReverse_scan_eval
    (row tail output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (hfree : ∀ symbol ∈ row, symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind (step unaryFrameMarkedRowOrderReverseProgram))^[
      2 * row.length]
      (some (unaryFrameMarkedRowOrderReverseCfg .scan
        buffer₁ buffer₂ test (row ++ tail) output work₁ [])) =
      some (unaryFrameMarkedRowOrderReverseCfg .scan
        (markedRowOrderReverseLastBuffer buffer₁ row) buffer₂ test
        tail output (row.reverse ++ work₁) []) := by
  induction row generalizing buffer₁ work₁ with
  | nil => rfl
  | cons symbol row ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hfree symbol (by simp)
      have htail : ∀ item ∈ row,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      rw [show 2 * (symbol :: row).length = 2 * row.length + 1 + 1 by
        simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [flip, Option.bind_some]
      rw [show step unaryFrameMarkedRowOrderReverseProgram
          (unaryFrameMarkedRowOrderReverseCfg .scan
            buffer₁ buffer₂ test (symbol :: row ++ tail) output work₁ []) =
          some (unaryFrameMarkedRowOrderReverseCfg (.save symbol)
            (some symbol) buffer₂ test (row ++ tail) output work₁ []) by
        simp [step, unaryFrameMarkedRowOrderReverseProgram,
          unaryFrameMarkedRowOrderReverseCfg, stepOp, hsymbol]]
      simp only [Option.bind_some]
      change
        (flip Option.bind (step unaryFrameMarkedRowOrderReverseProgram))^[
          2 * row.length]
          (some (unaryFrameMarkedRowOrderReverseCfg .scan
            (some symbol) buffer₂ test (row ++ tail) output
            (symbol :: work₁) [])) = _
      have hrun := ih (buffer₁ := some symbol)
        (work₁ := symbol :: work₁) htail
      simpa [markedRowOrderReverseLastBuffer, List.reverse_cons,
        List.append_assoc] using hrun

private theorem markedRowOrderReverse_transfer_eval
    (source input output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    (flip Option.bind (step unaryFrameMarkedRowOrderReverseProgram))^[
      2 * source.length + 1]
      (some (unaryFrameMarkedRowOrderReverseCfg .transfer
        buffer₁ buffer₂ test input output source [])) =
      some (unaryFrameMarkedRowOrderReverseCfg .scan
        none buffer₂ test input (source.reverse ++ output) [] []) := by
  induction source generalizing buffer₁ output with
  | nil => rfl
  | cons symbol source ih =>
      rw [show 2 * (symbol :: source).length + 1 =
          (2 * source.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedRowOrderReverseProgram))^[
          2 * source.length + 1]
          (some (unaryFrameMarkedRowOrderReverseCfg .transfer
            (some symbol) buffer₂ test input (symbol :: output)
            source [])) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (buffer₁ := some symbol) (output := symbol :: output)

private def markedRowOrderReverse_oneRow_run
    (row tail output : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd) :
    EvalsToInTime (step unaryFrameMarkedRowOrderReverseProgram)
      (unaryFrameMarkedRowOrderReverseLoopCfg
        (row ++ .frameEnd :: tail) output)
      (some (unaryFrameMarkedRowOrderReverseLoopCfg tail
        (row ++ .frameEnd :: output)))
      (4 * row.length + 3) := by
  let afterScan := unaryFrameMarkedRowOrderReverseCfg .scan
    (markedRowOrderReverseLastBuffer none row) none false
    (.frameEnd :: tail) output row.reverse []
  let afterBoundary := unaryFrameMarkedRowOrderReverseCfg .boundary
    (some .frameEnd) none false tail output row.reverse []
  let afterMark := unaryFrameMarkedRowOrderReverseCfg .transfer
    (some .frameEnd) none false tail (.frameEnd :: output) row.reverse []
  have hscan : EvalsToInTime
      (step unaryFrameMarkedRowOrderReverseProgram)
      (unaryFrameMarkedRowOrderReverseLoopCfg
        (row ++ .frameEnd :: tail) output)
      (some afterScan) (2 * row.length) :=
    ⟨⟨2 * row.length, by
      simpa [afterScan, unaryFrameMarkedRowOrderReverseLoopCfg] using
        markedRowOrderReverse_scan_eval row (.frameEnd :: tail)
          output [] none none false hfree⟩, le_rfl⟩
  have hboundary : EvalsToInTime
      (step unaryFrameMarkedRowOrderReverseProgram)
      afterScan (some afterBoundary) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hmark : EvalsToInTime
      (step unaryFrameMarkedRowOrderReverseProgram)
      afterBoundary (some afterMark) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have htransfer : EvalsToInTime
      (step unaryFrameMarkedRowOrderReverseProgram)
      afterMark
      (some (unaryFrameMarkedRowOrderReverseLoopCfg tail
        (row ++ .frameEnd :: output)))
      (2 * row.length + 1) := ⟨⟨2 * row.length + 1, by
        simpa [afterMark, unaryFrameMarkedRowOrderReverseLoopCfg,
          List.append_assoc] using
          markedRowOrderReverse_transfer_eval row.reverse tail
            (.frameEnd :: output) (some .frameEnd) none false⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans
    (step unaryFrameMarkedRowOrderReverseProgram)
    (2 * row.length) 1 _ afterScan _ hscan hboundary
  let h₂ := EvalsToInTime.trans
    (step unaryFrameMarkedRowOrderReverseProgram)
    _ 1 _ afterBoundary _ h₁ hmark
  let full := EvalsToInTime.trans
    (step unaryFrameMarkedRowOrderReverseProgram)
    _ (2 * row.length + 1) _ afterMark _ h₂ htransfer
  convert full using 1 <;> omega

/-- Exact transition count of the row-order reversal pass. -/
def unaryFrameMarkedRowOrderReverseSteps
    (family : UnaryFrameMarkedRowFamily) : Nat :=
  (family.rows.map fun row => 4 * row.length + 3).sum + 2

/-- Exact clean-halt execution of row-order reversal. -/
def unaryFrameMarkedRowOrderReverse_run
    (family : UnaryFrameMarkedRowFamily) :
    EvalsToInTime (step unaryFrameMarkedRowOrderReverseProgram)
      (initialCfg unaryFrameMarkedRowOrderReverseProgram
        (encodeUnaryFrameMarkedRowFamily family))
      (some (haltCfg unaryFrameMarkedRowOrderReverseProgram
        (encodeUnaryFrameMarkedRowOrderReverse family)))
      (unaryFrameMarkedRowOrderReverseSteps family) := by
  let familyRun : ∀ (rows : List (List UnaryFrameSym))
      (hfree : ∀ row ∈ rows, ∀ symbol ∈ row,
        symbol ≠ UnaryFrameSym.frameEnd)
      (output : List UnaryFrameSym),
      EvalsToInTime (step unaryFrameMarkedRowOrderReverseProgram)
        (unaryFrameMarkedRowOrderReverseLoopCfg
          (rows.flatMap fun row => row ++ [.frameEnd]) output)
        (some (unaryFrameMarkedRowOrderReverseLoopCfg []
          ((rows.reverse.flatMap fun row => row ++ [.frameEnd]) ++ output)))
        ((rows.map fun row => 4 * row.length + 3).sum) := by
    intro rows hfree output
    induction rows generalizing output with
    | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
    | cons row rows ih =>
        let restInput := rows.flatMap fun item => item ++ [.frameEnd]
        let rowBlock := row ++ [.frameEnd]
        have hone := markedRowOrderReverse_oneRow_run row restInput output
          (fun symbol hsymbol => hfree row (by simp) symbol hsymbol)
        have hrest := ih
          (fun item hitem symbol hsymbol =>
            hfree item (by simp [hitem]) symbol hsymbol)
          (rowBlock ++ output)
        let full := EvalsToInTime.trans
          (step unaryFrameMarkedRowOrderReverseProgram)
          (4 * row.length + 3)
          ((rows.map fun item => 4 * item.length + 3).sum)
          _ (unaryFrameMarkedRowOrderReverseLoopCfg restInput
            (rowBlock ++ output)) _
          (by simpa [restInput, rowBlock] using hone)
          (by simpa [restInput, rowBlock] using hrest)
        simpa [restInput, rowBlock, List.reverse_cons,
          List.flatMap_append, List.append_assoc, Nat.add_comm] using full
  let rowsRun := familyRun family.rows family.frameEnd_free []
  have hrows : EvalsToInTime
      (step unaryFrameMarkedRowOrderReverseProgram)
      (unaryFrameMarkedRowOrderReverseLoopCfg
        (encodeUnaryFrameMarkedRowFamily family) [])
      (some (unaryFrameMarkedRowOrderReverseLoopCfg []
        (encodeUnaryFrameMarkedRowOrderReverse family)))
      ((family.rows.map fun row => 4 * row.length + 3).sum) := by
    simpa [encodeUnaryFrameMarkedRowFamily,
      encodeUnaryFrameMarkedRowOrderReverse] using rowsRun
  have hfinish : EvalsToInTime
      (step unaryFrameMarkedRowOrderReverseProgram)
      (unaryFrameMarkedRowOrderReverseLoopCfg []
        (encodeUnaryFrameMarkedRowOrderReverse family))
      (some (haltCfg unaryFrameMarkedRowOrderReverseProgram
        (encodeUnaryFrameMarkedRowOrderReverse family))) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step unaryFrameMarkedRowOrderReverseProgram)
    ((family.rows.map fun row => 4 * row.length + 3).sum) 2
    _ (unaryFrameMarkedRowOrderReverseLoopCfg []
      (encodeUnaryFrameMarkedRowOrderReverse family)) _ hrows hfinish
  have hinitial : unaryFrameMarkedRowOrderReverseLoopCfg
      (encodeUnaryFrameMarkedRowFamily family) [] =
      initialCfg unaryFrameMarkedRowOrderReverseProgram
        (encodeUnaryFrameMarkedRowFamily family) := rfl
  rw [hinitial] at full
  simpa [unaryFrameMarkedRowOrderReverseSteps,
    unaryFrameMarkedRowOrderReverseLoopCfg,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using full

/-- The exact cost is linear in the marked input size. -/
theorem unaryFrameMarkedRowOrderReverseSteps_le
    (family : UnaryFrameMarkedRowFamily) :
    unaryFrameMarkedRowOrderReverseSteps family ≤
      4 * (encodeUnaryFrameMarkedRowFamily family).length + 2 := by
  unfold unaryFrameMarkedRowOrderReverseSteps
    encodeUnaryFrameMarkedRowFamily
  induction family.rows with
  | nil => simp
  | cons row rows ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append, List.length_cons, List.length_nil]
      omega

/-- Row-order reversal is computed by one fixed linear-time TM2. -/
noncomputable def unaryFrameMarkedRowOrderReverse_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      encodeUnaryFrameMarkedRowOrderReverse where
  tm := compile unaryFrameMarkedRowOrderReverseProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 2
  outputsFun := fun family => by
    have builderRun := unaryFrameMarkedRowOrderReverse_run family
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedRowOrderReverseProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowOrderReverseProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowOrderReverseProgram)
          (encodeUnaryFrameMarkedRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowOrderReverseProgram)
          (encodeUnaryFrameMarkedRowOrderReverse family)))
        (unaryFrameMarkedRowOrderReverseSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameMarkedRowOrderReverseSteps family ≤
        (4 * Polynomial.X + 2).eval
          (encodeUnaryFrameMarkedRowFamily family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameMarkedRowOrderReverseSteps_le family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowOrderReverseProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowOrderReverseProgram)
          (encodeUnaryFrameMarkedRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowOrderReverseProgram)
          (encodeUnaryFrameMarkedRowOrderReverse family)))
        ((4 * Polynomial.X + 2).eval
          (encodeUnaryFrameMarkedRowFamily family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

end CLRS.Chapter34.Turing.PolyBuilder
