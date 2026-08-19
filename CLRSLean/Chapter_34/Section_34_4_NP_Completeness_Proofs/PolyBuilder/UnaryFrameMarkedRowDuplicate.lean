import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrame
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Duplicating frame-end-delimited rows

The remaining Cook--Levin validity-row compiler must use the same compact
one-hot payload twice: once for the canonical exactly-one operands and once
for the final-conjunction output-source invocations.  This module supplies a
fixed TM2 which duplicates every `frameEnd`-delimited row without treating
the payload as an oracle-side mathematical value.

The first pass emits the reverse of the duplicated family using the builder's
prepend-only output stack.  The standard verified reversal pass then exposes
the forward duplicated rows.  Every scratch stack is empty at row boundaries.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- A row family whose payloads do not contain the reserved row delimiter. -/
structure UnaryFrameMarkedRowFamily where
  rows : List (List UnaryFrameSym)
  frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row,
    symbol ≠ UnaryFrameSym.frameEnd

/-- Ordinary row-delimited source representation. -/
def encodeUnaryFrameMarkedRowFamily
    (family : UnaryFrameMarkedRowFamily) : List UnaryFrameSym :=
  family.rows.flatMap fun row => row ++ [.frameEnd]

/-- Duplicate every complete marked row, retaining both boundaries. -/
def encodeUnaryFrameDuplicatedMarkedRowFamily
    (family : UnaryFrameMarkedRowFamily) : List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    row ++ [.frameEnd] ++ row ++ [.frameEnd]

/-- Finite phases of the concrete row duplicator. -/
inductive UnaryFrameMarkedRowDuplicateLabel
  | scan
  | emit (symbol : UnaryFrameSym)
  | save (symbol : UnaryFrameSym)
  | firstBoundary
  | transfer
  | duplicate
  | duplicateEmit (symbol : UnaryFrameSym)
  | secondBoundary
  | finish
deriving DecidableEq, Fintype

/-- Prepend-order row duplicator.  The already-emitted first copy is retained
on the output stack while the second copy is reconstructed through the two
work stacks. -/
def unaryFrameMarkedRowDuplicateRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFrameMarkedRowDuplicateLabel
  main := .scan
  op
    | .scan => .popInput .finish fun symbol =>
        if symbol = .frameEnd then .firstBoundary else .emit symbol
    | .emit symbol => .pushOutput symbol (.save symbol)
    | .save symbol => .pushWork₁ symbol .scan
    | .firstBoundary => .pushOutput .frameEnd .transfer
    | .transfer => .moveWork₁Work₂ .duplicate (fun _ => .transfer)
    | .duplicate => .popWork₂ .secondBoundary .duplicateEmit
    | .duplicateEmit symbol => .pushOutput symbol .duplicate
    | .secondBoundary => .pushOutput .frameEnd .scan
    | .finish => .halt

private def unaryFrameMarkedRowDuplicateCfg
    (label : UnaryFrameMarkedRowDuplicateLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowDuplicateRevProgram where
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

/-- Clean public entry at a row boundary. -/
def unaryFrameMarkedRowDuplicateLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg unaryFrameMarkedRowDuplicateRevProgram :=
  unaryFrameMarkedRowDuplicateCfg .scan none none false
    input output [] []

private def markedRowDuplicateLastBuffer
    (initial : Option UnaryFrameSym) (symbols : List UnaryFrameSym) :
    Option UnaryFrameSym :=
  symbols.foldl (fun _ symbol => some symbol) initial

private theorem markedRowDuplicate_scanSymbols_eval
    (symbols tail output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (hfree : ∀ symbol ∈ symbols,
      symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind (step unaryFrameMarkedRowDuplicateRevProgram))^[
      3 * symbols.length]
      (some (unaryFrameMarkedRowDuplicateCfg .scan
        buffer₁ buffer₂ test (symbols ++ tail) output work₁ [])) =
      some (unaryFrameMarkedRowDuplicateCfg .scan
        (markedRowDuplicateLastBuffer buffer₁ symbols) buffer₂ test
        tail (symbols.reverse ++ output) (symbols.reverse ++ work₁) []) := by
  induction symbols generalizing buffer₁ output work₁ with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      rw [show 3 * (symbol :: rest).length = 3 * rest.length + 1 + 1 + 1 by
        simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      simp only [flip, Option.bind_some]
      rw [show step unaryFrameMarkedRowDuplicateRevProgram
          (unaryFrameMarkedRowDuplicateCfg .scan
            buffer₁ buffer₂ test (symbol :: rest ++ tail) output work₁ []) =
          some (unaryFrameMarkedRowDuplicateCfg (.emit symbol)
            (some symbol) buffer₂ test (rest ++ tail) output work₁ []) by
        simp [step, unaryFrameMarkedRowDuplicateRevProgram,
          unaryFrameMarkedRowDuplicateCfg, stepOp, hsymbol]]
      simp only [Option.bind_some]
      change
        (flip Option.bind (step unaryFrameMarkedRowDuplicateRevProgram))^[
          3 * rest.length]
          (some (unaryFrameMarkedRowDuplicateCfg .scan
            (some symbol) buffer₂ test (rest ++ tail)
            (symbol :: output) (symbol :: work₁) [])) = _
      have hrun := ih (output := symbol :: output)
        (work₁ := symbol :: work₁) (buffer₁ := some symbol) hrest
      simpa [markedRowDuplicateLastBuffer, List.reverse_cons,
        List.append_assoc] using hrun

private theorem markedRowDuplicate_transfer_eval
    (source target input output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    (flip Option.bind (step unaryFrameMarkedRowDuplicateRevProgram))^[
      source.length + 1]
      (some (unaryFrameMarkedRowDuplicateCfg .transfer
        buffer₁ buffer₂ test input output source target)) =
      some (unaryFrameMarkedRowDuplicateCfg .duplicate
        none buffer₂ test input output [] (source.reverse ++ target)) := by
  induction source generalizing buffer₁ target with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedRowDuplicateRevProgram))^[
          rest.length + 1]
          (some (unaryFrameMarkedRowDuplicateCfg .transfer
            (some symbol) buffer₂ test input output rest
            (symbol :: target))) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (buffer₁ := some symbol) (target := symbol :: target)

private theorem markedRowDuplicate_duplicate_eval
    (source input output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    (flip Option.bind (step unaryFrameMarkedRowDuplicateRevProgram))^[
      2 * source.length + 1]
      (some (unaryFrameMarkedRowDuplicateCfg .duplicate
        buffer₁ buffer₂ test input output work₁ source)) =
      some (unaryFrameMarkedRowDuplicateCfg .secondBoundary
        buffer₁ none test input (source.reverse ++ output) work₁ []) := by
  induction source generalizing buffer₂ output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step unaryFrameMarkedRowDuplicateRevProgram))^[
          2 * rest.length + 1]
          (some (unaryFrameMarkedRowDuplicateCfg .duplicate
            buffer₁ (some symbol) test input (symbol :: output)
            work₁ rest)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (buffer₂ := some symbol) (output := symbol :: output)

private def unaryFrameMarkedRowDuplicateBoundarySteps (row : List UnaryFrameSym) :
    Nat := 3 * row.length + 5

private def markedRowDuplicate_boundary_run
    (row tail output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    EvalsToInTime (step unaryFrameMarkedRowDuplicateRevProgram)
      (unaryFrameMarkedRowDuplicateCfg .scan
        buffer₁ buffer₂ test (.frameEnd :: tail)
        (row.reverse ++ output) row.reverse [])
      (some (unaryFrameMarkedRowDuplicateCfg .scan
        none none test tail
        ((row ++ [UnaryFrameSym.frameEnd] ++ row ++
          [UnaryFrameSym.frameEnd]).reverse ++ output)
        [] []))
      (unaryFrameMarkedRowDuplicateBoundarySteps row) := by
  let afterPop := unaryFrameMarkedRowDuplicateCfg .firstBoundary
    (some .frameEnd) buffer₂ test tail (row.reverse ++ output) row.reverse []
  let afterFirst := unaryFrameMarkedRowDuplicateCfg .transfer
    (some .frameEnd) buffer₂ test tail
    (.frameEnd :: row.reverse ++ output) row.reverse []
  let afterTransfer := unaryFrameMarkedRowDuplicateCfg .duplicate
    none buffer₂ test tail (.frameEnd :: row.reverse ++ output) [] row
  let afterDuplicate := unaryFrameMarkedRowDuplicateCfg .secondBoundary
    none none test tail
    (row.reverse ++ .frameEnd :: row.reverse ++ output) [] []
  let afterSecond := unaryFrameMarkedRowDuplicateCfg .scan
    none none test tail
    (.frameEnd :: row.reverse ++ .frameEnd :: row.reverse ++ output) [] []
  have hpop : EvalsToInTime (step unaryFrameMarkedRowDuplicateRevProgram)
      (unaryFrameMarkedRowDuplicateCfg .scan
        buffer₁ buffer₂ test (.frameEnd :: tail)
        (row.reverse ++ output) row.reverse [])
      (some afterPop) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hfirst : EvalsToInTime (step unaryFrameMarkedRowDuplicateRevProgram)
      afterPop (some afterFirst) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have htransfer : EvalsToInTime
      (step unaryFrameMarkedRowDuplicateRevProgram)
      afterFirst (some afterTransfer) (row.length + 1) :=
    ⟨⟨row.length + 1, by
      simpa [afterFirst, afterTransfer] using
        markedRowDuplicate_transfer_eval row.reverse [] tail
          (.frameEnd :: row.reverse ++ output) (some .frameEnd) buffer₂ test⟩,
      le_rfl⟩
  have hduplicate : EvalsToInTime
      (step unaryFrameMarkedRowDuplicateRevProgram)
      afterTransfer (some afterDuplicate) (2 * row.length + 1) :=
    ⟨⟨2 * row.length + 1, by
      simpa [afterTransfer, afterDuplicate] using
        markedRowDuplicate_duplicate_eval row tail
          (.frameEnd :: row.reverse ++ output) [] none buffer₂ test⟩,
      le_rfl⟩
  have hsecond : EvalsToInTime (step unaryFrameMarkedRowDuplicateRevProgram)
      afterDuplicate (some afterSecond) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans
    (step unaryFrameMarkedRowDuplicateRevProgram)
    1 1 _ afterPop _ hpop hfirst
  let h₂ := EvalsToInTime.trans
    (step unaryFrameMarkedRowDuplicateRevProgram)
    _ (row.length + 1) _ afterFirst _ h₁ htransfer
  let h₃ := EvalsToInTime.trans
    (step unaryFrameMarkedRowDuplicateRevProgram)
    _ (2 * row.length + 1) _ afterTransfer _ h₂ hduplicate
  let full := EvalsToInTime.trans
    (step unaryFrameMarkedRowDuplicateRevProgram)
    _ 1 _ afterDuplicate _ h₃ hsecond
  have hsteps : 1 + (2 * row.length + 1 + (row.length + 1 + (1 + 1))) =
      unaryFrameMarkedRowDuplicateBoundarySteps row := by
    simp [unaryFrameMarkedRowDuplicateBoundarySteps]
    omega
  simpa [afterSecond, List.reverse_append, List.append_assoc, hsteps] using full

/-- Exact cost of the prepend-order family pass. -/
def unaryFrameMarkedRowDuplicateRevSteps
    (family : UnaryFrameMarkedRowFamily) : Nat :=
  (family.rows.map fun row => 6 * row.length + 5).sum + 2

private def markedRowDuplicate_oneRow_run
    (row tail output : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd) :
    EvalsToInTime (step unaryFrameMarkedRowDuplicateRevProgram)
      (unaryFrameMarkedRowDuplicateLoopCfg
        (row ++ .frameEnd :: tail) output)
      (some (unaryFrameMarkedRowDuplicateLoopCfg tail
        ((row ++ [UnaryFrameSym.frameEnd] ++ row ++
          [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (6 * row.length + 5) := by
  let afterScan := unaryFrameMarkedRowDuplicateCfg .scan
    (markedRowDuplicateLastBuffer none row) none false
    (.frameEnd :: tail) (row.reverse ++ output) row.reverse []
  have hscan : EvalsToInTime
      (step unaryFrameMarkedRowDuplicateRevProgram)
      (unaryFrameMarkedRowDuplicateLoopCfg
        (row ++ .frameEnd :: tail) output)
      (some afterScan) (3 * row.length) :=
    ⟨⟨3 * row.length, by
      simpa [unaryFrameMarkedRowDuplicateLoopCfg, afterScan] using
        markedRowDuplicate_scanSymbols_eval row (.frameEnd :: tail)
          output [] none none false hfree⟩, le_rfl⟩
  have hboundary := markedRowDuplicate_boundary_run row tail output
    (markedRowDuplicateLastBuffer none row) none false
  let full := EvalsToInTime.trans
    (step unaryFrameMarkedRowDuplicateRevProgram)
    (3 * row.length) (unaryFrameMarkedRowDuplicateBoundarySteps row)
    _ afterScan _ hscan (by simpa [afterScan] using hboundary)
  have hsteps : unaryFrameMarkedRowDuplicateBoundarySteps row +
        3 * row.length = 6 * row.length + 5 := by
    simp [unaryFrameMarkedRowDuplicateBoundarySteps]
    omega
  simpa [hsteps, unaryFrameMarkedRowDuplicateLoopCfg] using full

/-- Exact clean-halt run of the prepend-order row duplicator. -/
def unaryFrameMarkedRowDuplicateRev_run
    (family : UnaryFrameMarkedRowFamily) :
    EvalsToInTime (step unaryFrameMarkedRowDuplicateRevProgram)
      (initialCfg unaryFrameMarkedRowDuplicateRevProgram
        (encodeUnaryFrameMarkedRowFamily family))
      (some (haltCfg unaryFrameMarkedRowDuplicateRevProgram
        (encodeUnaryFrameDuplicatedMarkedRowFamily family).reverse))
      (unaryFrameMarkedRowDuplicateRevSteps family) := by
  let familyRun : ∀ (rows : List (List UnaryFrameSym))
      (hfree : ∀ row ∈ rows, ∀ symbol ∈ row,
        symbol ≠ UnaryFrameSym.frameEnd)
      (output : List UnaryFrameSym),
      EvalsToInTime (step unaryFrameMarkedRowDuplicateRevProgram)
        (unaryFrameMarkedRowDuplicateLoopCfg
          (rows.flatMap fun row => row ++ [.frameEnd]) output)
        (some (unaryFrameMarkedRowDuplicateLoopCfg []
          ((rows.flatMap fun row =>
            row ++ [.frameEnd] ++ row ++ [.frameEnd]).reverse ++ output)))
        ((rows.map fun row => 6 * row.length + 5).sum) := by
    intro rows hfree output
    induction rows generalizing output with
    | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
    | cons row rest ih =>
        let restInput := rest.flatMap fun item => item ++ [.frameEnd]
        let rowBlock := row ++ [.frameEnd] ++ row ++ [.frameEnd]
        have hone := markedRowDuplicate_oneRow_run row restInput output
          (fun symbol hsymbol => hfree row (by simp) symbol hsymbol)
        have hrest := ih
          (fun item hitem symbol hsymbol =>
            hfree item (by simp [hitem]) symbol hsymbol)
          (rowBlock.reverse ++ output)
        let full := EvalsToInTime.trans
          (step unaryFrameMarkedRowDuplicateRevProgram)
          (6 * row.length + 5)
          ((rest.map fun item => 6 * item.length + 5).sum)
          _ (unaryFrameMarkedRowDuplicateLoopCfg restInput
              (rowBlock.reverse ++ output)) _
          (by simpa [restInput, rowBlock] using hone)
          (by simpa [restInput, rowBlock] using hrest)
        simpa [restInput, rowBlock, List.reverse_append,
          List.append_assoc, Nat.add_comm] using full
  let rowsRun := familyRun family.rows family.frameEnd_free []
  have hrows : EvalsToInTime
      (step unaryFrameMarkedRowDuplicateRevProgram)
      (unaryFrameMarkedRowDuplicateLoopCfg
        (encodeUnaryFrameMarkedRowFamily family) [])
      (some (unaryFrameMarkedRowDuplicateLoopCfg []
        (encodeUnaryFrameDuplicatedMarkedRowFamily family).reverse))
      ((family.rows.map fun row => 6 * row.length + 5).sum) := by
    simpa [encodeUnaryFrameMarkedRowFamily,
      encodeUnaryFrameDuplicatedMarkedRowFamily] using rowsRun
  have hfinish : EvalsToInTime
      (step unaryFrameMarkedRowDuplicateRevProgram)
      (unaryFrameMarkedRowDuplicateLoopCfg []
        (encodeUnaryFrameDuplicatedMarkedRowFamily family).reverse)
      (some (haltCfg unaryFrameMarkedRowDuplicateRevProgram
        (encodeUnaryFrameDuplicatedMarkedRowFamily family).reverse)) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans
    (step unaryFrameMarkedRowDuplicateRevProgram)
    ((family.rows.map fun row => 6 * row.length + 5).sum) 2
    _ (unaryFrameMarkedRowDuplicateLoopCfg []
      (encodeUnaryFrameDuplicatedMarkedRowFamily family).reverse) _
    hrows hfinish
  have hinitial : unaryFrameMarkedRowDuplicateLoopCfg
      (encodeUnaryFrameMarkedRowFamily family) [] =
      initialCfg unaryFrameMarkedRowDuplicateRevProgram
        (encodeUnaryFrameMarkedRowFamily family) := rfl
  rw [hinitial] at full
  simpa [unaryFrameMarkedRowDuplicateRevSteps,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using full

/-- The concrete first pass is linear in its complete marked input. -/
theorem unaryFrameMarkedRowDuplicateRevSteps_le
    (family : UnaryFrameMarkedRowFamily) :
    unaryFrameMarkedRowDuplicateRevSteps family ≤
      6 * (encodeUnaryFrameMarkedRowFamily family).length + 2 := by
  unfold unaryFrameMarkedRowDuplicateRevSteps
    encodeUnaryFrameMarkedRowFamily
  induction family.rows with
  | nil => simp
  | cons row rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.length_append, List.length_cons, List.length_nil]
      have ih' : (rest.map fun item => 6 * item.length + 5).sum + 2 ≤
          6 * (rest.flatMap fun item => item ++ [.frameEnd]).length + 2 := by
        simpa only using ih
      omega

/-- Compiled prepend-order row duplication. -/
noncomputable def unaryFrameMarkedRowDuplicateRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      (fun family : UnaryFrameMarkedRowFamily =>
        (encodeUnaryFrameDuplicatedMarkedRowFamily family).reverse) where
  tm := compile unaryFrameMarkedRowDuplicateRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X + 2
  outputsFun := fun family => by
    have builderRun := unaryFrameMarkedRowDuplicateRev_run family
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedRowDuplicateRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowDuplicateRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowDuplicateRevProgram)
          (encodeUnaryFrameMarkedRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowDuplicateRevProgram)
          (encodeUnaryFrameDuplicatedMarkedRowFamily family).reverse))
        (unaryFrameMarkedRowDuplicateRevSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : unaryFrameMarkedRowDuplicateRevSteps family ≤
        (6 * Polynomial.X + 2).eval
          (encodeUnaryFrameMarkedRowFamily family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameMarkedRowDuplicateRevSteps_le family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedRowDuplicateRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameMarkedRowDuplicateRevProgram)
          (encodeUnaryFrameMarkedRowFamily family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedRowDuplicateRevProgram)
          (encodeUnaryFrameDuplicatedMarkedRowFamily family).reverse))
        ((6 * Polynomial.X + 2).eval
          (encodeUnaryFrameMarkedRowFamily family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward row duplication, obtained by the standard verified reversal. -/
noncomputable def unaryFrameMarkedRowDuplicate_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      encodeUnaryFrameDuplicatedMarkedRowFamily := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameMarkedRowDuplicateRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
