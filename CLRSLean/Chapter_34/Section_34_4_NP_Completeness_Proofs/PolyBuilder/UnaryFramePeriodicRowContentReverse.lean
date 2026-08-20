import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowOrderReverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Periodic reversal of selected marked-row payloads

This fixed-control transform preserves row order and every `frameEnd` marker,
but reverses the symbols inside selected positions of a fixed row cycle.  The
selection predicate and positive period are compiled into finite control.

The first pass produces the reverse of the requested stream, which matches the
prepend-only output discipline.  The standard verified reverse machine then
restores the forward result.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Advance one position in a positive finite cycle. -/
def unaryFramePeriodicRowContentReverseNext (period : Nat)
    (hpositive : 0 < period) (position : Fin period) : Fin period :=
  if hnext : position.val + 1 < period then
    ⟨position.val + 1, hnext⟩
  else
    ⟨0, hpositive⟩

/-- Row payloads after applying a periodic reversal mask. -/
def unaryFramePeriodicRowContentReverseRowsFrom
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) :
    Fin period → List (List UnaryFrameSym) → List (List UnaryFrameSym)
  | _, [] => []
  | position, row :: rows =>
      (if reverseAt position then row.reverse else row) ::
        unaryFramePeriodicRowContentReverseRowsFrom period hpositive reverseAt
          (unaryFramePeriodicRowContentReverseNext period hpositive position)
          rows

/-- Forward marked-row result of the periodic payload transform. -/
def encodeUnaryFramePeriodicRowContentReverse
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool)
    (family : UnaryFrameMarkedRowFamily) : List UnaryFrameSym :=
  (unaryFramePeriodicRowContentReverseRowsFrom period hpositive reverseAt
      ⟨0, hpositive⟩ family.rows).flatMap fun row =>
        row ++ [.frameEnd]

inductive UnaryFramePeriodicRowContentReverseLabel (period : Nat)
  | scan (position : Fin period)
  | emit (position : Fin period) (symbol : UnaryFrameSym)
  | save (position : Fin period) (symbol : UnaryFrameSym)
  | transfer (position : Fin period)
  | transferEmit (position : Fin period) (symbol : UnaryFrameSym)
  | mark (position : Fin period)
  | finish
deriving DecidableEq, Fintype

/-- Prepend-order first pass.  Unselected rows are copied directly; selected
rows are buffered once, canceling the output-stack reversal for that row. -/
def unaryFramePeriodicRowContentReverseRevProgram
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) : Program UnaryFrameSym UnaryFrameSym where
  Label := UnaryFramePeriodicRowContentReverseLabel period
  main := .scan ⟨0, hpositive⟩
  op
    | .scan position => .popInput .finish fun symbol =>
        if symbol = .frameEnd then .transfer position
        else if reverseAt position then .save position symbol
        else .emit position symbol
    | .emit position symbol => .pushOutput symbol (.scan position)
    | .save position symbol => .pushWork₁ symbol (.scan position)
    | .transfer position =>
        .popWork₁ (.mark position) (.transferEmit position)
    | .transferEmit position symbol =>
        .pushOutput symbol (.transfer position)
    | .mark position => .pushOutput .frameEnd
        (.scan (unaryFramePeriodicRowContentReverseNext
          period hpositive position))
    | .finish => .halt

private def unaryFramePeriodicRowContentReverseCfg
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool)
    (label : UnaryFramePeriodicRowContentReverseLabel period)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym) :
    BuilderCfg
      (unaryFramePeriodicRowContentReverseRevProgram
        period hpositive reverseAt) where
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

private def unaryFramePeriodicRowContentReverseLoopCfg
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) (position : Fin period)
    (input output : List UnaryFrameSym) :
    BuilderCfg
      (unaryFramePeriodicRowContentReverseRevProgram
        period hpositive reverseAt) :=
  unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
    (.scan position) none none false input output [] []

private def periodicRowContentReverseLastBuffer
    (initial : Option UnaryFrameSym) (symbols : List UnaryFrameSym) :
    Option UnaryFrameSym :=
  symbols.foldl (fun _ symbol => some symbol) initial

private theorem periodicRowContentReverse_preserve_scan_eval
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) (position : Fin period)
    (row tail output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (hmask : reverseAt position = false)
    (hfree : ∀ symbol ∈ row, symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind (step
      (unaryFramePeriodicRowContentReverseRevProgram
        period hpositive reverseAt)))^[2 * row.length]
      (some (unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
        (.scan position) buffer₁ buffer₂ test
        (row ++ tail) output [] [])) =
      some (unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
        (.scan position) (periodicRowContentReverseLastBuffer buffer₁ row)
        buffer₂ test tail (row.reverse ++ output) [] []) := by
  induction row generalizing buffer₁ output with
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
      rw [show step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt)
          (unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
            (.scan position) buffer₁ buffer₂ test
            (symbol :: row ++ tail) output [] []) =
          some (unaryFramePeriodicRowContentReverseCfg period hpositive
            reverseAt (.emit position symbol) (some symbol) buffer₂ test
            (row ++ tail) output [] []) by
        simp [step, unaryFramePeriodicRowContentReverseRevProgram,
          unaryFramePeriodicRowContentReverseCfg, stepOp, hsymbol, hmask]]
      simp only [Option.bind_some]
      change
        (flip Option.bind (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt)))^[2 * row.length]
          (some (unaryFramePeriodicRowContentReverseCfg period hpositive
            reverseAt (.scan position) (some symbol) buffer₂ test
            (row ++ tail) (symbol :: output) [] [])) = _
      simpa [periodicRowContentReverseLastBuffer, List.reverse_cons,
        List.append_assoc] using
        ih (buffer₁ := some symbol) (output := symbol :: output) htail

private theorem periodicRowContentReverse_reverse_scan_eval
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) (position : Fin period)
    (row tail output work₁ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (hmask : reverseAt position = true)
    (hfree : ∀ symbol ∈ row, symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind (step
      (unaryFramePeriodicRowContentReverseRevProgram
        period hpositive reverseAt)))^[2 * row.length]
      (some (unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
        (.scan position) buffer₁ buffer₂ test
        (row ++ tail) output work₁ [])) =
      some (unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
        (.scan position) (periodicRowContentReverseLastBuffer buffer₁ row)
        buffer₂ test tail output (row.reverse ++ work₁) []) := by
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
      rw [show step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt)
          (unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
            (.scan position) buffer₁ buffer₂ test
            (symbol :: row ++ tail) output work₁ []) =
          some (unaryFramePeriodicRowContentReverseCfg period hpositive
            reverseAt (.save position symbol) (some symbol) buffer₂ test
            (row ++ tail) output work₁ []) by
        simp [step, unaryFramePeriodicRowContentReverseRevProgram,
          unaryFramePeriodicRowContentReverseCfg, stepOp, hsymbol, hmask]]
      simp only [Option.bind_some]
      change
        (flip Option.bind (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt)))^[2 * row.length]
          (some (unaryFramePeriodicRowContentReverseCfg period hpositive
            reverseAt (.scan position) (some symbol) buffer₂ test
            (row ++ tail) output (symbol :: work₁) [])) = _
      have hrun := ih (buffer₁ := some symbol)
        (work₁ := symbol :: work₁) htail
      simpa [periodicRowContentReverseLastBuffer, List.reverse_cons,
        List.append_assoc] using hrun

private theorem periodicRowContentReverse_transfer_eval
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) (position : Fin period)
    (source input output : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool) :
    (flip Option.bind (step
      (unaryFramePeriodicRowContentReverseRevProgram
        period hpositive reverseAt)))^[2 * source.length + 1]
      (some (unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
        (.transfer position) buffer₁ buffer₂ test input output source [])) =
      some (unaryFramePeriodicRowContentReverseCfg period hpositive reverseAt
        (.mark position) none buffer₂ test input
        (source.reverse ++ output) [] []) := by
  induction source generalizing buffer₁ output with
  | nil => rfl
  | cons symbol source ih =>
      rw [show 2 * (symbol :: source).length + 1 =
          (2 * source.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt)))^[2 * source.length + 1]
          (some (unaryFramePeriodicRowContentReverseCfg period hpositive
            reverseAt (.transfer position) (some symbol) buffer₂ test input
            (symbol :: output) source [])) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (buffer₁ := some symbol) (output := symbol :: output)

/-- Exact execution of one row from one cycle position to the next. -/
private def periodicRowContentReverse_oneRow_run
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) (position : Fin period)
    (row tail output : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd) :
    EvalsToInTime (step
      (unaryFramePeriodicRowContentReverseRevProgram
        period hpositive reverseAt))
      (unaryFramePeriodicRowContentReverseLoopCfg period hpositive reverseAt
        position (row ++ .frameEnd :: tail) output)
      (some (unaryFramePeriodicRowContentReverseLoopCfg period hpositive
        reverseAt
        (unaryFramePeriodicRowContentReverseNext period hpositive position)
        tail
        (((if reverseAt position then row.reverse else row) ++
          [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (2 * row.length +
        (if reverseAt position then 2 * row.length else 0) + 3) := by
  cases hmask : reverseAt position with
  | false =>
      let afterScan := unaryFramePeriodicRowContentReverseCfg period hpositive
        reverseAt (.scan position)
        (periodicRowContentReverseLastBuffer none row) none false
        (.frameEnd :: tail) (row.reverse ++ output) [] []
      let afterBoundary := unaryFramePeriodicRowContentReverseCfg period
        hpositive reverseAt (.transfer position) (some .frameEnd) none false
        tail (row.reverse ++ output) [] []
      let afterTransfer := unaryFramePeriodicRowContentReverseCfg period
        hpositive reverseAt (.mark position) none none false tail
        (row.reverse ++ output) [] []
      have hscan : EvalsToInTime (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt))
          (unaryFramePeriodicRowContentReverseLoopCfg period hpositive
            reverseAt position (row ++ .frameEnd :: tail) output)
          (some afterScan) (2 * row.length) :=
        ⟨⟨2 * row.length, by
          simpa [afterScan, unaryFramePeriodicRowContentReverseLoopCfg] using
            periodicRowContentReverse_preserve_scan_eval period hpositive
              reverseAt position row (.frameEnd :: tail) output none none
              false hmask hfree⟩, le_rfl⟩
      have hboundary : EvalsToInTime (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt))
          afterScan (some afterBoundary) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have htransfer : EvalsToInTime (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt))
          afterBoundary (some afterTransfer) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have hmark : EvalsToInTime (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt))
          afterTransfer
          (some (unaryFramePeriodicRowContentReverseLoopCfg period hpositive
            reverseAt
            (unaryFramePeriodicRowContentReverseNext period hpositive position)
            tail (.frameEnd :: row.reverse ++ output))) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      let first := EvalsToInTime.trans _ _ _ _ afterScan _ hscan hboundary
      let second := EvalsToInTime.trans _ _ _ _ afterBoundary _ first htransfer
      let full := EvalsToInTime.trans _ _ _ _ afterTransfer _ second hmark
      simp only [Bool.false_eq_true, if_false, List.reverse_append,
        List.reverse_singleton, List.singleton_append]
      have hsteps : 1 + (1 + (1 + 2 * row.length)) =
          2 * row.length + 3 := by omega
      rw [← hsteps]
      exact full
  | true =>
      let afterScan := unaryFramePeriodicRowContentReverseCfg period hpositive
        reverseAt (.scan position)
        (periodicRowContentReverseLastBuffer none row) none false
        (.frameEnd :: tail) output row.reverse []
      let afterBoundary := unaryFramePeriodicRowContentReverseCfg period
        hpositive reverseAt (.transfer position) (some .frameEnd) none false
        tail output row.reverse []
      let afterTransfer := unaryFramePeriodicRowContentReverseCfg period
        hpositive reverseAt (.mark position) none none false tail
        (row ++ output) [] []
      have hscan : EvalsToInTime (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt))
          (unaryFramePeriodicRowContentReverseLoopCfg period hpositive
            reverseAt position (row ++ .frameEnd :: tail) output)
          (some afterScan) (2 * row.length) :=
        ⟨⟨2 * row.length, by
          simpa [afterScan, unaryFramePeriodicRowContentReverseLoopCfg] using
            periodicRowContentReverse_reverse_scan_eval period hpositive
              reverseAt position row (.frameEnd :: tail) output [] none none
              false hmask hfree⟩, le_rfl⟩
      have hboundary : EvalsToInTime (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt))
          afterScan (some afterBoundary) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have htransfer : EvalsToInTime (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt))
          afterBoundary (some afterTransfer) (2 * row.length + 1) :=
        ⟨⟨2 * row.length + 1, by
          simpa [afterBoundary, afterTransfer] using
            periodicRowContentReverse_transfer_eval period hpositive reverseAt
              position row.reverse tail output (some .frameEnd) none false⟩,
          le_rfl⟩
      have hmark : EvalsToInTime (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt))
          afterTransfer
          (some (unaryFramePeriodicRowContentReverseLoopCfg period hpositive
            reverseAt
            (unaryFramePeriodicRowContentReverseNext period hpositive position)
            tail (.frameEnd :: row ++ output))) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let first := EvalsToInTime.trans _ _ _ _ afterScan _ hscan hboundary
      let second := EvalsToInTime.trans _ _ _ _ afterBoundary _ first htransfer
      let full := EvalsToInTime.trans _ _ _ _ afterTransfer _ second hmark
      simp only [if_true, List.reverse_append,
        List.reverse_singleton, List.reverse_reverse,
        List.singleton_append]
      have hsteps : 1 + (2 * row.length + 1 + (1 + 2 * row.length)) =
          2 * row.length + 2 * row.length + 3 := by omega
      rw [← hsteps]
      exact full

/-- Exact cost of the prepend-order first pass. -/
def unaryFramePeriodicRowContentReverseStepsFrom
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) :
    Fin period → List (List UnaryFrameSym) → Nat
  | _, [] => 2
  | position, row :: rows =>
      2 * row.length +
        (if reverseAt position then 2 * row.length else 0) + 3 +
      unaryFramePeriodicRowContentReverseStepsFrom period hpositive reverseAt
        (unaryFramePeriodicRowContentReverseNext period hpositive position)
        rows

/-- Exact clean-halt run producing the reverse of the requested stream. -/
def unaryFramePeriodicRowContentReverseRev_run
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool)
    (family : UnaryFrameMarkedRowFamily) :
    EvalsToInTime (step
      (unaryFramePeriodicRowContentReverseRevProgram
        period hpositive reverseAt))
      (initialCfg
        (unaryFramePeriodicRowContentReverseRevProgram
          period hpositive reverseAt)
        (encodeUnaryFrameMarkedRowFamily family))
      (some (haltCfg
        (unaryFramePeriodicRowContentReverseRevProgram
          period hpositive reverseAt)
        (encodeUnaryFramePeriodicRowContentReverse
          period hpositive reverseAt family).reverse))
      (unaryFramePeriodicRowContentReverseStepsFrom period hpositive reverseAt
        ⟨0, hpositive⟩ family.rows) := by
  let rowsRun : ∀ (position : Fin period)
      (rows : List (List UnaryFrameSym))
      (hfree : ∀ row ∈ rows, ∀ symbol ∈ row,
        symbol ≠ UnaryFrameSym.frameEnd)
      (output : List UnaryFrameSym),
      EvalsToInTime (step
        (unaryFramePeriodicRowContentReverseRevProgram
          period hpositive reverseAt))
        (unaryFramePeriodicRowContentReverseLoopCfg period hpositive reverseAt
          position (rows.flatMap fun row => row ++ [.frameEnd]) output)
        (some (haltCfg
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt)
          (((unaryFramePeriodicRowContentReverseRowsFrom period hpositive
            reverseAt position rows).flatMap fun row =>
              row ++ [UnaryFrameSym.frameEnd]).reverse ++ output)))
        (unaryFramePeriodicRowContentReverseStepsFrom period hpositive
          reverseAt position rows) := by
    intro position rows hfree output
    induction rows generalizing position output with
    | nil =>
        have hfinish : EvalsToInTime (step
            (unaryFramePeriodicRowContentReverseRevProgram
              period hpositive reverseAt))
            (unaryFramePeriodicRowContentReverseLoopCfg period hpositive
              reverseAt position [] output)
            (some (haltCfg
              (unaryFramePeriodicRowContentReverseRevProgram
                period hpositive reverseAt) output)) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
        simpa [unaryFramePeriodicRowContentReverseStepsFrom,
          unaryFramePeriodicRowContentReverseLoopCfg,
          unaryFramePeriodicRowContentReverseRowsFrom] using hfinish
    | cons row rows ih =>
        let next := unaryFramePeriodicRowContentReverseNext
          period hpositive position
        let restInput := rows.flatMap fun item => item ++ [.frameEnd]
        let transformedRow := if reverseAt position then row.reverse else row
        have hone := periodicRowContentReverse_oneRow_run period hpositive
          reverseAt position row restInput output
          (fun symbol hsymbol => hfree row (by simp) symbol hsymbol)
        have hrest := ih next
          (fun item hitem symbol hsymbol =>
            hfree item (by simp [hitem]) symbol hsymbol)
          ((transformedRow ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        let full := EvalsToInTime.trans (step
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt)) _ _ _
          (unaryFramePeriodicRowContentReverseLoopCfg period hpositive
            reverseAt next restInput
            ((transformedRow ++ [UnaryFrameSym.frameEnd]).reverse ++ output)) _
          (by simpa [next, restInput, transformedRow] using hone)
          (by simpa [next, restInput, transformedRow] using hrest)
        convert full using 1 <;> simp [
          unaryFramePeriodicRowContentReverseStepsFrom,
          unaryFramePeriodicRowContentReverseRowsFrom,
          List.reverse_append, List.append_assoc] <;> omega
  have run := rowsRun ⟨0, hpositive⟩ family.rows
    family.frameEnd_free []
  have hinitial :
      unaryFramePeriodicRowContentReverseLoopCfg period hpositive reverseAt
          ⟨0, hpositive⟩
          (family.rows.flatMap fun row => row ++ [UnaryFrameSym.frameEnd]) [] =
        initialCfg
          (unaryFramePeriodicRowContentReverseRevProgram
            period hpositive reverseAt)
          (family.rows.flatMap fun row =>
            row ++ [UnaryFrameSym.frameEnd]) := rfl
  rw [hinitial] at run
  simpa [encodeUnaryFrameMarkedRowFamily,
    encodeUnaryFramePeriodicRowContentReverse,
    unaryFramePeriodicRowContentReverseLoopCfg] using run

/-- The first-pass cost is linear in the marked input length. -/
theorem unaryFramePeriodicRowContentReverseStepsFrom_le
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) (position : Fin period)
    (rows : List (List UnaryFrameSym)) :
    unaryFramePeriodicRowContentReverseStepsFrom period hpositive reverseAt
        position rows ≤
      4 * (rows.flatMap fun row => row ++ [.frameEnd]).length + 2 := by
  induction rows generalizing position with
  | nil => simp [unaryFramePeriodicRowContentReverseStepsFrom]
  | cons row rows ih =>
      simp only [unaryFramePeriodicRowContentReverseStepsFrom,
        List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil]
      have hbranch : (if reverseAt position then 2 * row.length else 0) ≤
          2 * row.length := by split <;> omega
      have hrest := ih
        (unaryFramePeriodicRowContentReverseNext period hpositive position)
      omega

/-- The periodic selected-row transform is computed by a concrete fixed
polynomial-time TM2 (linear first pass followed by linear reversal). -/
noncomputable def
    unaryFramePeriodicRowContentReverse_computableInPolyTime
    (period : Nat) (hpositive : 0 < period)
    (reverseAt : Fin period → Bool) :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      (encodeUnaryFramePeriodicRowContentReverse
        period hpositive reverseAt) := by
  let first : _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedRowFamily id
      (fun family : UnaryFrameMarkedRowFamily =>
        (encodeUnaryFramePeriodicRowContentReverse
          period hpositive reverseAt family).reverse) :=
    { tm := compile
        (unaryFramePeriodicRowContentReverseRevProgram
          period hpositive reverseAt)
      inputAlphabet := Equiv.refl _
      outputAlphabet := Equiv.refl _
      time := 4 * Polynomial.X + 2
      outputsFun := fun family => by
        have builderRun := unaryFramePeriodicRowContentReverseRev_run
          period hpositive reverseAt family
        have compiledRun := compile_evalsToInTime _ builderRun
        have htime := unaryFramePeriodicRowContentReverseStepsFrom_le
          period hpositive reverseAt ⟨0, hpositive⟩ family.rows
        have machineRun : _root_.StateTransition.EvalsToInTime
            (compile (unaryFramePeriodicRowContentReverseRevProgram
              period hpositive reverseAt)).step
            (_root_.Turing.initList
              (compile (unaryFramePeriodicRowContentReverseRevProgram
                period hpositive reverseAt))
              (encodeUnaryFrameMarkedRowFamily family))
            (some (_root_.Turing.haltList
              (compile (unaryFramePeriodicRowContentReverseRevProgram
                period hpositive reverseAt))
              (encodeUnaryFramePeriodicRowContentReverse
                period hpositive reverseAt family).reverse))
            (unaryFramePeriodicRowContentReverseStepsFrom period hpositive
              reverseAt ⟨0, hpositive⟩ family.rows) := by
          simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
        have htime' :
            unaryFramePeriodicRowContentReverseStepsFrom period hpositive
                reverseAt ⟨0, hpositive⟩ family.rows ≤
              (4 * Polynomial.X + 2).eval
                (encodeUnaryFrameMarkedRowFamily family).length := by
          simpa only [Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X, Polynomial.eval_ofNat,
            encodeUnaryFrameMarkedRowFamily] using htime
        have boundedRun : _root_.StateTransition.EvalsToInTime
            (compile (unaryFramePeriodicRowContentReverseRevProgram
              period hpositive reverseAt)).step
            (_root_.Turing.initList
              (compile (unaryFramePeriodicRowContentReverseRevProgram
                period hpositive reverseAt))
              (encodeUnaryFrameMarkedRowFamily family))
            (some (_root_.Turing.haltList
              (compile (unaryFramePeriodicRowContentReverseRevProgram
                period hpositive reverseAt))
              (encodeUnaryFramePeriodicRowContentReverse
                period hpositive reverseAt family).reverse))
            ((4 * Polynomial.X + 2).eval
              (encodeUnaryFrameMarkedRowFamily family).length) :=
          ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime'⟩
        simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch first
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
