import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorClique.Source
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRowsFormat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import Mathlib.Tactic

/-!
# VERTEX-COVER to HAM-CYCLE machine: selector-clique formatter

The established pair-row formatter already knows how to emit one edge per
lower endpoint while retaining a row counter as the upper endpoint.  This
wrapper loads the runtime selector base into that counter once and then runs
the old controller unchanged.  The proof below transports the old exact
field simulation and supplies the shifted row invariant.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorClique

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- Typed source expected by the offset-aware formatter. -/
def offsetPairRowsFormatInput (family : UnaryFrameAffinePrefixRows) :
    List UnaryFrameSym :=
  encodeUnaryFrameBlock family.base ++
    unaryFrameAffinePrefixRowsStream family

/-- Forward selector-pair encoding for one consecutive interval. -/
def offsetCompletePairEdgeStream (base count : Nat) : List CliqueSym :=
  (List.range count).flatMap fun upper =>
    (List.range upper).flatMap fun lower =>
      encodeCliqueEdge (base + lower, base + upper)

/-- Structural relabeling of the already verified pair formatter. -/
private def relabelOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
    Op Γ Δ Λ → Op Γ Δ Μ
  | .pushOutput symbol next => .pushOutput symbol (tag next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (tag next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (tag next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .inc₁ next => .inc₁ (tag next)
  | .inc₂ next => .inc₂ (tag next)
  | .inc₃ next => .inc₃ (tag next)
  | .dec₁ nextZero nextSucc => .dec₁ (tag nextZero) (tag nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (tag nextZero) (tag nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (tag nextZero) (tag nextSucc)
  | .jump next => .jump (tag next)
  | .halt => .halt

inductive OffsetPairRowsLabel
  | loadBase | incBase
  | core (label : TMClique.PairRowsFormatLabel)
deriving DecidableEq, Fintype

/-- Load the unary selector base, then execute the existing formatter. -/
def offsetPairRowsFormatRevProgram : Program UnaryFrameSym CliqueSym where
  Label := OffsetPairRowsLabel
  main := .loadBase
  op
    | .loadBase => .popInput (.core .invalid) fun
        | .tick => .incBase
        | .separator => .core .scan
        | .frameEnd => .core .invalid
    | .incBase => .inc₁ .loadBase
    | .core label => relabelOp .core
        (TMClique.pairRowsFormatRevProgram.op label)

def relabelCfg (c : BuilderCfg TMClique.pairRowsFormatRevProgram) :
    BuilderCfg offsetPairRowsFormatRevProgram where
  label := c.label.map .core
  buffer₁ := c.buffer₁
  buffer₂ := c.buffer₂
  test := c.test
  input := c.input
  output := c.output
  work₁ := c.work₁
  work₂ := c.work₂
  counter₁ := c.counter₁
  counter₂ := c.counter₂
  counter₃ := c.counter₃

def offsetCfg (label : OffsetPairRowsLabel)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym)
    (upper saved : Nat) : BuilderCfg offsetPairRowsFormatRevProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := List.replicate upper ()
  counter₂ := List.replicate saved ()
  counter₃ := []

private theorem relabel_stepOp
    (op : Op UnaryFrameSym CliqueSym TMClique.PairRowsFormatLabel)
    (c : BuilderCfg TMClique.pairRowsFormatRevProgram) :
    stepOp (relabelOp OffsetPairRowsLabel.core op) (relabelCfg c) =
      relabelCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [relabelOp, relabelCfg, stepOp] <;>
    first | rfl | split <;> rfl

private theorem lift_step
    (c : BuilderCfg TMClique.pairRowsFormatRevProgram) :
    step offsetPairRowsFormatRevProgram (relabelCfg c) =
      Option.map relabelCfg (step TMClique.pairRowsFormatRevProgram c) := by
  unfold step
  rw [show (relabelCfg c).label = c.label.map .core by rfl]
  cases hlabel : c.label with
  | none => simp
  | some label =>
      simp only [Option.map_some]
      change some (stepOp
          (relabelOp OffsetPairRowsLabel.core
            (TMClique.pairRowsFormatRevProgram.op label))
          (relabelCfg c)) = _
      exact congrArg some
        (relabel_stepOp (TMClique.pairRowsFormatRevProgram.op label) c)

private theorem iterate_none {σ : Type} (f : σ → Option σ) (n : Nat) :
    (flip Option.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih

private theorem lift_iterations (n : Nat)
    (c : BuilderCfg TMClique.pairRowsFormatRevProgram) :
    (flip Option.bind (step offsetPairRowsFormatRevProgram))^[n]
        (some (relabelCfg c)) =
      Option.map relabelCfg
        ((flip Option.bind (step TMClique.pairRowsFormatRevProgram))^[n]
          (some c)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      change (flip Option.bind (step offsetPairRowsFormatRevProgram))^[n]
          (step offsetPairRowsFormatRevProgram (relabelCfg c)) =
        Option.map relabelCfg
          ((flip Option.bind
            (step TMClique.pairRowsFormatRevProgram))^[n]
              (step TMClique.pairRowsFormatRevProgram c))
      rw [lift_step]
      cases hnext : step TMClique.pairRowsFormatRevProgram c with
      | none =>
          simp only [Option.map_none]
          rw [iterate_none (step offsetPairRowsFormatRevProgram) n,
            iterate_none (step TMClique.pairRowsFormatRevProgram) n]
          rfl
      | some next =>
          simp only [Option.map_some]
          exact ih next

def lift_run {a b : BuilderCfg TMClique.pairRowsFormatRevProgram}
    {bound : Nat}
    (run : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      a (some b) bound) :
    EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (relabelCfg a) (some (relabelCfg b)) bound := by
  refine ⟨⟨run.steps, ?_⟩, run.steps_le_m⟩
  have lifted := lift_iterations run.steps a
  have sourceRun :
      (flip Option.bind
        (step TMClique.pairRowsFormatRevProgram))^[run.steps] (some a) =
        some b := run.evals_in_steps
  rw [sourceRun] at lifted
  exact lifted

theorem loadBase_eval (remaining loaded : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    (flip Option.bind (step offsetPairRowsFormatRevProgram))^[
        2 * remaining + 1]
      (some (offsetCfg .loadBase buffer test
        (List.replicate remaining .tick ++ .separator :: tail)
        output loaded 0)) =
      some (relabelCfg (TMClique.pairRowsFormatCfg .scan
        (some .separator) test tail output (loaded + remaining) 0)) := by
  induction remaining generalizing loaded buffer with
  | zero =>
      change step offsetPairRowsFormatRevProgram
          (offsetCfg .loadBase buffer test (.separator :: tail)
            output loaded 0) =
        some (relabelCfg (TMClique.pairRowsFormatCfg .scan
          (some .separator) test tail output loaded 0))
      rfl
  | succ remaining ih =>
      rw [show 2 * (remaining + 1) + 1 =
          (2 * remaining + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change (flip Option.bind (step offsetPairRowsFormatRevProgram))^[
          2 * remaining + 1]
        (some (offsetCfg .loadBase (some .tick) test
          (List.replicate remaining .tick ++ .separator :: tail)
          output (loaded + 1) 0)) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (loaded + 1) (some .tick)

/-- Shifted edge family for a consecutive interval of row ordinals. -/
def offsetEdgesFrom (base row : Nat) : Nat → List CliqueSym
  | 0 => []
  | count + 1 =>
      ((List.range row).flatMap fun lower =>
        encodeCliqueEdge (base + lower, base + row)) ++
        offsetEdgesFrom base (row + 1) count

/-- Exact formatting cost for one shifted row. -/
def offsetRowSteps (base row : Nat) : Nat :=
  TMClique.pairRowsFormatValuesSteps
    ((List.range row).map (base + ·)) (base + row) + 2

def offsetRowsSteps (base row : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      offsetRowSteps base row + offsetRowsSteps base (row + 1) count

def valuesRun (values : List Nat) (upper : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    Σ finalBuffer, Σ finalTest,
      EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
        (TMClique.pairRowsFormatCfg .scan buffer test
          (encodeUnaryFrame values ++ tail) output upper 0)
        (some (TMClique.pairRowsFormatCfg .scan finalBuffer finalTest tail
          ((values.flatMap fun lower =>
            encodeCliqueEdge (lower, upper)).reverse ++ output) upper 0))
        (TMClique.pairRowsFormatValuesSteps values upper) := by
  induction values generalizing buffer test output with
  | nil =>
      exact ⟨buffer, test,
        ⟨⟨0, by simp [encodeUnaryFrame]⟩, le_rfl⟩⟩
  | cons lower values ih =>
      let first := TMClique.pairRowsFormat_fieldRun lower upper buffer test
        (encodeUnaryFrame values ++ tail) output
      rcases ih (some .separator) false
          ((encodeCliqueEdge (lower, upper)).reverse ++ output) with
        ⟨finalBuffer, finalTest, remaining⟩
      refine ⟨finalBuffer, finalTest, ?_⟩
      let full := EvalsToInTime.trans
        (step TMClique.pairRowsFormatRevProgram)
        (TMClique.pairRowsFormatFieldSteps lower upper)
        (TMClique.pairRowsFormatValuesSteps values upper)
        _ _ _ first remaining
      simpa [encodeUnaryFrame, TMClique.pairRowsFormatValuesSteps,
        List.reverse_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

private def rowRun (base row : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    Σ finalTest,
      EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
        (TMClique.pairRowsFormatCfg .scan buffer test
          (encodeUnaryFrame ((List.range row).map (base + ·)) ++
            .frameEnd :: tail)
          output (base + row) 0)
        (some (TMClique.pairRowsFormatCfg .scan (some .frameEnd)
          finalTest tail
          ((((List.range row).map (base + ·)).flatMap fun lower =>
            encodeCliqueEdge (lower, base + row)).reverse ++ output)
          (base + (row + 1)) 0))
        (offsetRowSteps base row) := by
  rcases valuesRun ((List.range row).map (base + ·)) (base + row)
      buffer test (.frameEnd :: tail) output with
    ⟨finalBuffer, finalTest, fields⟩
  let afterFields := TMClique.pairRowsFormatCfg .scan finalBuffer finalTest
    (.frameEnd :: tail)
    ((((List.range row).map (base + ·)).flatMap fun lower =>
      encodeCliqueEdge (lower, base + row)).reverse ++ output)
    (base + row) 0
  let afterRow := TMClique.pairRowsFormatCfg .scan (some .frameEnd) finalTest
    tail
    ((((List.range row).map (base + ·)).flatMap fun lower =>
      encodeCliqueEdge (lower, base + row)).reverse ++ output)
    ((base + row) + 1) 0
  have advance : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      afterFields (some afterRow) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  refine ⟨finalTest, ?_⟩
  let full := EvalsToInTime.trans
    (step TMClique.pairRowsFormatRevProgram)
    (TMClique.pairRowsFormatValuesSteps
      ((List.range row).map (base + ·)) (base + row)) 2
    _ _ _ fields advance
  simpa [afterFields, afterRow, offsetRowSteps, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using full

private def rowsRun (base row count : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    Σ finalBuffer, Σ finalTest,
      EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
        (TMClique.pairRowsFormatCfg .scan buffer test
          (unaryFrameAffinePrefixRowsStreamFrom (base + row)
            (encodeUnaryFrame ((List.range row).map (base + ·))) count ++ tail)
          output (base + row) 0)
        (some (TMClique.pairRowsFormatCfg .scan finalBuffer finalTest tail
          ((offsetEdgesFrom base row count).reverse ++ output)
          (base + row + count) 0))
        (offsetRowsSteps base row count) := by
  induction count generalizing row buffer test output with
  | zero =>
      exact ⟨buffer, test, ⟨⟨0, by
        simp [unaryFrameAffinePrefixRowsStreamFrom,
          offsetEdgesFrom]⟩, le_rfl⟩⟩
  | succ count ih =>
      let nextInput := unaryFrameAffinePrefixRowsStreamFrom
        (base + (row + 1))
        (encodeUnaryFrame ((List.range (row + 1)).map (base + ·))) count
      rcases rowRun base row buffer test (nextInput ++ tail) output with
        ⟨rowTest, first⟩
      rcases ih (row + 1) (some .frameEnd) rowTest
          ((((List.range row).map (base + ·)).flatMap fun lower =>
            encodeCliqueEdge (lower, base + row)).reverse ++ output) with
        ⟨finalBuffer, finalTest, remaining⟩
      refine ⟨finalBuffer, finalTest, ?_⟩
      let full := EvalsToInTime.trans
        (step TMClique.pairRowsFormatRevProgram)
        (offsetRowSteps base row) (offsetRowsSteps base (row + 1) count)
        _ _ _ first remaining
      simpa [unaryFrameAffinePrefixRowsStreamFrom, nextInput,
        List.range_succ, encodeUnaryFrame, offsetEdgesFrom, offsetRowsSteps,
        List.flatMap_map, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem offsetEdgesFrom_eq (base row count : Nat) :
    offsetEdgesFrom base row count =
      (List.range' row count).flatMap fun upper =>
        (List.range upper).flatMap fun lower =>
          encodeCliqueEdge (base + lower, base + upper) := by
  induction count generalizing row with
  | zero => rfl
  | succ count ih =>
      simp [offsetEdgesFrom, List.range'_succ, ih]

theorem offsetEdgesFrom_zero (base count : Nat) :
    offsetEdgesFrom base 0 count = offsetCompletePairEdgeStream base count := by
  rw [offsetEdgesFrom_eq]
  unfold offsetCompletePairEdgeStream
  rw [List.range_eq_range']

theorem clearUpper_eval (upper : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (output : List CliqueSym) :
    (flip Option.bind (step TMClique.pairRowsFormatRevProgram))^[upper + 1]
      (some (TMClique.pairRowsFormatCfg .clearRow buffer test [] output
        upper 0)) =
      some (TMClique.pairRowsFormatCfg .halt buffer false [] output 0 0) := by
  induction upper generalizing test with
  | zero => rfl
  | succ upper ih =>
      rw [show upper + 1 + 1 = (upper + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change (flip Option.bind
          (step TMClique.pairRowsFormatRevProgram))^[upper + 1]
        (some (TMClique.pairRowsFormatCfg .clearRow buffer true [] output
          upper 0)) = _
      exact ih true

def offsetPairRowsFormatRevSteps (family : UnaryFrameAffinePrefixRows) : Nat :=
  2 * family.base + 1 + offsetRowsSteps family.base 0 family.count +
    (family.base + family.count) + 3

def offsetPairRowsFormatRev_run (family : UnaryFrameAffinePrefixRows) :
    EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (initialCfg offsetPairRowsFormatRevProgram
        (offsetPairRowsFormatInput family))
      (some (haltCfg offsetPairRowsFormatRevProgram
        (offsetCompletePairEdgeStream family.base family.count).reverse))
      (offsetPairRowsFormatRevSteps family) := by
  have hinput : offsetPairRowsFormatInput family =
      encodeUnaryFrameBlock family.base ++
        unaryFrameAffinePrefixRowsStreamFrom family.base
          (encodeUnaryFrame ((List.range 0).map (family.base + ·)))
          family.count := by
    simp [offsetPairRowsFormatInput,
      unaryFrameAffinePrefixRowsStream_eq_from, encodeUnaryFrame]
  have load : EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (initialCfg offsetPairRowsFormatRevProgram
        (offsetPairRowsFormatInput family))
      (some (relabelCfg (TMClique.pairRowsFormatCfg .scan
        (some .separator) false
        (unaryFrameAffinePrefixRowsStreamFrom family.base
          (encodeUnaryFrame ((List.range 0).map (family.base + ·)))
          family.count) [] family.base 0)))
      (2 * family.base + 1) :=
    ⟨⟨2 * family.base + 1, by
      simpa [initialCfg, offsetPairRowsFormatRevProgram, offsetCfg,
        encodeUnaryFrameBlock, hinput] using
        loadBase_eval family.base 0 none false
          (unaryFrameAffinePrefixRowsStreamFrom family.base
            (encodeUnaryFrame ((List.range 0).map (family.base + ·)))
            family.count) []⟩, le_rfl⟩
  rcases rowsRun family.base 0 family.count (some .separator) false [] [] with
    ⟨finalBuffer, finalTest, rows⟩
  have rowsLifted := lift_run rows
  have rowsLifted' : EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (relabelCfg (TMClique.pairRowsFormatCfg .scan
        (some .separator) false
        (unaryFrameAffinePrefixRowsStreamFrom family.base
          (encodeUnaryFrame ((List.range 0).map (family.base + ·)))
          family.count) [] family.base 0))
      (some (relabelCfg (TMClique.pairRowsFormatCfg .scan
        finalBuffer finalTest []
        (offsetCompletePairEdgeStream family.base family.count).reverse
        (family.base + family.count) 0)))
      (offsetRowsSteps family.base 0 family.count) := by
    simpa [offsetEdgesFrom_zero, Nat.add_assoc] using rowsLifted
  let afterScan := TMClique.pairRowsFormatCfg .clearRow none finalTest []
    (offsetCompletePairEdgeStream family.base family.count).reverse
    (family.base + family.count) 0
  have scan : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      (TMClique.pairRowsFormatCfg .scan finalBuffer finalTest []
        (offsetCompletePairEdgeStream family.base family.count).reverse
        (family.base + family.count) 0)
      (some afterScan) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeHalt := TMClique.pairRowsFormatCfg .halt none false []
    (offsetCompletePairEdgeStream family.base family.count).reverse 0 0
  have clear : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      afterScan (some beforeHalt) (family.base + family.count + 1) :=
    ⟨⟨family.base + family.count + 1, by
      simpa [afterScan, beforeHalt] using clearUpper_eval
        (family.base + family.count) none finalTest
        (offsetCompletePairEdgeStream family.base family.count).reverse⟩,
      le_rfl⟩
  have stop : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      beforeHalt
      (some (haltCfg TMClique.pairRowsFormatRevProgram
        (offsetCompletePairEdgeStream family.base family.count).reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have cleanupCore := EvalsToInTime.trans
    (step TMClique.pairRowsFormatRevProgram) 1
      (family.base + family.count + 1) _ _ _ scan clear
  have cleanupCore' := EvalsToInTime.trans
    (step TMClique.pairRowsFormatRevProgram) _ 1 _ _ _ cleanupCore stop
  have cleanup := lift_run cleanupCore'
  have cleanup' : EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (relabelCfg (TMClique.pairRowsFormatCfg .scan finalBuffer finalTest []
        (offsetCompletePairEdgeStream family.base family.count).reverse
        (family.base + family.count) 0))
      (some (haltCfg offsetPairRowsFormatRevProgram
        (offsetCompletePairEdgeStream family.base family.count).reverse))
      (family.base + family.count + 3) := by
    simpa [relabelCfg, TMClique.pairRowsFormatRevProgram,
      offsetPairRowsFormatRevProgram, haltCfg, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using cleanup
  let throughRows := EvalsToInTime.trans (step offsetPairRowsFormatRevProgram)
    (2 * family.base + 1) (offsetRowsSteps family.base 0 family.count)
    _ _ _ load rowsLifted'
  let full := EvalsToInTime.trans (step offsetPairRowsFormatRevProgram)
    _ (family.base + family.count + 3) _ _ _ throughRows cleanup'
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by
    simp [offsetPairRowsFormatRevSteps]
    omega)

private theorem fieldSteps_le {lower upper : Nat} (h : lower < upper) :
    TMClique.pairRowsFormatFieldSteps lower upper ≤ 7 * (upper + 1) := by
  simp [TMClique.pairRowsFormatFieldSteps]
  omega

private theorem valuesSteps_le_general (values : List Nat) (upper : Nat)
    (hvalues : ∀ lower ∈ values, lower < upper) :
    TMClique.pairRowsFormatValuesSteps values upper ≤
      values.length * (7 * (upper + 1)) := by
  induction values with
  | nil => simp [TMClique.pairRowsFormatValuesSteps]
  | cons lower values ih =>
      have hhead := fieldSteps_le (hvalues lower (by simp))
      have htail : ∀ value ∈ values, value < upper := by
        intro value hvalue
        exact hvalues value (by simp [hvalue])
      have hrest := ih htail
      simp only [TMClique.pairRowsFormatValuesSteps, List.map_cons,
        List.sum_cons, List.length_cons]
      calc
        _ ≤ 7 * (upper + 1) + values.length * (7 * (upper + 1)) :=
          Nat.add_le_add hhead hrest
        _ = (values.length + 1) * (7 * (upper + 1)) := by ring

private theorem valuesSteps_le (base row : Nat) :
    TMClique.pairRowsFormatValuesSteps
        ((List.range row).map (base + ·)) (base + row) ≤
      row * (7 * (base + row + 1)) := by
  have h := valuesSteps_le_general
    ((List.range row).map (base + ·)) (base + row) (by
      intro lower hlower
      rw [List.mem_map] at hlower
      rcases hlower with ⟨index, hindex, rfl⟩
      have := List.mem_range.mp hindex
      omega)
  simpa using h

private theorem rowSteps_le (base row : Nat) :
    offsetRowSteps base row ≤ 9 * (base + row + 1) ^ 2 := by
  have h := valuesSteps_le base row
  simp only [offsetRowSteps]
  nlinarith

private theorem rowsSteps_le (base row count : Nat) :
    offsetRowsSteps base row count ≤
      count * (9 * (base + row + count + 1) ^ 2) := by
  induction count generalizing row with
  | zero => simp [offsetRowsSteps]
  | succ count ih =>
      let total := base + row + (count + 1) + 1
      have hrow := rowSteps_le base row
      have hrow' : offsetRowSteps base row ≤ 9 * total ^ 2 :=
        hrow.trans (Nat.mul_le_mul_left 9
          (Nat.pow_le_pow_left (by simp [total]) 2))
      have hrest := ih (row + 1)
      have hrest' : offsetRowsSteps base (row + 1) count ≤
          count * (9 * total ^ 2) := by
        simpa [total, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hrest
      simp only [offsetRowsSteps]
      calc
        _ ≤ 9 * total ^ 2 + count * (9 * total ^ 2) :=
          Nat.add_le_add hrow' hrest'
        _ = (count + 1) * (9 * total ^ 2) := by ring

private theorem rowCount_le_streamFrom (current : Nat)
    (payload : List UnaryFrameSym) (count : Nat) :
    count ≤ (unaryFrameAffinePrefixRowsStreamFrom current payload count).length := by
  induction count generalizing current payload with
  | zero => simp
  | succ count ih =>
      simp only [unaryFrameAffinePrefixRowsStreamFrom, List.length_append,
        List.length_cons, List.length_nil]
      have hrest := ih (current + 1)
        (payload ++ encodeUnaryFrameBlock current)
      omega

theorem base_add_count_le_input_length (family : UnaryFrameAffinePrefixRows) :
    family.base + family.count + 1 ≤
      (offsetPairRowsFormatInput family).length := by
  rw [offsetPairRowsFormatInput, List.length_append,
    unaryFrameAffinePrefixRowsStream_eq_from]
  have hcount := rowCount_le_streamFrom family.base [] family.count
  simp [encodeUnaryFrameBlock]
  omega

theorem offsetPairRowsFormatRevSteps_le_input
    (family : UnaryFrameAffinePrefixRows) :
    offsetPairRowsFormatRevSteps family ≤
      20 * (offsetPairRowsFormatInput family).length ^ 3 + 20 := by
  have hrows := rowsSteps_le family.base 0 family.count
  let n := family.base + family.count + 1
  have hn : 1 ≤ n := by simp [n]
  have hcount : family.count ≤ n := by dsimp [n]; omega
  have hrows' : offsetRowsSteps family.base 0 family.count ≤ 9 * n ^ 3 := by
    calc
      _ ≤ family.count * (9 * n ^ 2) := by simpa [n] using hrows
      _ ≤ n * (9 * n ^ 2) := Nat.mul_le_mul_right _ hcount
      _ = 9 * n ^ 3 := by ring
  have hninput := base_add_count_le_input_length family
  have hcubic := Nat.pow_le_pow_left hninput 3
  simp only [offsetPairRowsFormatRevSteps]
  calc
    _ ≤ 12 * n ^ 3 + 20 := by
      dsimp [n] at hrows' ⊢
      nlinarith [show n ≤ n ^ 3 by
        exact Nat.le_pow (a := n) (by omega)]
    _ ≤ 20 * n ^ 3 + 20 := by omega
    _ ≤ 20 * (offsetPairRowsFormatInput family).length ^ 3 + 20 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 20 hcubic) 20

noncomputable def offsetPairRowsFormatRevComputableInPolyTime :
    TM2ComputableInPolyTime offsetPairRowsFormatInput id
      (fun family =>
        (offsetCompletePairEdgeStream family.base family.count).reverse) where
  tm := compile offsetPairRowsFormatRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * Polynomial.X ^ 3 + 20
  outputsFun := fun family => by
    have builderRun := offsetPairRowsFormatRev_run family
    have compiledRun := compile_evalsToInTime
      offsetPairRowsFormatRevProgram builderRun
    have machineRun : EvalsToInTime
        (compile offsetPairRowsFormatRevProgram).step
        (_root_.Turing.initList (compile offsetPairRowsFormatRevProgram)
          (offsetPairRowsFormatInput family))
        (some (_root_.Turing.haltList (compile offsetPairRowsFormatRevProgram)
          (offsetCompletePairEdgeStream family.base family.count).reverse))
        (offsetPairRowsFormatRevSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : offsetPairRowsFormatRevSteps family ≤
        (20 * Polynomial.X ^ 3 + 20).eval
          (offsetPairRowsFormatInput family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        offsetPairRowsFormatRevSteps_le_input family
    have boundedRun : EvalsToInTime
        (compile offsetPairRowsFormatRevProgram).step
        (_root_.Turing.initList (compile offsetPairRowsFormatRevProgram)
          (offsetPairRowsFormatInput family))
        (some (_root_.Turing.haltList (compile offsetPairRowsFormatRevProgram)
          (offsetCompletePairEdgeStream family.base family.count).reverse))
        ((20 * Polynomial.X ^ 3 + 20).eval
          (offsetPairRowsFormatInput family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward-order fixed formatter. -/
noncomputable def offsetPairRowsFormatComputableInPolyTime :
    TM2ComputableInPolyTime offsetPairRowsFormatInput id
      (fun family => offsetCompletePairEdgeStream family.base family.count) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    offsetPairRowsFormatRevComputableInPolyTime
    (reverse_computableInPolyTime (Γ := CliqueSym))
  simpa only [Function.comp_def, List.reverse_reverse] using
    Classical.choice composed

theorem offsetCompletePairEdgeStream_selectorCliqueEdges
    (edgeCount selectorCount : Nat) :
    offsetCompletePairEdgeStream (selectorBase edgeCount) selectorCount =
      (selectorCliqueEdges edgeCount selectorCount).flatMap encodeCliqueEdge := by
  induction selectorCount with
  | zero => rfl
  | succ selectorCount ih =>
      rw [offsetCompletePairEdgeStream, List.range_succ,
        List.flatMap_append]
      simp only [List.flatMap_singleton]
      change offsetCompletePairEdgeStream (selectorBase edgeCount)
          selectorCount ++ _ = _
      rw [ih, selectorCliqueEdges, List.flatMap_append]
      simp [List.flatMap_map, selectorVertex]

/-- Raw-input selector-clique stream. -/
def stream (input : List CliqueSym) : List CliqueSym :=
  offsetCompletePairEdgeStream (family input).base (family input).count

noncomputable def formatInputAsFamilyComputableInPolyTime :
    TM2ComputableInPolyTime id offsetPairRowsFormatInput family := by
  let raw := formatInputComputableInPolyTime
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        change _root_.Turing.TM2OutputsInTime raw.tm
          (List.map raw.inputAlphabet.invFun input)
          (some (List.map raw.outputAlphabet.invFun
            (offsetPairRowsFormatInput (family input))))
          (raw.time.eval input.length)
        simpa [formatInput, offsetPairRowsFormatInput, baseField_eq, rows,
          family] using raw.outputsFun input }

/-- A fixed polynomial-time TM2 emits all selector-selector edges. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id stream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    formatInputAsFamilyComputableInPolyTime
    offsetPairRowsFormatComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => offsetCompletePairEdgeStream
      (family input).base (family input).count)
  simpa only [Function.comp_def] using Classical.choice composed

theorem stream_encode (I : VertexCoverInstance) :
    stream (encodeVertexCoverInstance I) =
      (selectorCliqueEdges I.edges.length I.targetSize).flatMap
        encodeCliqueEdge := by
  rw [stream, family_encode]
  exact offsetCompletePairEdgeStream_selectorCliqueEdges _ _

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorClique
