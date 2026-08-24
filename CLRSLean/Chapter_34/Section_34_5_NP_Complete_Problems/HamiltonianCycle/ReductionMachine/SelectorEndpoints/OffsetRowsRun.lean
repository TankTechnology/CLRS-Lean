import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorEndpoints.OffsetRowsCore
import Mathlib.Tactic

/-!
# HAM-CYCLE selector endpoints: generic offset-row simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

open PolyBuilder
open SelectorClique

/-- One arbitrary marked row is formatted while advancing the runtime upper
endpoint exactly once. -/
def offsetMarkedRowRun (values : List Nat) (upper : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    Σ finalTest,
      EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
        (TMClique.pairRowsFormatCfg .scan buffer test
          (encodeUnaryFrame values ++ .frameEnd :: tail)
          output upper 0)
        (some (TMClique.pairRowsFormatCfg .scan (some .frameEnd)
          finalTest tail
          ((values.flatMap fun lower =>
            encodeCliqueEdge (lower, upper)).reverse ++ output)
          (upper + 1) 0))
        (offsetMarkedRowSteps values upper) := by
  rcases valuesRun values upper buffer test (.frameEnd :: tail) output with
    ⟨finalBuffer, finalTest, fields⟩
  let afterFields := TMClique.pairRowsFormatCfg .scan finalBuffer finalTest
    (.frameEnd :: tail)
    ((values.flatMap fun lower =>
      encodeCliqueEdge (lower, upper)).reverse ++ output)
    upper 0
  let afterRow := TMClique.pairRowsFormatCfg .scan (some .frameEnd) finalTest
    tail
    ((values.flatMap fun lower =>
      encodeCliqueEdge (lower, upper)).reverse ++ output)
    (upper + 1) 0
  have advance : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      afterFields (some afterRow) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  refine ⟨finalTest, ?_⟩
  let full := EvalsToInTime.trans
    (step TMClique.pairRowsFormatRevProgram)
    (TMClique.pairRowsFormatValuesSteps values upper) 2
    _ _ _ fields advance
  simpa [afterFields, afterRow, offsetMarkedRowSteps, Nat.add_comm] using full

/-- Exact simulation of an arbitrary marked-row suffix. -/
def offsetMarkedRowsRun (base row : Nat) (rows : List (List Nat))
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    Σ finalBuffer, Σ finalTest,
      EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
        (TMClique.pairRowsFormatCfg .scan buffer test
          (rows.flatMap (fun values =>
            encodeUnaryFrame values ++ [.frameEnd]) ++ tail)
          output (base + row) 0)
        (some (TMClique.pairRowsFormatCfg .scan finalBuffer finalTest tail
          ((offsetRowsEdgeStreamFrom base row rows).reverse ++ output)
          (base + row + rows.length) 0))
        (offsetMarkedRowsSteps base row rows) := by
  induction rows generalizing row buffer test output with
  | nil =>
      exact ⟨buffer, test, ⟨⟨0, by
        simp [offsetRowsEdgeStreamFrom]⟩, le_rfl⟩⟩
  | cons values rows ih =>
      let nextInput := rows.flatMap fun rowValues =>
        encodeUnaryFrame rowValues ++ [.frameEnd]
      rcases offsetMarkedRowRun values (base + row) buffer test
          (nextInput ++ tail) output with
        ⟨rowTest, first⟩
      rcases ih (row + 1) (some .frameEnd) rowTest
          ((values.flatMap fun lower =>
            encodeCliqueEdge (lower, base + row)).reverse ++ output) with
        ⟨finalBuffer, finalTest, remaining⟩
      refine ⟨finalBuffer, finalTest, ?_⟩
      let full := EvalsToInTime.trans
        (step TMClique.pairRowsFormatRevProgram)
        (offsetMarkedRowSteps values (base + row))
        (offsetMarkedRowsSteps base (row + 1) rows)
        _ _ _ first remaining
      simpa [nextInput, offsetRowsEdgeStreamFrom, offsetMarkedRowsSteps,
        List.reverse_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- The shared offset controller accepts every typed arbitrary row family,
not only the triangular selector-clique specialization. -/
def offsetRowsFormatRev_run (family : OffsetRowsFamily) :
    EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (initialCfg offsetPairRowsFormatRevProgram
        (encodeOffsetRowsFamily family))
      (some (haltCfg offsetPairRowsFormatRevProgram
        (offsetRowsEdgeStream family).reverse))
      (offsetRowsFormatRevSteps family) := by
  have load : EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (initialCfg offsetPairRowsFormatRevProgram
        (encodeOffsetRowsFamily family))
      (some (relabelCfg (TMClique.pairRowsFormatCfg .scan
        (some .separator) false
        (family.rows.flatMap fun row =>
          encodeUnaryFrame row ++ [.frameEnd])
        [] family.base 0)))
      (2 * family.base + 1) :=
    ⟨⟨2 * family.base + 1, by
      simpa [initialCfg, offsetPairRowsFormatRevProgram, offsetCfg,
        encodeOffsetRowsFamily, encodeUnaryFrameBlock] using
        loadBase_eval family.base 0 none false
          (family.rows.flatMap fun row =>
            encodeUnaryFrame row ++ [.frameEnd]) []⟩, le_rfl⟩
  rcases offsetMarkedRowsRun family.base 0 family.rows
      (some .separator) false [] [] with
    ⟨finalBuffer, finalTest, rows⟩
  have rowsLifted := lift_run rows
  have rowsLifted' : EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (relabelCfg (TMClique.pairRowsFormatCfg .scan
        (some .separator) false
        (family.rows.flatMap fun row =>
          encodeUnaryFrame row ++ [.frameEnd])
        [] family.base 0))
      (some (relabelCfg (TMClique.pairRowsFormatCfg .scan
        finalBuffer finalTest []
        (offsetRowsEdgeStream family).reverse
        (family.base + family.rows.length) 0)))
      (offsetMarkedRowsSteps family.base 0 family.rows) := by
    simpa [offsetRowsEdgeStream, Nat.add_assoc] using rowsLifted
  let afterScan := TMClique.pairRowsFormatCfg .clearRow none finalTest []
    (offsetRowsEdgeStream family).reverse
    (family.base + family.rows.length) 0
  have scan : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      (TMClique.pairRowsFormatCfg .scan finalBuffer finalTest []
        (offsetRowsEdgeStream family).reverse
        (family.base + family.rows.length) 0)
      (some afterScan) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeHalt := TMClique.pairRowsFormatCfg .halt none false []
    (offsetRowsEdgeStream family).reverse 0 0
  have clear : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      afterScan (some beforeHalt) (family.base + family.rows.length + 1) :=
    ⟨⟨family.base + family.rows.length + 1, by
      simpa [afterScan, beforeHalt] using clearUpper_eval
        (family.base + family.rows.length) none finalTest
        (offsetRowsEdgeStream family).reverse⟩, le_rfl⟩
  have stop : EvalsToInTime (step TMClique.pairRowsFormatRevProgram)
      beforeHalt
      (some (haltCfg TMClique.pairRowsFormatRevProgram
        (offsetRowsEdgeStream family).reverse)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have cleanupCore := EvalsToInTime.trans
    (step TMClique.pairRowsFormatRevProgram) 1
      (family.base + family.rows.length + 1) _ _ _ scan clear
  have cleanupCore' := EvalsToInTime.trans
    (step TMClique.pairRowsFormatRevProgram) _ 1 _ _ _ cleanupCore stop
  have cleanup := lift_run cleanupCore'
  have cleanup' : EvalsToInTime (step offsetPairRowsFormatRevProgram)
      (relabelCfg (TMClique.pairRowsFormatCfg .scan
        finalBuffer finalTest []
        (offsetRowsEdgeStream family).reverse
        (family.base + family.rows.length) 0))
      (some (haltCfg offsetPairRowsFormatRevProgram
        (offsetRowsEdgeStream family).reverse))
      (family.base + family.rows.length + 3) := by
    simpa [relabelCfg, TMClique.pairRowsFormatRevProgram,
      offsetPairRowsFormatRevProgram, haltCfg, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using cleanup
  let throughRows := EvalsToInTime.trans (step offsetPairRowsFormatRevProgram)
    (2 * family.base + 1)
    (offsetMarkedRowsSteps family.base 0 family.rows)
    _ _ _ load rowsLifted'
  let full := EvalsToInTime.trans (step offsetPairRowsFormatRevProgram)
    _ (family.base + family.rows.length + 3) _ _ _ throughRows cleanup'
  refine ⟨full.toEvalsTo, ?_⟩
  exact full.steps_le_m.trans (by
    simp [offsetRowsFormatRevSteps]
    omega)

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints
