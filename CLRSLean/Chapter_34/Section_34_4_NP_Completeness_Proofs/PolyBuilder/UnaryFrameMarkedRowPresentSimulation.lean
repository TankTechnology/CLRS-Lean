import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowPresentCore
import Mathlib.Tactic

/-!
# Marking every delimited row as present: exact simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev presentStep := step unaryFrameMarkedRowPresentRevProgram

private def presentLastBuffer
    (initial : Option UnaryFrameSym) :
    List UnaryFrameSym → Option UnaryFrameSym :=
  List.foldl (fun _ symbol => some symbol) initial

/-- Copy a `frameEnd`-free payload while remaining inside one row. -/
private def present_scanPayload_run
    (symbols tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym)
    (hfree : ∀ symbol ∈ symbols,
      symbol ≠ UnaryFrameSym.frameEnd) :
    EvalsToInTime presentStep
      (unaryFrameMarkedRowPresentCfg .scan buffer
        (symbols ++ tail) output)
      (some (unaryFrameMarkedRowPresentCfg .scan
        (presentLastBuffer buffer symbols) tail
        (symbols.reverse ++ output)))
      (2 * symbols.length) := by
  induction symbols generalizing buffer output with
  | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      have hfirst : EvalsToInTime presentStep
          (unaryFrameMarkedRowPresentCfg .scan buffer
            (symbol :: rest ++ tail) output)
          (some (unaryFrameMarkedRowPresentCfg .scan (some symbol)
            (rest ++ tail) (symbol :: output))) 2 := by
        cases symbol with
        | tick => exact ⟨⟨2, rfl⟩, le_rfl⟩
        | separator => exact ⟨⟨2, rfl⟩, le_rfl⟩
        | frameEnd => contradiction
      have htail := ih (buffer := some symbol) (output := symbol :: output)
        hrest
      let full := EvalsToInTime.trans presentStep 2 (2 * rest.length) _ _ _
        hfirst htail
      rw [show 2 * rest.length + 2 =
          2 * (symbol :: rest).length by simp; omega] at full
      simpa [presentLastBuffer, List.reverse_cons, List.append_assoc] using full

/-- Consume one complete marked row and return to the next row boundary. -/
private def present_oneRow_run
    (row tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym)
    (hfree : ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd) :
    EvalsToInTime presentStep
      (unaryFrameMarkedRowPresentCfg .beginRow buffer
        (row ++ .frameEnd :: tail) output)
      (some (unaryFrameMarkedRowPresentCfg .beginRow
        (some .frameEnd) tail
        ((UnaryFrameSym.tick :: row ++
          [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (2 * row.length + 3) := by
  cases row with
  | nil => exact ⟨⟨3, rfl⟩, le_rfl⟩
  | cons symbol rest =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      let afterFirst := unaryFrameMarkedRowPresentCfg .scan (some symbol)
        (rest ++ .frameEnd :: tail)
          (symbol :: UnaryFrameSym.tick :: output)
      have hfirst : EvalsToInTime presentStep
          (unaryFrameMarkedRowPresentCfg .beginRow buffer
            (symbol :: rest ++ .frameEnd :: tail) output)
          (some afterFirst) 3 := by
        cases symbol with
        | tick => exact ⟨⟨3, rfl⟩, le_rfl⟩
        | separator => exact ⟨⟨3, rfl⟩, le_rfl⟩
        | frameEnd => contradiction
      have hscan := present_scanPayload_run rest (.frameEnd :: tail)
        (symbol :: UnaryFrameSym.tick :: output) (some symbol) hrest
      let beforeBoundary := unaryFrameMarkedRowPresentCfg .scan
        (presentLastBuffer (some symbol) rest) (.frameEnd :: tail)
        (rest.reverse ++ symbol :: UnaryFrameSym.tick :: output)
      have hboundary : EvalsToInTime presentStep beforeBoundary
          (some (unaryFrameMarkedRowPresentCfg .beginRow
            (some .frameEnd) tail
            (.frameEnd :: rest.reverse ++
              symbol :: UnaryFrameSym.tick :: output))) 2 :=
        ⟨⟨2, rfl⟩, le_rfl⟩
      let first := EvalsToInTime.trans presentStep 3 (2 * rest.length) _
        afterFirst beforeBoundary hfirst (by
          simpa [afterFirst, beforeBoundary] using hscan)
      let full := EvalsToInTime.trans presentStep
        (2 * rest.length + 3) 2 _ beforeBoundary _ first hboundary
      rw [show 2 + (2 * rest.length + 3) =
          2 * (symbol :: rest).length + 3 by simp; omega] at full
      simpa [List.reverse_cons, List.reverse_append,
        List.append_assoc] using full

def unaryFrameMarkedRowPresentRevSteps
    (family : UnaryFrameMarkedRowFamily) : Nat :=
  (family.rows.map fun row => 2 * row.length + 3).sum + 3

/-- Exact clean-halt run of the prepend-order all-present formatter. -/
def unaryFrameMarkedRowPresentRev_run
    (family : UnaryFrameMarkedRowFamily) :
    EvalsToInTime presentStep
      (initialCfg unaryFrameMarkedRowPresentRevProgram
        (encodeUnaryFrameMarkedRowFamily family))
      (some (haltCfg unaryFrameMarkedRowPresentRevProgram
        (encodeUnaryFramePresentMarkedRowFamily family).reverse))
      (unaryFrameMarkedRowPresentRevSteps family) := by
  let rowsRun : ∀ (rows : List (List UnaryFrameSym))
      (hfree : ∀ row ∈ rows, ∀ symbol ∈ row,
        symbol ≠ UnaryFrameSym.frameEnd)
      (buffer : Option UnaryFrameSym) (output : List UnaryFrameSym),
      EvalsToInTime presentStep
        (unaryFrameMarkedRowPresentCfg .beginRow buffer
          (rows.flatMap fun row => row ++ [.frameEnd]) output)
        (some (unaryFrameMarkedRowPresentCfg .beginRow
          (if rows.isEmpty then buffer else some .frameEnd) []
          ((rows.flatMap fun row => .tick :: row ++ [.frameEnd]).reverse ++
            output)))
        ((rows.map fun row => 2 * row.length + 3).sum) := by
    intro rows hfree buffer output
    induction rows generalizing buffer output with
    | nil => exact ⟨⟨0, rfl⟩, le_rfl⟩
    | cons row rest ih =>
        let restInput := rest.flatMap fun item => item ++ [.frameEnd]
        let rowOutput := (UnaryFrameSym.tick :: row ++
          [UnaryFrameSym.frameEnd]).reverse ++ output
        have hone := present_oneRow_run row restInput output buffer
          (fun symbol hsymbol => hfree row (by simp) symbol hsymbol)
        have hrest := ih
          (fun item hitem symbol hsymbol =>
            hfree item (by simp [hitem]) symbol hsymbol)
          (some .frameEnd) rowOutput
        let full := EvalsToInTime.trans presentStep
          (2 * row.length + 3)
          ((rest.map fun item => 2 * item.length + 3).sum) _
          (unaryFrameMarkedRowPresentCfg .beginRow (some .frameEnd)
            restInput rowOutput) _
          (by simpa [restInput, rowOutput] using hone)
          (by simpa [restInput, rowOutput] using hrest)
        simpa [restInput, rowOutput, List.reverse_append,
          List.append_assoc, Nat.add_comm] using full
  have hrows := rowsRun family.rows family.frameEnd_free none []
  let beforeFinal := unaryFrameMarkedRowPresentCfg .beginRow
    (if family.rows.isEmpty then none else some .frameEnd) []
    (family.rows.flatMap
      (fun row => .tick :: row ++ [.frameEnd])).reverse
  have hfinal : EvalsToInTime presentStep beforeFinal
      (some (haltCfg unaryFrameMarkedRowPresentRevProgram
        (encodeUnaryFramePresentMarkedRowFamily family).reverse)) 3 := by
    let body := family.rows.flatMap
      (fun row => UnaryFrameSym.tick :: row ++ [.frameEnd])
    have raw : EvalsToInTime presentStep beforeFinal
        (some (haltCfg unaryFrameMarkedRowPresentRevProgram
          (.frameEnd :: body.reverse))) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
    simpa [encodeUnaryFramePresentMarkedRowFamily, body,
      List.reverse_append] using raw
  let full := EvalsToInTime.trans presentStep
    ((family.rows.map fun row => 2 * row.length + 3).sum) 3 _
    beforeFinal _ (by
      simpa [encodeUnaryFrameMarkedRowFamily, beforeFinal] using hrows)
    hfinal
  simpa [unaryFrameMarkedRowPresentRevSteps,
    encodeUnaryFrameMarkedRowFamily, initialCfg,
    unaryFrameMarkedRowPresentRevProgram,
    unaryFrameMarkedRowPresentCfg, Nat.add_comm] using full

end CLRS.Chapter34.Turing.PolyBuilder
