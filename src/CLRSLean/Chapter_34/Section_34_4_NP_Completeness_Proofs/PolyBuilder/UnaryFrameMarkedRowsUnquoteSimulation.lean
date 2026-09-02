import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowsUnquoteCore
import Mathlib.Tactic

/-!
# Exact simulation of marked-row decoding
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev unquoteStep := step unaryFrameMarkedRowsUnquoteRevProgram

/-- Exact number of controller steps on every marked-row decoder branch. -/
def unaryFrameMarkedRowsUnquoteSteps : List UnaryFrameSym → Nat
  | [] => 2
  | .frameEnd :: tail => 2 + unaryFrameMarkedRowsUnquoteSteps tail
  | [.tick] => 3
  | .tick :: .tick :: rest => 3 + unaryFrameMarkedRowsUnquoteSteps rest
  | .tick :: .separator :: rest => 3 + unaryFrameMarkedRowsUnquoteSteps rest
  | .tick :: .frameEnd :: tail => tail.length + 4
  | [.separator] => 3
  | .separator :: .tick :: rest => 3 + unaryFrameMarkedRowsUnquoteSteps rest
  | .separator :: .separator :: tail => tail.length + 4
  | .separator :: .frameEnd :: tail => tail.length + 4

/-- Draining an ignored suffix clears the input buffer and halts cleanly. -/
private def unaryFrameMarkedRowsUnquote_drain_run
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    EvalsToInTime unquoteStep
      (unaryFrameMarkedRowsUnquoteCfg .drain buffer input output)
      (some (haltCfg unaryFrameMarkedRowsUnquoteRevProgram output))
      (input.length + 2) := by
  induction input generalizing buffer with
  | nil => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | cons symbol rest ih =>
      have hfirst : EvalsToInTime unquoteStep
          (unaryFrameMarkedRowsUnquoteCfg .drain buffer (symbol :: rest) output)
          (some (unaryFrameMarkedRowsUnquoteCfg .drain (some symbol) rest output)) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans unquoteStep 1 (rest.length + 2)
        _ (unaryFrameMarkedRowsUnquoteCfg .drain (some symbol) rest output) _
        hfirst (ih (some symbol))
      convert full using 1 <;> simp <;> omega

/-- Exact contextual run of the marked-row reverse-output decoder. -/
def unaryFrameMarkedRowsUnquoteRev_context
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    EvalsToInTime unquoteStep
      (unaryFrameMarkedRowsUnquoteCfg .scan buffer input output)
      (some (haltCfg unaryFrameMarkedRowsUnquoteRevProgram
        ((unquoteUnaryFrameMarkedRows input).reverse ++ output)))
      (unaryFrameMarkedRowsUnquoteSteps input) := by
  match input with
  | [] => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | [first] =>
      cases first with
      | tick => exact ⟨⟨3, rfl⟩, le_rfl⟩
      | separator => exact ⟨⟨3, rfl⟩, le_rfl⟩
      | frameEnd => exact ⟨⟨4, rfl⟩, le_rfl⟩
  | first :: second :: tail =>
      cases first with
      | frameEnd =>
          have hprefix : EvalsToInTime unquoteStep
              (unaryFrameMarkedRowsUnquoteCfg .scan buffer
                (.frameEnd :: second :: tail) output)
              (some (unaryFrameMarkedRowsUnquoteCfg .scan
                (some .frameEnd) (second :: tail)
                (.frameEnd :: output))) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
          let full := EvalsToInTime.trans unquoteStep 2
            (unaryFrameMarkedRowsUnquoteSteps (second :: tail)) _
            (unaryFrameMarkedRowsUnquoteCfg .scan
              (some .frameEnd) (second :: tail) (.frameEnd :: output)) _
            hprefix (unaryFrameMarkedRowsUnquoteRev_context
              (some .frameEnd) (second :: tail) (.frameEnd :: output))
          convert full using 1 <;>
            simp [unaryFrameMarkedRowsUnquoteSteps,
              unquoteUnaryFrameMarkedRows, List.reverse_cons,
              List.append_assoc] <;> omega
      | tick =>
          cases second with
          | tick =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameMarkedRowsUnquoteCfg .scan buffer
                    (.tick :: .tick :: tail) output)
                  (some (unaryFrameMarkedRowsUnquoteCfg .scan (some .tick) tail
                    (.tick :: output))) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 3
                (unaryFrameMarkedRowsUnquoteSteps tail) _
                (unaryFrameMarkedRowsUnquoteCfg .scan (some .tick) tail
                  (.tick :: output)) _ hprefix
                (unaryFrameMarkedRowsUnquoteRev_context
                  (some .tick) tail (.tick :: output))
              convert full using 1 <;>
                simp [unaryFrameMarkedRowsUnquoteSteps, unquoteUnaryFrameMarkedRows,
                  List.reverse_cons, List.append_assoc] <;> omega
          | separator =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameMarkedRowsUnquoteCfg .scan buffer
                    (.tick :: .separator :: tail) output)
                  (some (unaryFrameMarkedRowsUnquoteCfg .scan (some .separator) tail
                    (.separator :: output))) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 3
                (unaryFrameMarkedRowsUnquoteSteps tail) _
                (unaryFrameMarkedRowsUnquoteCfg .scan (some .separator) tail
                  (.separator :: output)) _ hprefix
                (unaryFrameMarkedRowsUnquoteRev_context
                  (some .separator) tail (.separator :: output))
              convert full using 1 <;>
                simp [unaryFrameMarkedRowsUnquoteSteps, unquoteUnaryFrameMarkedRows,
                  List.reverse_cons, List.append_assoc] <;> omega
          | frameEnd =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameMarkedRowsUnquoteCfg .scan buffer
                    (.tick :: .frameEnd :: tail) output)
                  (some (unaryFrameMarkedRowsUnquoteCfg .drain
                    (some .frameEnd) tail output)) 2 :=
                ⟨⟨2, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 2
                (tail.length + 2) _
                (unaryFrameMarkedRowsUnquoteCfg .drain
                  (some .frameEnd) tail output) _ hprefix
                (unaryFrameMarkedRowsUnquote_drain_run
                  (some .frameEnd) tail output)
              convert full using 1 <;>
                simp [unaryFrameMarkedRowsUnquoteSteps,
                  unquoteUnaryFrameMarkedRows] <;> omega
      | separator =>
          cases second with
          | tick =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameMarkedRowsUnquoteCfg .scan buffer
                    (.separator :: .tick :: tail) output)
                  (some (unaryFrameMarkedRowsUnquoteCfg .scan (some .tick) tail
                    (.frameEnd :: output))) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 3
                (unaryFrameMarkedRowsUnquoteSteps tail) _
                (unaryFrameMarkedRowsUnquoteCfg .scan (some .tick) tail
                  (.frameEnd :: output)) _ hprefix
                (unaryFrameMarkedRowsUnquoteRev_context
                  (some .tick) tail (.frameEnd :: output))
              convert full using 1 <;>
                simp [unaryFrameMarkedRowsUnquoteSteps, unquoteUnaryFrameMarkedRows,
                  List.reverse_cons, List.append_assoc] <;> omega
          | separator =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameMarkedRowsUnquoteCfg .scan buffer
                    (.separator :: .separator :: tail) output)
                  (some (unaryFrameMarkedRowsUnquoteCfg .drain
                    (some .separator) tail output)) 2 :=
                ⟨⟨2, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 2
                (tail.length + 2) _
                (unaryFrameMarkedRowsUnquoteCfg .drain
                  (some .separator) tail output) _ hprefix
                (unaryFrameMarkedRowsUnquote_drain_run
                  (some .separator) tail output)
              convert full using 1 <;>
                simp [unaryFrameMarkedRowsUnquoteSteps,
                  unquoteUnaryFrameMarkedRows] <;> omega
          | frameEnd =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameMarkedRowsUnquoteCfg .scan buffer
                    (.separator :: .frameEnd :: tail) output)
                  (some (unaryFrameMarkedRowsUnquoteCfg .drain
                    (some .frameEnd) tail output)) 2 :=
                ⟨⟨2, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 2
                (tail.length + 2) _
                (unaryFrameMarkedRowsUnquoteCfg .drain
                  (some .frameEnd) tail output) _ hprefix
                (unaryFrameMarkedRowsUnquote_drain_run
                  (some .frameEnd) tail output)
              convert full using 1 <;>
                simp [unaryFrameMarkedRowsUnquoteSteps,
                  unquoteUnaryFrameMarkedRows] <;> omega

termination_by input.length
decreasing_by all_goals simp_wf

/-- Canonical exact decoder run. -/
def unaryFrameMarkedRowsUnquoteRev_run (input : List UnaryFrameSym) :
    EvalsToInTime unquoteStep
      (initialCfg unaryFrameMarkedRowsUnquoteRevProgram input)
      (some (haltCfg unaryFrameMarkedRowsUnquoteRevProgram
        (unquoteUnaryFrameMarkedRows input).reverse))
      (unaryFrameMarkedRowsUnquoteSteps input) := by
  change EvalsToInTime unquoteStep
    (unaryFrameMarkedRowsUnquoteCfg .scan none input []) _ _
  simpa using unaryFrameMarkedRowsUnquoteRev_context none input []

/-- The marked-row decoder is uniformly linear in its physical input length. -/
theorem unaryFrameMarkedRowsUnquoteSteps_le (input : List UnaryFrameSym) :
    unaryFrameMarkedRowsUnquoteSteps input ≤ 3 * input.length + 3 := by
  induction input using unaryFrameMarkedRowsUnquoteSteps.induct <;>
    simp_all [unaryFrameMarkedRowsUnquoteSteps] <;> omega

end CLRS.Chapter34.Turing.PolyBuilder
