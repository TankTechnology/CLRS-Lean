import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRowsFormatCore
import Mathlib.Tactic

/-!
# Formatting triangular pair rows: exact simulation
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private theorem pairRows_replicate_append_cons {alpha : Type}
    (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem pairRows_emitUpper_eval (upper saved : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym) :
    (flip Option.bind (step pairRowsFormatRevProgram))^[3 * upper + 1]
      (some (pairRowsFormatCfg .emitUpper buffer test input output upper saved)) =
      some (pairRowsFormatCfg .restoreUpper buffer false input
        (List.replicate upper CliqueSym.tick ++ output) 0 (saved + upper)) := by
  induction upper generalizing saved test output with
  | zero => rfl
  | succ upper ih =>
      rw [show 3 * (upper + 1) + 1 = (3 * upper + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step pairRowsFormatRevProgram))^[3 * upper + 1]
          (some (pairRowsFormatCfg .emitUpper buffer true input
            (.tick :: output) upper (saved + 1))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_succ, pairRows_replicate_append_cons] using
        ih (saved + 1) true (.tick :: output)

private theorem pairRows_restoreUpper_eval (saved restored : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (input : List UnaryFrameSym) (output : List CliqueSym) :
    (flip Option.bind (step pairRowsFormatRevProgram))^[2 * saved + 1]
      (some (pairRowsFormatCfg .restoreUpper buffer test input output
        restored saved)) =
      some (pairRowsFormatCfg .finishEdge buffer false input output
        (restored + saved) 0) := by
  induction saved generalizing restored test with
  | zero => rfl
  | succ saved ih =>
      rw [show 2 * (saved + 1) + 1 = (2 * saved + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step pairRowsFormatRevProgram))^[2 * saved + 1]
          (some (pairRowsFormatCfg .restoreUpper buffer true input output
            (restored + 1) saved)) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (restored + 1) true

private theorem pairRows_copyLower_eval (remaining : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym)
    (upper saved : Nat) :
    (flip Option.bind (step pairRowsFormatRevProgram))^[2 * remaining + 1]
      (some (pairRowsFormatCfg .copyLower buffer test
        (List.replicate remaining .tick ++ .separator :: tail)
        output upper saved)) =
      some (pairRowsFormatCfg .pushPairSep (some .separator) test tail
        (List.replicate remaining CliqueSym.tick ++ output) upper saved) := by
  induction remaining generalizing buffer output with
  | zero => rfl
  | succ remaining ih =>
      rw [show 2 * (remaining + 1) + 1 =
          (2 * remaining + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step pairRowsFormatRevProgram))^[
            2 * remaining + 1]
          (some (pairRowsFormatCfg .copyLower (some .tick) test
            (List.replicate remaining .tick ++ .separator :: tail)
            (.tick :: output) upper saved)) = _
      simpa [List.replicate_succ, pairRows_replicate_append_cons] using
        ih (some .tick) (.tick :: output)

/-- Exact cost of formatting one lower endpoint in the current row. -/
def pairRowsFormatFieldSteps (lower upper : Nat) : Nat :=
  2 * lower + 5 * upper + 6

private theorem pairRows_prependCliqueTicks_eq (count : Nat)
    (suffix : List CliqueSym) :
    prependCliqueTicks count suffix =
      List.replicate count CliqueSym.tick ++ suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem pairRows_encodeCliqueEdge_reverse (lower upper : Nat) :
    (encodeCliqueEdge (lower, upper)).reverse =
      CliqueSym.recordEnd ::
        (List.replicate upper CliqueSym.tick ++
          CliqueSym.pairSep ::
            (List.replicate lower CliqueSym.tick ++ [.edgeMark])) := by
  simp [encodeCliqueEdge, pairRows_prependCliqueTicks_eq,
    List.reverse_append]

/-- One complete unary lower-endpoint field becomes one reverse-order edge
record while the upper row counter is restored exactly. -/
def pairRowsFormat_fieldRun (lower upper : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    EvalsToInTime (step pairRowsFormatRevProgram)
      (pairRowsFormatCfg .scan buffer test
        (encodeUnaryFrameBlock lower ++ tail) output upper 0)
      (some (pairRowsFormatCfg .scan (some .separator) false tail
        ((encodeCliqueEdge (lower, upper)).reverse ++ output) upper 0))
      (pairRowsFormatFieldSteps lower upper) := by
  cases lower with
  | zero =>
      have hprefix : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .scan buffer test
            (encodeUnaryFrameBlock 0 ++ tail) output upper 0)
          (some (pairRowsFormatCfg .emitUpper (some .separator) test tail
            (.pairSep :: .edgeMark :: output) upper 0)) 3 := by
        exact ⟨⟨3, rfl⟩, le_rfl⟩
      have hupper : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .emitUpper (some .separator) test tail
            (.pairSep :: .edgeMark :: output) upper 0)
          (some (pairRowsFormatCfg .restoreUpper (some .separator) false tail
            (List.replicate upper .tick ++ .pairSep :: .edgeMark :: output)
            0 upper)) (3 * upper + 1) := by
        exact ⟨⟨3 * upper + 1, by
          simpa using pairRows_emitUpper_eval upper 0
            (some .separator) test tail
              (.pairSep :: .edgeMark :: output)⟩, le_rfl⟩
      have hrestore : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .restoreUpper (some .separator) false tail
            (List.replicate upper .tick ++ .pairSep :: .edgeMark :: output)
            0 upper)
          (some (pairRowsFormatCfg .finishEdge (some .separator) false tail
            (List.replicate upper .tick ++ .pairSep :: .edgeMark :: output)
            upper 0)) (2 * upper + 1) := by
        exact ⟨⟨2 * upper + 1, by
          simpa using pairRows_restoreUpper_eval upper 0
            (some .separator) false tail
              (List.replicate upper .tick ++
                .pairSep :: .edgeMark :: output)⟩,
          le_rfl⟩
      have hfinish : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .finishEdge (some .separator) false tail
            (List.replicate upper .tick ++ .pairSep :: .edgeMark :: output)
            upper 0)
          (some (pairRowsFormatCfg .scan (some .separator) false tail
            (.recordEnd :: List.replicate upper .tick ++
              .pairSep :: .edgeMark :: output) upper 0)) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        3 (3 * upper + 1) _ _ _ hprefix hupper
      let h₂ := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        ((3 * upper + 1) + 3) (2 * upper + 1) _ _ _ h₁ hrestore
      let full := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        ((2 * upper + 1) + ((3 * upper + 1) + 3)) 1 _ _ _ h₂ hfinish
      have htime : 1 + (2 * upper + 1 + (3 * upper + 1 + 3)) =
          pairRowsFormatFieldSteps 0 upper := by
        simp [pairRowsFormatFieldSteps]
        omega
      rw [← htime]
      rw [pairRows_encodeCliqueEdge_reverse]
      simpa using full
  | succ lower =>
      have hprefix : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .scan buffer test
            (encodeUnaryFrameBlock (lower + 1) ++ tail) output upper 0)
          (some (pairRowsFormatCfg .copyLower (some .tick) test
            (List.replicate lower .tick ++ .separator :: tail)
            (.tick :: .edgeMark :: output) upper 0)) 3 := by
        have hexplicit : EvalsToInTime (step pairRowsFormatRevProgram)
            (pairRowsFormatCfg .scan buffer test
              (.tick :: List.replicate lower .tick ++ .separator :: tail)
              output upper 0)
            (some (pairRowsFormatCfg .copyLower (some .tick) test
              (List.replicate lower .tick ++ .separator :: tail)
              (.tick :: .edgeMark :: output) upper 0)) 3 :=
          ⟨⟨3, rfl⟩, le_rfl⟩
        simpa [encodeUnaryFrameBlock, List.replicate_succ] using hexplicit
      have hcopy : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .copyLower (some .tick) test
            (List.replicate lower .tick ++ .separator :: tail)
            (.tick :: .edgeMark :: output) upper 0)
          (some (pairRowsFormatCfg .pushPairSep (some .separator) test tail
            (List.replicate lower .tick ++ .tick :: .edgeMark :: output)
            upper 0)) (2 * lower + 1) := by
        exact ⟨⟨2 * lower + 1,
          pairRows_copyLower_eval lower (some .tick) test tail
            (.tick :: .edgeMark :: output) upper 0⟩, le_rfl⟩
      have hpair : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .pushPairSep (some .separator) test tail
            (List.replicate lower .tick ++ .tick :: .edgeMark :: output)
            upper 0)
          (some (pairRowsFormatCfg .emitUpper (some .separator) test tail
            (.pairSep :: (List.replicate lower .tick ++
              (.tick :: .edgeMark :: output))) upper 0)) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hupper : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .emitUpper (some .separator) test tail
            (.pairSep :: (List.replicate lower .tick ++
              (.tick :: .edgeMark :: output))) upper 0)
          (some (pairRowsFormatCfg .restoreUpper (some .separator) false tail
            (List.replicate upper .tick ++
              (.pairSep :: (List.replicate lower .tick ++
                (.tick :: .edgeMark :: output))))
            0 upper)) (3 * upper + 1) := by
        exact ⟨⟨3 * upper + 1, by
          simpa using pairRows_emitUpper_eval upper 0
            (some .separator) test tail
              (.pairSep :: (List.replicate lower .tick ++
                (.tick :: .edgeMark :: output)))⟩, le_rfl⟩
      have hrestore : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .restoreUpper (some .separator) false tail
            (List.replicate upper .tick ++
              (.pairSep :: (List.replicate lower .tick ++
                (.tick :: .edgeMark :: output))))
            0 upper)
          (some (pairRowsFormatCfg .finishEdge (some .separator) false tail
            (List.replicate upper .tick ++
              (.pairSep :: (List.replicate lower .tick ++
                (.tick :: .edgeMark :: output))))
            upper 0)) (2 * upper + 1) := by
        exact ⟨⟨2 * upper + 1, by
          simpa using pairRows_restoreUpper_eval upper 0
            (some .separator) false tail
            (List.replicate upper .tick ++
              (.pairSep :: (List.replicate lower .tick ++
                (.tick :: .edgeMark :: output))))⟩,
          le_rfl⟩
      have hfinish : EvalsToInTime (step pairRowsFormatRevProgram)
          (pairRowsFormatCfg .finishEdge (some .separator) false tail
            (List.replicate upper .tick ++
              (.pairSep :: (List.replicate lower .tick ++
                (.tick :: .edgeMark :: output))))
            upper 0)
          (some (pairRowsFormatCfg .scan (some .separator) false tail
            (.recordEnd :: List.replicate upper .tick ++
              (.pairSep :: (List.replicate lower .tick ++
                (.tick :: .edgeMark :: output))))
            upper 0)) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      let h₁ := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        3 (2 * lower + 1) _ _ _ hprefix hcopy
      let h₂ := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        ((2 * lower + 1) + 3) 1 _ _ _ h₁ hpair
      let h₃ := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        (1 + ((2 * lower + 1) + 3)) (3 * upper + 1) _ _ _ h₂ hupper
      let h₄ := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        ((3 * upper + 1) + (1 + ((2 * lower + 1) + 3)))
          (2 * upper + 1) _ _ _ h₃ hrestore
      let full := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        ((2 * upper + 1) +
          ((3 * upper + 1) + (1 + ((2 * lower + 1) + 3))))
          1 _ _ _ h₄ hfinish
      have htime :
          1 + (2 * upper + 1 +
            (3 * upper + 1 + (1 + (2 * lower + 1 + 3)))) =
          pairRowsFormatFieldSteps (lower + 1) upper := by
        simp [pairRowsFormatFieldSteps]
        omega
      rw [← htime]
      rw [pairRows_encodeCliqueEdge_reverse]
      simpa [List.replicate_succ,
        pairRows_replicate_append_cons] using full

end TMClique
end Turing
end Chapter34
end CLRS
