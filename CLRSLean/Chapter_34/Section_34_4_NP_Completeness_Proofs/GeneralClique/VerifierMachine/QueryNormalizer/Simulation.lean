import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Basic
import Mathlib.Tactic

/-!
# Query normalization: one-record simulation
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer

open PolyBuilder

set_option maxHeartbeats 1000000

private theorem replicate_append_cons {alpha : Type}
    (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem prependCliqueTicks_eq_replicate (count : Nat)
    (tail : List CliqueSym) :
    prependCliqueTicks count tail = List.replicate count .tick ++ tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [prependCliqueTicks, List.replicate_succ, ih]

private theorem loadLeft_eval (remaining saved : Nat)
    (tail output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool) :
    (flip Option.bind (step revProgram))^[2 * remaining + 1]
      (some (cfg .left buffer test
        (List.replicate remaining .tick ++ .pairSep :: tail)
        output (List.replicate saved ()) [] [])) =
      some (cfg .right (some .pairSep) test tail output
        (List.replicate (saved + remaining) ()) [] []) := by
  induction remaining generalizing saved buffer output with
  | zero => rfl
  | succ remaining ih =>
      rw [show 2 * (remaining + 1) + 1 =
          (2 * remaining + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[2 * remaining + 1]
          (some (cfg .left (some .tick) test
            (List.replicate remaining .tick ++ .pairSep :: tail)
            output (List.replicate (saved + 1) ()) [] [])) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_succ, replicate_append_cons] using
        ih (saved := saved + 1) (buffer := some CliqueSym.tick)
          (output := output)

private theorem loadRight_eval (left remaining saved : Nat)
    (tail output : List CliqueSym) (buffer : Option CliqueSym)
    (test : Bool) :
    (flip Option.bind (step revProgram))^[2 * remaining + 1]
      (some (cfg .right buffer test
        (List.replicate remaining .tick ++ .recordEnd :: tail)
        output (List.replicate left ()) (List.replicate saved ()) [])) =
      some (cfg .compareLeft (some .recordEnd) test tail output
        (List.replicate left ())
        (List.replicate (saved + remaining) ()) []) := by
  induction remaining generalizing saved buffer with
  | zero => rfl
  | succ remaining ih =>
      rw [show 2 * (remaining + 1) + 1 =
          (2 * remaining + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[2 * remaining + 1]
          (some (cfg .right (some .tick) test
            (List.replicate remaining .tick ++ .recordEnd :: tail)
            output (List.replicate left ())
            (List.replicate (saved + 1) ()) [])) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_succ, replicate_append_cons] using
        ih (saved + 1) (some CliqueSym.tick)

private theorem compareLeftLess_eval (matched left extra : Nat)
    (tail output : List CliqueSym) (buffer : Option CliqueSym)
    (test : Bool) :
    (flip Option.bind (step revProgram))^[3 * left + 2]
      (some (cfg .compareLeft buffer test tail output
        (List.replicate left ())
        (List.replicate (left + extra + 1) ())
        (List.replicate matched ()))) =
      some (cfg (.restoreMatched .leftLess) buffer true tail output []
        (List.replicate extra ()) (List.replicate (matched + left) ())) := by
  induction left generalizing matched test with
  | zero =>
      simp [Function.iterate_succ_apply, flip, step, revProgram, cfg,
        stepOp, List.replicate_succ]
  | succ left ih =>
      rw [show left + 1 + extra + 1 =
        (left + extra + 1) + 1 by omega, List.replicate_succ]
      rw [show 3 * (left + 1) + 2 = (3 * left + 2) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[3 * left + 2]
          (some (cfg .compareLeft buffer true tail output
            (List.replicate left ())
            (List.replicate (left + extra + 1) ())
            (List.replicate (matched + 1) ()))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (matched + 1) true

private theorem compareEqual_eval (matched value : Nat)
    (tail output : List CliqueSym) (buffer : Option CliqueSym)
    (test : Bool) :
    (flip Option.bind (step revProgram))^[3 * value + 2]
      (some (cfg .compareLeft buffer test tail output
        (List.replicate value ()) (List.replicate value ())
        (List.replicate matched ()))) =
      some (cfg (.restoreMatched .equal) buffer false tail output [] []
        (List.replicate (matched + value) ())) := by
  induction value generalizing matched test with
  | zero => rfl
  | succ value ih =>
      simp only [List.replicate_succ]
      rw [show 3 * (value + 1) + 2 = (3 * value + 2) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[3 * value + 2]
          (some (cfg .compareLeft buffer true tail output
            (List.replicate value ()) (List.replicate value ())
            (List.replicate (matched + 1) ()))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (matched + 1) true

private theorem compareRightLess_eval (matched right extra : Nat)
    (tail output : List CliqueSym) (buffer : Option CliqueSym)
    (test : Bool) :
    (flip Option.bind (step revProgram))^[3 * right + 2]
      (some (cfg .compareLeft buffer test tail output
        (List.replicate (right + extra + 1) ())
        (List.replicate right ()) (List.replicate matched ()))) =
      some (cfg (.restoreMatched .rightLess) buffer false tail output
        (List.replicate extra ()) []
        (List.replicate (matched + right) ())) := by
  induction right generalizing matched test with
  | zero =>
      simp [Function.iterate_succ_apply, flip, step, revProgram, cfg,
        stepOp, List.replicate_succ]
  | succ right ih =>
      rw [show right + 1 + extra + 1 =
        (right + extra + 1) + 1 by omega, List.replicate_succ]
      rw [show 3 * (right + 1) + 2 = (3 * right + 2) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[3 * right + 2]
          (some (cfg .compareLeft buffer true tail output
            (List.replicate (right + extra + 1) ())
            (List.replicate right ())
            (List.replicate (matched + 1) ()))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (matched + 1) true

private def afterMatchedRestore : EndpointOrder → Label
  | .leftLess => .restoreExtraRight
  | .equal => .pushEdgeMark .equal
  | .rightLess => .restoreExtraLeft

private theorem restoreMatched_eval (order : EndpointOrder)
    (matched left right : Nat) (tail output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool) :
    (flip Option.bind (step revProgram))^[3 * matched + 1]
      (some (cfg (.restoreMatched order) buffer test tail output
        (List.replicate left ()) (List.replicate right ())
        (List.replicate matched ()))) =
      some (cfg (afterMatchedRestore order) buffer false tail output
        (List.replicate (left + matched) ())
        (List.replicate (right + matched) ()) []) := by
  induction matched generalizing left right test with
  | zero =>
      cases order <;> rfl
  | succ matched ih =>
      rw [show 3 * (matched + 1) + 1 =
          (3 * matched + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[3 * matched + 1]
          (some (cfg (.restoreMatched order) buffer true tail output
            (List.replicate (left + 1) ())
            (List.replicate (right + 1) ())
            (List.replicate matched ()))) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (left + 1) (right + 1) true

private theorem drainLeftCounter_eval (order : EndpointOrder)
    (count : Nat) (tail output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool)
    (other : Nat) (scratch : Nat)
    (horder : order = .leftLess ∨ order = .equal) :
    (flip Option.bind (step revProgram))^[2 * count + 1]
      (some (cfg (.lower order) buffer test tail output
        (List.replicate count ()) (List.replicate other ())
        (List.replicate scratch ()))) =
      some (cfg (.pushPairSeparator order) buffer false tail
        (List.replicate count .tick ++ output) []
        (List.replicate other ()) (List.replicate scratch ())) := by
  rcases horder with rfl | rfl
  all_goals
    induction count generalizing test output with
    | zero => rfl
    | succ count ih =>
        simp only [List.replicate_succ]
        rw [show 2 * (count + 1) + 1 =
            (2 * count + 1) + 1 + 1 by omega,
          Function.iterate_succ_apply, Function.iterate_succ_apply]
        change
          (flip Option.bind (step revProgram))^[2 * count + 1]
            (some (cfg _ buffer true tail (.tick :: output)
              (List.replicate count ()) (List.replicate other ())
              (List.replicate scratch ()))) = _
        simpa [List.replicate_succ, replicate_append_cons] using
          ih (test := true) (output := .tick :: output)

private theorem drainRightLower_eval (count : Nat)
    (tail output : List CliqueSym) (buffer : Option CliqueSym)
    (test : Bool) (other scratch : Nat) :
    (flip Option.bind (step revProgram))^[2 * count + 1]
      (some (cfg (.lower .rightLess) buffer test tail output
        (List.replicate other ()) (List.replicate count ())
        (List.replicate scratch ()))) =
      some (cfg (.pushPairSeparator .rightLess) buffer false tail
        (List.replicate count .tick ++ output)
        (List.replicate other ()) [] (List.replicate scratch ())) := by
  induction count generalizing test output with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ]
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[2 * count + 1]
          (some (cfg (.lower .rightLess) buffer true tail (.tick :: output)
            (List.replicate other ()) (List.replicate count ())
            (List.replicate scratch ()))) = _
      simpa [List.replicate_succ, replicate_append_cons] using
        ih (test := true) (output := .tick :: output)

private theorem drainRightCounter_eval (order : EndpointOrder)
    (count : Nat) (tail output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool)
    (other scratch : Nat)
    (horder : order = .leftLess ∨ order = .equal) :
    (flip Option.bind (step revProgram))^[2 * count + 1]
      (some (cfg (.upper order) buffer test tail output
        (List.replicate other ()) (List.replicate count ())
        (List.replicate scratch ()))) =
      some (cfg .pushRecordEnd buffer false tail
        (List.replicate count .tick ++ output)
        (List.replicate other ()) [] (List.replicate scratch ())) := by
  rcases horder with rfl | rfl
  all_goals
    induction count generalizing test output with
    | zero => rfl
    | succ count ih =>
        simp only [List.replicate_succ]
        rw [show 2 * (count + 1) + 1 =
            (2 * count + 1) + 1 + 1 by omega,
          Function.iterate_succ_apply, Function.iterate_succ_apply]
        change
          (flip Option.bind (step revProgram))^[2 * count + 1]
            (some (cfg _ buffer true tail (.tick :: output)
              (List.replicate other ()) (List.replicate count ())
              (List.replicate scratch ()))) = _
        simpa [List.replicate_succ, replicate_append_cons] using
          ih (test := true) (output := .tick :: output)

private theorem drainLeftUpper_eval (count : Nat)
    (tail output : List CliqueSym) (buffer : Option CliqueSym)
    (test : Bool) (other scratch : Nat) :
    (flip Option.bind (step revProgram))^[2 * count + 1]
      (some (cfg (.upper .rightLess) buffer test tail output
        (List.replicate count ()) (List.replicate other ())
        (List.replicate scratch ()))) =
      some (cfg .pushRecordEnd buffer false tail
        (List.replicate count .tick ++ output) []
        (List.replicate other ()) (List.replicate scratch ())) := by
  induction count generalizing test output with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ]
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step revProgram))^[2 * count + 1]
          (some (cfg (.upper .rightLess) buffer true tail (.tick :: output)
            (List.replicate count ()) (List.replicate other ())
            (List.replicate scratch ()))) = _
      simpa [List.replicate_succ, replicate_append_cons] using
        ih (test := true) (output := .tick :: output)

/-- Exact cost for one canonical raw query record. -/
def rowSteps (edge : Nat × Nat) : Nat :=
  4 * (edge.1 + edge.2) +
    6 * min edge.1 edge.2 + 12

/-- One canonical query is normalized, prepended in reverse physical order,
and leaves all counters clear at the next row boundary. -/
def rowRun (edge : Nat × Nat) (tail output : List CliqueSym)
    (buffer : Option CliqueSym) (test : Bool) :
    EvalsToInTime (step revProgram)
      (cfg .scan buffer test (encodeCliqueEdge edge ++ tail) output [] [] [])
      (some (cfg .scan (some .recordEnd) false tail
        ((encodeCliqueEdge (normalizeQuery edge)).reverse ++ output)
        [] [] []))
      (rowSteps edge) := by
  rcases edge with ⟨left, right⟩
  have scan : EvalsToInTime (step revProgram)
      (cfg .scan buffer test
        (encodeCliqueEdge (left, right) ++ tail) output [] [] [])
      (some (cfg .left (some .edgeMark) test
        (List.replicate left .tick ++ .pairSep ::
          List.replicate right .tick ++ .recordEnd :: tail)
        output [] [] [])) 1 := by
    simpa [encodeCliqueEdge, prependCliqueTicks_eq_replicate]
      using (show EvalsToInTime (step revProgram)
        (cfg .scan buffer test
          (.edgeMark :: List.replicate left .tick ++ .pairSep ::
            List.replicate right .tick ++ .recordEnd :: tail)
          output [] [] [])
        (some (cfg .left (some .edgeMark) test
          (List.replicate left .tick ++ .pairSep ::
            List.replicate right .tick ++ .recordEnd :: tail)
          output [] [] [])) 1 from ⟨⟨1, rfl⟩, le_rfl⟩)
  have loadLeft : EvalsToInTime (step revProgram)
      (cfg .left (some .edgeMark) test
        (List.replicate left .tick ++ .pairSep ::
          List.replicate right .tick ++ .recordEnd :: tail)
        output [] [] [])
      (some (cfg .right (some .pairSep) test
        (List.replicate right .tick ++ .recordEnd :: tail)
        output (List.replicate left ()) [] [])) (2 * left + 1) :=
    ⟨⟨2 * left + 1, by simpa using
      (loadLeft_eval left 0
        (List.replicate right .tick ++ .recordEnd :: tail) output
        (some .edgeMark) test)⟩, le_rfl⟩
  have loadRight : EvalsToInTime (step revProgram)
      (cfg .right (some .pairSep) test
        (List.replicate right .tick ++ .recordEnd :: tail)
        output (List.replicate left ()) [] [])
      (some (cfg .compareLeft (some .recordEnd) test tail output
        (List.replicate left ()) (List.replicate right ()) []))
      (2 * right + 1) :=
    ⟨⟨2 * right + 1, by simpa using
      (loadRight_eval left right 0 tail output (some .pairSep) test)⟩,
      le_rfl⟩
  let loaded₁ := EvalsToInTime.trans (step revProgram)
    1 (2 * left + 1) _ _ _ scan loadLeft
  let loaded := EvalsToInTime.trans (step revProgram)
    _ (2 * right + 1) _ _ _ loaded₁ loadRight
  by_cases hlr : left < right
  · let extra := right - left - 1
    have hright : right = left + extra + 1 := by
      simp only [extra]
      omega
    have compare : EvalsToInTime (step revProgram)
        (cfg .compareLeft (some .recordEnd) test tail output
          (List.replicate left ())
          (List.replicate right ()) [])
        (some (cfg (.restoreMatched .leftLess) (some .recordEnd) true
          tail output [] (List.replicate extra ())
          (List.replicate left ()))) (3 * left + 2) :=
      ⟨⟨3 * left + 2, by simpa [hright] using
        (compareLeftLess_eval 0 left extra tail output
          (some .recordEnd) test)⟩, le_rfl⟩
    have restore : EvalsToInTime (step revProgram)
        (cfg (.restoreMatched .leftLess) (some .recordEnd) true tail output
          [] (List.replicate extra ()) (List.replicate left ()))
        (some (cfg (.pushEdgeMark .leftLess) (some .recordEnd) false tail output
          (List.replicate left ())
          (List.replicate (left + extra + 1) ()) []))
        (3 * left + 2) := by
      have matched : EvalsToInTime (step revProgram)
          (cfg (.restoreMatched .leftLess) (some .recordEnd) true tail output
            [] (List.replicate extra ()) (List.replicate left ()))
          (some (cfg .restoreExtraRight (some .recordEnd) false tail output
            (List.replicate left ())
            (List.replicate (extra + left) ()) []))
          (3 * left + 1) :=
        ⟨⟨3 * left + 1, by simpa [afterMatchedRestore] using
          (restoreMatched_eval .leftLess left 0 extra tail output
            (some .recordEnd) true)⟩, le_rfl⟩
      have extraStep : EvalsToInTime (step revProgram)
          (cfg .restoreExtraRight (some .recordEnd) false tail output
            (List.replicate left ())
            (List.replicate (extra + left) ()) [])
          (some (cfg (.pushEdgeMark .leftLess) (some .recordEnd) false
            tail output (List.replicate left ())
            (List.replicate (left + extra + 1) ()) [])) 1 := by
        simpa only [show extra + left = left + extra by omega,
          List.replicate_succ] using
          (show EvalsToInTime (step revProgram)
            (cfg .restoreExtraRight (some .recordEnd) false tail output
              (List.replicate left ())
              (List.replicate (extra + left) ()) [])
            (some (cfg (.pushEdgeMark .leftLess) (some .recordEnd) false
              tail output (List.replicate left ())
              (() :: List.replicate (extra + left) ()) [])) 1 from
            ⟨⟨1, rfl⟩, le_rfl⟩)
      let full := EvalsToInTime.trans (step revProgram)
        (3 * left + 1) 1 _ _ _ matched extraStep
      convert full using 1 <;> omega
    have pushMark : EvalsToInTime (step revProgram)
        (cfg (.pushEdgeMark .leftLess) (some .recordEnd) false tail output
          (List.replicate left ())
          (List.replicate (left + extra + 1) ()) [])
        (some (cfg (.lower .leftLess) (some .recordEnd) false tail
          (.edgeMark :: output) (List.replicate left ())
          (List.replicate (left + extra + 1) ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
    have lower : EvalsToInTime (step revProgram)
        (cfg (.lower .leftLess) (some .recordEnd) false tail
          (.edgeMark :: output) (List.replicate left ())
          (List.replicate (left + extra + 1) ()) [])
        (some (cfg (.pushPairSeparator .leftLess) (some .recordEnd) false
          tail (List.replicate left .tick ++ .edgeMark :: output) []
          (List.replicate (left + extra + 1) ()) [])) (2 * left + 1) :=
      ⟨⟨2 * left + 1, drainLeftCounter_eval .leftLess left tail
        (.edgeMark :: output) (some .recordEnd) false
        (left + extra + 1) 0 (Or.inl rfl)⟩, le_rfl⟩
    have separator : EvalsToInTime (step revProgram)
        (cfg (.pushPairSeparator .leftLess) (some .recordEnd) false tail
          (List.replicate left .tick ++ .edgeMark :: output) []
          (List.replicate (left + extra + 1) ()) [])
        (some (cfg (.upper .leftLess) (some .recordEnd) false tail
          (.pairSep :: List.replicate left .tick ++ .edgeMark :: output) []
          (List.replicate (left + extra + 1) ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
    have upper : EvalsToInTime (step revProgram)
        (cfg (.upper .leftLess) (some .recordEnd) false tail
          (.pairSep :: List.replicate left .tick ++ .edgeMark :: output) []
          (List.replicate (left + extra + 1) ()) [])
        (some (cfg .pushRecordEnd (some .recordEnd) false tail
          (List.replicate (left + extra + 1) .tick ++ .pairSep ::
            List.replicate left .tick ++ .edgeMark :: output) [] [] []))
        (2 * (left + extra + 1) + 1) :=
      ⟨⟨2 * (left + extra + 1) + 1, by
        simpa [List.cons_append, List.append_assoc] using
          (drainRightCounter_eval .leftLess
          (left + extra + 1) tail
          (.pairSep :: (List.replicate left .tick ++ .edgeMark :: output))
          (some .recordEnd) false 0 0 (Or.inl rfl))⟩, le_rfl⟩
    have endRow : EvalsToInTime (step revProgram)
        (cfg .pushRecordEnd (some .recordEnd) false tail
          (List.replicate (left + extra + 1) .tick ++ .pairSep ::
            List.replicate left .tick ++ .edgeMark :: output) [] [] [])
        (some (cfg .scan (some .recordEnd) false tail
          (.recordEnd :: List.replicate (left + extra + 1) .tick ++
            .pairSep :: List.replicate left .tick ++ .edgeMark :: output)
          [] [] [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
    let compared := EvalsToInTime.trans (step revProgram)
      _ (3 * left + 2) _ _ _ loaded compare
    let restored := EvalsToInTime.trans (step revProgram)
      _ (3 * left + 2) _ _ _ compared restore
    let marked := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ restored pushMark
    let lowerDone := EvalsToInTime.trans (step revProgram)
      _ (2 * left + 1) _ _ _ marked lower
    let separated := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ lowerDone separator
    let upperDone := EvalsToInTime.trans (step revProgram)
      _ (2 * (left + extra + 1) + 1) _ _ _ separated upper
    let full := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ upperDone endRow
    convert full using 1 <;>
      simp [rowSteps, normalizeQuery, hright,
        encodeCliqueEdge, prependCliqueTicks_eq_replicate,
        List.reverse_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
    omega
  · by_cases hrl : right < left
    · let extra := left - right - 1
      have hleft : left = right + extra + 1 := by
        simp only [extra]
        omega
      have compare : EvalsToInTime (step revProgram)
          (cfg .compareLeft (some .recordEnd) test tail output
            (List.replicate left ())
            (List.replicate right ()) [])
          (some (cfg (.restoreMatched .rightLess) (some .recordEnd) false
            tail output (List.replicate extra ()) []
            (List.replicate right ()))) (3 * right + 2) :=
        ⟨⟨3 * right + 2, by simpa [hleft] using
          (compareRightLess_eval 0 right extra tail output
            (some .recordEnd) test)⟩, le_rfl⟩
      have restore : EvalsToInTime (step revProgram)
          (cfg (.restoreMatched .rightLess) (some .recordEnd) false tail
            output (List.replicate extra ()) [] (List.replicate right ()))
          (some (cfg (.pushEdgeMark .rightLess) (some .recordEnd) false tail
            output (List.replicate (right + extra + 1) ())
            (List.replicate right ()) [])) (3 * right + 2) := by
        have matched : EvalsToInTime (step revProgram)
            (cfg (.restoreMatched .rightLess) (some .recordEnd) false tail
              output (List.replicate extra ()) [] (List.replicate right ()))
            (some (cfg .restoreExtraLeft (some .recordEnd) false tail output
              (List.replicate (extra + right) ())
              (List.replicate right ()) [])) (3 * right + 1) :=
          ⟨⟨3 * right + 1, by simpa [afterMatchedRestore] using
            (restoreMatched_eval .rightLess right extra 0 tail output
              (some .recordEnd) false)⟩, le_rfl⟩
        have extraStep : EvalsToInTime (step revProgram)
            (cfg .restoreExtraLeft (some .recordEnd) false tail output
              (List.replicate (extra + right) ())
              (List.replicate right ()) [])
            (some (cfg (.pushEdgeMark .rightLess) (some .recordEnd) false
              tail output (List.replicate (right + extra + 1) ())
              (List.replicate right ()) [])) 1 := by
          simpa only [show extra + right = right + extra by omega,
            List.replicate_succ] using
            (show EvalsToInTime (step revProgram)
              (cfg .restoreExtraLeft (some .recordEnd) false tail output
                (List.replicate (extra + right) ())
                (List.replicate right ()) [])
              (some (cfg (.pushEdgeMark .rightLess) (some .recordEnd) false
                tail output (() :: List.replicate (extra + right) ())
                (List.replicate right ()) [])) 1 from
              ⟨⟨1, rfl⟩, le_rfl⟩)
        let full := EvalsToInTime.trans (step revProgram)
          (3 * right + 1) 1 _ _ _ matched extraStep
        convert full using 1 <;> omega
      have pushMark : EvalsToInTime (step revProgram)
          (cfg (.pushEdgeMark .rightLess) (some .recordEnd) false tail output
            (List.replicate (right + extra + 1) ())
            (List.replicate right ()) [])
          (some (cfg (.lower .rightLess) (some .recordEnd) false tail
            (.edgeMark :: output) (List.replicate (right + extra + 1) ())
            (List.replicate right ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have lower : EvalsToInTime (step revProgram)
          (cfg (.lower .rightLess) (some .recordEnd) false tail
            (.edgeMark :: output) (List.replicate (right + extra + 1) ())
            (List.replicate right ()) [])
          (some (cfg (.pushPairSeparator .rightLess) (some .recordEnd) false
            tail (List.replicate right .tick ++ .edgeMark :: output)
            (List.replicate (right + extra + 1) ()) [] []))
          (2 * right + 1) :=
        ⟨⟨2 * right + 1, drainRightLower_eval right tail
          (.edgeMark :: output) (some .recordEnd) false
          (right + extra + 1) 0⟩, le_rfl⟩
      have separator : EvalsToInTime (step revProgram)
          (cfg (.pushPairSeparator .rightLess) (some .recordEnd) false tail
            (List.replicate right .tick ++ .edgeMark :: output)
            (List.replicate (right + extra + 1) ()) [] [])
          (some (cfg (.upper .rightLess) (some .recordEnd) false tail
            (.pairSep :: (List.replicate right .tick ++ .edgeMark :: output))
            (List.replicate (right + extra + 1) ()) [] [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have upper : EvalsToInTime (step revProgram)
          (cfg (.upper .rightLess) (some .recordEnd) false tail
            (.pairSep :: (List.replicate right .tick ++ .edgeMark :: output))
            (List.replicate (right + extra + 1) ()) [] [])
          (some (cfg .pushRecordEnd (some .recordEnd) false tail
            (List.replicate (right + extra + 1) .tick ++ .pairSep ::
              List.replicate right .tick ++ .edgeMark :: output) [] [] []))
          (2 * (right + extra + 1) + 1) :=
        ⟨⟨2 * (right + extra + 1) + 1, by
          simpa [List.cons_append, List.append_assoc] using
            (drainLeftUpper_eval
            (right + extra + 1) tail
            (.pairSep ::
              (List.replicate right .tick ++ .edgeMark :: output))
            (some .recordEnd) false 0 0)⟩, le_rfl⟩
      have endRow : EvalsToInTime (step revProgram)
          (cfg .pushRecordEnd (some .recordEnd) false tail
            (List.replicate (right + extra + 1) .tick ++ .pairSep ::
              List.replicate right .tick ++ .edgeMark :: output) [] [] [])
          (some (cfg .scan (some .recordEnd) false tail
            (.recordEnd :: List.replicate (right + extra + 1) .tick ++
              .pairSep :: List.replicate right .tick ++ .edgeMark :: output)
            [] [] [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      let compared := EvalsToInTime.trans (step revProgram)
        _ (3 * right + 2) _ _ _ loaded compare
      let restored := EvalsToInTime.trans (step revProgram)
        _ (3 * right + 2) _ _ _ compared restore
      let marked := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ restored pushMark
      let lowerDone := EvalsToInTime.trans (step revProgram)
        _ (2 * right + 1) _ _ _ marked lower
      let separated := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ lowerDone separator
      let upperDone := EvalsToInTime.trans (step revProgram)
        _ (2 * (right + extra + 1) + 1) _ _ _ separated upper
      let full := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ upperDone endRow
      convert full using 1 <;>
        simp [rowSteps, normalizeQuery, hleft,
          encodeCliqueEdge, prependCliqueTicks_eq_replicate,
          List.reverse_append, List.append_assoc, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
      omega
    · have heq : left = right := by omega
      subst right
      have compare : EvalsToInTime (step revProgram)
          (cfg .compareLeft (some .recordEnd) test tail output
            (List.replicate left ()) (List.replicate left ()) [])
          (some (cfg (.restoreMatched .equal) (some .recordEnd) false
            tail output [] [] (List.replicate left ())))
          (3 * left + 2) :=
        ⟨⟨3 * left + 2, by simpa using (compareEqual_eval 0 left
          tail output (some .recordEnd) test)⟩, le_rfl⟩
      have restore : EvalsToInTime (step revProgram)
          (cfg (.restoreMatched .equal) (some .recordEnd) false tail output
            [] [] (List.replicate left ()))
          (some (cfg (.pushEdgeMark .equal) (some .recordEnd) false tail
            output (List.replicate left ()) (List.replicate left ()) []))
          (3 * left + 1) :=
        ⟨⟨3 * left + 1, by simpa [afterMatchedRestore] using
          (restoreMatched_eval .equal left 0 0 tail output
            (some .recordEnd) false)⟩, le_rfl⟩
      have pushMark : EvalsToInTime (step revProgram)
          (cfg (.pushEdgeMark .equal) (some .recordEnd) false tail output
            (List.replicate left ()) (List.replicate left ()) [])
          (some (cfg (.lower .equal) (some .recordEnd) false tail
            (.edgeMark :: output) (List.replicate left ())
            (List.replicate left ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have lower : EvalsToInTime (step revProgram)
          (cfg (.lower .equal) (some .recordEnd) false tail
            (.edgeMark :: output) (List.replicate left ())
            (List.replicate left ()) [])
          (some (cfg (.pushPairSeparator .equal) (some .recordEnd) false
            tail (List.replicate left .tick ++ .edgeMark :: output) []
            (List.replicate left ()) [])) (2 * left + 1) :=
        ⟨⟨2 * left + 1, drainLeftCounter_eval .equal left tail
          (.edgeMark :: output) (some .recordEnd) false left 0
          (Or.inr rfl)⟩, le_rfl⟩
      have separator : EvalsToInTime (step revProgram)
          (cfg (.pushPairSeparator .equal) (some .recordEnd) false tail
            (List.replicate left .tick ++ .edgeMark :: output) []
            (List.replicate left ()) [])
          (some (cfg (.upper .equal) (some .recordEnd) false tail
            (.pairSep :: (List.replicate left .tick ++ .edgeMark :: output))
            [] (List.replicate left ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have upper : EvalsToInTime (step revProgram)
          (cfg (.upper .equal) (some .recordEnd) false tail
            (.pairSep :: (List.replicate left .tick ++ .edgeMark :: output))
            [] (List.replicate left ()) [])
          (some (cfg .pushRecordEnd (some .recordEnd) false tail
            (List.replicate left .tick ++ .pairSep ::
              List.replicate left .tick ++ .edgeMark :: output) [] [] []))
          (2 * left + 1) :=
        ⟨⟨2 * left + 1, by simpa [List.cons_append,
          List.append_assoc] using
          (drainRightCounter_eval .equal left tail
            (.pairSep ::
              (List.replicate left .tick ++ .edgeMark :: output))
            (some .recordEnd) false 0 0 (Or.inr rfl))⟩, le_rfl⟩
      have endRow : EvalsToInTime (step revProgram)
          (cfg .pushRecordEnd (some .recordEnd) false tail
            (List.replicate left .tick ++ .pairSep ::
              List.replicate left .tick ++ .edgeMark :: output) [] [] [])
          (some (cfg .scan (some .recordEnd) false tail
            (.recordEnd :: List.replicate left .tick ++ .pairSep ::
              List.replicate left .tick ++ .edgeMark :: output) [] [] [])) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      let compared := EvalsToInTime.trans (step revProgram)
        _ (3 * left + 2) _ _ _ loaded compare
      let restored := EvalsToInTime.trans (step revProgram)
        _ (3 * left + 1) _ _ _ compared restore
      let marked := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ restored pushMark
      let lowerDone := EvalsToInTime.trans (step revProgram)
        _ (2 * left + 1) _ _ _ marked lower
      let separated := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ lowerDone separator
      let upperDone := EvalsToInTime.trans (step revProgram)
        _ (2 * left + 1) _ _ _ separated upper
      let full := EvalsToInTime.trans (step revProgram) _ 1 _ _ _ upperDone endRow
      have exactRun : EvalsToInTime (step revProgram)
          (cfg .scan buffer test
            (encodeCliqueEdge (left, left) ++ tail) output [] [] [])
          (some (cfg .scan (some .recordEnd) false tail
            ((encodeCliqueEdge (normalizeQuery (left, left))).reverse ++
              output) [] [] []))
          (14 * left + 11) := by
        convert full using 1 <;>
          simp [normalizeQuery, encodeCliqueEdge,
            prependCliqueTicks_eq_replicate, List.reverse_append,
            List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] <;> omega
      refine ⟨exactRun.toEvalsTo, exactRun.steps_le_m.trans ?_⟩
      simp [rowSteps]
      omega

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
