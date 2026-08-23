import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.EdgeLookup.Edges

/-!
# General CLIQUE verifier: canonical query loading

The two unary endpoints preceding the pair separator are loaded into persistent
counters.  The lemmas are suffix-parametric so they compose directly with the
encoded instance that follows the separator.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup

open PolyBuilder

/-- Load a canonical unary left endpoint and consume its pair separator. -/
def queryLeft_run (remaining loaded right : Nat)
    (rest : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .queryLeft buffer₁ buffer₂ test
        (List.replicate remaining (some .tick) ++ some .pairSep :: rest) []
        (List.replicate loaded ()) (List.replicate right ()) [])
      (some (cfg .queryRight (some (some .pairSep)) buffer₂ test rest []
        (List.replicate (remaining + loaded) ())
        (List.replicate right ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing loaded buffer₁ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg .incQueryLeft (some (some .tick)) buffer₂ test
        (List.replicate remaining (some .tick) ++ some .pairSep :: rest) []
        (List.replicate loaded ()) (List.replicate right ()) []
      let afterInc := cfg .queryLeft (some (some .tick)) buffer₂ test
        (List.replicate remaining (some .tick) ++ some .pairSep :: rest) []
        (List.replicate (loaded + 1) ()) (List.replicate right ()) []
      have first : EvalsToInTime (step program)
          (cfg .queryLeft buffer₁ buffer₂ test
            (List.replicate (remaining + 1) (some .tick) ++
              some .pairSep :: rest) []
            (List.replicate loaded ()) (List.replicate right ()) [])
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, List.replicate_succ, step, program, cfg,
            stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterInc) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, afterInc, List.replicate_succ, step,
            program, cfg, stepOp]⟩, le_rfl⟩
      have restRun := ih (loaded + 1) (some (some .tick))
      have throughInc := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ throughInc restRun
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using full

/-- Load a canonical unary right endpoint and consume its record terminator. -/
def queryRight_run (left remaining loaded : Nat)
    (rest : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .queryRight buffer₁ buffer₂ test
        (List.replicate remaining (some .tick) ++ some .recordEnd :: rest) []
        (List.replicate left ()) (List.replicate loaded ()) [])
      (some (cfg .pairSeparator (some (some .recordEnd)) buffer₂ test rest []
        (List.replicate left ())
        (List.replicate (remaining + loaded) ()) []))
      (2 * remaining + 1) := by
  induction remaining generalizing loaded buffer₁ with
  | zero =>
      exact ⟨⟨1, by
        simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := cfg .incQueryRight (some (some .tick)) buffer₂ test
        (List.replicate remaining (some .tick) ++ some .recordEnd :: rest) []
        (List.replicate left ()) (List.replicate loaded ()) []
      let afterInc := cfg .queryRight (some (some .tick)) buffer₂ test
        (List.replicate remaining (some .tick) ++ some .recordEnd :: rest) []
        (List.replicate left ()) (List.replicate (loaded + 1) ()) []
      have first : EvalsToInTime (step program)
          (cfg .queryRight buffer₁ buffer₂ test
            (List.replicate (remaining + 1) (some .tick) ++
              some .recordEnd :: rest) []
            (List.replicate left ()) (List.replicate loaded ()) [])
          (some afterPop) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, List.replicate_succ, step, program, cfg,
            stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterInc) 1 := by
        exact ⟨⟨1, by
          simp [flip, afterPop, afterInc, List.replicate_succ, step,
            program, cfg, stepOp]⟩, le_rfl⟩
      have restRun := ih (loaded + 1) (some (some .tick))
      have throughInc := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * remaining + 1) _ afterInc _ throughInc restRun
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.EdgeLookup
