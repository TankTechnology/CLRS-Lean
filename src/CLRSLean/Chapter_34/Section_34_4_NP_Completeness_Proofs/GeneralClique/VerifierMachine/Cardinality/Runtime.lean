import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Cardinality.Semantics

/-!
# General CLIQUE verifier: polynomial runtime of the cardinality pass

The independent run is linear in the paired raw input.  Compiling the fixed
controller therefore yields the concrete polynomial-time Boolean component
used by the full verifier construction.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality

open PolyBuilder
open _root_.Turing

private theorem targetTooLargeSteps_le (input : List CliqueSym) :
    targetTooLargeSteps input ≤ input.length + 4 := by
  induction input with
  | nil => simp [targetTooLargeSteps]
  | cons symbol input ih =>
      cases symbol <;> simp [targetTooLargeSteps] at ih ⊢ <;> omega

private theorem targetSteps_le (count : Nat) (input : List CliqueSym) :
    targetSteps count input ≤ 2 * input.length + count + 4 := by
  induction input generalizing count with
  | nil => simp [targetSteps]
  | cons symbol input ih =>
      have hind := ih count
      cases symbol <;> try simp [targetSteps] <;> try omega
      case tick =>
        cases count with
        | zero =>
            have h := targetTooLargeSteps_le input
            simp [targetSteps]
            omega
        | succ count =>
            have h := ih count
            simp [targetSteps]
            omega

private theorem headerSteps_le (count : Nat) (input : List CliqueSym) :
    headerSteps count input ≤ 2 * input.length + count + 4 := by
  induction input with
  | nil => simp [headerSteps]
  | cons symbol input ih =>
      cases symbol <;> try simp [headerSteps] <;> try omega
      case fieldSep =>
        have h := targetSteps_le count input
        simp [headerSteps]
        omega

/-- Total step budget recorded by the exact run. -/
def cardinalitySteps (certificate input : List CliqueSym) : Nat :=
  certificateSteps certificate +
    headerSteps (certificate.count .vertexMark) input

/-- The exact controller run is bounded by a uniform linear polynomial in the
length of the separator-based pair encoding. -/
theorem cardinalitySteps_le (certificate input : List CliqueSym) :
    cardinalitySteps certificate input ≤
      3 * (pairEncoding certificate input).length + 5 := by
  have hcount : certificate.count .vertexMark ≤ certificate.length :=
    List.count_le_length
  have hheader := headerSteps_le
    (certificate.count .vertexMark) input
  simp only [cardinalitySteps, certificateSteps, pairEncoding,
    List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

/-- The cardinality controller produces the specified singleton Boolean output
within its displayed linear budget. -/
def cardinality_outputs_in_time (certificate input : List CliqueSym) :
    TM2OutputsInTime (compile program) (pairEncoding certificate input)
      (some (boolEncoding (cardinalityPass certificate input)))
      (3 * (pairEncoding certificate input).length + 5) := by
  have builderRun := cardinality_run certificate input
  have compiledRun := compile_evalsToInTime program builderRun
  change EvalsToInTime (compile program).step
      (initList (compile program) (pairEncoding certificate input))
      (some (haltList (compile program)
        [cardinalityPass certificate input]))
      (3 * (pairEncoding certificate input).length + 5)
  refine ⟨⟨compiledRun.steps, ?_⟩, compiledRun.steps_le_m.trans
    (cardinalitySteps_le certificate input)⟩
  convert compiledRun.evals_in_steps using 1 <;>
    simp only [encodeCfg_initialCfg, encodeCfg_haltCfg] <;> rfl

/-- Polynomial-time computability of the concrete cardinality component on
raw certificate/instance pairs. -/
noncomputable def cardinalityPassComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun pr : List CliqueSym × List CliqueSym => pairEncoding pr.1 pr.2)
      boolEncoding (fun pr => cardinalityPass pr.1 pr.2) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 5
  outputsFun := fun pr => by
    rcases pr with ⟨certificate, input⟩
    have run := cardinality_outputs_in_time certificate input
    convert run using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Cardinality
