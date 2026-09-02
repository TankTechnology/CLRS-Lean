import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Soundness

/-!
# Exact semantics of the Cook--Levin verifier circuit

The closed general circuit is satisfiable exactly for instances belonging to
the verified language.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Closing the final builder preserves its conjunction value. -/
theorem verifierCircuit_eval {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool) :
    (verifierCircuit W x).eval inputs =
      (verifierConjunction W x).1.evalWire inputs
        (verifierConjunction W x).2 := by
  rfl

/-- The circuit exposes exactly the external inputs used by the complete
public tableau rows. -/
theorem verifierCircuit_inputCount {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierCircuit W x).inputCount = tableauInputCount W.machine.tm
      ((verifierHeight W).eval x.length)
      ((verifierHorizon W).eval x.length) := by
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let input := verifierInputBoundary W x
  let accepting := verifierAcceptingBoundary W x
  have hext : rows.builder.Extends (verifierConjunction W x).1 :=
    (((((pool.extension.trans validity.extension).trans transitions.extension).trans
      initial.extension).trans input.extension).trans accepting.extension).trans
        (CircuitBuilder.conjunction_extends accepting.builder
          (verifierConstraintWires W x) (verifierConstraintWires_valid W x))
  change (verifierConjunction W x).1.inputCount = _
  rw [hext.1]
  exact allocateTableauRows_inputCount W.machine.tm
    ((verifierHeight W).eval x.length)
    ((verifierHorizon W).eval x.length)

/-- Headline Cook--Levin tableau theorem: the generated well-formed general
circuit is satisfiable exactly on members of the verified language. -/
theorem verifierCircuit_satisfiable_iff {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    GeneralCircuitSatisfiable (verifierCircuit W x) ↔ x ∈ L := by
  constructor
  · rintro ⟨_, assignment, htrue⟩
    apply (exists_isVerifierTableau_iff W x).1
    apply verifierConjunction_sound W x
      (fun i => if hi : i < (verifierCircuit W x).inputCount then
        assignment ⟨i, hi⟩ else false)
    simpa only [verifierCircuit_eval] using htrue
  · intro hx
    rcases (W.correct x).1 hx with ⟨c, hc, hverify⟩
    let assignment : Fin (verifierCircuit W x).inputCount → Bool :=
      fun i => verifierTableauInputs W c x hc i.val
    refine ⟨verifierCircuit_wellFormed W x, assignment, ?_⟩
    rw [verifierCircuit_eval]
    have hinputs :
        (fun i => if hi : i < (verifierCircuit W x).inputCount then
          assignment ⟨i, hi⟩ else false) = verifierTableauInputs W c x hc := by
      funext i
      by_cases hi : i < (verifierCircuit W x).inputCount
      · simp [hi, assignment]
      · rw [dif_neg hi]
        unfold verifierTableauInputs
        rw [dif_neg]
        intro hrows
        apply hi
        rw [verifierCircuit_inputCount]
        rw [← allocateTableauRows_inputCount W.machine.tm
          ((verifierHeight W).eval x.length)
          ((verifierHorizon W).eval x.length)]
        exact hrows
    rw [hinputs]
    exact W.verifierConjunction_complete hc hverify

end

end CLRS.Chapter34.Turing.CookLevin
