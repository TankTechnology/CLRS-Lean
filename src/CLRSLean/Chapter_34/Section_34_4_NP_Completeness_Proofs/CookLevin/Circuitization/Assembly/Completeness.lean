import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Evaluation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Semantics

/-!
# Completeness of the assembled verifier circuit

An accepting bounded certificate supplies the concrete tableau assignment.
Every family and boundary output is then true, hence so is the final
conjunction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing

noncomputable section

/-- The concrete certificate assignment decodes every public row correctly in
any later builder extending the row-allocation prefix. -/
theorem VerifierWitness.verifierRows_eval_at
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ} (hc : c.length ≤ W.certificateBound.eval x.length)
    {next : CircuitBuilder} (hext : (verifierRows W x).builder.Extends next)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval x.length))) :
    evalBundle next (verifierTableauInputs W c x hc)
        ((verifierRows W x).rows row)
        (((verifierRows W x).rowValid row).mono hext) =
      some (verifierTableauCfg W c x row.val) := by
  rw [evalBundle_extends hext (verifierTableauInputs W c x hc)
    ((verifierRows W x).rows row) ((verifierRows W x).rowValid row)]
  simpa [verifierRows, verifierTableauInputs] using
    W.allocateTableauRows_eval_verifierTableau hc row

/-- Every canonical-validity component is true on the concrete tableau. -/
theorem VerifierWitness.verifierValidity_output_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ} (hc : c.length ≤ W.certificateBound.eval x.length)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval x.length))) :
    (verifierValidity W x).builder.evalWire
        (verifierTableauInputs W c x hc)
        ((verifierValidity W x).outputs row) = true := by
  let rows := verifierRows W x
  let pool := verifierPool W x
  apply (validCfgCircuitFamily_eval_iff pool.builder rows.rows
    (fun r => (rows.rowValid r).mono pool.extension) _ row).2
  rw [W.verifierRows_eval_at hc pool.extension row]
  rfl

/-- Every local transition component is true on the concrete tableau. -/
theorem VerifierWitness.verifierTransitions_output_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ} (hc : c.length ≤ W.certificateBound.eval x.length)
    (step : Fin ((verifierHorizon W).eval x.length)) :
    (verifierTransitions W x).builder.evalWire
        (verifierTableauInputs W c x hc)
        ((verifierTransitions W x).outputs step) = true := by
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let hext := pool.extension.trans validity.extension
  have hdecoded : ∀ row,
      evalBundle validity.builder (verifierTableauInputs W c x hc)
        (rows.rows row) ((rows.rowValid row).mono hext) =
          some (verifierTableauCfg W c x row.val) := by
    intro row
    exact W.verifierRows_eval_at hc hext row
  exact (transitionCircuitFamily_eval_iff W.machine.tm
    ((verifierHeight W).eval x.length) validity.builder rows.rows
    (fun row => (rows.rowValid row).mono hext)
    (verifierTableauInputs W c x hc)
    (fun row => verifierTableauCfg W c x row.val) hdecoded step).2 (by
      simpa using verifierTableauCfg_step W c x step.val)

/-- The complete symbolic initial boundary is true on the concrete tableau. -/
theorem VerifierWitness.verifierInitialBoundary_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ} (hc : c.length ≤ W.certificateBound.eval x.length) :
    (verifierInitialBoundary W x).builder.evalWire
        (verifierTableauInputs W c x hc)
        (verifierInitialBoundary W x).wire = true := by
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let hext := pool.extension.trans
    (validity.extension.trans transitions.extension)
  let first := verifierFirstRow ((verifierHorizon W).eval x.length)
  let row := rows.rows first
  let hrow := (rows.rowValid first).mono hext
  have hdecoded : evalBundle transitions.builder
      (verifierTableauInputs W c x hc) row hrow =
        some (verifierInitialCfg W c x) := by
    dsimp only [row, hrow]
    simpa [first, verifierFirstRow, verifierTableauCfg] using
      W.verifierRows_eval_at hc hext first
  have hrep : (evalStackBits transitions.builder
      (verifierTableauInputs W c x hc) (row.stack W.machine.tm.k₀)).Represents
        (List.map W.machine.inputAlphabet.invFun (pairEncoding c x)) := by
    simpa [evalStackBits_cfgStack, verifierInitialCfg,
      _root_.Turing.initList] using
      evalBundle_stack_represents transitions.builder
        (verifierTableauInputs W c x hc) row hrow hdecoded W.machine.tm.k₀
  unfold verifierInitialBoundary
  apply (symbolicInitialCfgCircuit_eval_iff W.machine.tm
    ((verifierHeight W).eval x.length) transitions.builder
    (pool.pool.mono (validity.extension.trans transitions.extension))
    (verifierTableauInputs W c x hc) row hrow
    (row.stack W.machine.tm.k₀) (hrow.stack _) _ hrep).2
  exact hdecoded

/-- The input-shape boundary is true on the concrete bounded certificate. -/
theorem VerifierWitness.verifierInputBoundary_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ} (hc : c.length ≤ W.certificateBound.eval x.length) :
    (verifierInputBoundary W x).builder.evalWire
        (verifierTableauInputs W c x hc)
        (verifierInputBoundary W x).wire = true := by
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let hext := pool.extension.trans (validity.extension.trans
    (transitions.extension.trans initial.extension))
  let first := verifierFirstRow ((verifierHorizon W).eval x.length)
  let row := rows.rows first
  let hrow := (rows.rowValid first).mono hext
  have hdecoded := W.verifierRows_eval_at hc hext first
  have hrep : (evalStackBits initial.builder
      (verifierTableauInputs W c x hc) (row.stack W.machine.tm.k₀)).Represents
        (List.map W.machine.inputAlphabet.invFun (pairEncoding c x)) := by
    simpa [evalStackBits_cfgStack, verifierTableauCfg, verifierInitialCfg,
      _root_.Turing.initList, first, verifierFirstRow] using
      evalBundle_stack_represents initial.builder
        (verifierTableauInputs W c x hc) row hrow hdecoded W.machine.tm.k₀
  unfold verifierInputBoundary
  apply (verifierInputShapeCircuit_eval_iff W
    ((verifierHeight W).eval x.length) initial.builder
    (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans initial.extension)))
    (row.stack W.machine.tm.k₀) (hrow.stack _) x
    (verifierTableauInputs W c x hc) _ hrep).2
  exact ⟨c, hc, rfl⟩

/-- The exact accepting boundary is true for an accepting certificate. -/
theorem VerifierWitness.verifierAcceptingBoundary_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ} (hc : c.length ≤ W.certificateBound.eval x.length)
    (hverify : W.verify c x = true) :
    (verifierAcceptingBoundary W x).builder.evalWire
        (verifierTableauInputs W c x hc)
        (verifierAcceptingBoundary W x).wire = true := by
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let input := verifierInputBoundary W x
  let hext := pool.extension.trans (validity.extension.trans
    (transitions.extension.trans (initial.extension.trans input.extension)))
  let last := Fin.last ((verifierHorizon W).eval x.length)
  let row := rows.rows last
  let hrow := (rows.rowValid last).mono hext
  have hdecoded := W.verifierRows_eval_at hc hext last
  unfold verifierAcceptingBoundary
  apply (acceptingOutputCircuit_eval_iff W.machine.tm
    ((verifierHeight W).eval x.length) input.builder
    (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans (initial.extension.trans input.extension))))
    (verifierTableauInputs W c x hc) row hrow _).2
  rw [hdecoded]
  congr 1
  exact verifierTableauCfg_last_of_accepts W hc hverify

/-- An accepting certificate makes the assembled final conjunction true. -/
theorem VerifierWitness.verifierConjunction_complete
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ} (hc : c.length ≤ W.certificateBound.eval x.length)
    (hverify : W.verify c x = true) :
    (verifierConjunction W x).1.evalWire
        (verifierTableauInputs W c x hc)
        (verifierConjunction W x).2 = true := by
  apply verifierConjunction_true_of_components W x
      (verifierTableauInputs W c x hc)
  · exact W.verifierValidity_output_true hc
  · exact W.verifierTransitions_output_true hc
  · exact W.verifierInitialBoundary_true hc
  · exact W.verifierInputBoundary_true hc
  · exact W.verifierAcceptingBoundary_true hc hverify

end

end CLRS.Chapter34.Turing.CookLevin
