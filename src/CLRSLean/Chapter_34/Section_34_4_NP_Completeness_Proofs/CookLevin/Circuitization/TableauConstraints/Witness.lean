import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.Families
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauWitness

/-!
# Concrete witnesses for whole-tableau constraint families

The certificate-induced verifier tableau satisfies every serial row-validity
and adjacent-transition output.  The converse helpers recover decoded rows and
the stuttering chain from true family outputs.  Boundary constraints and the
final conjunction remain outside this layer.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Concrete builders and assignment -/

/-- Total external-input assignment induced by one bounded certificate. -/
def verifierTableauInputs {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (c x : List Γ)
    (hc : c.length ≤ W.certificateBound.eval x.length) : Nat → Bool :=
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  let allocation := allocateTableauRows W.machine.tm H T
  fun input => if hinput : input < allocation.builder.inputCount then
    verifierTableauAssignment W c x hc ⟨input, hinput⟩ else false

/-- Serial canonical-validity family over all allocated verifier rows. -/
def verifierValidityFamily {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  let allocation := allocateTableauRows W.machine.tm H T
  validCfgCircuitFamily allocation.builder allocation.rows allocation.rowValid

/-- Serial local-transition family over all adjacent verifier rows. -/
def verifierTransitionFamily {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :=
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  let allocation := allocateTableauRows W.machine.tm H T
  transitionCircuitFamily W.machine.tm H allocation.builder allocation.rows
    allocation.rowValid

/-! ## Concrete completeness -/

/-- Every concrete verifier row makes its canonical-validity output true. -/
theorem VerifierWitness.verifierValidityFamily_output_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length)
    (row : Fin (tableauRowCount ((verifierHorizon W).eval x.length))) :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierValidityFamily W x
    family.builder.evalWire inputs (family.outputs row) = true := by
  dsimp only [verifierTableauInputs, verifierValidityFamily]
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  let allocation := allocateTableauRows W.machine.tm H T
  apply (validCfgCircuitFamily_eval_iff allocation.builder allocation.rows
    allocation.rowValid _ row).2
  rw [W.allocateTableauRows_eval_verifierTableau hc row]
  rfl

/-- All concrete row-validity outputs are true. -/
theorem VerifierWitness.verifierValidityFamily_outputs_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierValidityFamily W x
    ∀ row, family.builder.evalWire inputs (family.outputs row) = true := by
  dsimp only
  intro row
  exact W.verifierValidityFamily_output_true hc row

/-- The finite list of concrete row-validity values is entirely true. -/
theorem VerifierWitness.verifierValidityFamily_outputs_list_all
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierValidityFamily W x
    (List.ofFn fun row =>
      family.builder.evalWire inputs (family.outputs row)).all id = true := by
  rw [List.all_eq_true]
  intro value hvalue
  simp only [List.mem_ofFn] at hvalue
  rcases hvalue with ⟨row, rfl⟩
  exact W.verifierValidityFamily_output_true hc row

/-- Every adjacent concrete verifier row pair makes its transition output
true. -/
theorem VerifierWitness.verifierTransitionFamily_output_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length)
    (step : Fin ((verifierHorizon W).eval x.length)) :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierTransitionFamily W x
    family.builder.evalWire inputs (family.outputs step) = true := by
  dsimp only [verifierTableauInputs, verifierTransitionFamily]
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  let allocation := allocateTableauRows W.machine.tm H T
  have hdecoded := fun row =>
    W.allocateTableauRows_eval_verifierTableau hc row
  exact (transitionCircuitFamily_eval_iff W.machine.tm H allocation.builder
    allocation.rows allocation.rowValid _
    (fun row => verifierTableauCfg W c x row.val) hdecoded step).2 (by
      simpa using verifierTableauCfg_step W c x step.val)

/-- All concrete adjacent-row transition outputs are true. -/
theorem VerifierWitness.verifierTransitionFamily_outputs_true
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierTransitionFamily W x
    ∀ step, family.builder.evalWire inputs (family.outputs step) = true := by
  dsimp only
  intro step
  exact W.verifierTransitionFamily_output_true hc step

/-- The finite list of concrete adjacent-transition values is entirely true. -/
theorem VerifierWitness.verifierTransitionFamily_outputs_list_all
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierTransitionFamily W x
    (List.ofFn fun step =>
      family.builder.evalWire inputs (family.outputs step)).all id = true := by
  rw [List.all_eq_true]
  intro value hvalue
  simp only [List.mem_ofFn] at hvalue
  rcases hvalue with ⟨step, rfl⟩
  exact W.verifierTransitionFamily_output_true hc step

/-! ## Generic soundness projections -/

/-- If every row-validity family output is true, each original public row has
a unique decoded machine configuration. -/
theorem validCfgCircuitFamily_existsUnique_decoded
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) (inputs : Nat → Bool)
    (hall : ∀ row,
      (validCfgCircuitFamily base rows hrows).builder.evalWire inputs
        ((validCfgCircuitFamily base rows hrows).outputs row) = true)
    (row : Fin n) :
    ∃! cfg : tm.Cfg, evalBundle base inputs (rows row) (hrows row) = some cfg := by
  have hsome := (validCfgCircuitFamily_eval_iff base rows hrows inputs row).mp
    (hall row)
  rcases Option.isSome_iff_exists.mp hsome with ⟨cfg, hcfg⟩
  refine ⟨cfg, hcfg, ?_⟩
  intro other hother
  rw [hcfg] at hother
  exact (Option.some.inj hother).symm

/-- If every transition-family output is true and the public rows decode to
the supplied configurations, those configurations form the complete local
stuttering chain. -/
theorem transitionCircuitFamily_stutter_chain
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) (inputs : Nat → Bool)
    (configs : Fin (T + 1) → tm.Cfg)
    (hdecoded : ∀ row,
      evalBundle base inputs (rows row) (hrows row) = some (configs row))
    (hall : ∀ step,
      (transitionCircuitFamily tm H base rows hrows).builder.evalWire inputs
        ((transitionCircuitFamily tm H base rows hrows).outputs step) = true) :
    ∀ step : Fin T,
      configs step.succ = stutterStep tm (configs step.castSucc) := by
  intro step
  exact (transitionCircuitFamily_eval_iff tm H base rows hrows inputs configs
    hdecoded step).mp (hall step)

end

end CLRS.Chapter34.Turing.CookLevin
