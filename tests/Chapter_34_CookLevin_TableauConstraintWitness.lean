import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.Witness

/-!
# Chapter 34 tableau-constraint witness regressions

The concrete verifier tableau must satisfy every validity and transition family
output, while the generic reverse helpers recover decoded rows and the stutter
chain from true family outputs.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

#check verifierTableauInputs
#check verifierValidityFamily
#check verifierTransitionFamily
#check VerifierWitness.verifierValidityFamily_output_true
#check VerifierWitness.verifierValidityFamily_outputs_true
#check VerifierWitness.verifierValidityFamily_outputs_list_all
#check VerifierWitness.verifierTransitionFamily_output_true
#check VerifierWitness.verifierTransitionFamily_outputs_true
#check VerifierWitness.verifierTransitionFamily_outputs_list_all
#check validCfgCircuitFamily_existsUnique_decoded
#check transitionCircuitFamily_stutter_chain

variable {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
variable {c x : List Γ}
variable (hc : c.length ≤ W.certificateBound.eval x.length)

example
    (row : Fin (tableauRowCount ((verifierHorizon W).eval x.length))) :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierValidityFamily W x
    family.builder.evalWire inputs (family.outputs row) = true :=
  W.verifierValidityFamily_output_true hc row

example :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierValidityFamily W x
    (List.ofFn fun row =>
      family.builder.evalWire inputs (family.outputs row)).all id = true :=
  W.verifierValidityFamily_outputs_list_all hc

example
    (step : Fin ((verifierHorizon W).eval x.length)) :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierTransitionFamily W x
    family.builder.evalWire inputs (family.outputs step) = true :=
  W.verifierTransitionFamily_output_true hc step

example :
    let inputs := verifierTableauInputs W c x hc
    let family := verifierTransitionFamily W x
    (List.ofFn fun step =>
      family.builder.evalWire inputs (family.outputs step)).all id = true :=
  W.verifierTransitionFamily_outputs_list_all hc

section SoundnessHelpers

variable {tm : _root_.Turing.FinTM2} {H n T : Nat}
variable (base : CircuitBuilder) (inputs : Nat → Bool)

example (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base)
    (hall : ∀ row,
      (validCfgCircuitFamily base rows hrows).builder.evalWire inputs
        ((validCfgCircuitFamily base rows hrows).outputs row) = true)
    (row : Fin n) :
    ∃! cfg : tm.Cfg,
      evalBundle base inputs (rows row) (hrows row) = some cfg :=
  validCfgCircuitFamily_existsUnique_decoded base rows hrows inputs hall row

example (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base)
    (configs : Fin (T + 1) → tm.Cfg)
    (hdecoded : ∀ row,
      evalBundle base inputs (rows row) (hrows row) = some (configs row))
    (hall : ∀ step,
      (transitionCircuitFamily tm H base rows hrows).builder.evalWire inputs
        ((transitionCircuitFamily tm H base rows hrows).outputs step) = true)
    (step : Fin T) :
    configs step.succ = stutterStep tm (configs step.castSucc) :=
  transitionCircuitFamily_stutter_chain tm H base rows hrows inputs configs
    hdecoded hall step

end SoundnessHelpers

end

end CLRS.Chapter34.Turing.CookLevin
