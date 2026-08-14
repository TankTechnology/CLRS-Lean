import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.Families
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauLayout

/-!
# Chapter 34 whole-tableau constraint-family regressions

Focused structural and semantic checks for serial row-validity and adjacent-row
transition families.  Boundary constraints and their final conjunction are
intentionally outside this test.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing

noncomputable section

#check ValidCfgCircuitFamilyResult
#check ValidCfgCircuitFamilyGateTrace
#check validCfgCircuitFamilyGateTrace
#check validCfgCircuitFamilyGateTrace_length
#check validCfgCircuitFamilyGateTrace_gates_eq_flatMap
#check validCfgCircuitFamily
#check validCfgCircuitFamily_gates_eq
#check validCfgCircuitFamily_output_eq_trace
#check validCfgCircuitFamily_extends
#check validCfgCircuitFamily_outputs_valid
#check validCfgCircuitFamily_gate_delta
#check validCfgCircuitFamily_evalCfgBits
#check validCfgCircuitFamily_evalBundle
#check validCfgCircuitFamily_eval_iff
#check validCfgCircuitFamily_proof_irrel

#check TransitionCircuitFamilyResult
#check transitionCircuitFamily
#check transitionCircuitFamily_extends
#check transitionCircuitFamily_outputs_valid
#check transitionCircuitFamily_gate_delta
#check transitionCircuitFamily_evalCfgBits
#check transitionCircuitFamily_evalBundle
#check transitionCircuitFamily_eval_iff
#check transitionCircuitFamily_proof_irrel

private abbrev FamilyMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .halt

private def emptyFamilyBase : CircuitBuilder := CircuitBuilder.empty 0

private def emptyRows : Fin 0 → CfgWires FamilyMachine 0 := Fin.elim0

private theorem emptyRowsValid : ∀ i, (emptyRows i).ValidIn emptyFamilyBase :=
  fun i => Fin.elim0 i

private def emptyValidityFamily :=
  validCfgCircuitFamily emptyFamilyBase emptyRows emptyRowsValid

example : emptyValidityFamily.builder = emptyFamilyBase := rfl

example : emptyValidityFamily.builder.gates.length =
    emptyFamilyBase.gates.length + 0 * validCfgGateCost FamilyMachine 0 :=
  validCfgCircuitFamily_gate_delta emptyFamilyBase emptyRows emptyRowsValid

private def threeRows := allocateTableauRows FamilyMachine 0 2

private def threeRowValidityFamily :=
  validCfgCircuitFamily threeRows.builder threeRows.rows threeRows.rowValid

example : threeRowValidityFamily.builder.gates.length =
    threeRows.builder.gates.length + 3 * validCfgGateCost FamilyMachine 0 :=
  validCfgCircuitFamily_gate_delta threeRows.builder threeRows.rows
    threeRows.rowValid

example : threeRowValidityFamily.builder.gates =
    threeRows.builder.gates ++
      (validCfgCircuitFamilyGateTrace threeRows.builder.gates.length
        3 threeRows.rows).gates :=
  validCfgCircuitFamily_gates_eq threeRows.builder threeRows.rows
    threeRows.rowValid

example (row : Fin 3) : threeRowValidityFamily.outputs row =
    (validCfgCircuitFamilyGateTrace threeRows.builder.gates.length
      3 threeRows.rows).outputs row :=
  validCfgCircuitFamily_output_eq_trace threeRows.builder threeRows.rows
    threeRows.rowValid row

example (row : Fin 3) : threeRowValidityFamily.builder.WireValid
    (threeRowValidityFamily.outputs row) :=
  validCfgCircuitFamily_outputs_valid threeRows.builder threeRows.rows
    threeRows.rowValid row

example (inputs : Nat → Bool) (row : Fin 3) :
    evalCfgBits threeRowValidityFamily.builder inputs (threeRows.rows row) =
      evalCfgBits threeRows.builder inputs (threeRows.rows row) :=
  validCfgCircuitFamily_evalCfgBits threeRows.builder threeRows.rows
    threeRows.rowValid inputs row

private def oneRow := allocateTableauRows FamilyMachine 0 0

private def zeroTransitionFamily :=
  transitionCircuitFamily FamilyMachine 0 oneRow.builder oneRow.rows oneRow.rowValid

example : zeroTransitionFamily.builder = oneRow.builder := rfl

example : zeroTransitionFamily.builder.gates.length =
    oneRow.builder.gates.length + 0 * transitionCircuitGateCost FamilyMachine 0 :=
  transitionCircuitFamily_gate_delta FamilyMachine 0 oneRow.builder oneRow.rows
    oneRow.rowValid

private def twoTransitionFamily :=
  transitionCircuitFamily FamilyMachine 0 threeRows.builder threeRows.rows
    threeRows.rowValid

example : twoTransitionFamily.builder.gates.length =
    threeRows.builder.gates.length + 2 * transitionCircuitGateCost FamilyMachine 0 :=
  transitionCircuitFamily_gate_delta FamilyMachine 0 threeRows.builder
    threeRows.rows threeRows.rowValid

example (step : Fin 2) : twoTransitionFamily.builder.WireValid
    (twoTransitionFamily.outputs step) :=
  transitionCircuitFamily_outputs_valid FamilyMachine 0 threeRows.builder
    threeRows.rows threeRows.rowValid step

example (inputs : Nat → Bool)
    (configs : Fin 3 → FamilyMachine.Cfg)
    (hdecoded : ∀ row,
      evalBundle threeRows.builder inputs (threeRows.rows row)
        (threeRows.rowValid row) = some (configs row))
    (step : Fin 2) :
    twoTransitionFamily.builder.evalWire inputs
        (twoTransitionFamily.outputs step) = true ↔
      configs step.succ = stutterStep FamilyMachine (configs step.castSucc) := by
  exact transitionCircuitFamily_eval_iff FamilyMachine 0 threeRows.builder
    threeRows.rows threeRows.rowValid inputs configs hdecoded step

#print axioms validCfgCircuitFamily_gates_eq
#print axioms validCfgCircuitFamily_output_eq_trace
#print axioms validCfgCircuitFamilyGateTrace_gates_eq_flatMap

end

end CLRS.Chapter34.Turing.CookLevin
