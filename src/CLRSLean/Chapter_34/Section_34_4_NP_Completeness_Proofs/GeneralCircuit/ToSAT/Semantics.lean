import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CircuitSAT
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Basic

/-!
# General circuit satisfiability to SAT: semantics

This file gives the textbook formula associated with an honest acyclic general
Boolean circuit.  Declared circuit inputs keep their natural-number indices;
gate `j` is represented by formula variable `c.inputCount + j`.  The final
formula asserts the designated output and conjoins one exact consistency
equation for every gate.

Main result:

- `generalCircuitSatisfiable_iff_satisfiable_generalCircuitToFormula`: a
  well-formed general circuit is satisfiable exactly when its generated formula
  is satisfiable.
-/

namespace CLRS.Chapter34

/-! ## Formula construction -/

/-- Formula-variable index assigned to a circuit gate.  The first
`c.inputCount` variables are reserved for declared circuit inputs. -/
def generalCircuitGateVar (c : Circuit) (gateIndex : Nat) : Nat :=
  c.inputCount + gateIndex

/-- Formula expression denoting the value computed by one general-circuit
gate.  Dependency indices refer to the gate-variable block. -/
def generalCircuitGateExpr (c : Circuit) : CircuitGate → Formula
  | .input inputIndex => .var inputIndex
  | .const value => .const value
  | .not source => .not (.var (generalCircuitGateVar c source))
  | .and left right =>
      .and (.var (generalCircuitGateVar c left))
        (.var (generalCircuitGateVar c right))
  | .or left right =>
      .or (.var (generalCircuitGateVar c left))
        (.var (generalCircuitGateVar c right))

/-- Consistency equation connecting gate `gateIndex` to its defining
expression. -/
def generalCircuitGateFormula (c : Circuit) (gateIndex : Nat)
    (gate : CircuitGate) : Formula :=
  .iff (.var (generalCircuitGateVar c gateIndex))
    (generalCircuitGateExpr c gate)

/-- Right-associated conjunction of gate-consistency equations, starting at a
runtime gate index. -/
def generalCircuitGateFormulasAux (c : Circuit) : Nat → List CircuitGate → Formula
  | _, [] => .const true
  | gateIndex, gate :: gates =>
      .and (generalCircuitGateFormula c gateIndex gate)
        (generalCircuitGateFormulasAux c (gateIndex + 1) gates)

/-- The textbook formula for a general circuit: assert the selected output and
all gate equations. -/
def generalCircuitToFormula (c : Circuit) : Formula :=
  .and (.var (generalCircuitGateVar c c.output))
    (generalCircuitGateFormulasAux c 0 c.gates)

/-! ## Completeness -/

/-- Extend a finite circuit-input assignment with the values of every evaluated
gate. -/
private def circuitFormulaAssignment (c : Circuit)
    (assignment : Fin c.inputCount → Bool) (i : Nat) : Bool :=
  if hi : i < c.inputCount then assignment ⟨i, hi⟩
  else
    (c.evalValues (fun j => if hj : j < c.inputCount then assignment ⟨j, hj⟩ else false)).getD
      (i - c.inputCount) false

private lemma circuitFormulaAssignment_input (c : Circuit)
    (assignment : Fin c.inputCount → Bool) (i : Nat) (hi : i < c.inputCount) :
    circuitFormulaAssignment c assignment i = assignment ⟨i, hi⟩ := by
  simp [circuitFormulaAssignment, hi]

private lemma circuitFormulaAssignment_gate (c : Circuit)
    (assignment : Fin c.inputCount → Bool) (i : Nat) :
    circuitFormulaAssignment c assignment (generalCircuitGateVar c i) =
      (c.evalValues
        (fun j => if hj : j < c.inputCount then assignment ⟨j, hj⟩ else false)).getD i false := by
  simp [circuitFormulaAssignment, generalCircuitGateVar]

private lemma eval_generalCircuitGateFormula (c : Circuit)
    (assignment : Fin c.inputCount → Bool) (hwellFormed : c.WellFormed)
    (i : Nat) (hi : i < c.gates.length) :
    Formula.eval
        (generalCircuitGateFormula c i (c.gates.get ⟨i, hi⟩))
        (circuitFormulaAssignment c assignment) = true := by
  let inputs : Nat → Bool :=
    fun j => if hj : j < c.inputCount then assignment ⟨j, hj⟩ else false
  have hgate := Circuit.evalValues_getElem_eq_gateEquation c inputs hwellFormed i hi
  have hvalid := hwellFormed.2 i hi
  have hsize : i < (c.evalValues inputs).size := by
    simpa [Circuit.evalValues_size] using hi
  generalize hcurrent : c.gates.get ⟨i, hi⟩ = current at hgate hvalid ⊢
  cases current with
  | input inputIndex =>
      have hinputValid : inputIndex < c.inputCount := by
        simpa [CircuitGate.ValidAt] using hvalid
      change ((circuitFormulaAssignment c assignment (generalCircuitGateVar c i) ==
        circuitFormulaAssignment c assignment inputIndex) = true)
      rw [circuitFormulaAssignment_gate]
      rw [circuitFormulaAssignment_input c assignment inputIndex hinputValid]
      rw [show (c.evalValues inputs).getD i false =
          (c.evalValues inputs)[i]'hsize by simp [Array.getD, hsize]]
      simpa [CircuitGate.GateEquation, inputs, hinputValid] using hgate
  | const value =>
      change ((circuitFormulaAssignment c assignment (generalCircuitGateVar c i) == value) = true)
      rw [circuitFormulaAssignment_gate]
      rw [show (c.evalValues inputs).getD i false =
          (c.evalValues inputs)[i]'hsize by simp [Array.getD, hsize]]
      simpa [CircuitGate.GateEquation] using hgate
  | not source =>
      obtain ⟨hsource, hgate⟩ := by
        simpa [CircuitGate.GateEquation] using hgate
      have hsourceSize : source < (c.evalValues inputs).size :=
        Nat.lt_trans hsource hsize
      change ((circuitFormulaAssignment c assignment (generalCircuitGateVar c i) ==
        !circuitFormulaAssignment c assignment (generalCircuitGateVar c source)) = true)
      rw [circuitFormulaAssignment_gate, circuitFormulaAssignment_gate]
      rw [show (c.evalValues inputs).getD i false =
          (c.evalValues inputs)[i]'hsize by simp [Array.getD, hsize]]
      rw [show (c.evalValues inputs).getD source false =
          (c.evalValues inputs)[source]'hsourceSize by simp [Array.getD, hsourceSize]]
      simp [hgate]
  | and left right =>
      obtain ⟨hleft, hright, hgate⟩ := by
        simpa [CircuitGate.GateEquation] using hgate
      have hleftSize : left < (c.evalValues inputs).size := Nat.lt_trans hleft hsize
      have hrightSize : right < (c.evalValues inputs).size := Nat.lt_trans hright hsize
      change ((circuitFormulaAssignment c assignment (generalCircuitGateVar c i) ==
        (circuitFormulaAssignment c assignment (generalCircuitGateVar c left) &&
          circuitFormulaAssignment c assignment (generalCircuitGateVar c right))) = true)
      rw [circuitFormulaAssignment_gate, circuitFormulaAssignment_gate,
        circuitFormulaAssignment_gate]
      rw [show (c.evalValues inputs).getD i false =
          (c.evalValues inputs)[i]'hsize by simp [Array.getD, hsize]]
      rw [show (c.evalValues inputs).getD left false =
          (c.evalValues inputs)[left]'hleftSize by simp [Array.getD, hleftSize]]
      rw [show (c.evalValues inputs).getD right false =
          (c.evalValues inputs)[right]'hrightSize by simp [Array.getD, hrightSize]]
      simp [hgate]
  | or left right =>
      obtain ⟨hleft, hright, hgate⟩ := by
        simpa [CircuitGate.GateEquation] using hgate
      have hleftSize : left < (c.evalValues inputs).size := Nat.lt_trans hleft hsize
      have hrightSize : right < (c.evalValues inputs).size := Nat.lt_trans hright hsize
      change ((circuitFormulaAssignment c assignment (generalCircuitGateVar c i) ==
        (circuitFormulaAssignment c assignment (generalCircuitGateVar c left) ||
          circuitFormulaAssignment c assignment (generalCircuitGateVar c right))) = true)
      rw [circuitFormulaAssignment_gate, circuitFormulaAssignment_gate,
        circuitFormulaAssignment_gate]
      rw [show (c.evalValues inputs).getD i false =
          (c.evalValues inputs)[i]'hsize by simp [Array.getD, hsize]]
      rw [show (c.evalValues inputs).getD left false =
          (c.evalValues inputs)[left]'hleftSize by simp [Array.getD, hleftSize]]
      rw [show (c.evalValues inputs).getD right false =
          (c.evalValues inputs)[right]'hrightSize by simp [Array.getD, hrightSize]]
      simp [hgate]

private lemma eval_generalCircuitGateFormulasAux (c : Circuit)
    (assignment : Fin c.inputCount → Bool) (hwellFormed : c.WellFormed)
    (pre rest : List CircuitGate) (hsplit : c.gates = pre ++ rest) :
    Formula.eval (generalCircuitGateFormulasAux c pre.length rest)
      (circuitFormulaAssignment c assignment) = true := by
  induction rest generalizing pre with
  | nil => simp [generalCircuitGateFormulasAux, Formula.eval]
  | cons gate rest ih =>
      have hi : pre.length < c.gates.length := by
        rw [hsplit]
        simp
      have hgate : c.gates.get ⟨pre.length, hi⟩ = gate := by
        have hgateOption : c.gates[pre.length]? = some gate := by
          rw [hsplit]
          simp
        rw [List.getElem?_eq_getElem hi] at hgateOption
        exact Option.some.inj hgateOption
      have hhead := eval_generalCircuitGateFormula c assignment hwellFormed pre.length hi
      rw [hgate] at hhead
      have htail := ih (pre := pre ++ [gate]) (by simpa [List.append_assoc] using hsplit)
      simpa [generalCircuitGateFormulasAux, Formula.eval, hhead, htail,
        List.length_append] using And.intro hhead htail

/-- A satisfying circuit assignment extends to a satisfying assignment of the
generated formula. -/
lemma generalCircuitSatisfiable_implies_formulaSatisfiable (c : Circuit) :
    GeneralCircuitSatisfiable c →
      Formula.Satisfiable (generalCircuitToFormula c) := by
  rintro ⟨hwellFormed, assignment, houtput⟩
  refine ⟨circuitFormulaAssignment c assignment, ?_⟩
  have hconstraints := eval_generalCircuitGateFormulasAux c assignment hwellFormed
    [] c.gates (by simp)
  have hconstraints' :
      Formula.eval (generalCircuitGateFormulasAux c 0 c.gates)
        (circuitFormulaAssignment c assignment) = true := by
    simpa using hconstraints
  have houtputVar :
      circuitFormulaAssignment c assignment (generalCircuitGateVar c c.output) = true := by
    rw [circuitFormulaAssignment_gate]
    have hsize : c.output < (c.evalValues
        (fun j => if hj : j < c.inputCount then assignment ⟨j, hj⟩ else false)).size := by
      simpa [Circuit.evalValues_size] using hwellFormed.1
    rw [show (c.evalValues
          (fun j => if hj : j < c.inputCount then assignment ⟨j, hj⟩ else false)).getD
          c.output false =
        (c.evalValues
          (fun j => if hj : j < c.inputCount then assignment ⟨j, hj⟩ else false))[c.output]'hsize by
        simp [Array.getD, hsize]]
    simpa [Circuit.eval_eq_getElem c _ hwellFormed] using houtput
  simp [generalCircuitToFormula, Formula.eval, houtputVar, hconstraints']

/-! ## Soundness -/

private lemma eval_generalCircuitGateFormulasAux_true
    (c : Circuit) (τ : Nat → Bool) (i : Nat) : ∀ rest : List CircuitGate,
    Formula.eval (generalCircuitGateFormulasAux c i rest) τ = true →
      ∀ j : Nat, (hj : j < rest.length) →
        Formula.eval
          (generalCircuitGateFormula c (i + j) (rest.get ⟨j, hj⟩)) τ = true := by
  intro rest
  induction rest generalizing i with
  | nil =>
      intro _ j hj
      simp at hj
  | cons gate rest ih =>
      intro h j hj
      have hparts :
          Formula.eval (generalCircuitGateFormula c i gate) τ = true ∧
            Formula.eval (generalCircuitGateFormulasAux c (i + 1) rest) τ = true := by
        simpa [generalCircuitGateFormulasAux, Formula.eval] using h
      cases j with
      | zero => simpa using hparts.1
      | succ j =>
          have hj' : j < rest.length := by simpa using hj
          have htail := ih (i := i + 1) hparts.2 j hj'
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- A satisfying formula assignment determines the unique gate-by-gate circuit
evaluation for a well-formed circuit. -/
private lemma evalValues_eq_formulaAssignment (c : Circuit) (τ : Nat → Bool)
    (hwellFormed : c.WellFormed)
    (hconstraints :
      Formula.eval (generalCircuitGateFormulasAux c 0 c.gates) τ = true) :
    ∀ i : Nat, (hi : i < c.gates.length) →
      (c.evalValues (fun j => if _hj : j < c.inputCount then τ j else false))[i]'
          (by simpa [Circuit.evalValues_size] using hi) =
        τ (generalCircuitGateVar c i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      let inputs : Nat → Bool :=
        fun j => if hj : j < c.inputCount then τ j else false
      have hformula := eval_generalCircuitGateFormulasAux_true c τ 0 c.gates
        hconstraints i hi
      have hactual := Circuit.evalValues_getElem_eq_gateEquation c inputs hwellFormed i hi
      have hvalid := hwellFormed.2 i hi
      generalize hcurrent : c.gates.get ⟨i, hi⟩ = current at hformula hactual hvalid
      cases current with
      | input inputIndex =>
          have hinputValid : inputIndex < c.inputCount := by
            simpa [CircuitGate.ValidAt] using hvalid
          have hformula' : τ (generalCircuitGateVar c i) = τ inputIndex := by
            simpa [generalCircuitGateFormula, generalCircuitGateExpr,
              Formula.eval] using hformula
          have hactual' :
              (c.evalValues inputs)[i]'(by simpa [Circuit.evalValues_size] using hi) =
                inputs inputIndex := by
            simpa only [CircuitGate.GateEquation] using hactual
          rw [show inputs inputIndex = τ inputIndex by simp [inputs, hinputValid]] at hactual'
          exact hactual'.trans hformula'.symm
      | const value =>
          have hformula' : τ (generalCircuitGateVar c i) = value := by
            simpa [generalCircuitGateFormula, generalCircuitGateExpr,
              Formula.eval] using hformula
          have hactual' :
              (c.evalValues inputs)[i]'(by simpa [Circuit.evalValues_size] using hi) =
                value := by
            simpa [CircuitGate.GateEquation] using hactual
          exact hactual'.trans hformula'.symm
      | not source =>
          obtain ⟨hsource, hactual'⟩ := by
            simpa [CircuitGate.GateEquation] using hactual
          have hsourceEq := ih source hsource (Nat.lt_trans hsource hi)
          have hformula' :
              τ (generalCircuitGateVar c i) = !τ (generalCircuitGateVar c source) := by
            simpa [generalCircuitGateFormula, generalCircuitGateExpr,
              Formula.eval] using hformula
          rw [hactual', hsourceEq, hformula']
      | and left right =>
          obtain ⟨hleft, hright, hactual'⟩ := by
            simpa [CircuitGate.GateEquation] using hactual
          have hleftEq := ih left hleft (Nat.lt_trans hleft hi)
          have hrightEq := ih right hright (Nat.lt_trans hright hi)
          have hformula' :
              τ (generalCircuitGateVar c i) =
                (τ (generalCircuitGateVar c left) &&
                  τ (generalCircuitGateVar c right)) := by
            simpa [generalCircuitGateFormula, generalCircuitGateExpr,
              Formula.eval] using hformula
          rw [hactual', hleftEq, hrightEq, hformula']
      | or left right =>
          obtain ⟨hleft, hright, hactual'⟩ := by
            simpa [CircuitGate.GateEquation] using hactual
          have hleftEq := ih left hleft (Nat.lt_trans hleft hi)
          have hrightEq := ih right hright (Nat.lt_trans hright hi)
          have hformula' :
              τ (generalCircuitGateVar c i) =
                (τ (generalCircuitGateVar c left) ||
                  τ (generalCircuitGateVar c right)) := by
            simpa [generalCircuitGateFormula, generalCircuitGateExpr,
              Formula.eval] using hformula
          rw [hactual', hleftEq, hrightEq, hformula']

/-- A satisfying assignment of the generated formula restricts to a satisfying
assignment of the original well-formed circuit. -/
lemma formulaSatisfiable_implies_generalCircuitSatisfiable (c : Circuit)
    (hwellFormed : c.WellFormed) :
    Formula.Satisfiable (generalCircuitToFormula c) →
      GeneralCircuitSatisfiable c := by
  rintro ⟨τ, hτ⟩
  have hparts :
      τ (generalCircuitGateVar c c.output) = true ∧
        Formula.eval (generalCircuitGateFormulasAux c 0 c.gates) τ = true := by
    simpa [generalCircuitToFormula, Formula.eval] using hτ
  refine ⟨hwellFormed, fun i => τ i, ?_⟩
  let inputs : Nat → Bool :=
    fun j => if hj : j < c.inputCount then τ j else false
  have hvalue := evalValues_eq_formulaAssignment c τ hwellFormed hparts.2
    c.output hwellFormed.1
  rw [Circuit.eval_eq_getElem c inputs hwellFormed]
  exact hvalue.trans hparts.1

/-- **General CIRCUIT-SAT to SAT, semantic form.**  For a well-formed circuit,
the direct consistency formula is satisfiable exactly when the circuit is. -/
theorem generalCircuitSatisfiable_iff_satisfiable_generalCircuitToFormula
    (c : Circuit) (hwellFormed : c.WellFormed) :
    GeneralCircuitSatisfiable c ↔
      Formula.Satisfiable (generalCircuitToFormula c) :=
  ⟨generalCircuitSatisfiable_implies_formulaSatisfiable c,
    formulaSatisfiable_implies_generalCircuitSatisfiable c hwellFormed⟩

end CLRS.Chapter34
