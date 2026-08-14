import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Core

/-!
# Chapter 34 verifier-input shape circuit regressions

This file checks the structural core only: it deliberately does not import an
initial-row wrapper or state the semantic iff reserved for the next slice.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

#check verifierInputArmGateCost
#check verifierInputShapeGateCost
#check VerifierInputShapeResult
#check verifierInputShapeCircuit
#check verifierInputShapeCircuit_extends
#check verifierInputShapeCircuit_wireValid
#check verifierInputShapeCircuit_gate_delta
#check verifierInputShapeCircuit_proof_irrel

private def poolStack {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    {base : CircuitBuilder} (pool : base.BoolWirePool) : StackWires tm H k where
  height := fun _ => pool.trueWire
  cell := fun _ _ => pool.trueWire

private theorem poolStack_valid {tm : _root_.Turing.FinTM2} {H : Nat}
    {k : tm.K} {base : CircuitBuilder} (pool : base.BoolWirePool) :
    (poolStack (tm := tm) (H := H) (k := k) pool).ValidIn base :=
  ⟨fun _ => pool.trueValid, fun _ _ => pool.trueValid⟩

-- At height zero no certificate length fits.  The circuit emits only the
-- one-arm final disjunction: one false seed and one OR gate.
example {L : Language Empty} (W : VerifierWitness L)
    (hbound : W.certificateBound.eval 0 = 0) :
    let allocation := CircuitBuilder.allocateBoolWirePool
      (CircuitBuilder.empty 0)
    let inputStack : StackWires W.machine.tm 0 W.machine.tm.k₀ :=
      poolStack allocation.pool
    (verifierInputShapeCircuit W 0 allocation.builder allocation.pool
      inputStack (poolStack_valid allocation.pool) []).builder.gates.length =
        allocation.builder.gates.length + 2 := by
  dsimp only
  rw [verifierInputShapeCircuit_gate_delta]
  simp [verifierInputShapeGateCost, verifierInputArmGateCost, hbound]

-- With bound one, one fixed public symbol, and height three, both length arms
-- fit.  The exact delta is 3 separator NOTs + (4 + 5) arm gates + 3 final OR
-- gates, independent of the verifier machine's reachable-alphabet cardinality.
example {L : Language Bool} (W : VerifierWitness L)
    (hbound : W.certificateBound.eval 1 = 1) :
    let allocation := CircuitBuilder.allocateBoolWirePool
      (CircuitBuilder.empty 0)
    let inputStack : StackWires W.machine.tm 3 W.machine.tm.k₀ :=
      poolStack allocation.pool
    (verifierInputShapeCircuit W 3 allocation.builder allocation.pool
      inputStack (poolStack_valid allocation.pool) [true]).builder.gates.length =
        allocation.builder.gates.length + 15 := by
  dsimp only
  rw [verifierInputShapeCircuit_gate_delta]
  rw [show verifierInputShapeGateCost W 3 [true] = 15 by
    have hbound' : W.certificateBound.eval [true].length = 1 := by
      simpa using hbound
    rw [verifierInputShapeGateCost, hbound']
    change 3 + (∑ length : Fin 2,
      verifierInputArmGateCost 3 1 length.val) + 3 = 15
    rw [Fin.sum_univ_two]
    norm_num [verifierInputArmGateCost]]

end

end CLRS.Chapter34.Turing.CookLevin
