import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh.Semantics

/-!
# CLRS Section 34.4 - Finite fresh-transition witnesses

This module specializes offset-parametric Nat-assignment completeness to the
canonical zero-offset circuit and packages the witness in the finite assignment
shape used by general-circuit satisfiability.

Main results:

- Theorem {lit}`freshTransitionCircuit_complete`: finite local completeness.
- Theorem {lit}`freshTransitionCircuit_sound`: direct canonical soundness.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Extend a finite assignment exactly as general-circuit satisfiability does. -/
def finiteCircuitInputs (b : CircuitBuilder)
    (assignment : Fin b.inputCount → Bool) : Nat → Bool :=
  fun i => if hi : i < b.inputCount then assignment ⟨i, hi⟩ else false

/-- Every bounded genuine step has a finite satisfying assignment for the
canonical fresh two-row circuit.  Both source and target height premises are
essential: a pop may reduce an oversized source into a fitting target. -/
theorem freshTransitionCircuit_complete
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hstep : next = stutterStep tm current)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H) :
    ∃ assignment : Fin (freshTransitionCircuit tm H).builder.inputCount → Bool,
      let inputs := finiteCircuitInputs (freshTransitionCircuit tm H).builder
        assignment
      evalBundle (freshTransitionCircuit tm H).builder inputs
          (freshTransitionCircuit tm H).current
          (freshTransitionCircuit tm H).currentValid = some current ∧
        evalBundle (freshTransitionCircuit tm H).builder inputs
          (freshTransitionCircuit tm H).next
          (freshTransitionCircuit tm H).nextValid = some next ∧
        (freshTransitionCircuit tm H).builder.evalWire inputs
          (freshTransitionCircuit tm H).wire = true := by
  let hnextAlphabet : CfgAlphabetBounded tm next := by
    rw [hstep]
    exact stutterStep_alphabetBounded tm hcurrentAlphabet
  let natInputs := freshTransitionInputsAt tm H (freshCurrentLayout tm H)
    (fun _ => false) current next hcurrentAlphabet hcurrentHeight
    hnextAlphabet hnextHeight
  let assignment : Fin (freshTransitionCircuit tm H).builder.inputCount →
      Bool := fun i => natInputs i.val
  refine ⟨assignment, ?_⟩
  have hfinite :
      finiteCircuitInputs (freshTransitionCircuit tm H).builder assignment =
        natInputs := by
    funext i
    by_cases hi : i < (freshTransitionCircuit tm H).builder.inputCount
    · simp [finiteCircuitInputs, assignment, hi]
    · have hfinish : (freshNextLayout tm H).finish ≤ i := by
        have hcount := freshTransitionCircuit_inputCount tm H
        unfold freshTransitionInputCount at hcount
        omega
      have hcurrentFinish : (freshCurrentLayout tm H).finish ≤ i := by
        apply le_trans ?_ hfinish
        simp [freshNextLayout, CfgInputLayout.next,
          CfgInputLayout.finish]
      rw [finiteCircuitInputs, dif_neg hi]
      change false = natInputs i
      rw [show natInputs i = false by
        dsimp only [natInputs, freshTransitionInputsAt]
        change (freshNextLayout tm H).writeCfgBits
          ((freshCurrentLayout tm H).writeCfgBits (fun _ => false)
            (encodeRawCfgBits
              (encodeCfg tm hcurrentAlphabet hcurrentHeight)))
          (encodeRawCfgBits (encodeCfg tm hnextAlphabet hnextHeight)) i =
            false
        rw [(freshNextLayout tm H).writeCfgBits_outside
          _ _ (Or.inr hfinish)]
        rw [(freshCurrentLayout tm H).writeCfgBits_outside
          _ _ (Or.inr hcurrentFinish)]]
  rw [hfinite]
  exact freshTransitionCircuitAt_complete_nat tm H
    (freshTransitionStart tm H) (freshCurrentLayout tm H)
    (freshTransitionLayouts_fit tm H) (fun _ => false) current next
    hcurrentAlphabet hcurrentHeight hstep hnextHeight

/-- Direct soundness projection for the canonical fresh local circuit. -/
theorem freshTransitionCircuit_sound
    (tm : _root_.Turing.FinTM2) (H : Nat) (inputs : Nat → Bool)
    {current next : tm.Cfg}
    (hcurrentDecoded :
      evalBundle (freshTransitionCircuit tm H).builder inputs
        (freshTransitionCircuit tm H).current
        (freshTransitionCircuit tm H).currentValid = some current)
    (hnextDecoded :
      evalBundle (freshTransitionCircuit tm H).builder inputs
        (freshTransitionCircuit tm H).next
        (freshTransitionCircuit tm H).nextValid = some next)
    (htransition :
      (freshTransitionCircuit tm H).builder.evalWire inputs
        (freshTransitionCircuit tm H).wire = true) :
    next = stutterStep tm current :=
  freshTransitionCircuitAt_sound tm H (freshTransitionStart tm H)
    (freshCurrentLayout tm H) (freshTransitionLayouts_fit tm H) inputs
    hcurrentDecoded hnextDecoded htransition

end

end CLRS.Chapter34.Turing.CookLevin
