import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Semantics

/-!
# CLRS Section 34.4 - Fresh local-transition completeness

Two consecutive external-input layouts support simultaneous canonical row
encodings because the second write preserves every coordinate of the first.
The existing arbitrary-row transition theorem then proves the final internal
constraint wire.  A canonical wrapper packages the total Nat assignment in
the same finite-assignment form used by general-circuit satisfiability.

Main results:

- Theorem {lit}`freshTransitionCircuitAt_complete_nat`: reusable completeness
  over an arbitrary starting builder, offset, and base assignment.
- Theorem {lit}`freshTransitionCircuitAt_sound`: direct soundness of the fresh
  offset-parametric construction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Two disjoint canonical writes -/

/-- Patch canonical current and next rows into consecutive external-input
intervals, retaining the caller's assignment everywhere else. -/
def freshTransitionInputsAt
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (layout : CfgInputLayout tm H) (assignment : Nat → Bool)
    (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hnextAlphabet : CfgAlphabetBounded tm next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H) : Nat → Bool :=
  layout.next.writeCfgBits
    (layout.writeCfgBits assignment
      (encodeRawCfgBits
        (encodeCfg tm hcurrentAlphabet hcurrentHeight)))
    (encodeRawCfgBits (encodeCfg tm hnextAlphabet hnextHeight))

/-- The second canonical write does not overwrite a first-row coordinate. -/
theorem freshTransitionInputsAt_current_index
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (layout : CfgInputLayout tm H) (assignment : Nat → Bool)
    (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hnextAlphabet : CfgAlphabetBounded tm next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H)
    (slot : CfgSlot tm H) :
    freshTransitionInputsAt tm H layout assignment current next
        hcurrentAlphabet hcurrentHeight hnextAlphabet hnextHeight
        (layout.index slot).val =
      encodeRawCfgBits (encodeCfg tm hcurrentAlphabet hcurrentHeight) slot := by
  exact CfgInputLayout.writeCfgBits_index_of_disjoint
    (CfgInputLayout.next_disjoint layout) assignment
    (encodeRawCfgBits (encodeCfg tm hcurrentAlphabet hcurrentHeight))
    (encodeRawCfgBits (encodeCfg tm hnextAlphabet hnextHeight)) slot

/-- Reading a second-row coordinate returns the target canonical bit. -/
theorem freshTransitionInputsAt_next_index
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (layout : CfgInputLayout tm H) (assignment : Nat → Bool)
    (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hnextAlphabet : CfgAlphabetBounded tm next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H)
    (slot : CfgSlot tm H) :
    freshTransitionInputsAt tm H layout assignment current next
        hcurrentAlphabet hcurrentHeight hnextAlphabet hnextHeight
        (layout.next.index slot).val =
      encodeRawCfgBits (encodeCfg tm hnextAlphabet hnextHeight) slot := by
  exact CfgInputLayout.writeCfgBits_at layout.next
    (layout.writeCfgBits assignment
      (encodeRawCfgBits (encodeCfg tm hcurrentAlphabet hcurrentHeight)))
    (encodeRawCfgBits (encodeCfg tm hnextAlphabet hnextHeight)) slot

/-- Both canonical writes preserve the caller's assignment at every input
outside both row intervals. -/
theorem freshTransitionInputsAt_outside
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (layout : CfgInputLayout tm H) (assignment : Nat → Bool)
    (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hnextAlphabet : CfgAlphabetBounded tm next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H)
    (inputIndex : Nat)
    (hcurrentOutside : inputIndex < layout.base ∨
      layout.finish ≤ inputIndex)
    (hnextOutside : inputIndex < layout.next.base ∨
      layout.next.finish ≤ inputIndex) :
    freshTransitionInputsAt tm H layout assignment current next
        hcurrentAlphabet hcurrentHeight hnextAlphabet hnextHeight inputIndex =
      assignment inputIndex := by
  rw [freshTransitionInputsAt,
    layout.next.writeCfgBits_outside _ _ hnextOutside,
    layout.writeCfgBits_outside _ _ hcurrentOutside]

/-! ## Offset-parametric completeness and soundness -/

/-- Any genuine bounded local step has a satisfying total Nat assignment on
two freshly allocated consecutive row layouts.  The arbitrary base assignment
is preserved outside those two intervals, making this lemma reusable while a
larger tableau assignment is assembled. -/
theorem freshTransitionCircuitAt_complete_nat
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount)
    (baseAssignment : Nat → Bool) (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hstep : next = stutterStep tm current)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H) :
    let final := freshTransitionCircuitAt tm H start layout hfit
    let hnextAlphabet : CfgAlphabetBounded tm next := by
      rw [hstep]
      exact stutterStep_alphabetBounded tm hcurrentAlphabet
    let inputs := freshTransitionInputsAt tm H layout baseAssignment
      current next hcurrentAlphabet hcurrentHeight
      hnextAlphabet hnextHeight
    evalBundle final.builder inputs final.current final.currentValid =
        some current ∧
      evalBundle final.builder inputs final.next final.nextValid = some next ∧
      final.builder.evalWire inputs final.wire = true := by
  let hnextAlphabet : CfgAlphabetBounded tm next := by
    rw [hstep]
    exact stutterStep_alphabetBounded tm hcurrentAlphabet
  let inputs := freshTransitionInputsAt tm H layout baseAssignment
    current next hcurrentAlphabet hcurrentHeight hnextAlphabet hnextHeight
  let currentAllocation :=
    freshCurrentAllocationAt tm H start layout hfit
  let nextAllocation := freshNextAllocationAt tm H start layout hfit
  have hcurrentAtNext : currentAllocation.wires.ValidIn
      nextAllocation.builder :=
    currentAllocation.valid.mono nextAllocation.extension
  let transition := transitionCircuit tm H nextAllocation.builder
    currentAllocation.wires nextAllocation.wires hcurrentAtNext
    nextAllocation.valid
  have hcurrentDecodedAtCurrent :
      evalBundle currentAllocation.builder inputs currentAllocation.wires
        currentAllocation.valid = some current := by
    apply evalBundle_encodeCfg
    funext slot
    rw [evalCfgBits, currentAllocation.eval_slot]
    exact freshTransitionInputsAt_current_index tm H layout baseAssignment
      current next hcurrentAlphabet hcurrentHeight hnextAlphabet hnextHeight slot
  have hcurrentDecodedAtNext :
      evalBundle nextAllocation.builder inputs currentAllocation.wires
        hcurrentAtNext = some current := by
    rw [evalBundle_extends nextAllocation.extension inputs
      currentAllocation.wires currentAllocation.valid]
    exact hcurrentDecodedAtCurrent
  have hnextDecodedAtNext :
      evalBundle nextAllocation.builder inputs nextAllocation.wires
        nextAllocation.valid = some next := by
    exact nextAllocation.evalBundle_write_encodeCfg
      (layout.writeCfgBits baseAssignment
        (encodeRawCfgBits (encodeCfg tm hcurrentAlphabet hcurrentHeight)))
      hnextAlphabet hnextHeight
  have hcurrentDecodedFinal :
      evalBundle transition.builder inputs currentAllocation.wires
        (hcurrentAtNext.mono transition.extension) = some current := by
    rw [evalBundle_extends transition.extension inputs
      currentAllocation.wires hcurrentAtNext]
    exact hcurrentDecodedAtNext
  have hnextDecodedFinal :
      evalBundle transition.builder inputs nextAllocation.wires
        (nextAllocation.valid.mono transition.extension) = some next := by
    rw [evalBundle_extends transition.extension inputs
      nextAllocation.wires nextAllocation.valid]
    exact hnextDecodedAtNext
  have htransition : transition.builder.evalWire inputs transition.wire = true :=
    (transitionCircuit_eval_iff tm H nextAllocation.builder inputs
      currentAllocation.wires nextAllocation.wires hcurrentAtNext
      nextAllocation.valid hcurrentDecodedAtNext hnextDecodedAtNext).mpr hstep
  change evalBundle transition.builder inputs currentAllocation.wires
      (hcurrentAtNext.mono transition.extension) = some current ∧
    evalBundle transition.builder inputs nextAllocation.wires
      (nextAllocation.valid.mono transition.extension) = some next ∧
    transition.builder.evalWire inputs transition.wire = true
  exact ⟨hcurrentDecodedFinal, hnextDecodedFinal, htransition⟩

/-- Soundness of an offset-parametric fresh construction is inherited from
the arbitrary-valid-bundle local transition theorem. -/
theorem freshTransitionCircuitAt_sound
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) (inputs : Nat → Bool)
    {current next : tm.Cfg}
    (hcurrentDecoded :
      let final := freshTransitionCircuitAt tm H start layout hfit
      evalBundle final.builder inputs final.current final.currentValid =
        some current)
    (hnextDecoded :
      let final := freshTransitionCircuitAt tm H start layout hfit
      evalBundle final.builder inputs final.next final.nextValid = some next)
    (htransition :
      let final := freshTransitionCircuitAt tm H start layout hfit
      final.builder.evalWire inputs final.wire = true) :
    next = stutterStep tm current := by
  let currentAllocation :=
    freshCurrentAllocationAt tm H start layout hfit
  let nextAllocation := freshNextAllocationAt tm H start layout hfit
  have hcurrentAtNext : currentAllocation.wires.ValidIn
      nextAllocation.builder :=
    currentAllocation.valid.mono nextAllocation.extension
  let transition := transitionCircuit tm H nextAllocation.builder
    currentAllocation.wires nextAllocation.wires hcurrentAtNext
    nextAllocation.valid
  have hcurrentAtBase :
      evalBundle nextAllocation.builder inputs currentAllocation.wires
        hcurrentAtNext = some current := by
    rw [← evalBundle_extends transition.extension inputs
      currentAllocation.wires hcurrentAtNext]
    exact hcurrentDecoded
  have hnextAtBase :
      evalBundle nextAllocation.builder inputs nextAllocation.wires
        nextAllocation.valid = some next := by
    rw [← evalBundle_extends transition.extension inputs
      nextAllocation.wires nextAllocation.valid]
    exact hnextDecoded
  exact transitionCircuit_sound tm H nextAllocation.builder inputs
    currentAllocation.wires nextAllocation.wires hcurrentAtNext
    nextAllocation.valid hcurrentAtBase hnextAtBase htransition

end

end CLRS.Chapter34.Turing.CookLevin
