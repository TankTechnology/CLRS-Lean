import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh

/-!
# Chapter 34 Cook--Levin fresh-transition regressions

Actual finite-witness regressions for height-zero immediate halt and stutter,
three pushes into a fitting target row, nonaliasing row gates, preservation of
the first row by the second write, and a nonzero offset construction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Height-zero immediate halt and stutter -/

private abbrev HaltMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Empty
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .halt

private def haltSource : HaltMachine.Cfg where
  l := some ()
  var := ()
  stk := fun _ => []

private def haltedEmpty : HaltMachine.Cfg where
  l := none
  var := ()
  stk := fun _ => []

private theorem haltSourceAlphabet :
    CfgAlphabetBounded HaltMachine haltSource := by
  intro k a
  cases k
  exact Empty.elim a

private theorem haltedEmptyAlphabet :
    CfgAlphabetBounded HaltMachine haltedEmpty := by
  intro k a
  cases k
  exact Empty.elim a

private theorem haltSourceHeight :
    ∀ k, (haltSource.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

private theorem haltedEmptyHeight :
    ∀ k, (haltedEmpty.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

-- The finite witness decodes both height-zero rows and makes the actual final
-- internal transition wire true.
example :
    ∃ assignment :
        Fin (freshTransitionCircuit HaltMachine 0).builder.inputCount → Bool,
      let inputs := finiteCircuitInputs
        (freshTransitionCircuit HaltMachine 0).builder assignment
      evalBundle (freshTransitionCircuit HaltMachine 0).builder inputs
          (freshTransitionCircuit HaltMachine 0).current
          (freshTransitionCircuit HaltMachine 0).currentValid =
          some haltSource ∧
        evalBundle (freshTransitionCircuit HaltMachine 0).builder inputs
          (freshTransitionCircuit HaltMachine 0).next
          (freshTransitionCircuit HaltMachine 0).nextValid =
          some haltedEmpty ∧
        (freshTransitionCircuit HaltMachine 0).builder.evalWire inputs
          (freshTransitionCircuit HaltMachine 0).wire = true :=
  freshTransitionCircuit_complete HaltMachine 0 haltSource haltedEmpty
    haltSourceAlphabet haltSourceHeight rfl haltedEmptyHeight

-- Reserved-none is a genuine stuttering transition at height zero.
example :
    ∃ assignment :
        Fin (freshTransitionCircuit HaltMachine 0).builder.inputCount → Bool,
      let inputs := finiteCircuitInputs
        (freshTransitionCircuit HaltMachine 0).builder assignment
      evalBundle (freshTransitionCircuit HaltMachine 0).builder inputs
          (freshTransitionCircuit HaltMachine 0).current
          (freshTransitionCircuit HaltMachine 0).currentValid =
          some haltedEmpty ∧
        evalBundle (freshTransitionCircuit HaltMachine 0).builder inputs
          (freshTransitionCircuit HaltMachine 0).next
          (freshTransitionCircuit HaltMachine 0).nextValid =
          some haltedEmpty ∧
        (freshTransitionCircuit HaltMachine 0).builder.evalWire inputs
          (freshTransitionCircuit HaltMachine 0).wire = true := by
  apply freshTransitionCircuit_complete HaltMachine 0 haltedEmpty haltedEmpty
    haltedEmptyAlphabet haltedEmptyHeight
  · exact (stutterStep_halted HaltMachine rfl).symm
  · exact haltedEmptyHeight

-- The consecutive layouts and their actual internal input gates are distinct.
example : freshCurrentLayout HaltMachine 0 ≠ freshNextLayout HaltMachine 0 := by
  intro heq
  have hbase := congrArg CfgInputLayout.base heq
  simp [freshCurrentLayout, freshNextLayout, CfgInputLayout.next,
    CfgInputLayout.finish, cfgBitCount] at hbase

example (currentSlot nextSlot : CfgSlot HaltMachine 0) :
    (freshTransitionCircuit HaltMachine 0).current currentSlot ≠
      (freshTransitionCircuit HaltMachine 0).next nextSlot :=
  freshTransitionCircuit_rows_wire_ne HaltMachine 0 currentSlot nextSlot

example : (freshTransitionCircuit HaltMachine 0).builder.gates.length =
    2 * cfgBitCount HaltMachine 0 +
      transitionCircuitGateCost HaltMachine 0 :=
  freshTransitionCircuit_gate_delta HaltMachine 0

/-! ## Fitting multi-push target and preserved first write -/

private abbrev ThreePushMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push () (fun _ => true)
    (.push () (fun _ => false) (.push () (fun _ => true) .halt))

private def threePushSource : ThreePushMachine.Cfg where
  l := some ()
  var := ()
  stk := fun _ => []

private def threePushTarget : ThreePushMachine.Cfg :=
  stutterStep ThreePushMachine threePushSource

private theorem threePushSourceAlphabet :
    CfgAlphabetBounded ThreePushMachine threePushSource := by
  intro k a ha
  cases k
  simp [threePushSource] at ha

private theorem threePushSourceHeight :
    ∀ k, (threePushSource.stk k).length ≤ 3 := by
  intro k
  cases k
  simp [threePushSource]

private theorem threePushTargetHeight :
    ∀ k, (threePushTarget.stk k).length ≤ 3 := by
  intro k
  cases k
  rw [show threePushTarget.stk () = [true, false, true] from rfl]
  decide

-- All three pushed symbols are represented and the finite witness accepts.
example : threePushTarget.stk () = [true, false, true] := rfl

example :
    ∃ assignment :
        Fin (freshTransitionCircuit ThreePushMachine 3).builder.inputCount →
          Bool,
      let inputs := finiteCircuitInputs
        (freshTransitionCircuit ThreePushMachine 3).builder assignment
      evalBundle (freshTransitionCircuit ThreePushMachine 3).builder inputs
          (freshTransitionCircuit ThreePushMachine 3).current
          (freshTransitionCircuit ThreePushMachine 3).currentValid =
          some threePushSource ∧
        evalBundle (freshTransitionCircuit ThreePushMachine 3).builder inputs
          (freshTransitionCircuit ThreePushMachine 3).next
          (freshTransitionCircuit ThreePushMachine 3).nextValid =
          some threePushTarget ∧
        (freshTransitionCircuit ThreePushMachine 3).builder.evalWire inputs
          (freshTransitionCircuit ThreePushMachine 3).wire = true :=
  freshTransitionCircuit_complete ThreePushMachine 3 threePushSource
    threePushTarget threePushSourceAlphabet threePushSourceHeight rfl
    threePushTargetHeight

-- This explicitly exercises the frame fact used by completeness: the second
-- write leaves every first-row coordinate equal to its current encoding.
example (slot : CfgSlot ThreePushMachine 3) :
    freshTransitionInputsAt ThreePushMachine 3
        (freshCurrentLayout ThreePushMachine 3) (fun _ => true)
        threePushSource threePushTarget threePushSourceAlphabet
        threePushSourceHeight
        (stutterStep_alphabetBounded ThreePushMachine threePushSourceAlphabet)
        threePushTargetHeight
        ((freshCurrentLayout ThreePushMachine 3).index slot).val =
      encodeRawCfgBits
        (encodeCfg ThreePushMachine threePushSourceAlphabet
          threePushSourceHeight) slot :=
  freshTransitionInputsAt_current_index ThreePushMachine 3
    (freshCurrentLayout ThreePushMachine 3) (fun _ => true)
    threePushSource threePushTarget threePushSourceAlphabet
    threePushSourceHeight
    (stutterStep_alphabetBounded ThreePushMachine threePushSourceAlphabet)
    threePushTargetHeight slot

/-! ## Nonzero offset reuse -/

private def offsetLayout : CfgInputLayout ThreePushMachine 3 := ⟨11⟩

private def offsetStart : CircuitBuilder :=
  CircuitBuilder.empty offsetLayout.next.finish

private theorem offsetFits : offsetLayout.next.Fits offsetStart.inputCount :=
  Nat.le_refl _

-- External input zero lies before both offset row intervals, so both writes
-- preserve the caller's `true` bit there.
example :
    freshTransitionInputsAt ThreePushMachine 3 offsetLayout (fun _ => true)
        threePushSource threePushTarget threePushSourceAlphabet
        threePushSourceHeight
        (stutterStep_alphabetBounded ThreePushMachine threePushSourceAlphabet)
        threePushTargetHeight 0 = true := by
  apply freshTransitionInputsAt_outside
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)

-- The nonzero-offset instance records the same exact two-row allocation plus
-- local-transition gate delta as the generic constructor theorem.
example :
    (freshTransitionCircuitAt ThreePushMachine 3 offsetStart offsetLayout
      offsetFits).builder.gates.length =
        offsetStart.gates.length + 2 * cfgBitCount ThreePushMachine 3 +
          transitionCircuitGateCost ThreePushMachine 3 :=
  freshTransitionCircuitAt_gate_delta ThreePushMachine 3 offsetStart
    offsetLayout offsetFits

-- The tableau-facing theorem works at a nonzero external-input offset and
-- preserves the caller-supplied `true` assignment outside the two rows.
example :
    let final := freshTransitionCircuitAt ThreePushMachine 3 offsetStart
      offsetLayout offsetFits
    let inputs := freshTransitionInputsAt ThreePushMachine 3 offsetLayout
      (fun _ => true) threePushSource threePushTarget threePushSourceAlphabet
      threePushSourceHeight
      (stutterStep_alphabetBounded ThreePushMachine threePushSourceAlphabet)
      threePushTargetHeight
    evalBundle final.builder inputs final.current final.currentValid =
        some threePushSource ∧
      evalBundle final.builder inputs final.next final.nextValid =
        some threePushTarget ∧
      final.builder.evalWire inputs final.wire = true :=
  freshTransitionCircuitAt_complete_nat ThreePushMachine 3 offsetStart
    offsetLayout offsetFits (fun _ => true) threePushSource threePushTarget
    threePushSourceAlphabet threePushSourceHeight rfl threePushTargetHeight

end

end CLRS.Chapter34.Turing.CookLevin
