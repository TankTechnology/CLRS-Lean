import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits
/-!
# Chapter 34 Cook--Levin local-transition regressions

Small actual-allocation regressions for halted stuttering, immediate halt,
multi-push workspace use, temporary overflow, final overflow rejection, and
the exact local gate delta.
-/
namespace CLRS.Chapter34.Turing.CookLevin
noncomputable section
/-! ## Two real public-row allocations -/

/-- First public row layout for a transition regression. -/
private def pairCurrentLayout (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgInputLayout tm H := ⟨0⟩
/-- Consecutive, disjoint next-row layout for a transition regression. -/
private def pairNextLayout (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgInputLayout tm H := (pairCurrentLayout tm H).next
/-- Empty builder whose external-input range covers both public layouts. -/
private def pairStart (tm : _root_.Turing.FinTM2) (H : Nat) : CircuitBuilder :=
  CircuitBuilder.empty (pairNextLayout tm H).finish
/-- Allocate the current row first. -/
private def pairCurrentAllocation (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgInputAllocation (pairStart tm H) (pairCurrentLayout tm H) :=
  allocateCfgInputs (pairStart tm H) (pairCurrentLayout tm H) (by
    change (pairCurrentLayout tm H).finish ≤ (pairNextLayout tm H).finish
    simp [pairNextLayout, CfgInputLayout.next, CfgInputLayout.finish])

/-- Allocate the disjoint next row after the current row's internal gates. -/
private def pairNextAllocation (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgInputAllocation (pairCurrentAllocation tm H).builder
      (pairNextLayout tm H) :=
  allocateCfgInputs (pairCurrentAllocation tm H).builder
    (pairNextLayout tm H) (by
      change (pairNextLayout tm H).finish ≤
        (pairCurrentAllocation tm H).builder.inputCount
      rw [(pairCurrentAllocation tm H).extension.1]
      exact Nat.le_refl _)

/-- Both public rows' internal input wires live in this common builder. -/
private abbrev pairBuilder (tm : _root_.Turing.FinTM2) (H : Nat) :=
  (pairNextAllocation tm H).builder
/-- Current-row wires transported through the next-row allocation. -/
private theorem pairCurrentValid (tm : _root_.Turing.FinTM2) (H : Nat) :
    (pairCurrentAllocation tm H).wires.ValidIn (pairBuilder tm H) :=
  (pairCurrentAllocation tm H).valid.mono (pairNextAllocation tm H).extension

/-- Patch canonical current and next rows into their disjoint public inputs. -/
private def pairInputs (tm : _root_.Turing.FinTM2) (H : Nat)
    (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hnextAlphabet : CfgAlphabetBounded tm next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H) : Nat → Bool :=
  (pairNextLayout tm H).writeCfgBits
    ((pairCurrentLayout tm H).writeCfgBits (fun _ => false)
      (encodeRawCfgBits (encodeCfg tm hcurrentAlphabet hcurrentHeight)))
    (encodeRawCfgBits (encodeCfg tm hnextAlphabet hnextHeight))

/-- The first allocated row decodes through the complete two-allocation
builder despite the later disjoint next-row patch. -/
private theorem pairCurrentDecoded (tm : _root_.Turing.FinTM2) (H : Nat)
    (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hnextAlphabet : CfgAlphabetBounded tm next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H) :
    evalBundle (pairBuilder tm H)
        (pairInputs tm H current next hcurrentAlphabet hcurrentHeight
          hnextAlphabet hnextHeight)
        (pairCurrentAllocation tm H).wires (pairCurrentValid tm H) =
      some current := by
  rw [evalBundle_extends (pairNextAllocation tm H).extension
    (pairInputs tm H current next hcurrentAlphabet hcurrentHeight
      hnextAlphabet hnextHeight)
    (pairCurrentAllocation tm H).wires (pairCurrentAllocation tm H).valid]
  apply evalBundle_encodeCfg
  funext slot
  rw [evalCfgBits, (pairCurrentAllocation tm H).eval_slot]
  exact CfgInputLayout.writeCfgBits_index_of_disjoint
    (CfgInputLayout.next_disjoint (pairCurrentLayout tm H))
    (fun _ => false)
    (encodeRawCfgBits (encodeCfg tm hcurrentAlphabet hcurrentHeight))
    (encodeRawCfgBits (encodeCfg tm hnextAlphabet hnextHeight)) slot

/-- The second allocated row decodes canonically in the common builder. -/
private theorem pairNextDecoded (tm : _root_.Turing.FinTM2) (H : Nat)
    (current next : tm.Cfg)
    (hcurrentAlphabet : CfgAlphabetBounded tm current)
    (hcurrentHeight : ∀ k, (current.stk k).length ≤ H)
    (hnextAlphabet : CfgAlphabetBounded tm next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ H) :
    evalBundle (pairBuilder tm H)
        (pairInputs tm H current next hcurrentAlphabet hcurrentHeight
          hnextAlphabet hnextHeight)
        (pairNextAllocation tm H).wires (pairNextAllocation tm H).valid =
      some next := by
  exact (pairNextAllocation tm H).evalBundle_write_encodeCfg
    ((pairCurrentLayout tm H).writeCfgBits (fun _ => false)
      (encodeRawCfgBits (encodeCfg tm hcurrentAlphabet hcurrentHeight)))
    hnextAlphabet hnextHeight

/-! ## Height-zero halt and stutter -/

/-- Empty-alphabet machine whose only actual label halts immediately. -/
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

/-- Nonhalted empty-stack source for the immediate-halt regression. -/
private def haltSource : HaltMachine.Cfg where
  l := some ()
  var := ()
  stk := fun _ => []

/-- Halted empty-stack row. -/
private def haltedEmpty : HaltMachine.Cfg where
  l := none
  var := ()
  stk := fun _ => []

/-- Empty stacks vacuously stay in the fixed reachable alphabet. -/
private theorem haltSourceAlphabet : CfgAlphabetBounded HaltMachine haltSource := by
  intro k a
  cases k
  exact Empty.elim a

/-- The halted empty row is alphabet bounded. -/
private theorem haltedEmptyAlphabet : CfgAlphabetBounded HaltMachine haltedEmpty := by
  intro k a
  cases k
  exact Empty.elim a

/-- Both empty rows fit at public height zero. -/
private theorem haltSourceHeight : ∀ k, (haltSource.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

/-- The halted target fits at public height zero. -/
private theorem haltedEmptyHeight : ∀ k, (haltedEmpty.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

/-- Actual allocated immediate-halt transition circuit. -/
private def haltTransition := transitionCircuit HaltMachine 0
  (pairBuilder HaltMachine 0)
  (pairCurrentAllocation HaltMachine 0).wires
  (pairNextAllocation HaltMachine 0).wires
  (pairCurrentValid HaltMachine 0) (pairNextAllocation HaltMachine 0).valid

-- A nonhalting source takes its real statement arm and reaches halt.
example : haltTransition.builder.evalWire
    (pairInputs HaltMachine 0 haltSource haltedEmpty haltSourceAlphabet
      haltSourceHeight haltedEmptyAlphabet haltedEmptyHeight)
    haltTransition.wire = true := by
  apply (transitionCircuit_eval_iff HaltMachine 0 (pairBuilder HaltMachine 0)
    _ (pairCurrentAllocation HaltMachine 0).wires
    (pairNextAllocation HaltMachine 0).wires (pairCurrentValid HaltMachine 0)
    (pairNextAllocation HaltMachine 0).valid
    (pairCurrentDecoded HaltMachine 0 haltSource haltedEmpty haltSourceAlphabet
      haltSourceHeight haltedEmptyAlphabet haltedEmptyHeight)
    (pairNextDecoded HaltMachine 0 haltSource haltedEmpty haltSourceAlphabet
      haltSourceHeight haltedEmptyAlphabet haltedEmptyHeight)).mpr
  rfl

-- A reserved-none height-zero row stutters and is accepted by the same actual circuit shape.
example :
    let circuit := transitionCircuit HaltMachine 0 (pairBuilder HaltMachine 0)
      (pairCurrentAllocation HaltMachine 0).wires
      (pairNextAllocation HaltMachine 0).wires
      (pairCurrentValid HaltMachine 0) (pairNextAllocation HaltMachine 0).valid
    circuit.builder.evalWire
      (pairInputs HaltMachine 0 haltedEmpty haltedEmpty haltedEmptyAlphabet
        haltedEmptyHeight haltedEmptyAlphabet haltedEmptyHeight)
      circuit.wire = true := by
  dsimp only
  apply (transitionCircuit_eval_iff HaltMachine 0 (pairBuilder HaltMachine 0)
    _ (pairCurrentAllocation HaltMachine 0).wires
    (pairNextAllocation HaltMachine 0).wires (pairCurrentValid HaltMachine 0)
    (pairNextAllocation HaltMachine 0).valid
    (pairCurrentDecoded HaltMachine 0 haltedEmpty haltedEmpty
      haltedEmptyAlphabet haltedEmptyHeight haltedEmptyAlphabet haltedEmptyHeight)
    (pairNextDecoded HaltMachine 0 haltedEmpty haltedEmpty
      haltedEmptyAlphabet haltedEmptyHeight haltedEmptyAlphabet haltedEmptyHeight)).mpr
  exact (stutterStep_halted HaltMachine rfl).symm

-- One exact-delta regression covers the complete allocated local pipeline.
example : haltTransition.builder.gates.length =
    (pairBuilder HaltMachine 0).gates.length +
      transitionCircuitGateCost HaltMachine 0 :=
  haltTransition.gate_delta

/-! ## Canonical two-label dispatch -/

/-- Two program labels whose statement arms push different symbols. -/
private abbrev MultiLabelMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Bool
  main := false
  σ := Unit
  initialState := ()
  m label := .push () (fun _ => label) .halt

/-- Select a label by its canonical finite dispatch position. -/
private noncomputable def multiLabelCanonical (i : Fin 2) : Bool :=
  (labelEquivFin MultiLabelMachine).symm i

/-- Empty source row at one selected program label. -/
private def multiLabelSource (label : Bool) : MultiLabelMachine.Cfg where
  l := some label
  var := ()
  stk := fun _ => []

/-- Exact complete target of the selected statement arm. -/
private def multiLabelTarget (label : Bool) : MultiLabelMachine.Cfg :=
  stutterStep MultiLabelMachine (multiLabelSource label)

private theorem multiLabelSourceAlphabet (label : Bool) :
    CfgAlphabetBounded MultiLabelMachine (multiLabelSource label) := by
  intro k a ha
  cases k
  simp [multiLabelSource] at ha

private theorem multiLabelTargetAlphabet (label : Bool) :
    CfgAlphabetBounded MultiLabelMachine (multiLabelTarget label) :=
  stutterStep_alphabetBounded MultiLabelMachine (multiLabelSourceAlphabet label)

private theorem multiLabelSourceHeight (label : Bool) :
    ∀ k, ((multiLabelSource label).stk k).length ≤ 1 := by
  intro k
  cases k
  simp [multiLabelSource]

private theorem multiLabelTargetHeight (label : Bool) :
    ∀ k, ((multiLabelTarget label).stk k).length ≤ 1 := by
  intro k
  cases k
  cases label <;> decide

@[simp] private theorem multiLabelTarget_stack (label : Bool) :
    (multiLabelTarget label).stk () = [label] := by
  cases label <;> rfl

-- The two canonical dispatch positions reach distinguishable complete rows.
private theorem multiLabelCanonicalTargets_ne :
    multiLabelTarget (multiLabelCanonical 0) ≠
      multiLabelTarget (multiLabelCanonical 1) := by
  have hlabels : multiLabelCanonical 0 ≠ multiLabelCanonical 1 := by
    intro hlabel
    have hcode := congrArg (labelEquivFin MultiLabelMachine) hlabel
    simp [multiLabelCanonical] at hcode
  intro htargets
  have hstack := congrArg (fun c => c.stk ()) htargets
  rw [multiLabelTarget_stack, multiLabelTarget_stack] at hstack
  exact hlabels (List.cons.inj hstack).1

/-- One actual circuit shape shared by both canonical label assignments. -/
private def multiLabelTransition := transitionCircuit MultiLabelMachine 1
  (pairBuilder MultiLabelMachine 1)
  (pairCurrentAllocation MultiLabelMachine 1).wires
  (pairNextAllocation MultiLabelMachine 1).wires
  (pairCurrentValid MultiLabelMachine 1)
  (pairNextAllocation MultiLabelMachine 1).valid

private def multiLabelAcceptance (label : Bool) : Prop :=
    multiLabelTransition.builder.evalWire
      (pairInputs MultiLabelMachine 1 (multiLabelSource label)
        (multiLabelTarget label) (multiLabelSourceAlphabet label)
        (multiLabelSourceHeight label) (multiLabelTargetAlphabet label)
        (multiLabelTargetHeight label)) multiLabelTransition.wire = true

private theorem multiLabelAccepted (label : Bool) :
    multiLabelAcceptance label := by
  unfold multiLabelAcceptance
  apply (transitionCircuit_eval_iff MultiLabelMachine 1
    (pairBuilder MultiLabelMachine 1) _
    (pairCurrentAllocation MultiLabelMachine 1).wires
    (pairNextAllocation MultiLabelMachine 1).wires
    (pairCurrentValid MultiLabelMachine 1)
    (pairNextAllocation MultiLabelMachine 1).valid
    (pairCurrentDecoded MultiLabelMachine 1 (multiLabelSource label)
      (multiLabelTarget label) (multiLabelSourceAlphabet label)
      (multiLabelSourceHeight label) (multiLabelTargetAlphabet label)
      (multiLabelTargetHeight label))
    (pairNextDecoded MultiLabelMachine 1 (multiLabelSource label)
      (multiLabelTarget label) (multiLabelSourceAlphabet label)
      (multiLabelSourceHeight label) (multiLabelTargetAlphabet label)
      (multiLabelTargetHeight label))).mpr
  rfl

theorem multiLabelFirstAccepted :
    multiLabelAcceptance (multiLabelCanonical 0) :=
  multiLabelAccepted (multiLabelCanonical 0)

theorem multiLabelSecondAccepted :
    multiLabelAcceptance (multiLabelCanonical 1) :=
  multiLabelAccepted (multiLabelCanonical 1)

-- 158 gates precede the final conjunction; the visible final `+ 1` locks its AND gate.
theorem multiLabelTransitionCost :
    transitionCircuitGateCost MultiLabelMachine 1 =
        2 + 92 + 3 + 61 + 1 ∧
      2 + 92 + 3 + 61 + 1 = 159 := by
  classical
  have hlabels : programLabels MultiLabelMachine =
      [multiLabelCanonical 0, multiLabelCanonical 1] := by
    rfl
  have hmax : maxPushesPerStep MultiLabelMachine = 1 := by
    simp [maxPushesPerStep, MultiLabelMachine, stmtMaxPushes]
  have hpublic : cfgBitCount MultiLabelMachine 1 = 10 := by
    simp [cfgBitCount, MultiLabelMachine, reachableAlphabet, stmtPushSet,
      labelCount, stateCount, Fintype.card_bool]
  have hwork : cfgBitCount MultiLabelMachine
      (workHeight MultiLabelMachine 1) = 14 := by
    simp [workHeight, hmax, cfgBitCount, MultiLabelMachine, reachableAlphabet,
      stmtPushSet, labelCount, stateCount, Fintype.card_bool]
  have harm (label : Bool) :
      compileStmtGateCost MultiLabelMachine (workHeight MultiLabelMachine 1)
        (MultiLabelMachine.m label) = 3 := by
    simp [MultiLabelMachine, compileStmtGateCost, reachableAlphabet,
      stmtPushSet, stateCount]
  have hdispatch : dispatchGateCost MultiLabelMachine 1 = 92 := by
    rw [dispatchGateCost, hlabels]
    simp [dispatchListGateCost, harm, hwork]
  rw [transitionCircuitGateCost, hdispatch, hmax, hpublic]
  norm_num

/-! ## Multi-push and temporary workspace -/

/-- One-stack machine that performs three pushes in one bundled step. -/
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

/-- Empty source of the three-push step. -/
private def threePushSource : ThreePushMachine.Cfg where
  l := some ()
  var := ()
  stk := fun _ => []

/-- Exact complete-row three-push target. -/
private def threePushTarget : ThreePushMachine.Cfg :=
  stutterStep ThreePushMachine threePushSource

/-- Empty source stacks are alphabet bounded. -/
private theorem threePushSourceAlphabet :
    CfgAlphabetBounded ThreePushMachine threePushSource := by
  intro k a ha
  cases k
  simp [threePushSource] at ha

/-- The exact step preserves the finite reachable alphabet. -/
private theorem threePushTargetAlphabet :
    CfgAlphabetBounded ThreePushMachine threePushTarget :=
  stutterStep_alphabetBounded ThreePushMachine threePushSourceAlphabet

/-- The three-push source fits at height three. -/
private theorem threePushSourceHeight :
    ∀ k, (threePushSource.stk k).length ≤ 3 := by
  intro k
  cases k
  simp [threePushSource]

/-- The exact three-push target fills, but does not exceed, height three. -/
private theorem threePushTargetHeight :
    ∀ k, (threePushTarget.stk k).length ≤ 3 := by
  intro k
  cases k
  rw [show threePushTarget.stk () = [true, false, true] from rfl]
  decide

-- The complete target row contains all three pushed symbols in stack order.
example : threePushTarget.stk () = [true, false, true] := rfl

-- An actual H=3 pair accepts the full multi-push target row.
example :
    let circuit := transitionCircuit ThreePushMachine 3
      (pairBuilder ThreePushMachine 3)
      (pairCurrentAllocation ThreePushMachine 3).wires
      (pairNextAllocation ThreePushMachine 3).wires
      (pairCurrentValid ThreePushMachine 3)
      (pairNextAllocation ThreePushMachine 3).valid
    circuit.builder.evalWire
      (pairInputs ThreePushMachine 3 threePushSource threePushTarget
        threePushSourceAlphabet threePushSourceHeight threePushTargetAlphabet
        threePushTargetHeight) circuit.wire = true := by
  dsimp only
  apply (transitionCircuit_eval_iff ThreePushMachine 3
    (pairBuilder ThreePushMachine 3) _
    (pairCurrentAllocation ThreePushMachine 3).wires
    (pairNextAllocation ThreePushMachine 3).wires
    (pairCurrentValid ThreePushMachine 3)
    (pairNextAllocation ThreePushMachine 3).valid
    (pairCurrentDecoded ThreePushMachine 3 threePushSource threePushTarget
      threePushSourceAlphabet threePushSourceHeight threePushTargetAlphabet
      threePushTargetHeight)
    (pairNextDecoded ThreePushMachine 3 threePushSource threePushTarget
      threePushSourceAlphabet threePushSourceHeight threePushTargetAlphabet
      threePushTargetHeight)).mpr
  rfl

/-- One push followed by one pop uses workspace but ends at height zero. -/
private abbrev PushPopMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push () (fun _ => true) (.pop () (fun state _ => state) .halt)

/-- Empty source of the temporary push-pop step. -/
private def pushPopSource : PushPopMachine.Cfg where
  l := some ()
  var := ()
  stk := fun _ => []

/-- The push-pop statement returns to an empty halted row. -/
private def pushPopTarget : PushPopMachine.Cfg :=
  stutterStep PushPopMachine pushPopSource

/-- Empty push-pop source stacks are alphabet bounded. -/
private theorem pushPopSourceAlphabet :
    CfgAlphabetBounded PushPopMachine pushPopSource := by
  intro k a ha
  cases k
  simp [pushPopSource] at ha

/-- The push-pop target remains in the finite support alphabet. -/
private theorem pushPopTargetAlphabet :
    CfgAlphabetBounded PushPopMachine pushPopTarget :=
  stutterStep_alphabetBounded PushPopMachine pushPopSourceAlphabet

/-- Both source and final target fit height zero. -/
private theorem pushPopSourceHeight : ∀ k, (pushPopSource.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

/-- Temporary workspace is discarded before the final height-zero row. -/
private theorem pushPopTargetHeight : ∀ k, (pushPopTarget.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

-- H=0 accepts a statement that temporarily pushes and then pops in workspace.
example :
    let circuit := transitionCircuit PushPopMachine 0
      (pairBuilder PushPopMachine 0)
      (pairCurrentAllocation PushPopMachine 0).wires
      (pairNextAllocation PushPopMachine 0).wires
      (pairCurrentValid PushPopMachine 0)
      (pairNextAllocation PushPopMachine 0).valid
    circuit.builder.evalWire
      (pairInputs PushPopMachine 0 pushPopSource pushPopTarget
        pushPopSourceAlphabet pushPopSourceHeight pushPopTargetAlphabet
        pushPopTargetHeight) circuit.wire = true := by
  dsimp only
  apply (transitionCircuit_eval_iff PushPopMachine 0
    (pairBuilder PushPopMachine 0) _
    (pairCurrentAllocation PushPopMachine 0).wires
    (pairNextAllocation PushPopMachine 0).wires
    (pairCurrentValid PushPopMachine 0)
    (pairNextAllocation PushPopMachine 0).valid
    (pairCurrentDecoded PushPopMachine 0 pushPopSource pushPopTarget
      pushPopSourceAlphabet pushPopSourceHeight pushPopTargetAlphabet
      pushPopTargetHeight)
    (pairNextDecoded PushPopMachine 0 pushPopSource pushPopTarget
      pushPopSourceAlphabet pushPopSourceHeight pushPopTargetAlphabet
      pushPopTargetHeight)).mpr
  rfl

/-! ## Final overflow rejection -/

/-- One-push machine whose real result cannot fit a public height-zero row. -/
private abbrev OnePushMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .push () (fun _ => true) .halt

/-- Height-zero one-push source. -/
private def onePushSource : OnePushMachine.Cfg where
  l := some ()
  var := ()
  stk := fun _ => []

/-- Deliberately undersized halted next row. -/
private def onePushWrongNext : OnePushMachine.Cfg where
  l := none
  var := ()
  stk := fun _ => []

/-- Empty source alphabet invariant. -/
private theorem onePushSourceAlphabet :
    CfgAlphabetBounded OnePushMachine onePushSource := by
  intro k a ha
  cases k
  simp [onePushSource] at ha

/-- Empty wrong-next alphabet invariant. -/
private theorem onePushWrongNextAlphabet :
    CfgAlphabetBounded OnePushMachine onePushWrongNext := by
  intro k a ha
  cases k
  simp [onePushWrongNext] at ha

/-- Both supplied public rows fit height zero. -/
private theorem onePushSourceHeight : ∀ k, (onePushSource.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

/-- The deliberately wrong next row fits height zero. -/
private theorem onePushWrongNextHeight :
    ∀ k, (onePushWrongNext.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

/-- The genuine one-push successor differs in its complete stack contents. -/
private theorem onePushWrongNext_ne_step :
    onePushWrongNext ≠ stutterStep OnePushMachine onePushSource := by
  intro heq
  have hstack := congrArg (fun c => c.stk ()) heq
  rw [show (stutterStep OnePushMachine onePushSource).stk () = [true] from rfl]
    at hstack
  simp [onePushWrongNext] at hstack

-- The fit-and-equality conjunction rejects an oversized final result.
example :
    let circuit := transitionCircuit OnePushMachine 0
      (pairBuilder OnePushMachine 0)
      (pairCurrentAllocation OnePushMachine 0).wires
      (pairNextAllocation OnePushMachine 0).wires
      (pairCurrentValid OnePushMachine 0)
      (pairNextAllocation OnePushMachine 0).valid
    circuit.builder.evalWire
      (pairInputs OnePushMachine 0 onePushSource onePushWrongNext
        onePushSourceAlphabet onePushSourceHeight onePushWrongNextAlphabet
        onePushWrongNextHeight) circuit.wire = false := by
  dsimp only
  apply Bool.eq_false_of_not_eq_true
  intro haccepted
  exact onePushWrongNext_ne_step
    ((transitionCircuit_eval_iff OnePushMachine 0
      (pairBuilder OnePushMachine 0) _
      (pairCurrentAllocation OnePushMachine 0).wires
      (pairNextAllocation OnePushMachine 0).wires
      (pairCurrentValid OnePushMachine 0)
      (pairNextAllocation OnePushMachine 0).valid
      (pairCurrentDecoded OnePushMachine 0 onePushSource onePushWrongNext
        onePushSourceAlphabet onePushSourceHeight onePushWrongNextAlphabet
        onePushWrongNextHeight)
      (pairNextDecoded OnePushMachine 0 onePushSource onePushWrongNext
        onePushSourceAlphabet onePushSourceHeight onePushWrongNextAlphabet
        onePushWrongNextHeight)).mp haccepted)

end

end CLRS.Chapter34.Turing.CookLevin
