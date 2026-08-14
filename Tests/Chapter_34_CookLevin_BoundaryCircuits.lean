import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BoundaryCircuits

/-!
# Chapter 34 Cook--Levin boundary regressions

Actual allocated-row tests for total concrete initial/accepting constraints and
the certificate-linked symbolic-input initial form.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

private abbrev BoundaryMachine : _root_.Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := fun _ => Bool
  Λ := Bool
  main := true
  σ := Bool
  initialState := false
  m _ := .branch (fun state => state)
    (.push true (fun _ => true) .halt)
    (.push true (fun _ => false) .halt)

private def boundaryBase (H : Nat) : CircuitBuilder :=
  CircuitBuilder.empty (cfgBitCount BoundaryMachine H)

private def boundaryLayout (H : Nat) : CfgInputLayout BoundaryMachine H := ⟨0⟩

private theorem boundaryLayoutFits (H : Nat) :
    (boundaryLayout H).Fits (boundaryBase H).inputCount := by
  unfold CfgInputLayout.Fits boundaryLayout boundaryBase
  simp only [CfgInputLayout.finish, CircuitBuilder.empty]
  simp

private noncomputable def boundaryAllocation (H : Nat) :=
  allocateCfgInputs (boundaryBase H) (boundaryLayout H) (boundaryLayoutFits H)

private noncomputable def boundaryPool (H : Nat) :=
  CircuitBuilder.allocateBoolWirePool (boundaryAllocation H).builder

private theorem boundaryRowValid (H : Nat) :
    (boundaryAllocation H).wires.ValidIn (boundaryPool H).builder :=
  (boundaryAllocation H).valid.mono (boundaryPool H).extension

private def boundaryInputs (H : Nat) (code : BoundedCfg BoundaryMachine H) :
    Nat → Bool :=
  (boundaryLayout H).writeCfgBits (fun _ => false) (encodeRawCfgBits code)

private theorem boundaryDecoded (H : Nat) (c : BoundaryMachine.Cfg)
    (halphabet : CfgAlphabetBounded BoundaryMachine c)
    (hheight : ∀ k, (c.stk k).length ≤ H) :
    evalBundle (boundaryPool H).builder
        (boundaryInputs H (encodeCfg BoundaryMachine halphabet hheight))
        (boundaryAllocation H).wires (boundaryRowValid H) = some c := by
  rw [evalBundle_extends (boundaryPool H).extension _
    (boundaryAllocation H).wires (boundaryAllocation H).valid]
  exact (boundaryAllocation H).evalBundle_write_encodeCfg
    (fun _ => false) halphabet hheight

/-! ## Concrete initial constraints -/

private theorem initAlphabet (xs : List Bool) :
    CfgAlphabetBounded BoundaryMachine
      (_root_.Turing.initList BoundaryMachine xs) :=
  initList_alphabetBounded BoundaryMachine xs

private theorem initHeight {H : Nat} (xs : List Bool) (hfit : xs.length ≤ H) :
    ∀ k, ((_root_.Turing.initList BoundaryMachine xs).stk k).length ≤ H := by
  intro k
  cases k <;> simp [_root_.Turing.initList]
  exact hfit

-- Height zero accepts the complete empty initial row.
example :
    let inputs := boundaryInputs 0
      (encodeCfg BoundaryMachine (initAlphabet []) (initHeight [] (by simp)))
    (initialCfgCircuit BoundaryMachine 0 (boundaryPool 0).builder
      (boundaryPool 0).pool (boundaryAllocation 0).wires
      (boundaryRowValid 0) []).builder.evalWire inputs
      (initialCfgCircuit BoundaryMachine 0 (boundaryPool 0).builder
        (boundaryPool 0).pool (boundaryAllocation 0).wires
        (boundaryRowValid 0) []).wire = true := by
  dsimp only
  rw [initialCfgCircuit_eval_iff]
  exact boundaryDecoded 0 _ (initAlphabet []) (initHeight [] (by simp))

-- Oversized concrete input emits and evaluates a real false constraint.
example (inputs : Nat → Bool) :
    (initialCfgCircuit BoundaryMachine 0 (boundaryPool 0).builder
      (boundaryPool 0).pool (boundaryAllocation 0).wires
      (boundaryRowValid 0) [true]).builder.evalWire inputs
      (initialCfgCircuit BoundaryMachine 0 (boundaryPool 0).builder
        (boundaryPool 0).pool (boundaryAllocation 0).wires
        (boundaryRowValid 0) [true]).wire = false := by
  rw [show initialCfgCircuit BoundaryMachine 0 (boundaryPool 0).builder
      (boundaryPool 0).pool (boundaryAllocation 0).wires
      (boundaryRowValid 0) [true] =
      falseBoundaryCircuit (boundaryPool 0).builder (boundaryPool 0).pool by
    simp [initialCfgCircuit]]
  exact falseBoundaryCircuit_eval _ _ _

-- Oversized accepting outputs likewise take the real constant-false branch.
example (inputs : Nat → Bool) :
    (acceptingOutputCircuit BoundaryMachine 0 (boundaryPool 0).builder
      (boundaryPool 0).pool (boundaryAllocation 0).wires
      (boundaryRowValid 0) [true]).builder.evalWire inputs
      (acceptingOutputCircuit BoundaryMachine 0 (boundaryPool 0).builder
        (boundaryPool 0).pool (boundaryAllocation 0).wires
        (boundaryRowValid 0) [true]).wire = false := by
  rw [show acceptingOutputCircuit BoundaryMachine 0 (boundaryPool 0).builder
      (boundaryPool 0).pool (boundaryAllocation 0).wires
      (boundaryRowValid 0) [true] =
      falseBoundaryCircuit (boundaryPool 0).builder (boundaryPool 0).pool by
    simp [acceptingOutputCircuit, AcceptingOutputFits]]
  exact falseBoundaryCircuit_eval _ _ _

private abbrev UnsupportedOutputMachine : _root_.Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .halt

private def unsupportedLayout : CfgInputLayout UnsupportedOutputMachine 1 := ⟨0⟩

private def unsupportedBase : CircuitBuilder :=
  CircuitBuilder.empty unsupportedLayout.finish

private theorem unsupportedLayoutFits :
    unsupportedLayout.Fits unsupportedBase.inputCount := by
  unfold CfgInputLayout.Fits unsupportedBase
  exact Nat.le_refl _

private noncomputable def unsupportedAllocation :=
  allocateCfgInputs unsupportedBase unsupportedLayout unsupportedLayoutFits

private noncomputable def unsupportedPool :=
  CircuitBuilder.allocateBoolWirePool unsupportedAllocation.builder

private theorem unsupportedEmptyHeight :
    ∀ k, ((_root_.Turing.initList UnsupportedOutputMachine []).stk k).length ≤ 1 := by
  intro k
  cases k <;> simp [_root_.Turing.initList]

private theorem unsupportedRowValid :
    unsupportedAllocation.wires.ValidIn unsupportedPool.builder :=
  unsupportedAllocation.valid.mono unsupportedPool.extension

private def unsupportedInputs : Nat → Bool :=
  unsupportedLayout.writeCfgBits (fun _ => false)
    (encodeRawCfgBits
      (encodeCfg UnsupportedOutputMachine
        (initList_alphabetBounded UnsupportedOutputMachine [])
        unsupportedEmptyHeight))

private theorem unsupportedRowDecoded :
    evalBundle unsupportedPool.builder unsupportedInputs
        unsupportedAllocation.wires unsupportedRowValid =
      some (_root_.Turing.initList UnsupportedOutputMachine []) := by
  rw [evalBundle_extends unsupportedPool.extension unsupportedInputs
    unsupportedAllocation.wires unsupportedAllocation.valid]
  exact unsupportedAllocation.evalBundle_write_encodeCfg (fun _ => false)
    (initList_alphabetBounded UnsupportedOutputMachine [])
    unsupportedEmptyHeight

-- A fitting output symbol outside program/input support is also rejected by
-- an actual false output, not by an external support assumption.
example :
    evalBundle unsupportedPool.builder unsupportedInputs
        unsupportedAllocation.wires unsupportedRowValid =
        some (_root_.Turing.initList UnsupportedOutputMachine []) ∧
      (acceptingOutputCircuit UnsupportedOutputMachine 1 unsupportedPool.builder
        unsupportedPool.pool unsupportedAllocation.wires unsupportedRowValid
        [true]).builder.evalWire unsupportedInputs
        (acceptingOutputCircuit UnsupportedOutputMachine 1 unsupportedPool.builder
          unsupportedPool.pool unsupportedAllocation.wires unsupportedRowValid
          [true]).wire = false := by
  refine ⟨unsupportedRowDecoded, ?_⟩
  rw [show acceptingOutputCircuit UnsupportedOutputMachine 1
      unsupportedPool.builder unsupportedPool.pool unsupportedAllocation.wires
      unsupportedRowValid [true] =
      falseBoundaryCircuit unsupportedPool.builder unsupportedPool.pool by
    simp [acceptingOutputCircuit, AcceptingOutputFits, reachableAlphabet,
      stmtPushSet, UnsupportedOutputMachine]]
  exact falseBoundaryCircuit_eval _ _ _

/-! ## Empty-support height-zero boundary -/

private abbrev EmptyBoundaryMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Empty
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .halt

private def emptyBoundaryLayout : CfgInputLayout EmptyBoundaryMachine 0 := ⟨0⟩

private def emptyBoundaryBase : CircuitBuilder :=
  CircuitBuilder.empty emptyBoundaryLayout.finish

private theorem emptyBoundaryLayoutFits :
    emptyBoundaryLayout.Fits emptyBoundaryBase.inputCount := by
  unfold CfgInputLayout.Fits emptyBoundaryBase
  exact Nat.le_refl _

private noncomputable def emptyBoundaryAllocation :=
  allocateCfgInputs emptyBoundaryBase emptyBoundaryLayout
    emptyBoundaryLayoutFits

private noncomputable def emptyBoundaryPool :=
  CircuitBuilder.allocateBoolWirePool emptyBoundaryAllocation.builder

private theorem emptyBoundaryHeight :
    ∀ k, ((_root_.Turing.initList EmptyBoundaryMachine []).stk k).length ≤ 0 := by
  intro k
  cases k
  simp [_root_.Turing.initList]

private theorem emptyBoundaryRowValid :
    emptyBoundaryAllocation.wires.ValidIn emptyBoundaryPool.builder :=
  emptyBoundaryAllocation.valid.mono emptyBoundaryPool.extension

private def emptyBoundaryInputs : Nat → Bool :=
  emptyBoundaryLayout.writeCfgBits (fun _ => false)
    (encodeRawCfgBits
      (encodeCfg EmptyBoundaryMachine
        (initList_alphabetBounded EmptyBoundaryMachine []) emptyBoundaryHeight))

private theorem emptyBoundaryRowDecoded :
    evalBundle emptyBoundaryPool.builder emptyBoundaryInputs
        emptyBoundaryAllocation.wires emptyBoundaryRowValid =
      some (_root_.Turing.initList EmptyBoundaryMachine []) := by
  rw [evalBundle_extends emptyBoundaryPool.extension emptyBoundaryInputs
    emptyBoundaryAllocation.wires emptyBoundaryAllocation.valid]
  exact emptyBoundaryAllocation.evalBundle_write_encodeCfg (fun _ => false)
    (initList_alphabetBounded EmptyBoundaryMachine []) emptyBoundaryHeight

-- Empty alphabet support and physical height zero still produce a complete
-- exact initial constraint with no cell coordinates.
example :
    evalBundle emptyBoundaryPool.builder emptyBoundaryInputs
        emptyBoundaryAllocation.wires emptyBoundaryRowValid =
        some (_root_.Turing.initList EmptyBoundaryMachine []) ∧
      (initialCfgCircuit EmptyBoundaryMachine 0 emptyBoundaryPool.builder
        emptyBoundaryPool.pool emptyBoundaryAllocation.wires
        emptyBoundaryRowValid []).builder.evalWire emptyBoundaryInputs
        (initialCfgCircuit EmptyBoundaryMachine 0 emptyBoundaryPool.builder
          emptyBoundaryPool.pool emptyBoundaryAllocation.wires
          emptyBoundaryRowValid []).wire = true := by
  refine ⟨emptyBoundaryRowDecoded, ?_⟩
  rw [initialCfgCircuit_eval_iff]
  exact emptyBoundaryRowDecoded

/-! ## Exact accepting constraints -/

private theorem haltAlphabet (xs : List Bool) :
    CfgAlphabetBounded BoundaryMachine
      (_root_.Turing.haltList BoundaryMachine xs) := by
  apply haltList_alphabetBounded_of_fits BoundaryMachine xs.length xs
  constructor
  · intro a ha
    fin_cases a <;> simp [reachableAlphabet, stmtPushSet, BoundaryMachine]
  · exact Nat.le_refl _

private theorem haltHeight (xs : List Bool) :
    ∀ k, ((_root_.Turing.haltList BoundaryMachine xs).stk k).length ≤ xs.length :=
  haltList_height_of_fits BoundaryMachine xs.length xs ⟨by
    intro a ha
    fin_cases a <;> simp [reachableAlphabet, stmtPushSet, BoundaryMachine],
    Nat.le_refl _⟩

private def exactOutput : List Bool := [true, false]

private def exactHalt := _root_.Turing.haltList BoundaryMachine exactOutput

private def exactHaltInputs : Nat → Bool :=
  boundaryInputs 2 (encodeCfg BoundaryMachine (haltAlphabet exactOutput)
    (haltHeight exactOutput))

-- Complete exact halt target is accepted.
example :
    (acceptingOutputCircuit BoundaryMachine 2 (boundaryPool 2).builder
      (boundaryPool 2).pool (boundaryAllocation 2).wires
      (boundaryRowValid 2) exactOutput).builder.evalWire exactHaltInputs
      (acceptingOutputCircuit BoundaryMachine 2 (boundaryPool 2).builder
        (boundaryPool 2).pool (boundaryAllocation 2).wires
        (boundaryRowValid 2) exactOutput).wire = true := by
  rw [acceptingOutputCircuit_eval_iff]
  exact boundaryDecoded 2 exactHalt (haltAlphabet exactOutput)
    (haltHeight exactOutput)

private def wrongStateHalt : BoundaryMachine.Cfg :=
  { exactHalt with var := true }

private theorem wrongStateHaltAlphabet :
    CfgAlphabetBounded BoundaryMachine wrongStateHalt := by
  intro k a ha
  exact (haltAlphabet exactOutput) k a (by
    change a ∈ (exactHalt.stk k)
    exact ha)

private theorem wrongStateHaltHeight :
    ∀ k, (wrongStateHalt.stk k).length ≤ 2 := by
  intro k
  exact (haltHeight exactOutput k : _)

-- A wrong state is rejected even though halted/top/output shape otherwise fits.
example :
    let inputs := boundaryInputs 2
      (encodeCfg BoundaryMachine wrongStateHaltAlphabet wrongStateHaltHeight)
    (acceptingOutputCircuit BoundaryMachine 2 (boundaryPool 2).builder
      (boundaryPool 2).pool (boundaryAllocation 2).wires
      (boundaryRowValid 2) exactOutput).builder.evalWire inputs
      (acceptingOutputCircuit BoundaryMachine 2 (boundaryPool 2).builder
        (boundaryPool 2).pool (boundaryAllocation 2).wires
        (boundaryRowValid 2) exactOutput).wire = false := by
  dsimp only
  apply Bool.eq_false_of_not_eq_true
  rw [acceptingOutputCircuit_eval_iff]
  rw [boundaryDecoded 2 wrongStateHalt wrongStateHaltAlphabet
    wrongStateHaltHeight]
  intro heq
  have heq := Option.some.inj heq
  have := congrArg _root_.Turing.TM2.Cfg.var heq
  simp [wrongStateHalt, exactHalt, exactOutput,
    _root_.Turing.haltList] at this

private def extraStackHalt : BoundaryMachine.Cfg where
  l := none
  var := false
  stk
    | false => [true]
    | true => exactOutput

private theorem extraStackHaltAlphabet :
    CfgAlphabetBounded BoundaryMachine extraStackHalt := by
  intro k a ha
  cases k with
  | false =>
      fin_cases a <;> simp [reachableAlphabet, stmtPushSet, BoundaryMachine]
  | true =>
      exact (haltAlphabet exactOutput) true a (by
        change a ∈ exactOutput
        exact ha)

private theorem extraStackHaltHeight :
    ∀ k, (extraStackHalt.stk k).length ≤ 2 := by
  intro k
  cases k <;> decide

-- Any extra non-output stack content is rejected.
example :
    let inputs := boundaryInputs 2
      (encodeCfg BoundaryMachine extraStackHaltAlphabet extraStackHaltHeight)
    (acceptingOutputCircuit BoundaryMachine 2 (boundaryPool 2).builder
      (boundaryPool 2).pool (boundaryAllocation 2).wires
      (boundaryRowValid 2) exactOutput).builder.evalWire inputs
      (acceptingOutputCircuit BoundaryMachine 2 (boundaryPool 2).builder
        (boundaryPool 2).pool (boundaryAllocation 2).wires
        (boundaryRowValid 2) exactOutput).wire = false := by
  dsimp only
  apply Bool.eq_false_of_not_eq_true
  rw [acceptingOutputCircuit_eval_iff]
  rw [boundaryDecoded 2 extraStackHalt extraStackHaltAlphabet
    extraStackHaltHeight]
  intro heq
  have heq := Option.some.inj heq
  have := congrFun (congrArg _root_.Turing.TM2.Cfg.stk heq) false
  simp [extraStackHalt, exactOutput, _root_.Turing.haltList] at this

-- Wrong exact output is rejected (not merely a top-symbol check).
example :
    let inputs := boundaryInputs 2
      (encodeCfg BoundaryMachine (haltAlphabet [true, true])
        (haltHeight [true, true]))
    (acceptingOutputCircuit BoundaryMachine 2 (boundaryPool 2).builder
      (boundaryPool 2).pool (boundaryAllocation 2).wires
      (boundaryRowValid 2) exactOutput).builder.evalWire inputs
      (acceptingOutputCircuit BoundaryMachine 2 (boundaryPool 2).builder
        (boundaryPool 2).pool (boundaryAllocation 2).wires
        (boundaryRowValid 2) exactOutput).wire = false := by
  dsimp only
  apply Bool.eq_false_of_not_eq_true
  rw [acceptingOutputCircuit_eval_iff]
  rw [boundaryDecoded 2 _ (haltAlphabet [true, true])
    (haltHeight [true, true])]
  intro heq
  have heq := Option.some.inj heq
  have := congrFun (congrArg _root_.Turing.TM2.Cfg.stk heq) true
  simp [exactOutput, _root_.Turing.haltList] at this

/-! ## Symbolic initial stack -/

private def symbolicStackLayout : CfgInputLayout BoundaryMachine 3 := ⟨0⟩

private def symbolicStackBase : CircuitBuilder :=
  CircuitBuilder.empty symbolicStackLayout.finish

private theorem symbolicStackLayoutFits :
    symbolicStackLayout.Fits symbolicStackBase.inputCount := by
  unfold CfgInputLayout.Fits symbolicStackBase
  exact Nat.le_refl _

private noncomputable def symbolicStackAllocation :=
  allocateCfgInputs symbolicStackBase symbolicStackLayout
    symbolicStackLayoutFits

private noncomputable def symbolicStackPool :=
  CircuitBuilder.allocateBoolWirePool symbolicStackAllocation.builder

private theorem symbolicStackRowValid :
    symbolicStackAllocation.wires.ValidIn symbolicStackPool.builder :=
  symbolicStackAllocation.valid.mono symbolicStackPool.extension

private def symbolicXs : List Bool := [true, false, true]

private theorem symbolicXsHeight : symbolicXs.length ≤ 3 := by decide

private theorem symbolicXsAlphabet :
    ∀ a, a ∈ symbolicXs → a ∈ reachableAlphabet BoundaryMachine false := by
  intro a ha
  simp [reachableAlphabet, stmtPushSet, BoundaryMachine]

private def symbolicInputs : Nat → Bool :=
  symbolicStackLayout.writeCfgBits (fun _ => false)
    (encodeRawCfgBits (encodeCfg BoundaryMachine (initAlphabet symbolicXs)
      (initHeight symbolicXs symbolicXsHeight)))

private theorem symbolicStackRepresents :
    (evalStackBits symbolicStackPool.builder symbolicInputs
      (symbolicStackAllocation.wires.stack false)).Represents symbolicXs := by
  change
    (evalStackBits symbolicStackPool.builder
      (symbolicStackLayout.writeCfgBits (fun _ => false)
        (encodeRawCfgBits (encodeCfg BoundaryMachine
          (initAlphabet symbolicXs)
          (initHeight symbolicXs symbolicXsHeight))))
      (symbolicStackAllocation.wires.stack false)).Represents symbolicXs
  rw [evalStackBits_extends symbolicStackPool.extension
    (symbolicStackLayout.writeCfgBits (fun _ => false)
      (encodeRawCfgBits (encodeCfg BoundaryMachine
        (initAlphabet symbolicXs)
        (initHeight symbolicXs symbolicXsHeight))))
    (symbolicStackAllocation.wires.stack false)
    (symbolicStackAllocation.valid.stack false)]
  rw [evalStackBits_cfgStack]
  have hbits := symbolicStackAllocation.evalCfgBits_write (fun _ => false)
    (encodeRawCfgBits (encodeCfg BoundaryMachine (initAlphabet symbolicXs)
      (initHeight symbolicXs symbolicXsHeight)))
  rw [hbits]
  change (encodeBoundedStackBits
    (encodeBoundedStack BoundaryMachine false symbolicXs
      symbolicXsAlphabet symbolicXsHeight)).Represents symbolicXs
  exact StackBits.Represents.of_encode (tm := BoundaryMachine) (W := 3)
    (k := false) symbolicXs symbolicXsAlphabet symbolicXsHeight

-- The real allocated nonuniform symbolic stack fixes the complete initial row,
-- including all three input cells and the empty non-input stack.
example :
    (symbolicInitialCfgCircuit BoundaryMachine 3 symbolicStackPool.builder
      symbolicStackPool.pool symbolicStackAllocation.wires
      symbolicStackRowValid (symbolicStackAllocation.wires.stack false)
      (symbolicStackRowValid.stack false)).builder.evalWire symbolicInputs
      (symbolicInitialCfgCircuit BoundaryMachine 3 symbolicStackPool.builder
        symbolicStackPool.pool symbolicStackAllocation.wires
        symbolicStackRowValid (symbolicStackAllocation.wires.stack false)
        (symbolicStackRowValid.stack false)).wire = true := by
  rw [symbolicInitialCfgCircuit_eval_iff BoundaryMachine 3
    symbolicStackPool.builder symbolicStackPool.pool symbolicInputs
    symbolicStackAllocation.wires symbolicStackRowValid
    (symbolicStackAllocation.wires.stack false)
    (symbolicStackRowValid.stack false) symbolicXs symbolicStackRepresents]
  rw [evalBundle_extends symbolicStackPool.extension symbolicInputs
    symbolicStackAllocation.wires symbolicStackAllocation.valid]
  exact symbolicStackAllocation.evalBundle_write_encodeCfg
    (fun _ => false) (initAlphabet symbolicXs)
    (initHeight symbolicXs symbolicXsHeight)

end

end CLRS.Chapter34.Turing.CookLevin
