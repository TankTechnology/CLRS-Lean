import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder

namespace CLRS.Chapter34.Turing.PolyBuilder

#check Stack
#check Alphabet
#check ControlState
#check Op
#check Program
#check BuilderCfg
#check stepOp
#check step
#check encodeCfg
#check compileOp
#check compile
#check compile_step
#check initialCfg
#check haltCfg
#check encodeCfg_initialCfg
#check encodeCfg_haltCfg
#check compile_evalsToInTime
#check evalsToInTime_trans_steps
#check compile_evalsToInTime_steps
#check BuilderOutputs
#check Outputs
#check Outputs.of_builder_run
#check PolyBound
#check ComputableInPolyTime
#check exactMonomialClock_length
#check exactMonomialClock_computableInPolyTime
#check exactPolynomialClock_length
#check exactPolynomialClock_computableInPolyTime

example {σ : Type} (f : σ → Option σ) {m₁ m₂ : Nat} {a b : σ}
    {c : Option σ}
    (first : _root_.StateTransition.EvalsToInTime f a (some b) m₁)
    (second : _root_.StateTransition.EvalsToInTime f b c m₂) :
    (_root_.StateTransition.EvalsToInTime.trans f m₁ m₂ a b c
      first second).steps = second.steps + first.steps :=
  evalsToInTime_trans_steps f m₁ m₂ a b c first second

example {Γ Δ : Type} [Fintype Γ] (P : Program Γ Δ)
    {c c' : BuilderCfg P} {bound : Nat}
    (run : _root_.StateTransition.EvalsToInTime
      (step P) c (some c') bound) :
    (compile_evalsToInTime P run).steps = run.steps :=
  compile_evalsToInTime_steps P run

/-! ## Executable instruction semantics -/

def oneOp (operation : Op Bool Bool Bool) : Program Bool Bool where
  Label := Bool
  main := false
  op label := if label then .halt else operation

def baseCfg (operation : Op Bool Bool Bool) : BuilderCfg (oneOp operation) where
  label := some false
  buffer₁ := none
  buffer₂ := none
  test := false
  input := []
  output := []
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

example :
    (step (oneOp (.pushOutput true true))
      (baseCfg (.pushOutput true true))).map
        (fun c => (c.label, c.output)) = some (some true, [true]) := rfl

example :
    (step (oneOp (.pushWork₁ true true))
      (baseCfg (.pushWork₁ true true))).map
        (fun c => (c.label, c.work₁)) = some (some true, [true]) := rfl

example :
    (step (oneOp (.pushWork₂ false true))
      (baseCfg (.pushWork₂ false true))).map
        (fun c => (c.label, c.work₂)) = some (some true, [false]) := rfl

-- Every move takes its empty continuation without changing its target.
example :
    (step (oneOp (.moveInputWork₁ false id))
      { baseCfg (.moveInputWork₁ false id) with work₁ := [false] }).map
        (fun c => (c.label, c.buffer₁, c.input, c.work₁)) =
      some (some false, none, [], [false]) := rfl

example :
    (step (oneOp (.moveWork₁Input false id))
      { baseCfg (.moveWork₁Input false id) with input := [false] }).map
        (fun c => (c.label, c.buffer₁, c.work₁, c.input)) =
      some (some false, none, [], [false]) := rfl

example :
    (step (oneOp (.moveInputWork₂ false id))
      { baseCfg (.moveInputWork₂ false id) with work₂ := [false] }).map
        (fun c => (c.label, c.buffer₂, c.input, c.work₂)) =
      some (some false, none, [], [false]) := rfl

example :
    (step (oneOp (.moveWork₂Input false id))
      { baseCfg (.moveWork₂Input false id) with input := [false] }).map
        (fun c => (c.label, c.buffer₂, c.work₂, c.input)) =
      some (some false, none, [], [false]) := rfl

example :
    (step (oneOp (.moveWork₁Work₂ false id))
      { baseCfg (.moveWork₁Work₂ false id) with work₂ := [false] }).map
        (fun c => (c.label, c.buffer₁, c.work₁, c.work₂)) =
      some (some false, none, [], [false]) := rfl

example :
    (step (oneOp (.moveWork₂Work₁ false id))
      { baseCfg (.moveWork₂Work₁ false id) with work₁ := [false] }).map
        (fun c => (c.label, c.buffer₂, c.work₂, c.work₁)) =
      some (some false, none, [], [false]) := rfl

-- A moved `true` symbol selects the symbol-dependent `true` label.
example :
    (step (oneOp (.moveInputWork₁ false id))
      { baseCfg (.moveInputWork₁ false id) with
        input := [true], work₁ := [false] }).map
        (fun c => (c.label, c.buffer₁, c.input, c.work₁)) =
      some (some true, some true, [], [true, false]) := rfl

example :
    (step (oneOp (.moveWork₁Input false id))
      { baseCfg (.moveWork₁Input false id) with
        input := [false], work₁ := [true] }).map
        (fun c => (c.label, c.buffer₁, c.work₁, c.input)) =
      some (some true, some true, [], [true, false]) := rfl

example :
    (step (oneOp (.moveInputWork₂ false id))
      { baseCfg (.moveInputWork₂ false id) with
        input := [true], work₂ := [false] }).map
        (fun c => (c.label, c.buffer₂, c.input, c.work₂)) =
      some (some true, some true, [], [true, false]) := rfl

example :
    (step (oneOp (.moveWork₂Input false id))
      { baseCfg (.moveWork₂Input false id) with
        input := [false], work₂ := [true] }).map
        (fun c => (c.label, c.buffer₂, c.work₂, c.input)) =
      some (some true, some true, [], [true, false]) := rfl

example :
    (step (oneOp (.moveWork₁Work₂ false id))
      { baseCfg (.moveWork₁Work₂ false id) with
        work₁ := [true], work₂ := [false] }).map
        (fun c => (c.label, c.buffer₁, c.work₁, c.work₂)) =
      some (some true, some true, [], [true, false]) := rfl

example :
    (step (oneOp (.moveWork₂Work₁ false id))
      { baseCfg (.moveWork₂Work₁ false id) with
        work₁ := [false], work₂ := [true] }).map
        (fun c => (c.label, c.buffer₂, c.work₂, c.work₁)) =
      some (some true, some true, [], [true, false]) := rfl

example :
    (step (oneOp (.copyInputWorks false id))
      { baseCfg (.copyInputWorks false id) with
        work₁ := [false], work₂ := [false] }).map
        (fun c => (c.label, c.buffer₁, c.input, c.work₁, c.work₂)) =
      some (some false, none, [], [false], [false]) := rfl

example :
    (step (oneOp (.copyInputWorks false id))
      { baseCfg (.copyInputWorks false id) with
        input := [true], work₁ := [false], work₂ := [false] }).map
        (fun c => (c.label, c.buffer₁, c.input, c.work₁, c.work₂)) =
      some (some true, some true, [], [true, false], [true, false]) := rfl

-- Each typed pop selects its empty or symbol-dependent continuation.
example :
    (step (oneOp (.popInput false id))
      (baseCfg (.popInput false id))).map
        (fun c => (c.label, c.buffer₁, c.input)) =
      some (some false, none, []) := rfl

example :
    (step (oneOp (.popInput false id))
      { baseCfg (.popInput false id) with input := [true, false] }).map
        (fun c => (c.label, c.buffer₁, c.input)) =
      some (some true, some true, [false]) := rfl

example :
    (step (oneOp (.popWork₁ false id))
      (baseCfg (.popWork₁ false id))).map
        (fun c => (c.label, c.buffer₁, c.work₁)) =
      some (some false, none, []) := rfl

example :
    (step (oneOp (.popWork₁ false id))
      { baseCfg (.popWork₁ false id) with work₁ := [true, false] }).map
        (fun c => (c.label, c.buffer₁, c.work₁)) =
      some (some true, some true, [false]) := rfl

example :
    (step (oneOp (.popWork₂ false id))
      (baseCfg (.popWork₂ false id))).map
        (fun c => (c.label, c.buffer₂, c.work₂)) =
      some (some false, none, []) := rfl

example :
    (step (oneOp (.popWork₂ false id))
      { baseCfg (.popWork₂ false id) with work₂ := [true, false] }).map
        (fun c => (c.label, c.buffer₂, c.work₂)) =
      some (some true, some true, [false]) := rfl

-- All three unary counters cover increment, zero decrement, and successor decrement.
example :
    (step (oneOp (.inc₁ true)) (baseCfg (.inc₁ true))).map
      (fun c => (c.label, c.counter₁)) = some (some true, [()]) := rfl

example :
    (step (oneOp (.inc₂ true)) (baseCfg (.inc₂ true))).map
      (fun c => (c.label, c.counter₂)) = some (some true, [()]) := rfl

example :
    (step (oneOp (.inc₃ true)) (baseCfg (.inc₃ true))).map
      (fun c => (c.label, c.counter₃)) = some (some true, [()]) := rfl

example :
    (step (oneOp (.dec₁ false true)) (baseCfg (.dec₁ false true))).map
      (fun c => (c.label, c.test, c.counter₁)) =
        some (some false, false, []) := rfl

example :
    (step (oneOp (.dec₁ false true))
      { baseCfg (.dec₁ false true) with counter₁ := [(), ()] }).map
      (fun c => (c.label, c.test, c.counter₁)) =
        some (some true, true, [()]) := rfl

example :
    (step (oneOp (.dec₂ false true)) (baseCfg (.dec₂ false true))).map
      (fun c => (c.label, c.test, c.counter₂)) =
        some (some false, false, []) := rfl

example :
    (step (oneOp (.dec₂ false true))
      { baseCfg (.dec₂ false true) with counter₂ := [(), ()] }).map
      (fun c => (c.label, c.test, c.counter₂)) =
        some (some true, true, [()]) := rfl

example :
    (step (oneOp (.dec₃ false true)) (baseCfg (.dec₃ false true))).map
      (fun c => (c.label, c.test, c.counter₃)) =
        some (some false, false, []) := rfl

example :
    (step (oneOp (.dec₃ false true))
      { baseCfg (.dec₃ false true) with counter₃ := [(), ()] }).map
      (fun c => (c.label, c.test, c.counter₃)) =
        some (some true, true, [()]) := rfl

example :
    (step (oneOp (.jump true)) (baseCfg (.jump true))).map
      (fun c => c.label) = some (some true) := rfl

example :
    (step (oneOp .halt)
      { baseCfg .halt with
        buffer₁ := some true
        buffer₂ := some false
        test := true }).map
      (fun c => (c.label, c.buffer₁, c.buffer₂, c.test)) =
        some (none, none, none, false) := rfl

-- Frame conditions: instructions only change the fields in their contracts.
example :
    (step (oneOp (.moveInputWork₁ false id))
      { baseCfg (.moveInputWork₁ false id) with
        buffer₂ := some false
        test := true
        input := [true]
        output := [false]
        counter₁ := [()]
        counter₂ := [(), ()]
        counter₃ := [()] }).map
      (fun c => (c.buffer₂, c.test, c.counter₁, c.counter₂, c.counter₃,
        c.output)) =
      some (some false, true, [()], [(), ()], [()], [false]) := rfl

example :
    (step (oneOp (.dec₁ false true))
      { baseCfg (.dec₁ false true) with
        buffer₁ := some true
        buffer₂ := some false
        input := [true]
        output := [false]
        work₁ := [false]
        work₂ := [true]
        counter₁ := [()] }).map
      (fun c => (c.buffer₁, c.buffer₂, c.input, c.work₁, c.work₂,
        c.output)) =
      some (some true, some false, [true], [false], [true], [false]) := rfl

example :
    (step (oneOp .halt)
      { baseCfg .halt with
        buffer₁ := some true
        buffer₂ := some false
        test := true
        input := [true]
        output := [false]
        work₁ := [false]
        work₂ := [true]
        counter₁ := [()]
        counter₂ := [(), ()]
        counter₃ := [()] }).map
      (fun c => (c.label, c.buffer₁, c.buffer₂, c.test, c.input, c.output,
        c.work₁, c.work₂, c.counter₁, c.counter₂, c.counter₃)) =
      some (none, none, none, false, [true], [false], [false], [true], [()],
        [(), ()], [()]) := rfl

/-! ## Compiler agreement representatives -/

example :
    (compile (oneOp (.pushOutput true true))).step
        (encodeCfg (baseCfg (.pushOutput true true))) =
      (step (oneOp (.pushOutput true true))
        (baseCfg (.pushOutput true true))).map encodeCfg :=
  compile_step _ _

example :
    (compile (oneOp (.pushWork₁ true true))).step
        (encodeCfg (baseCfg (.pushWork₁ true true))) =
      (step (oneOp (.pushWork₁ true true))
        (baseCfg (.pushWork₁ true true))).map encodeCfg :=
  compile_step _ _

example :
    (compile (oneOp (.pushWork₂ false true))).step
        (encodeCfg (baseCfg (.pushWork₂ false true))) =
      (step (oneOp (.pushWork₂ false true))
        (baseCfg (.pushWork₂ false true))).map encodeCfg :=
  compile_step _ _

example :
    let c := { baseCfg (.moveInputWork₁ false id) with input := [true] }
    (compile (oneOp (.moveInputWork₁ false id))).step (encodeCfg c) =
      (step (oneOp (.moveInputWork₁ false id)) c).map encodeCfg := by
  exact compile_step _ _

example :
    let c := { baseCfg (.copyInputWorks false id) with input := [true] }
    (compile (oneOp (.copyInputWorks false id))).step (encodeCfg c) =
      (step (oneOp (.copyInputWorks false id)) c).map encodeCfg := by
  exact compile_step _ _

example :
    let c := { baseCfg (.popWork₂ false id) with work₂ := [true] }
    (compile (oneOp (.popWork₂ false id))).step (encodeCfg c) =
      (step (oneOp (.popWork₂ false id)) c).map encodeCfg := by
  exact compile_step _ _

example :
    let c := { baseCfg (.dec₁ false true) with counter₁ := [()] }
    (compile (oneOp (.dec₁ false true))).step (encodeCfg c) =
      (step (oneOp (.dec₁ false true)) c).map encodeCfg := by
  exact compile_step _ _

example :
    (compile (oneOp (.jump true))).step (encodeCfg (baseCfg (.jump true))) =
      (step (oneOp (.jump true)) (baseCfg (.jump true))).map encodeCfg :=
  compile_step _ _

example :
    (compile (oneOp .halt)).step (encodeCfg (baseCfg .halt)) =
      (step (oneOp .halt) (baseCfg .halt)).map encodeCfg :=
  compile_step _ _

/-! ## Empty input alphabets remain supported -/

def emptyOneOp (operation : Op Empty Bool Bool) : Program Empty Bool where
  Label := Bool
  main := false
  op label := if label then .halt else operation

def emptyBaseCfg (operation : Op Empty Bool Bool) :
    BuilderCfg (emptyOneOp operation) where
  label := some false
  buffer₁ := none
  buffer₂ := none
  test := false
  input := []
  output := []
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

def emptyCounterCfg : BuilderCfg (emptyOneOp (.dec₁ true false)) :=
  { emptyBaseCfg (.dec₁ true false) with counter₁ := [()] }

def emptyNext (symbol : Empty) : Bool := nomatch symbol

example : (compile (emptyOneOp (.dec₁ true false))).initialState =
    (⟨none, none, false⟩ : ControlState Empty) := rfl

example :
    (compile (emptyOneOp (.dec₁ true false))).step
        (encodeCfg emptyCounterCfg) =
      (step (emptyOneOp (.dec₁ true false)) emptyCounterCfg).map encodeCfg :=
  compile_step _ _

example :
    let c := emptyBaseCfg (.moveInputWork₁ true emptyNext)
    (compile (emptyOneOp (.moveInputWork₁ true emptyNext))).step
        (encodeCfg c) =
      (step (emptyOneOp (.moveInputWork₁ true emptyNext)) c).map encodeCfg := by
  exact compile_step _ _

example :
    let c := emptyBaseCfg (.copyInputWorks true emptyNext)
    (compile (emptyOneOp (.copyInputWorks true emptyNext))).step
        (encodeCfg c) =
      (step (emptyOneOp (.copyInputWorks true emptyNext)) c).map encodeCfg := by
  exact compile_step _ _

example :
    (step (emptyOneOp (.dec₁ true false)) emptyCounterCfg).map
      (fun c => (c.label, c.test, c.counter₁)) =
        some (some false, true, []) := rfl

/-! ## Exact output witness and polynomial packaging -/

inductive ConstLabel
  | emit | finish
deriving DecidableEq, Fintype

def constProgram : Program Empty Bool where
  Label := ConstLabel
  main := .emit
  op
    | .emit => .pushOutput true .finish
    | .finish => .halt

def constSteps (_ : List Empty) : Nat := 2

theorem constBuilderOutputs :
    BuilderOutputs constProgram (fun _ => [true]) constSteps := by
  intro input
  have hinput : input = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact Nat.eq_zero_of_not_pos fun h =>
      Empty.elim (input.get ⟨0, h⟩)
  subst input
  constructor
  refine ⟨⟨2, ?_⟩, by simp [constSteps]⟩
  rfl

theorem constOutputs : Outputs constProgram (fun _ => [true]) constSteps :=
  Outputs.of_builder_run constBuilderOutputs

inductive PairLabel
  | emitSecond | emitFirst | finish
deriving DecidableEq, Fintype

/-- Because output pushes prepend, the program emits the desired pair in
reverse instruction order. -/
def pairProgram : Program Empty Bool where
  Label := PairLabel
  main := .emitSecond
  op
    | .emitSecond => .pushOutput true .emitFirst
    | .emitFirst => .pushOutput false .finish
    | .finish => .halt

def pairSteps (_ : List Empty) : Nat := 3

theorem pairBuilderOutputs :
    BuilderOutputs pairProgram (fun _ => [false, true]) pairSteps := by
  intro input
  have hinput : input = [] := by
    apply List.eq_nil_of_length_eq_zero
    exact Nat.eq_zero_of_not_pos fun h =>
      Empty.elim (input.get ⟨0, h⟩)
  subst input
  constructor
  refine ⟨⟨3, ?_⟩, by simp [pairSteps]⟩
  rfl

theorem pairOutputs : Outputs pairProgram (fun _ => [false, true]) pairSteps :=
  Outputs.of_builder_run pairBuilderOutputs

noncomputable def constPolyBound : PolyBound constSteps where
  polynomial := 2
  bound input := by simp [constSteps]

noncomputable def constComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id (fun _ : List Empty => [true]) :=
  ComputableInPolyTime constProgram (fun _ => [true]) constSteps
    constOutputs constPolyBound

end CLRS.Chapter34.Turing.PolyBuilder
