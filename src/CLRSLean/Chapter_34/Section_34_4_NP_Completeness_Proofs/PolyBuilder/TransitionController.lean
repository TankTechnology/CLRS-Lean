import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionScript

/-!
# One fixed controller for a local Cook--Levin transition check

The controller embeds the already verified dispatch, narrowing, equality, and
AND serializers.  Runtime phase boundaries are ordinary unary markers, and no
target gate byte is carried by the input.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Finite control of the five-phase local transition serializer. -/
inductive AffineTransitionControllerLabel
  | pushFalse
  | pushTrue
  | stmt (label : AffineStmtControllerLabel)
  | narrow (label : AffineOrFinLabel)
  | narrowClear
  | eqFin (label : AffineEqFinLabel)
  | eqClear
  | finalAnd (label : AffineOrFinLabel)
  | finalClear
  | finish
  | invalid
deriving DecidableEq, Fintype

/-- Structural label relabeling when the component and outer input alphabets
coincide. -/
def affineTransitionRelabelSameOp {Γ Δ Λ Μ : Type} (tag : Λ → Μ) :
    Op Γ Δ Λ → Op Γ Δ Μ
  | .pushOutput symbol next => .pushOutput symbol (tag next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (tag next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (tag next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (tag nextEmpty) (fun symbol => tag (nextMoved symbol))
  | .inc₁ next => .inc₁ (tag next)
  | .inc₂ next => .inc₂ (tag next)
  | .inc₃ next => .inc₃ (tag next)
  | .dec₁ nextZero nextSucc => .dec₁ (tag nextZero) (tag nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (tag nextZero) (tag nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (tag nextZero) (tag nextSucc)
  | .jump next => .jump (tag next)
  | .halt => .halt

/-- Narrowing finish consumes exactly its following phase marker. -/
def affineTransitionNarrowFinishTarget :
    AffineStmtScriptSym → AffineTransitionControllerLabel
  | .data .tick => .narrowClear
  | _ => .invalid

/-- Equality's coordinate loop either opens another frame or consumes the
marker that starts the final conjunction. -/
def affineTransitionEqCheckTarget :
    AffineStmtScriptSym → AffineTransitionControllerLabel
  | .data .frameEnd => .eqFin .clearMarker
  | .data .tick => .eqClear
  | _ => .invalid

/-- The final AND loop either opens its one encoded frame or consumes the
reserved local-transition terminator used by an outer family controller. -/
def affineTransitionFinalCheckTarget :
    AffineStmtScriptSym → AffineTransitionControllerLabel
  | .data .tick => .finalAnd .andClearMarker
  | .data .separator => .finalAnd .andToFamilyClear
  | .data .frameEnd => .finalClear
  | _ => .invalid

/-- One finite program executes all runtime-sized local-transition phases. -/
def affineTransitionRevProgram : Program AffineStmtScriptSym CircuitSym where
  Label := AffineTransitionControllerLabel
  main := .pushFalse
  op
    | .pushFalse => .pushOutput .constFalseMark .pushTrue
    | .pushTrue => .pushOutput .constTrueMark
        (.stmt affineStmtRevProgram.main)
    | .stmt .finish => .jump (.narrow .narrowSeed)
    | .stmt .invalid => .halt
    | .stmt label => affineTransitionRelabelSameOp .stmt
        (affineStmtRevProgram.op label)
    | .narrow .finish =>
        .popInput .invalid affineTransitionNarrowFinishTarget
    | .narrow .invalid => .halt
    | .narrow label => affineStmtRelabelOp .narrow .invalid
        (affineOrFinRevProgram.op label)
    | .narrowClear => .popWork₁ (.eqFin .seed) (fun _ => .invalid)
    | .eqFin .check =>
        .popInput (.eqFin .finish) affineTransitionEqCheckTarget
    | .eqFin .finish => .halt
    | .eqFin .invalid => .halt
    | .eqFin label => affineStmtRelabelOp .eqFin .invalid
        (affineEqFinRevProgram.op label)
    | .eqClear => .popWork₁ (.finalAnd .andCheck) (fun _ => .invalid)
    | .finalAnd .andCheck =>
        .popInput (.finalAnd .finish) affineTransitionFinalCheckTarget
    | .finalAnd .finish => .jump .finish
    | .finalAnd .invalid => .halt
    | .finalAnd label => affineStmtRelabelOp .finalAnd .invalid
        (affineOrFinRevProgram.op label)
    | .finalClear => .popWork₁ .finish (fun _ => .invalid)
    | .finish => .halt
    | .invalid => .halt

/-- Fieldwise configuration surface for the outer controller. -/
def affineTransitionCfg (label : AffineTransitionControllerLabel)
    (buffer₁ buffer₂ : Option AffineStmtScriptSym) (test : Bool)
    (input : List AffineStmtScriptSym) (output : List CircuitSym)
    (work₁ work₂ : List AffineStmtScriptSym)
    (first second third : List Unit) :
    BuilderCfg affineTransitionRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := first
  counter₂ := second
  counter₃ := third

/-- Clean entry with a caller-supplied output suffix. -/
def affineTransitionLoopCfg (input : List AffineStmtScriptSym)
    (output : List CircuitSym) : BuilderCfg affineTransitionRevProgram :=
  affineTransitionCfg .pushFalse none none false input output
    [] [] [] [] []

/-- Clean redirectable exit preserving a pure-unary outer-family suffix. -/
def affineTransitionFinishInputCfg (tail : List UnaryFrameSym)
    (output : List CircuitSym) : BuilderCfg affineTransitionRevProgram :=
  affineTransitionCfg .finish none none false (tail.map .data) output
    [] [] [] [] []

/-- Embed a statement-controller configuration. -/
def affineTransitionLiftStmtCfg
    (c : BuilderCfg affineStmtRevProgram) :
    BuilderCfg affineTransitionRevProgram where
  label := c.label.map .stmt
  buffer₁ := c.buffer₁
  buffer₂ := c.buffer₂
  test := c.test
  input := c.input
  output := c.output
  work₁ := c.work₁
  work₂ := c.work₂
  counter₁ := c.counter₁
  counter₂ := c.counter₂
  counter₃ := c.counter₃

/-- Embed a pure-unary component configuration into the shared input alphabet. -/
def affineTransitionLiftUnaryCfg {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineTransitionControllerLabel) (c : BuilderCfg P) :
    BuilderCfg affineTransitionRevProgram where
  label := c.label.map tag
  buffer₁ := c.buffer₁.map .data
  buffer₂ := c.buffer₂.map .data
  test := c.test
  input := c.input.map .data
  output := c.output
  work₁ := c.work₁.map .data
  work₂ := c.work₂.map .data
  counter₁ := c.counter₁
  counter₂ := c.counter₂
  counter₃ := c.counter₃

def affineTransitionLiftNarrowCfg
    (c : BuilderCfg affineOrFinRevProgram) :
    BuilderCfg affineTransitionRevProgram :=
  affineTransitionLiftUnaryCfg .narrow c

def affineTransitionLiftEqCfg (c : BuilderCfg affineEqFinRevProgram) :
    BuilderCfg affineTransitionRevProgram :=
  affineTransitionLiftUnaryCfg .eqFin c

def affineTransitionLiftAndCfg
    (c : BuilderCfg affineOrFinRevProgram) :
    BuilderCfg affineTransitionRevProgram :=
  affineTransitionLiftUnaryCfg .finalAnd c

theorem affineTransitionRelabelSame_stepOp
    (op : Op AffineStmtScriptSym CircuitSym AffineStmtControllerLabel)
    (c : BuilderCfg affineStmtRevProgram) :
    stepOp (affineTransitionRelabelSameOp
        AffineTransitionControllerLabel.stmt op)
        (affineTransitionLiftStmtCfg c) =
      affineTransitionLiftStmtCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases input <;> cases work₁ <;> cases work₂ <;>
    cases counter₁ <;> cases counter₂ <;> cases counter₃ <;>
    cases op <;> rfl

theorem affineTransitionRelabelUnary_stepOp
    {P : Program UnaryFrameSym CircuitSym}
    (tag : P.Label → AffineTransitionControllerLabel)
    (op : Op UnaryFrameSym CircuitSym P.Label) (c : BuilderCfg P) :
    stepOp (affineStmtRelabelOp tag AffineTransitionControllerLabel.invalid op)
        (affineTransitionLiftUnaryCfg tag c) =
      affineTransitionLiftUnaryCfg tag (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases input <;> cases work₁ <;> cases work₂ <;>
    cases counter₁ <;> cases counter₂ <;> cases counter₃ <;>
    cases op <;> rfl

private theorem affineTransition_op_stmt
    (label : AffineStmtControllerLabel) (hfinish : label ≠ .finish) :
    affineTransitionRevProgram.op (.stmt label) =
      affineTransitionRelabelSameOp .stmt
        (affineStmtRevProgram.op label) := by
  cases label <;> simp_all [affineTransitionRevProgram,
    affineStmtRevProgram, affineTransitionRelabelSameOp]

private theorem affineTransition_op_narrow
    (label : AffineOrFinLabel) (hfinish : label ≠ .finish) :
    affineTransitionRevProgram.op (.narrow label) =
      affineStmtRelabelOp .narrow .invalid
        (affineOrFinRevProgram.op label) := by
  cases label <;> simp_all [affineTransitionRevProgram,
    affineOrFinRevProgram, affineStmtRelabelOp]

private theorem affineTransition_op_finalAnd
    (label : AffineOrFinLabel) (hfinish : label ≠ .finish)
    (hcheck : label ≠ .andCheck) :
    affineTransitionRevProgram.op (.finalAnd label) =
      affineStmtRelabelOp .finalAnd .invalid
        (affineOrFinRevProgram.op label) := by
  cases label <;> simp_all [affineTransitionRevProgram,
    affineOrFinRevProgram, affineStmtRelabelOp]

private theorem affineTransition_op_eq
    (label : AffineEqFinLabel) (hcheck : label ≠ .check) :
    affineTransitionRevProgram.op (.eqFin label) =
      affineStmtRelabelOp .eqFin .invalid
        (affineEqFinRevProgram.op label) := by
  cases label <;> simp_all [affineTransitionRevProgram,
    affineEqFinRevProgram, affineStmtRelabelOp]

theorem affineTransitionLiftStmt_step
    (c : BuilderCfg affineStmtRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineTransitionRevProgram (affineTransitionLiftStmtCfg c) =
      Option.map affineTransitionLiftStmtCfg
        (step affineStmtRevProgram c) := by
  unfold step
  rw [show (affineTransitionLiftStmtCfg c).label =
    c.label.map .stmt by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hfinish : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineTransition_op_stmt label hfinish]
      change some (stepOp
          (affineTransitionRelabelSameOp AffineTransitionControllerLabel.stmt
            (affineStmtRevProgram.op label))
          (affineTransitionLiftStmtCfg c)) =
        some (affineTransitionLiftStmtCfg
          (stepOp (affineStmtRevProgram.op label) c))
      exact congrArg some
        (affineTransitionRelabelSame_stepOp
          (affineStmtRevProgram.op label) c)

theorem affineTransitionLiftNarrow_step
    (c : BuilderCfg affineOrFinRevProgram)
    (hexit : c.label ≠ some .finish) :
    step affineTransitionRevProgram (affineTransitionLiftNarrowCfg c) =
      Option.map affineTransitionLiftNarrowCfg
        (step affineOrFinRevProgram c) := by
  unfold step
  rw [show (affineTransitionLiftNarrowCfg c).label =
    c.label.map .narrow by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hfinish : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineTransition_op_narrow label hfinish]
      change some (stepOp
          (affineStmtRelabelOp AffineTransitionControllerLabel.narrow
            AffineTransitionControllerLabel.invalid
            (affineOrFinRevProgram.op label))
          (affineTransitionLiftNarrowCfg c)) =
        some (affineTransitionLiftNarrowCfg
          (stepOp (affineOrFinRevProgram.op label) c))
      exact congrArg some
        (affineTransitionRelabelUnary_stepOp
          AffineTransitionControllerLabel.narrow
          (affineOrFinRevProgram.op label) c)

/-- The final-AND state where the outer controller deliberately consumes its
reserved local-transition terminator. -/
def affineTransitionAndBoundaryBad
    (c : BuilderCfg affineOrFinRevProgram) : Prop :=
  c.label = some .andCheck ∧ ∃ tail, c.input = .frameEnd :: tail

theorem affineTransitionLiftAnd_step
    (c : BuilderCfg affineOrFinRevProgram)
    (hexit : c.label ≠ some .finish)
    (hsafe : ¬ affineTransitionAndBoundaryBad c) :
    step affineTransitionRevProgram (affineTransitionLiftAndCfg c) =
      Option.map affineTransitionLiftAndCfg
        (step affineOrFinRevProgram c) := by
  unfold step
  rw [show (affineTransitionLiftAndCfg c).label =
    c.label.map .finalAnd by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hfinish : label ≠ .finish := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      by_cases hcheck : label = .andCheck
      · subst label
        rcases c with
          ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
            counter₁, counter₂, counter₃⟩
        simp only at hlabel
        subst label
        cases input with
        | nil => rfl
        | cons head tail =>
            cases head with
            | tick => rfl
            | separator => rfl
            | frameEnd =>
                exfalso
                apply hsafe
                exact ⟨rfl, ⟨tail, rfl⟩⟩
      rw [affineTransition_op_finalAnd label hfinish hcheck]
      change some (stepOp
          (affineStmtRelabelOp AffineTransitionControllerLabel.finalAnd
            AffineTransitionControllerLabel.invalid
            (affineOrFinRevProgram.op label))
          (affineTransitionLiftAndCfg c)) =
        some (affineTransitionLiftAndCfg
          (stepOp (affineOrFinRevProgram.op label) c))
      exact congrArg some
        (affineTransitionRelabelUnary_stepOp
          AffineTransitionControllerLabel.finalAnd
          (affineOrFinRevProgram.op label) c)

/-- The equality state where the outer controller deliberately consumes the
phase boundary instead of following the standalone invalid branch. -/
def affineTransitionEqBoundaryBad
    (c : BuilderCfg affineEqFinRevProgram) : Prop :=
  c.label = some .check ∧
    ∃ head tail, c.input = head :: tail ∧ head ≠ .frameEnd

theorem affineTransitionLiftEq_step
    (c : BuilderCfg affineEqFinRevProgram)
    (hsafe : ¬ affineTransitionEqBoundaryBad c) :
    step affineTransitionRevProgram (affineTransitionLiftEqCfg c) =
      Option.map affineTransitionLiftEqCfg
        (step affineEqFinRevProgram c) := by
  unfold step
  rw [show (affineTransitionLiftEqCfg c).label =
    c.label.map .eqFin by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      simp only [Option.map_some]
      by_cases hcheck : label = .check
      · subst label
        rcases c with
          ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
            counter₁, counter₂, counter₃⟩
        simp only at hlabel
        subst label
        cases input with
        | nil => rfl
        | cons head tail =>
            cases head with
            | tick =>
                exfalso
                apply hsafe
                exact ⟨rfl, ⟨.tick, tail, rfl, by decide⟩⟩
            | frameEnd => rfl
            | separator =>
                exfalso
                apply hsafe
                exact ⟨rfl, ⟨.separator, tail, rfl, by decide⟩⟩
      rw [affineTransition_op_eq label hcheck]
      exact congrArg some
        (affineTransitionRelabelUnary_stepOp
          AffineTransitionControllerLabel.eqFin
          (affineEqFinRevProgram.op label) c)

private theorem affineTransition_iterate_bind_none {σ : Type}
    (f : σ → Option σ) :
    ∀ n : Nat, (flip Option.bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind f)^[n] none = none
      exact ih

private theorem affineTransition_haltLabel_no_return
    {Γ : Type} {P : Program Γ CircuitSym} (halt target : P.Label)
    (hop : P.op halt = .halt) (a b : BuilderCfg P)
    (ha : a.label = some halt) (hb : b.label = some target) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (step P a) ≠ some b := by
  intro n
  let halted : BuilderCfg P :=
    { a with label := none, buffer₁ := none, buffer₂ := none, test := false }
  have hstep : step P a = some halted := by
    unfold step
    rw [ha]
    simp [hop, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind (step P))^[n] (step P halted) ≠ some b
      have hnone : step P halted = none := rfl
      rw [hnone, affineTransition_iterate_bind_none]
      simp

private theorem affineTransition_lift_iterations_to_haltExit
    {Γ : Type} {P : Program Γ CircuitSym} (exit : P.Label)
    (hop : P.op exit = .halt)
    (tr : BuilderCfg P → BuilderCfg affineTransitionRevProgram)
    (hstep : ∀ c, c.label ≠ some exit →
      step affineTransitionRevProgram (tr c) = Option.map tr (step P c))
    {a b : BuilderCfg P} (hb : b.label = some exit) : ∀ n : Nat,
    (flip Option.bind (step P))^[n] (some a) = some b →
      (flip Option.bind (step affineTransitionRevProgram))^[n]
        (some (tr a)) = some (tr b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step P))^[n] (step P a) = some b at h
      change (flip Option.bind (step affineTransitionRevProgram))^[n]
        (step affineTransitionRevProgram (tr a)) = some (tr b)
      have haexit : a.label ≠ some exit := by
        intro ha
        exact affineTransition_haltLabel_no_return exit exit hop
          a b ha hb n h
      cases hsource : step P a with
      | none =>
          rw [hsource, affineTransition_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := hstep a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem affineTransitionEqBoundaryBad_step
    (c : BuilderCfg affineEqFinRevProgram)
    (hbad : affineTransitionEqBoundaryBad c) :
    ∃ d : BuilderCfg affineEqFinRevProgram,
      step affineEqFinRevProgram c = some d ∧
        d.label = some .invalid := by
  rcases hbad with ⟨hlabel, head, tail, hinput, hhead⟩
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at hinput hlabel
  subst input
  subst label
  cases head <;> simp_all [affineEqFinRevProgram, step, stepOp]

private theorem affineTransition_liftEq_iterations_avoiding
    {a b : BuilderCfg affineEqFinRevProgram}
    (hb : b.label = some .check) : ∀ n : Nat,
    (flip Option.bind (step affineEqFinRevProgram))^[n] (some a) = some b →
      (flip Option.bind (step affineTransitionRevProgram))^[n]
        (some (affineTransitionLiftEqCfg a)) =
          some (affineTransitionLiftEqCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineEqFinRevProgram))^[n]
        (step affineEqFinRevProgram a) = some b at h
      change (flip Option.bind (step affineTransitionRevProgram))^[n]
        (step affineTransitionRevProgram (affineTransitionLiftEqCfg a)) =
          some (affineTransitionLiftEqCfg b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact affineTransition_haltLabel_no_return
          AffineEqFinLabel.finish AffineEqFinLabel.check rfl
          a b ha hb n h
      have hasafe : ¬ affineTransitionEqBoundaryBad a := by
        intro hbad
        obtain ⟨d, hstep, hdlabel⟩ :=
          affineTransitionEqBoundaryBad_step a hbad
        cases n with
        | zero =>
            rw [hstep] at h
            injection h with hdb
            have hlabels := congrArg (fun cfg => cfg.label) hdb
            simp [hdlabel, hb] at hlabels
        | succ n =>
            rw [Function.iterate_succ_apply, hstep] at h
            change (flip Option.bind (step affineEqFinRevProgram))^[n]
              (step affineEqFinRevProgram d) = some b at h
            exact affineTransition_haltLabel_no_return
              AffineEqFinLabel.invalid AffineEqFinLabel.check rfl
              d b hdlabel hb n h
      cases hsource : step affineEqFinRevProgram a with
      | none =>
          rw [hsource, affineTransition_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := affineTransitionLiftEq_step a hasafe
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private theorem affineTransitionAndBoundaryBad_step
    (c : BuilderCfg affineOrFinRevProgram)
    (hbad : affineTransitionAndBoundaryBad c) :
    ∃ d : BuilderCfg affineOrFinRevProgram,
      step affineOrFinRevProgram c = some d ∧
        d.label = some .invalid := by
  rcases hbad with ⟨hlabel, tail, hinput⟩
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at hinput hlabel
  subst input
  subst label
  refine ⟨_, rfl, rfl⟩

private theorem affineTransition_liftAnd_iterations_avoiding
    (target : AffineOrFinLabel) (htarget : target ≠ .invalid)
    {a b : BuilderCfg affineOrFinRevProgram}
    (hb : b.label = some target) : ∀ n : Nat,
    (flip Option.bind (step affineOrFinRevProgram))^[n] (some a) = some b →
      (flip Option.bind (step affineTransitionRevProgram))^[n]
        (some (affineTransitionLiftAndCfg a)) =
          some (affineTransitionLiftAndCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      simp [hab]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind (step affineOrFinRevProgram))^[n]
        (step affineOrFinRevProgram a) = some b at h
      change (flip Option.bind (step affineTransitionRevProgram))^[n]
        (step affineTransitionRevProgram (affineTransitionLiftAndCfg a)) =
          some (affineTransitionLiftAndCfg b)
      have haexit : a.label ≠ some .finish := by
        intro ha
        exact affineTransition_haltLabel_no_return
          AffineOrFinLabel.finish target rfl a b ha hb n h
      have hasafe : ¬ affineTransitionAndBoundaryBad a := by
        intro hbad
        obtain ⟨d, hstep, hdlabel⟩ :=
          affineTransitionAndBoundaryBad_step a hbad
        cases n with
        | zero =>
            rw [hstep] at h
            injection h with hdb
            have hlabels := congrArg (fun cfg => cfg.label) hdb
            simp [hdlabel, hb] at hlabels
            exact htarget (Option.some.inj hlabels.symm)
        | succ n =>
            rw [Function.iterate_succ_apply, hstep] at h
            change (flip Option.bind (step affineOrFinRevProgram))^[n]
              (step affineOrFinRevProgram d) = some b at h
            exact affineTransition_haltLabel_no_return
              AffineOrFinLabel.invalid target rfl d b hdlabel hb n h
      cases hsource : step affineOrFinRevProgram a with
      | none =>
          rw [hsource, affineTransition_iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim := affineTransitionLiftAnd_step a haexit hasafe
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineTransitionLiftStmt_runToFinish
    {a b : BuilderCfg affineStmtRevProgram}
    (hb : b.label = some .finish) (m : Nat)
    (sourceRun : EvalsToInTime (step affineStmtRevProgram) a (some b) m) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftStmtCfg a)
      (some (affineTransitionLiftStmtCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineTransition_lift_iterations_to_haltExit
    AffineStmtControllerLabel.finish rfl
    affineTransitionLiftStmtCfg affineTransitionLiftStmt_step hb
    sourceRun.steps sourceRun.evals_in_steps

private def affineTransitionLiftNarrow_runToFinish
    {a b : BuilderCfg affineOrFinRevProgram}
    (hb : b.label = some .finish) (m : Nat)
    (sourceRun : EvalsToInTime (step affineOrFinRevProgram) a (some b) m) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftNarrowCfg a)
      (some (affineTransitionLiftNarrowCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineTransition_lift_iterations_to_haltExit AffineOrFinLabel.finish rfl
    affineTransitionLiftNarrowCfg affineTransitionLiftNarrow_step hb
    sourceRun.steps sourceRun.evals_in_steps

private def affineTransitionLiftAnd_runToFinish
    {a b : BuilderCfg affineOrFinRevProgram}
    (hb : b.label = some .finish) (m : Nat)
    (sourceRun : EvalsToInTime (step affineOrFinRevProgram) a (some b) m) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftAndCfg a)
      (some (affineTransitionLiftAndCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineTransition_liftAnd_iterations_avoiding .finish (by decide) hb
    sourceRun.steps sourceRun.evals_in_steps

private def affineTransitionLiftAnd_runToCheck
    {a b : BuilderCfg affineOrFinRevProgram}
    (hb : b.label = some .andCheck) (m : Nat)
    (sourceRun : EvalsToInTime (step affineOrFinRevProgram) a (some b) m) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftAndCfg a)
      (some (affineTransitionLiftAndCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineTransition_liftAnd_iterations_avoiding .andCheck (by decide) hb
    sourceRun.steps sourceRun.evals_in_steps

private def affineTransitionLiftEq_runToCheck
    {a b : BuilderCfg affineEqFinRevProgram}
    (hb : b.label = some .check) (m : Nat)
    (sourceRun : EvalsToInTime (step affineEqFinRevProgram) a (some b) m) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftEqCfg a)
      (some (affineTransitionLiftEqCfg b)) m := by
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineTransition_liftEq_iterations_avoiding hb
    sourceRun.steps sourceRun.evals_in_steps

private def affineTransitionBoolOutput (output : List CircuitSym) :
    List CircuitSym :=
  boolPoolGateStream.reverse ++ output

private def affineTransitionStmtOutput (script : AffineTransitionScript)
    (output : List CircuitSym) : List CircuitSym :=
  (affineStmtScriptGateStream script.dispatch).reverse ++
    affineTransitionBoolOutput output

private def affineTransitionNarrowOutput (script : AffineTransitionScript)
    (output : List CircuitSym) : List CircuitSym :=
  (affineOrThenNotGateStream script.narrowFrames
    script.narrowSource).reverse ++ affineTransitionStmtOutput script output

private def affineTransitionEqOutput (script : AffineTransitionScript)
    (output : List CircuitSym) : List CircuitSym :=
  (affineEqFinGateStream script.eqFrames).reverse ++
    affineTransitionNarrowOutput script output

private def affineTransitionFinalOutput (script : AffineTransitionScript)
    (output : List CircuitSym) : List CircuitSym :=
  (affineAndFinGateStream [script.finalAnd]).reverse ++
    affineTransitionEqOutput script output

private def affineTransitionNarrowTail (script : AffineTransitionScript) :
    List UnaryFrameSym :=
  .tick :: encodeAffineEqFinFrames script.eqFrames ++
    .tick :: encodeAffineAndFinFrames [script.finalAnd]

private def affineTransitionEqTail (script : AffineTransitionScript) :
    List UnaryFrameSym :=
  .tick :: encodeAffineAndFinFrames [script.finalAnd]

/-- Complete local-transition input followed by a reserved terminator and an
arbitrary pure-unary suffix owned by an outer family controller. -/
def encodeAffineTransitionScriptWithTail (script : AffineTransitionScript)
    (tail : List UnaryFrameSym) : List AffineStmtScriptSym :=
  encodeAffineStmtTransitionInput script.dispatch
    (encodeAffineOrThenNotInput script.narrowFrames script.narrowSource ++
      .tick :: encodeAffineEqFinFrames script.eqFrames ++
      .tick :: encodeAffineAndFinFrames [script.finalAnd] ++
      .frameEnd :: tail)

private def affineTransitionNarrowTailWithTail
    (script : AffineTransitionScript) (tail : List UnaryFrameSym) :
    List UnaryFrameSym :=
  .tick :: encodeAffineEqFinFrames script.eqFrames ++
    .tick :: encodeAffineAndFinFrames [script.finalAnd] ++
    .frameEnd :: tail

private def affineTransitionEqTailWithTail
    (script : AffineTransitionScript) (tail : List UnaryFrameSym) :
    List UnaryFrameSym :=
  .tick :: encodeAffineAndFinFrames [script.finalAnd] ++ .frameEnd :: tail

private def affineTransition_statement_run (script : AffineTransitionScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg (encodeAffineTransitionScript script) output)
      (some (affineTransitionLiftStmtCfg
        (affineStmtFinishInputCfg
          ((encodeAffineTransitionTail script).map .data)
          (affineTransitionStmtOutput script output))))
      (2 + affineStmtScriptFinishSteps script.dispatch) := by
  let boolOutput := affineTransitionBoolOutput output
  have hbool : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg (encodeAffineTransitionScript script) output)
      (some (affineTransitionLiftStmtCfg
        (affineStmtLoopCfg (encodeAffineTransitionScript script) boolOutput))) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  have hsource := affineStmt_runToFinishWithTail script.dispatch
    (encodeAffineTransitionTail script) boolOutput
  have hlift := affineTransitionLiftStmt_runToFinish rfl _ hsource
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    2 (affineStmtScriptFinishSteps script.dispatch) _
    (affineTransitionLiftStmtCfg
      (affineStmtLoopCfg (encodeAffineTransitionScript script) boolOutput)) _
    hbool (by
      simpa [encodeAffineTransitionScript, boolOutput] using hlift)
  convert full using 1
  · simp [affineTransitionStmtOutput,
      affineTransitionBoolOutput]
  · omega

private def affineTransition_narrow_run (script : AffineTransitionScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftStmtCfg
        (affineStmtFinishInputCfg
          ((encodeAffineTransitionTail script).map .data)
          (affineTransitionStmtOutput script output)))
      (some (affineTransitionLiftNarrowCfg
        (affineOrFinFinishInputCfg (affineTransitionNarrowTail script)
          (affineTransitionNarrowOutput script output))))
      (1 + affineOrThenNotUntilFinishSteps
        script.narrowFrames script.narrowSource) := by
  let stmtOutput := affineTransitionStmtOutput script output
  have hbridge : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftStmtCfg
        (affineStmtFinishInputCfg
          ((encodeAffineTransitionTail script).map .data) stmtOutput))
      (some (affineTransitionLiftNarrowCfg
        (affineOrThenNotLoopCfg
          (encodeAffineOrThenNotInput script.narrowFrames
            script.narrowSource ++ affineTransitionNarrowTail script)
          stmtOutput))) 1 := by
    have hinput : (encodeAffineTransitionTail script).map
        AffineStmtScriptSym.data =
        (encodeAffineOrThenNotInput script.narrowFrames
          script.narrowSource ++ affineTransitionNarrowTail script).map
            AffineStmtScriptSym.data := by
      simp [encodeAffineTransitionTail, affineTransitionNarrowTail,
        List.map_append, List.append_assoc]
    rw [hinput]
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hsource := affineOrThenNot_runToFinishWithTail
    script.narrowFrames script.narrowSource
    (affineTransitionNarrowTail script) stmtOutput
  have hlift := affineTransitionLiftNarrow_runToFinish rfl _ hsource
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    1 (affineOrThenNotUntilFinishSteps
      script.narrowFrames script.narrowSource) _
    (affineTransitionLiftNarrowCfg
      (affineOrThenNotLoopCfg
        (encodeAffineOrThenNotInput script.narrowFrames
          script.narrowSource ++ affineTransitionNarrowTail script)
        stmtOutput)) _ hbridge hlift
  convert full using 1
  · simp [affineTransitionNarrowOutput, stmtOutput]
  · omega

private def affineTransition_eq_run (script : AffineTransitionScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftNarrowCfg
        (affineOrFinFinishInputCfg (affineTransitionNarrowTail script)
          (affineTransitionNarrowOutput script output)))
      (some (affineTransitionLiftEqCfg
        (affineEqFinCheckCfg (affineTransitionEqTail script)
          (affineTransitionEqOutput script output))))
      (2 + (1 + affineEqFinBodySteps script.eqFrames)) := by
  let narrowOutput := affineTransitionNarrowOutput script output
  have hbridge : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftNarrowCfg
        (affineOrFinFinishInputCfg (affineTransitionNarrowTail script)
          narrowOutput))
      (some (affineTransitionLiftEqCfg
        (affineEqFinLoopCfg
          (encodeAffineEqFinFrames script.eqFrames ++
            affineTransitionEqTail script) narrowOutput))) 2 :=
    ⟨⟨2, by
      simp [flip, affineTransitionNarrowTail, affineTransitionEqTail,
        affineTransitionLiftNarrowCfg, affineTransitionLiftEqCfg,
        affineTransitionLiftUnaryCfg, affineOrFinFinishInputCfg,
        affineOrFinCfg, affineEqFinLoopCfg, affineEqFinCfg,
        affineTransitionRevProgram, step, stepOp,
        affineTransitionNarrowFinishTarget, List.map_append]⟩, le_rfl⟩
  have hsource := affineEqFin_runToCheck script.eqFrames
    (affineTransitionEqTail script) narrowOutput
  have hlift := affineTransitionLiftEq_runToCheck rfl _ hsource
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    2 (1 + affineEqFinBodySteps script.eqFrames) _
    (affineTransitionLiftEqCfg
      (affineEqFinLoopCfg
        (encodeAffineEqFinFrames script.eqFrames ++
          affineTransitionEqTail script) narrowOutput)) _ hbridge hlift
  convert full using 1
  · simp [affineTransitionEqOutput, narrowOutput]
  · omega

private def affineTransition_and_run (script : AffineTransitionScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftEqCfg
        (affineEqFinCheckCfg (affineTransitionEqTail script)
          (affineTransitionEqOutput script output)))
      (some (affineTransitionLiftAndCfg
        (affineOrFinFinishCfg (affineTransitionFinalOutput script output))))
      (2 + affineAndFinUntilFinishSteps [script.finalAnd]) := by
  let eqOutput := affineTransitionEqOutput script output
  have hbridge : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftEqCfg
        (affineEqFinCheckCfg (affineTransitionEqTail script) eqOutput))
      (some (affineTransitionLiftAndCfg
        (affineAndFinLoopCfg
          (encodeAffineAndFinFrames [script.finalAnd]) eqOutput))) 2 :=
    ⟨⟨2, by
      simp [flip, affineTransitionEqTail, affineTransitionLiftEqCfg,
        affineTransitionLiftAndCfg, affineTransitionLiftUnaryCfg,
        affineEqFinCheckCfg, affineEqFinCfg, affineAndFinLoopCfg,
        affineOrFinCfg, affineTransitionRevProgram,
        affineTransitionEqCheckTarget, step, stepOp]⟩,
      le_rfl⟩
  have hsource := affineAndFin_runToFinish [script.finalAnd] eqOutput
  have hlift := affineTransitionLiftAnd_runToFinish rfl _ hsource
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    2 (affineAndFinUntilFinishSteps [script.finalAnd]) _
    (affineTransitionLiftAndCfg
      (affineAndFinLoopCfg
        (encodeAffineAndFinFrames [script.finalAnd]) eqOutput)) _
    hbridge hlift
  convert full using 1
  · simp [affineTransitionFinalOutput, eqOutput]
  · omega

private def affineTransition_finish_run (script : AffineTransitionScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftAndCfg
        (affineOrFinFinishCfg (affineTransitionFinalOutput script output)))
      (some (haltCfg affineTransitionRevProgram
      (affineTransitionFinalOutput script output))) 2 :=
  ⟨⟨2, rfl⟩, le_rfl⟩

private def affineTransition_statement_runWithTail
    (script : AffineTransitionScript) (transitionTail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg
        (encodeAffineStmtTransitionInput script.dispatch transitionTail) output)
      (some (affineTransitionLiftStmtCfg
        (affineStmtFinishInputCfg (transitionTail.map .data)
          (affineTransitionStmtOutput script output))))
      (2 + affineStmtScriptFinishSteps script.dispatch) := by
  let boolOutput := affineTransitionBoolOutput output
  have hbool : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg
        (encodeAffineStmtTransitionInput script.dispatch transitionTail) output)
      (some (affineTransitionLiftStmtCfg
        (affineStmtLoopCfg
          (encodeAffineStmtTransitionInput script.dispatch transitionTail)
          boolOutput))) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hsource := affineStmt_runToFinishWithTail script.dispatch
    transitionTail boolOutput
  have hlift := affineTransitionLiftStmt_runToFinish rfl _ hsource
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    2 (affineStmtScriptFinishSteps script.dispatch) _
    (affineTransitionLiftStmtCfg
      (affineStmtLoopCfg
        (encodeAffineStmtTransitionInput script.dispatch transitionTail)
        boolOutput)) _ hbool hlift
  convert full using 1
  · simp [affineTransitionStmtOutput, affineTransitionBoolOutput, boolOutput]
  · omega

private def affineTransition_narrow_runWithTail
    (script : AffineTransitionScript) (narrowTail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftStmtCfg
        (affineStmtFinishInputCfg
          ((encodeAffineOrThenNotInput script.narrowFrames
            script.narrowSource ++ narrowTail).map .data)
          (affineTransitionStmtOutput script output)))
      (some (affineTransitionLiftNarrowCfg
        (affineOrFinFinishInputCfg narrowTail
          (affineTransitionNarrowOutput script output))))
      (1 + affineOrThenNotUntilFinishSteps
        script.narrowFrames script.narrowSource) := by
  let stmtOutput := affineTransitionStmtOutput script output
  have hbridge : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftStmtCfg
        (affineStmtFinishInputCfg
          ((encodeAffineOrThenNotInput script.narrowFrames
            script.narrowSource ++ narrowTail).map .data) stmtOutput))
      (some (affineTransitionLiftNarrowCfg
        (affineOrThenNotLoopCfg
          (encodeAffineOrThenNotInput script.narrowFrames
            script.narrowSource ++ narrowTail) stmtOutput))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have hsource := affineOrThenNot_runToFinishWithTail
    script.narrowFrames script.narrowSource narrowTail stmtOutput
  have hlift := affineTransitionLiftNarrow_runToFinish rfl _ hsource
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    1 (affineOrThenNotUntilFinishSteps
      script.narrowFrames script.narrowSource) _
    (affineTransitionLiftNarrowCfg
      (affineOrThenNotLoopCfg
        (encodeAffineOrThenNotInput script.narrowFrames
          script.narrowSource ++ narrowTail) stmtOutput)) _ hbridge hlift
  convert full using 1
  · simp [affineTransitionNarrowOutput, stmtOutput]
  · omega

private def affineTransition_eq_runWithTail
    (script : AffineTransitionScript) (eqTail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftNarrowCfg
        (affineOrFinFinishInputCfg
          (.tick :: encodeAffineEqFinFrames script.eqFrames ++ eqTail)
          (affineTransitionNarrowOutput script output)))
      (some (affineTransitionLiftEqCfg
        (affineEqFinCheckCfg eqTail
          (affineTransitionEqOutput script output))))
      (2 + (1 + affineEqFinBodySteps script.eqFrames)) := by
  let narrowOutput := affineTransitionNarrowOutput script output
  have hbridge : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftNarrowCfg
        (affineOrFinFinishInputCfg
          (.tick :: encodeAffineEqFinFrames script.eqFrames ++ eqTail)
          narrowOutput))
      (some (affineTransitionLiftEqCfg
        (affineEqFinLoopCfg
          (encodeAffineEqFinFrames script.eqFrames ++ eqTail)
          narrowOutput))) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hsource := affineEqFin_runToCheck script.eqFrames eqTail narrowOutput
  have hlift := affineTransitionLiftEq_runToCheck rfl _ hsource
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    2 (1 + affineEqFinBodySteps script.eqFrames) _
    (affineTransitionLiftEqCfg
      (affineEqFinLoopCfg
        (encodeAffineEqFinFrames script.eqFrames ++ eqTail) narrowOutput)) _
    hbridge hlift
  convert full using 1
  · simp [affineTransitionEqOutput, narrowOutput]
  · omega

private def affineTransition_and_finish_runWithTail
    (script : AffineTransitionScript) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftEqCfg
        (affineEqFinCheckCfg
          (.tick :: encodeAffineAndFinFrames [script.finalAnd] ++
            .frameEnd :: tail)
          (affineTransitionEqOutput script output)))
      (some (affineTransitionFinishInputCfg tail
        (affineTransitionFinalOutput script output)))
      (2 + affineAndFinBodySteps [script.finalAnd] + 2) := by
  let eqOutput := affineTransitionEqOutput script output
  have hbridge : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftEqCfg
        (affineEqFinCheckCfg
          (.tick :: encodeAffineAndFinFrames [script.finalAnd] ++
            .frameEnd :: tail) eqOutput))
      (some (affineTransitionLiftAndCfg
        (affineAndFinLoopCfg
          (encodeAffineAndFinFrames [script.finalAnd] ++ .frameEnd :: tail)
          eqOutput))) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  have hsource := affineAndFinFrames_runToCheck [script.finalAnd]
    (.frameEnd :: tail) eqOutput
  have hlift := affineTransitionLiftAnd_runToCheck rfl _ hsource
  let gateOutput := affineTransitionFinalOutput script output
  have hfinish : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLiftAndCfg
        (affineAndFinLoopCfg (.frameEnd :: tail) gateOutput))
      (some (affineTransitionFinishInputCfg tail gateOutput)) 2 :=
    ⟨⟨2, rfl⟩, le_rfl⟩
  let throughBody := EvalsToInTime.trans (step affineTransitionRevProgram)
    2 (affineAndFinBodySteps [script.finalAnd]) _
    (affineTransitionLiftAndCfg
      (affineAndFinLoopCfg
        (encodeAffineAndFinFrames [script.finalAnd] ++ .frameEnd :: tail)
        eqOutput)) _ hbridge hlift
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    (2 + affineAndFinBodySteps [script.finalAnd]) 2 _
    (affineTransitionLiftAndCfg
      (affineAndFinLoopCfg (.frameEnd :: tail) gateOutput)) _
    (by
      convert throughBody using 1
      · simp [affineTransitionFinalOutput, gateOutput, eqOutput]
      · omega)
    hfinish
  convert full using 1
  omega

/-- Exact runtime of the fixed five-phase local-transition controller. -/
def affineTransitionRunSteps (script : AffineTransitionScript) : Nat :=
  2 + affineStmtScriptFinishSteps script.dispatch +
    (1 + affineOrThenNotUntilFinishSteps
      script.narrowFrames script.narrowSource) +
    (2 + (1 + affineEqFinBodySteps script.eqFrames)) +
    (2 + affineAndFinUntilFinishSteps [script.finalAnd]) + 2

/-- Exact runtime to the clean redirectable finish used by a runtime-length
family of local transition scripts. -/
def affineTransitionRunToFinishSteps
    (script : AffineTransitionScript) : Nat :=
  2 + affineStmtScriptFinishSteps script.dispatch +
    (1 + affineOrThenNotUntilFinishSteps
      script.narrowFrames script.narrowSource) +
    (2 + (1 + affineEqFinBodySteps script.eqFrames)) +
    (2 + affineAndFinBodySteps [script.finalAnd] + 2)

/-- Execute one complete local-transition script, consume its reserved local
terminator, and preserve an arbitrary outer-family suffix. -/
def affineTransition_runToFinishWithTail
    (script : AffineTransitionScript) (tail : List UnaryFrameSym)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg
        (encodeAffineTransitionScriptWithTail script tail) output)
      (some (affineTransitionFinishInputCfg tail
        ((affineTransitionGateStream script).reverse ++ output)))
      (affineTransitionRunToFinishSteps script) := by
  let narrowTail := affineTransitionNarrowTailWithTail script tail
  let eqTail := affineTransitionEqTailWithTail script tail
  have hstmt := affineTransition_statement_runWithTail script
    (encodeAffineOrThenNotInput script.narrowFrames script.narrowSource ++
      narrowTail) output
  have hnarrow := affineTransition_narrow_runWithTail script narrowTail output
  have heq := affineTransition_eq_runWithTail script eqTail output
  have hand := affineTransition_and_finish_runWithTail script tail output
  let throughNarrowRaw := EvalsToInTime.trans
    (step affineTransitionRevProgram)
    (2 + affineStmtScriptFinishSteps script.dispatch)
    (1 + affineOrThenNotUntilFinishSteps
      script.narrowFrames script.narrowSource) _ _ _ hstmt hnarrow
  have throughNarrow : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg
        (encodeAffineStmtTransitionInput script.dispatch
          (encodeAffineOrThenNotInput script.narrowFrames
            script.narrowSource ++ narrowTail)) output)
      (some (affineTransitionLiftNarrowCfg
        (affineOrFinFinishInputCfg narrowTail
          (affineTransitionNarrowOutput script output))))
      (2 + affineStmtScriptFinishSteps script.dispatch +
        (1 + affineOrThenNotUntilFinishSteps
          script.narrowFrames script.narrowSource)) := by
    convert throughNarrowRaw using 1
    omega
  let throughEqRaw := EvalsToInTime.trans (step affineTransitionRevProgram)
    (2 + affineStmtScriptFinishSteps script.dispatch +
      (1 + affineOrThenNotUntilFinishSteps
        script.narrowFrames script.narrowSource))
    (2 + (1 + affineEqFinBodySteps script.eqFrames)) _ _ _
    throughNarrow (by
      simpa [narrowTail, eqTail, affineTransitionNarrowTailWithTail,
        affineTransitionEqTailWithTail, List.append_assoc] using heq)
  have throughEq : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg
        (encodeAffineStmtTransitionInput script.dispatch
          (encodeAffineOrThenNotInput script.narrowFrames
            script.narrowSource ++ narrowTail)) output)
      (some (affineTransitionLiftEqCfg
        (affineEqFinCheckCfg eqTail
          (affineTransitionEqOutput script output))))
      (2 + affineStmtScriptFinishSteps script.dispatch +
        (1 + affineOrThenNotUntilFinishSteps
          script.narrowFrames script.narrowSource) +
        (2 + (1 + affineEqFinBodySteps script.eqFrames))) := by
    convert throughEqRaw using 1
    · simp [eqTail, affineTransitionEqTailWithTail]
    · omega
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    (2 + affineStmtScriptFinishSteps script.dispatch +
      (1 + affineOrThenNotUntilFinishSteps
        script.narrowFrames script.narrowSource) +
      (2 + (1 + affineEqFinBodySteps script.eqFrames)))
    (2 + affineAndFinBodySteps [script.finalAnd] + 2) _ _ _
    throughEq (by simpa [eqTail, affineTransitionEqTailWithTail,
      List.append_assoc] using hand)
  convert full using 1
  · simp [encodeAffineTransitionScriptWithTail, narrowTail,
      affineTransitionNarrowTailWithTail, List.append_assoc]
  · simp [affineTransitionFinalOutput, affineTransitionEqOutput,
      affineTransitionNarrowOutput, affineTransitionStmtOutput,
      affineTransitionBoolOutput, affineTransitionGateStream,
      List.reverse_append, List.append_assoc]
  · simp [affineTransitionRunToFinishSteps]
    omega

/-- One fixed finite program emits exactly the reverse of the local
transition gate stream and then halts. -/
def affineTransition_run (script : AffineTransitionScript)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg (encodeAffineTransitionScript script) output)
      (some (haltCfg affineTransitionRevProgram
        ((affineTransitionGateStream script).reverse ++ output)))
      (affineTransitionRunSteps script) := by
  have hstmt := affineTransition_statement_run script output
  have hnarrow := affineTransition_narrow_run script output
  have heq := affineTransition_eq_run script output
  have hand := affineTransition_and_run script output
  have hfinish := affineTransition_finish_run script output
  let throughNarrowRaw := EvalsToInTime.trans
    (step affineTransitionRevProgram)
    (2 + affineStmtScriptFinishSteps script.dispatch)
    (1 + affineOrThenNotUntilFinishSteps
      script.narrowFrames script.narrowSource) _ _ _ hstmt hnarrow
  have throughNarrow : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg (encodeAffineTransitionScript script) output)
      (some (affineTransitionLiftNarrowCfg
        (affineOrFinFinishInputCfg (affineTransitionNarrowTail script)
          (affineTransitionNarrowOutput script output))))
      (2 + affineStmtScriptFinishSteps script.dispatch +
        (1 + affineOrThenNotUntilFinishSteps
          script.narrowFrames script.narrowSource)) := by
    convert throughNarrowRaw using 1
    omega
  let throughEqRaw := EvalsToInTime.trans (step affineTransitionRevProgram)
    (2 + affineStmtScriptFinishSteps script.dispatch +
      (1 + affineOrThenNotUntilFinishSteps
        script.narrowFrames script.narrowSource))
    (2 + (1 + affineEqFinBodySteps script.eqFrames)) _ _ _
    throughNarrow heq
  have throughEq : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg (encodeAffineTransitionScript script) output)
      (some (affineTransitionLiftEqCfg
        (affineEqFinCheckCfg (affineTransitionEqTail script)
          (affineTransitionEqOutput script output))))
      (2 + affineStmtScriptFinishSteps script.dispatch +
        (1 + affineOrThenNotUntilFinishSteps
          script.narrowFrames script.narrowSource) +
        (2 + (1 + affineEqFinBodySteps script.eqFrames))) := by
    convert throughEqRaw using 1
    omega
  let throughAndRaw := EvalsToInTime.trans (step affineTransitionRevProgram)
    (2 + affineStmtScriptFinishSteps script.dispatch +
      (1 + affineOrThenNotUntilFinishSteps
        script.narrowFrames script.narrowSource) +
      (2 + (1 + affineEqFinBodySteps script.eqFrames)))
    (2 + affineAndFinUntilFinishSteps [script.finalAnd]) _ _ _
    throughEq hand
  have throughAnd : EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg (encodeAffineTransitionScript script) output)
      (some (affineTransitionLiftAndCfg
        (affineOrFinFinishCfg (affineTransitionFinalOutput script output))))
      (2 + affineStmtScriptFinishSteps script.dispatch +
        (1 + affineOrThenNotUntilFinishSteps
          script.narrowFrames script.narrowSource) +
        (2 + (1 + affineEqFinBodySteps script.eqFrames)) +
        (2 + affineAndFinUntilFinishSteps [script.finalAnd])) := by
    convert throughAndRaw using 1
    omega
  let full := EvalsToInTime.trans (step affineTransitionRevProgram)
    (2 + affineStmtScriptFinishSteps script.dispatch +
      (1 + affineOrThenNotUntilFinishSteps
        script.narrowFrames script.narrowSource) +
      (2 + (1 + affineEqFinBodySteps script.eqFrames)) +
      (2 + affineAndFinUntilFinishSteps [script.finalAnd])) 2 _ _ _
    throughAnd hfinish
  convert full using 1
  · simp [affineTransitionFinalOutput, affineTransitionEqOutput,
      affineTransitionNarrowOutput, affineTransitionStmtOutput,
      affineTransitionBoolOutput, affineTransitionGateStream,
      List.reverse_append, List.append_assoc]
  · simp [affineTransitionRunSteps]
    omega

/-- Canonical execution theorem for the concrete Cook--Levin local-transition
script extracted from the semantic builder. -/
def compileTransitionScript_run
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionRevProgram)
      (affineTransitionLoopCfg
        (encodeAffineTransitionScript
          (compileTransitionScript tm H base current next hcurrent hnext))
        output)
      (some (haltCfg affineTransitionRevProgram
        (((transitionCircuitGateTrace tm H base current next hcurrent hnext).gates.flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineTransitionRunSteps
        (compileTransitionScript tm H base current next hcurrent hnext)) := by
  simpa [compileTransitionScript_gateStream_eq_trace] using
    affineTransition_run
      (compileTransitionScript tm H base current next hcurrent hnext) output

/-- The exact fixed-controller runtime is linear in the complete concrete
operand script, hence polynomial in its input encoding length. -/
theorem affineTransition_steps_le (script : AffineTransitionScript) :
    affineTransitionRunSteps script ≤
      500 * (encodeAffineTransitionScript script).length + 20 := by
  have hstmt := affineStmtScriptFinish_steps_le script.dispatch
  have hnarrow' := affineOrThenNotRev_steps_le
    script.narrowFrames script.narrowSource
  have hnarrow :
      affineOrThenNotUntilFinishSteps script.narrowFrames
          script.narrowSource ≤
        100 * (encodeAffineOrThenNotInput script.narrowFrames
          script.narrowSource).length + 2 := by
    simp [affineOrThenNotRevSteps] at hnarrow'
    omega
  have heq : affineEqFinBodySteps script.eqFrames ≤
      113 * (encodeAffineEqFinFrames script.eqFrames).length := by
    induction script.eqFrames with
    | nil => rfl
    | cons frame rest ih =>
        have hframe := affineEqFinPair_steps_le frame
        simp only [affineEqFinBodySteps, encodeAffineEqFinFrames,
          List.flatMap_cons, List.length_append] at *
        omega
  have hand' := affineAndFinRev_steps_le [script.finalAnd]
  have hand : affineAndFinUntilFinishSteps [script.finalAnd] ≤
      100 * (encodeAffineAndFinFrames [script.finalAnd]).length + 2 := by
    simp [affineAndFinRevSteps] at hand'
    omega
  have hlen : (encodeAffineTransitionScript script).length =
      (encodeAffineStmtControllerInput script.dispatch).length + 3 +
        (encodeAffineOrThenNotInput script.narrowFrames
          script.narrowSource).length + 1 +
        (encodeAffineEqFinFrames script.eqFrames).length + 1 +
        (encodeAffineAndFinFrames [script.finalAnd]).length := by
    simp [encodeAffineTransitionScript, encodeAffineStmtTransitionInput,
      encodeAffineTransitionTail, affineStmtTransitionBoundaryCode,
      encodeAffineStmtControllerInput, List.length_append]
    omega
  simp only [affineTransitionRunSteps]
  omega

end CLRS.Chapter34.Turing.PolyBuilder
