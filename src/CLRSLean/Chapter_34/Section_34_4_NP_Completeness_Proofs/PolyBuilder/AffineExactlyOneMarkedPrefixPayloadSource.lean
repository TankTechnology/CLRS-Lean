import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource
import Mathlib.Tactic

/-!
# Expanding a marked exactly-one prefix while preserving its row payload

Each input row has the form

`compactExactlyOne ++ frameEnd ++ payload ++ frameEnd`.

The fixed controller expands only the first segment, emits the outer-family
leading tick, and copies the second segment byte-for-byte.  Its output is

`tick ++ canonicalExactlyOne ++ frameEnd ++ payload ++ frameEnd`.

This is the row-local bridge needed when one physical Cook--Levin row copy
feeds canonical one-hot expansion and the other copy retains later operands.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- A compact one-hot row paired with an opaque delimiter-free payload. -/
structure AffineExactlyOneMarkedPrefixPayloadFamily where
  rows : List (List AffineExactlyOneFrame × List UnaryFrameSym)
  payload_frameEnd_free : ∀ row ∈ rows, ∀ symbol ∈ row.2,
    symbol ≠ UnaryFrameSym.frameEnd

/-- Physical source encoding for the prefix-expanding controller. -/
def encodeAffineExactlyOneMarkedPrefixPayloadInput
    (family : AffineExactlyOneMarkedPrefixPayloadFamily) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    encodeAffineExactlyOneCompactFamily row.1 ++ [.frameEnd] ++
      row.2 ++ [.frameEnd]

/-- Exact output encoding: expanded prefix and untouched payload. -/
def encodeAffineExactlyOneMarkedPrefixPayloadOutput
    (family : AffineExactlyOneMarkedPrefixPayloadFamily) :
    List UnaryFrameSym :=
  family.rows.flatMap fun row =>
    .tick :: (encodeAffineExactlyOneFamily row.1 ++ .frameEnd ::
      (row.2 ++ [.frameEnd]))

/-- Outer phases around the already verified compact-frame expander. -/
inductive AffineExactlyOneMarkedPrefixPayloadLabel
  | check
  | save (symbol : UnaryFrameSym)
  | restore
  | clearBuffer
  | markRow
  | body (label : AffineExactlyOneFrameExpandLabel)
  | clearPrefixEnd
  | copyPayload
  | emitPayload (symbol : UnaryFrameSym)
  | emitPayloadEnd
  | clearPayloadEnd
  | finish
  | invalid
deriving DecidableEq, Fintype

private def affineExactlyOneMarkedPrefixPayloadRelabelOp :
    Op UnaryFrameSym UnaryFrameSym AffineExactlyOneFrameExpandLabel →
      Op UnaryFrameSym UnaryFrameSym
        AffineExactlyOneMarkedPrefixPayloadLabel
  | .pushOutput symbol next => .pushOutput symbol (.body next)
  | .pushWork₁ symbol next => .pushWork₁ symbol (.body next)
  | .pushWork₂ symbol next => .pushWork₂ symbol (.body next)
  | .moveInputWork₁ nextEmpty nextMoved =>
      .moveInputWork₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₁Input nextEmpty nextMoved =>
      .moveWork₁Input (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveInputWork₂ nextEmpty nextMoved =>
      .moveInputWork₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₂Input nextEmpty nextMoved =>
      .moveWork₂Input (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₁Work₂ nextEmpty nextMoved =>
      .moveWork₁Work₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .moveWork₂Work₁ nextEmpty nextMoved =>
      .moveWork₂Work₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .copyInputWorks nextEmpty nextMoved =>
      .copyInputWorks (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popInput nextEmpty nextMoved =>
      .popInput (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popWork₁ nextEmpty nextMoved =>
      .popWork₁ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .popWork₂ nextEmpty nextMoved =>
      .popWork₂ (.body nextEmpty) (fun symbol => .body (nextMoved symbol))
  | .inc₁ next => .inc₁ (.body next)
  | .inc₂ next => .inc₂ (.body next)
  | .inc₃ next => .inc₃ (.body next)
  | .dec₁ nextZero nextSucc => .dec₁ (.body nextZero) (.body nextSucc)
  | .dec₂ nextZero nextSucc => .dec₂ (.body nextZero) (.body nextSucc)
  | .dec₃ nextZero nextSucc => .dec₃ (.body nextZero) (.body nextSucc)
  | .jump next => .jump (.body next)
  | .halt => .halt

/-- Fixed payload-preserving prefix expander. -/
def affineExactlyOneMarkedPrefixPayloadRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneMarkedPrefixPayloadLabel
  main := .check
  op
    | .check => .popInput .finish .save
    | .save symbol => .pushWork₁ symbol .restore
    | .restore => .moveWork₁Input .invalid (fun _ => .clearBuffer)
    | .clearBuffer => .popWork₁ .markRow (fun _ => .invalid)
    | .markRow =>
        .pushOutput .tick (.body affineExactlyOneFrameExpandRevProgram.main)
    | .body (.loader .invalid) =>
        .pushOutput .frameEnd .clearPrefixEnd
    | .body label => affineExactlyOneMarkedPrefixPayloadRelabelOp
        (affineExactlyOneFrameExpandRevProgram.op label)
    | .clearPrefixEnd => .popWork₁ .copyPayload (fun _ => .copyPayload)
    | .copyPayload => .popInput .invalid fun
        | .frameEnd => .emitPayloadEnd
        | symbol => .emitPayload symbol
    | .emitPayload symbol => .pushOutput symbol .copyPayload
    | .emitPayloadEnd => .pushOutput .frameEnd .clearPayloadEnd
    | .clearPayloadEnd => .popWork₁ .check (fun _ => .check)
    | .finish => .halt
    | .invalid => .halt

private def affineExactlyOneMarkedPrefixPayloadCfg
    (label : AffineExactlyOneMarkedPrefixPayloadLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (first second third : List Unit) :
    BuilderCfg affineExactlyOneMarkedPrefixPayloadRevProgram where
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

/-- Clean family loop header. -/
def affineExactlyOneMarkedPrefixPayloadLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneMarkedPrefixPayloadRevProgram :=
  affineExactlyOneMarkedPrefixPayloadCfg .check none none false input output
    [] [] [] [] []

private def affineExactlyOneMarkedPrefixPayloadCopyCfg
    (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneMarkedPrefixPayloadRevProgram :=
  affineExactlyOneMarkedPrefixPayloadCfg .copyPayload buffer none false
    input output [] [] [] [] []

private def liftAffineExactlyOneMarkedPrefixPayloadBodyCfg
    (c : BuilderCfg affineExactlyOneFrameExpandRevProgram) :
    BuilderCfg affineExactlyOneMarkedPrefixPayloadRevProgram where
  label := c.label.map .body
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

private theorem affineExactlyOneMarkedPrefixPayloadRelabel_stepOp
    (op : Op UnaryFrameSym UnaryFrameSym AffineExactlyOneFrameExpandLabel)
    (c : BuilderCfg affineExactlyOneFrameExpandRevProgram) :
    stepOp (affineExactlyOneMarkedPrefixPayloadRelabelOp op)
        (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg c) =
      liftAffineExactlyOneMarkedPrefixPayloadBodyCfg (stepOp op c) := by
  rcases c with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  cases op <;>
    simp only [affineExactlyOneMarkedPrefixPayloadRelabelOp,
      liftAffineExactlyOneMarkedPrefixPayloadBodyCfg, stepOp] <;>
    first
    | rfl
    | split <;> rfl

private theorem affineExactlyOneMarkedPrefixPayload_op_body
    (label : AffineExactlyOneFrameExpandLabel)
    (hexit : label ≠ .loader .invalid) :
    affineExactlyOneMarkedPrefixPayloadRevProgram.op (.body label) =
      affineExactlyOneMarkedPrefixPayloadRelabelOp
        (affineExactlyOneFrameExpandRevProgram.op label) := by
  cases label <;>
    simp_all [affineExactlyOneMarkedPrefixPayloadRevProgram]

private theorem liftAffineExactlyOneMarkedPrefixPayloadBody_step
    (c : BuilderCfg affineExactlyOneFrameExpandRevProgram)
    (hexit : c.label ≠ some (.loader .invalid)) :
    step affineExactlyOneMarkedPrefixPayloadRevProgram
        (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg c) =
      Option.map liftAffineExactlyOneMarkedPrefixPayloadBodyCfg
        (step affineExactlyOneFrameExpandRevProgram c) := by
  unfold step
  rw [show (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg c).label =
      c.label.map .body by rfl]
  cases hlabel : c.label with
  | none => rfl
  | some label =>
      have hlabelExit : label ≠ .loader .invalid := by
        intro h
        apply hexit
        simpa [hlabel] using congrArg some h
      simp only [Option.map_some]
      rw [affineExactlyOneMarkedPrefixPayload_op_body label hlabelExit]
      exact congrArg some
        (affineExactlyOneMarkedPrefixPayloadRelabel_stepOp
          (affineExactlyOneFrameExpandRevProgram.op label) c)

private theorem affineExactlyOneFrameExpand_invalid_no_return
    (a b : BuilderCfg affineExactlyOneFrameExpandRevProgram)
    (ha : a.label = some (.loader .invalid))
    (hb : b.label = some (.loader .invalid)) (n : Nat) :
    (flip Option.bind (step affineExactlyOneFrameExpandRevProgram))^[n]
        (step affineExactlyOneFrameExpandRevProgram a) ≠ some b := by
  rcases a with
    ⟨label, buffer₁, buffer₂, test, input, output, work₁, work₂,
      counter₁, counter₂, counter₃⟩
  simp only at ha
  subst label
  let halted : BuilderCfg affineExactlyOneFrameExpandRevProgram :=
    { label := none
      buffer₁ := none
      buffer₂ := none
      test := false
      input := input
      output := output
      work₁ := work₁
      work₂ := work₂
      counter₁ := counter₁
      counter₂ := counter₂
      counter₃ := counter₃ }
  have hstep : step affineExactlyOneFrameExpandRevProgram
      { label := some (.loader .invalid), buffer₁ := buffer₁,
        buffer₂ := buffer₂, test := test, input := input,
        output := output, work₁ := work₁, work₂ := work₂,
        counter₁ := counter₁, counter₂ := counter₂,
        counter₃ := counter₃ } = some halted := by
    simp [step, affineExactlyOneFrameExpandRevProgram,
      unaryTripleLoaderProgramFor, relabelLoaderOp, stepOp, halted]
  cases n with
  | zero =>
      rw [hstep]
      intro h
      have hlabel := congrArg (fun cfg => cfg.label) (Option.some.inj h)
      simp [halted, hb] at hlabel
  | succ n =>
      rw [hstep, Function.iterate_succ_apply]
      change (flip Option.bind
        (step affineExactlyOneFrameExpandRevProgram))^[n]
          (step affineExactlyOneFrameExpandRevProgram halted) ≠ some b
      have hnone : step affineExactlyOneFrameExpandRevProgram halted = none :=
        rfl
      rw [hnone, iterate_bind_none]
      simp

private theorem
    affineExactlyOneMarkedPrefixPayload_lift_iterations_to_invalid
    {a b : BuilderCfg affineExactlyOneFrameExpandRevProgram}
    (hb : b.label = some (.loader .invalid)) : ∀ n : Nat,
    (flip Option.bind (step affineExactlyOneFrameExpandRevProgram))^[n]
        (some a) = some b →
      (flip Option.bind
        (step affineExactlyOneMarkedPrefixPayloadRevProgram))^[n]
        (some (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg a)) =
          some (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg b) := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      injection h with hab
      subst a
      rfl
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h ⊢
      change (flip Option.bind
        (step affineExactlyOneFrameExpandRevProgram))^[n]
          (step affineExactlyOneFrameExpandRevProgram a) = some b at h
      change (flip Option.bind
        (step affineExactlyOneMarkedPrefixPayloadRevProgram))^[n]
          (step affineExactlyOneMarkedPrefixPayloadRevProgram
            (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg a)) =
              some (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg b)
      have haexit : a.label ≠ some (.loader .invalid) := by
        intro ha
        exact affineExactlyOneFrameExpand_invalid_no_return
          a b ha hb n h
      cases hsource : step affineExactlyOneFrameExpandRevProgram a with
      | none =>
          rw [hsource, iterate_bind_none] at h
          contradiction
      | some c =>
          have hsim :=
            liftAffineExactlyOneMarkedPrefixPayloadBody_step a haexit
          rw [hsource] at hsim
          simp only [Option.map_some] at hsim
          rw [hsim]
          rw [hsource] at h
          exact ih h

private def affineExactlyOneMarkedPrefixPayload_dispatch_run
    (input output : List UnaryFrameSym) (hinput : input ≠ []) :
    EvalsToInTime (step affineExactlyOneMarkedPrefixPayloadRevProgram)
      (affineExactlyOneMarkedPrefixPayloadLoopCfg input output)
      (some (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg
        (affineExactlyOneFrameExpandLoopCfg input (.tick :: output)))) 5 := by
  cases input with
  | nil => contradiction
  | cons symbol rest => exact ⟨⟨5, rfl⟩, le_rfl⟩

private def affineExactlyOneMarkedPrefixPayload_body_run
    (frames : List AffineExactlyOneFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedPrefixPayloadRevProgram)
      (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg
        (affineExactlyOneFrameExpandLoopCfg
          (encodeAffineExactlyOneCompactFamily frames ++ .frameEnd :: tail)
          output))
      (some (liftAffineExactlyOneMarkedPrefixPayloadBodyCfg
        (affineExactlyOneFrameExpandInvalidCfg tail
          ((encodeAffineExactlyOneFamily frames).reverse ++ output))))
      (affineExactlyOneFrameExpandToInvalidSteps frames) := by
  have sourceRun := affineExactlyOneFrameExpand_runToInvalid
    frames tail output
  refine ⟨⟨sourceRun.steps, ?_⟩, sourceRun.steps_le_m⟩
  exact affineExactlyOneMarkedPrefixPayload_lift_iterations_to_invalid rfl
    sourceRun.steps sourceRun.evals_in_steps

private def affineExactlyOneMarkedPrefixPayload_copy_run
    (payload tail output : List UnaryFrameSym)
    (buffer : Option UnaryFrameSym)
    (hfree : ∀ symbol ∈ payload, symbol ≠ UnaryFrameSym.frameEnd) :
    EvalsToInTime (step affineExactlyOneMarkedPrefixPayloadRevProgram)
      (affineExactlyOneMarkedPrefixPayloadCopyCfg buffer
        (payload ++ .frameEnd :: tail) output)
      (some (affineExactlyOneMarkedPrefixPayloadLoopCfg tail
        (.frameEnd :: payload.reverse ++ output)))
      (2 * payload.length + 3) := by
  induction payload generalizing buffer output with
  | nil => exact ⟨⟨3, rfl⟩, le_rfl⟩
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      have hfirst : EvalsToInTime
          (step affineExactlyOneMarkedPrefixPayloadRevProgram)
          (affineExactlyOneMarkedPrefixPayloadCopyCfg buffer
            ((symbol :: rest) ++ .frameEnd :: tail) output)
          (some (affineExactlyOneMarkedPrefixPayloadCopyCfg (some symbol)
            (rest ++ .frameEnd :: tail) (symbol :: output))) 2 := by
        cases symbol <;> simp_all
        all_goals exact ⟨⟨2, rfl⟩, le_rfl⟩
      have htail := ih (symbol :: output) (some symbol) hrest
      let full := EvalsToInTime.trans
        (step affineExactlyOneMarkedPrefixPayloadRevProgram)
        2 (2 * rest.length + 3) _
        (affineExactlyOneMarkedPrefixPayloadCopyCfg (some symbol)
          (rest ++ .frameEnd :: tail) (symbol :: output)) _ hfirst htail
      convert full using 1 <;> simp [List.append_assoc] <;> omega

/-- Exact controller cost, including the final empty dispatch and halt. -/
def affineExactlyOneMarkedPrefixPayloadSteps :
    List (List AffineExactlyOneFrame × List UnaryFrameSym) → Nat
  | [] => 2
  | row :: rest =>
      5 + affineExactlyOneFrameExpandToInvalidSteps row.1 + 2 +
        (2 * row.2.length + 3) +
        affineExactlyOneMarkedPrefixPayloadSteps rest

/-- Exact clean-halt execution on every well-formed prefix/payload family. -/
def affineExactlyOneMarkedPrefixPayload_runFrom
    (family : AffineExactlyOneMarkedPrefixPayloadFamily)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneMarkedPrefixPayloadRevProgram)
      (affineExactlyOneMarkedPrefixPayloadLoopCfg
        (encodeAffineExactlyOneMarkedPrefixPayloadInput family) output)
      (some (haltCfg affineExactlyOneMarkedPrefixPayloadRevProgram
        ((encodeAffineExactlyOneMarkedPrefixPayloadOutput family).reverse ++
          output)))
      (affineExactlyOneMarkedPrefixPayloadSteps family.rows) := by
  let familyRun : ∀
      (rows : List (List AffineExactlyOneFrame × List UnaryFrameSym)),
      (∀ row ∈ rows, ∀ symbol ∈ row.2,
        symbol ≠ UnaryFrameSym.frameEnd) →
      ∀ output : List UnaryFrameSym,
      EvalsToInTime (step affineExactlyOneMarkedPrefixPayloadRevProgram)
        (affineExactlyOneMarkedPrefixPayloadLoopCfg
          (rows.flatMap fun row =>
            encodeAffineExactlyOneCompactFamily row.1 ++ [.frameEnd] ++
              row.2 ++ [.frameEnd]) output)
        (some (haltCfg affineExactlyOneMarkedPrefixPayloadRevProgram
          ((rows.flatMap fun row =>
            .tick :: (encodeAffineExactlyOneFamily row.1 ++ .frameEnd ::
              (row.2 ++ [.frameEnd]))).reverse ++ output)))
        (affineExactlyOneMarkedPrefixPayloadSteps rows) := by
    intro rows hfree output
    induction rows generalizing output with
    | nil => exact ⟨⟨2, rfl⟩, le_rfl⟩
    | cons row rest ih =>
        let restInput := rest.flatMap fun item =>
          encodeAffineExactlyOneCompactFamily item.1 ++ [.frameEnd] ++
            item.2 ++ [.frameEnd]
        let expandedOutput :=
          (encodeAffineExactlyOneFamily row.1).reverse ++ .tick :: output
        let prefixMarkedOutput := .frameEnd :: expandedOutput
        let payloadOutput :=
          .frameEnd :: row.2.reverse ++ prefixMarkedOutput
        let bodyStart := liftAffineExactlyOneMarkedPrefixPayloadBodyCfg
          (affineExactlyOneFrameExpandLoopCfg
            (encodeAffineExactlyOneCompactFamily row.1 ++ .frameEnd ::
              (row.2 ++ .frameEnd :: restInput)) (.tick :: output))
        let bodyDone := liftAffineExactlyOneMarkedPrefixPayloadBodyCfg
          (affineExactlyOneFrameExpandInvalidCfg
            (row.2 ++ .frameEnd :: restInput) expandedOutput)
        let copyStart := affineExactlyOneMarkedPrefixPayloadCopyCfg none
          (row.2 ++ .frameEnd :: restInput) prefixMarkedOutput
        have hinvocation :
            encodeAffineExactlyOneCompactFamily row.1 ++ .frameEnd ::
                (row.2 ++ .frameEnd :: restInput) ≠ [] := by simp
        have hrowFree : ∀ symbol ∈ row.2,
            symbol ≠ UnaryFrameSym.frameEnd := by
          intro symbol hsymbol
          exact hfree row (by simp) symbol hsymbol
        have hrestFree : ∀ item ∈ rest, ∀ symbol ∈ item.2,
            symbol ≠ UnaryFrameSym.frameEnd := by
          intro item hitem symbol hsymbol
          exact hfree item (by simp [hitem]) symbol hsymbol
        have hdispatch : EvalsToInTime
            (step affineExactlyOneMarkedPrefixPayloadRevProgram)
            (affineExactlyOneMarkedPrefixPayloadLoopCfg
              (encodeAffineExactlyOneCompactFamily row.1 ++ .frameEnd ::
                (row.2 ++ .frameEnd :: restInput)) output)
            (some bodyStart) 5 := by
          simpa [bodyStart] using
            affineExactlyOneMarkedPrefixPayload_dispatch_run _ output
              hinvocation
        have hbody : EvalsToInTime
            (step affineExactlyOneMarkedPrefixPayloadRevProgram)
            bodyStart (some bodyDone)
            (affineExactlyOneFrameExpandToInvalidSteps row.1) := by
          simpa [bodyStart, bodyDone, expandedOutput] using
            affineExactlyOneMarkedPrefixPayload_body_run row.1
              (row.2 ++ .frameEnd :: restInput) (.tick :: output)
        have hbridge : EvalsToInTime
            (step affineExactlyOneMarkedPrefixPayloadRevProgram)
            bodyDone (some copyStart) 2 := by
          refine ⟨⟨2, ?_⟩, le_rfl⟩
          rfl
        have hcopy : EvalsToInTime
            (step affineExactlyOneMarkedPrefixPayloadRevProgram)
            copyStart
            (some (affineExactlyOneMarkedPrefixPayloadLoopCfg
              restInput payloadOutput))
            (2 * row.2.length + 3) := by
          simpa [copyStart, prefixMarkedOutput, payloadOutput,
            List.append_assoc] using
            affineExactlyOneMarkedPrefixPayload_copy_run row.2 restInput
              prefixMarkedOutput none hrowFree
        have hrest := ih hrestFree payloadOutput
        let h₁ := EvalsToInTime.trans
          (step affineExactlyOneMarkedPrefixPayloadRevProgram)
          5 _ _ bodyStart _ hdispatch hbody
        let h₂ := EvalsToInTime.trans
          (step affineExactlyOneMarkedPrefixPayloadRevProgram)
          _ 2 _ bodyDone _ h₁ hbridge
        let h₃ := EvalsToInTime.trans
          (step affineExactlyOneMarkedPrefixPayloadRevProgram)
          _ _ _ copyStart _ h₂ hcopy
        let full := EvalsToInTime.trans
          (step affineExactlyOneMarkedPrefixPayloadRevProgram)
          _ _ _
          (affineExactlyOneMarkedPrefixPayloadLoopCfg
            restInput payloadOutput) _ h₃ hrest
        convert full using 1
        · simp [restInput, List.append_assoc]
        · simp [payloadOutput, prefixMarkedOutput, expandedOutput,
            List.reverse_append, List.append_assoc]
        · simp [affineExactlyOneMarkedPrefixPayloadSteps]
          omega
  simpa [encodeAffineExactlyOneMarkedPrefixPayloadInput,
    encodeAffineExactlyOneMarkedPrefixPayloadOutput] using
    familyRun family.rows family.payload_frameEnd_free output

/-- The complete run is linear in the marked input up to the inherited
compact-frame expansion constant. -/
theorem affineExactlyOneMarkedPrefixPayloadSteps_le
    (family : AffineExactlyOneMarkedPrefixPayloadFamily) :
    affineExactlyOneMarkedPrefixPayloadSteps family.rows ≤
      11 * (encodeAffineExactlyOneMarkedPrefixPayloadInput family).length +
        2 := by
  let familyBound : ∀
      (rows : List (List AffineExactlyOneFrame × List UnaryFrameSym)),
      affineExactlyOneMarkedPrefixPayloadSteps rows ≤
        11 * (rows.flatMap fun row =>
          encodeAffineExactlyOneCompactFamily row.1 ++ [.frameEnd] ++
            row.2 ++ [.frameEnd]).length + 2 := by
    intro rows
    induction rows with
    | nil => simp [affineExactlyOneMarkedPrefixPayloadSteps]
    | cons row rest ih =>
        have hprefix := affineExactlyOneFrameExpandToInvalidSteps_le row.1
        simp only [affineExactlyOneMarkedPrefixPayloadSteps,
          List.flatMap_cons, List.length_append, List.length_cons,
          List.length_nil]
        omega
  simpa [encodeAffineExactlyOneMarkedPrefixPayloadInput] using
    familyBound family.rows

/-- Prepend-order compiled prefix expander. -/
noncomputable def
    affineExactlyOneMarkedPrefixPayloadRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneMarkedPrefixPayloadInput id
      (fun family : AffineExactlyOneMarkedPrefixPayloadFamily =>
        (encodeAffineExactlyOneMarkedPrefixPayloadOutput family).reverse) where
  tm := compile affineExactlyOneMarkedPrefixPayloadRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 11 * Polynomial.X + 2
  outputsFun := fun family => by
    have builderRun :=
      affineExactlyOneMarkedPrefixPayload_runFrom family []
    have compiledRun := compile_evalsToInTime
      affineExactlyOneMarkedPrefixPayloadRevProgram builderRun
    have hinitial : affineExactlyOneMarkedPrefixPayloadLoopCfg
        (encodeAffineExactlyOneMarkedPrefixPayloadInput family) [] =
          initialCfg affineExactlyOneMarkedPrefixPayloadRevProgram
            (encodeAffineExactlyOneMarkedPrefixPayloadInput family) := rfl
    rw [hinitial] at compiledRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneMarkedPrefixPayloadRevProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneMarkedPrefixPayloadRevProgram)
          (encodeAffineExactlyOneMarkedPrefixPayloadInput family))
        (some (_root_.Turing.haltList
          (compile affineExactlyOneMarkedPrefixPayloadRevProgram)
          (encodeAffineExactlyOneMarkedPrefixPayloadOutput family).reverse))
        (affineExactlyOneMarkedPrefixPayloadSteps family.rows) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : affineExactlyOneMarkedPrefixPayloadSteps family.rows ≤
        (11 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneMarkedPrefixPayloadInput family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat] using
        affineExactlyOneMarkedPrefixPayloadSteps_le family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneMarkedPrefixPayloadRevProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneMarkedPrefixPayloadRevProgram)
          (encodeAffineExactlyOneMarkedPrefixPayloadInput family))
        (some (_root_.Turing.haltList
          (compile affineExactlyOneMarkedPrefixPayloadRevProgram)
          (encodeAffineExactlyOneMarkedPrefixPayloadOutput family).reverse))
        ((11 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneMarkedPrefixPayloadInput family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward payload-preserving marked prefix expansion. -/
noncomputable def
    affineExactlyOneMarkedPrefixPayload_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeAffineExactlyOneMarkedPrefixPayloadInput id
      encodeAffineExactlyOneMarkedPrefixPayloadOutput := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      affineExactlyOneMarkedPrefixPayloadRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
