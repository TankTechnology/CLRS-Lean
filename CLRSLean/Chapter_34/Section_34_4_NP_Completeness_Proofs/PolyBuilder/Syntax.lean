import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
# A typed bounded-builder language

This file defines the small instruction language used by the Chapter 34
polynomial-time builders and gives it semantics independently of the TM2
compiler. The three symbol stacks share an alphabet by construction, while the
output and unary-counter stacks cannot participate in ill-typed moves.
-/

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The fixed stack layout of a bounded builder. -/
inductive Stack
  | input | output | work₁ | work₂ | counter₁ | counter₂ | counter₃
deriving DecidableEq, Fintype, Inhabited

/-- The alphabet carried by each typed stack. -/
abbrev Alphabet (Γ Δ : Type) : Stack → Type
  | .input | .work₁ | .work₂ => Γ
  | .output => Δ
  | .counter₁ | .counter₂ | .counter₃ => Unit

/-- Finite internal state used by the compiled machine.

The Boolean is independent of the symbol buffers so counter tests remain
representable even when the input alphabet is empty.
-/
structure ControlState (Γ : Type) where
  buffer₁ : Option Γ
  buffer₂ : Option Γ
  test : Bool

private def controlStateEquiv {Γ : Type} :
    (Option Γ × Option Γ × Bool) ≃ ControlState Γ where
  toFun state := ⟨state.1, state.2.1, state.2.2⟩
  invFun state := (state.buffer₁, state.buffer₂, state.test)
  left_inv state := by cases state; rfl
  right_inv state := by cases state; rfl

instance {Γ : Type} [Fintype Γ] : Fintype (ControlState Γ) :=
  Fintype.ofEquiv (Option Γ × Option Γ × Bool) controlStateEquiv

/-- One atomic bounded-builder instruction.

{lit}`pushOutput symbol next` prepends {lit}`symbol` to the observable output stack.
Consequently, an output-emitting macro for a multi-symbol chunk must execute
its {lit}`pushOutput` instructions in reverse chunk order.
-/
inductive Op (Γ Δ Λ : Type)
  | pushOutput (symbol : Δ) (next : Λ)
  | moveInputWork₁ (nextEmpty : Λ) (nextMoved : Γ → Λ)
  | moveWork₁Input (nextEmpty : Λ) (nextMoved : Γ → Λ)
  | moveInputWork₂ (nextEmpty : Λ) (nextMoved : Γ → Λ)
  | moveWork₂Input (nextEmpty : Λ) (nextMoved : Γ → Λ)
  | moveWork₁Work₂ (nextEmpty : Λ) (nextMoved : Γ → Λ)
  | moveWork₂Work₁ (nextEmpty : Λ) (nextMoved : Γ → Λ)
  | copyInputWorks (nextEmpty : Λ) (nextCopied : Γ → Λ)
  | popInput (nextEmpty : Λ) (nextSome : Γ → Λ)
  | popWork₁ (nextEmpty : Λ) (nextSome : Γ → Λ)
  | popWork₂ (nextEmpty : Λ) (nextSome : Γ → Λ)
  | inc₁ (next : Λ) | inc₂ (next : Λ) | inc₃ (next : Λ)
  | dec₁ (nextZero nextSucc : Λ)
  | dec₂ (nextZero nextSucc : Λ)
  | dec₃ (nextZero nextSucc : Λ)
  | jump (next : Λ)
  | halt

/-- A finite-control builder program. -/
structure Program (Γ Δ : Type) where
  Label : Type
  [labelDecidableEq : DecidableEq Label]
  [labelFintype : Fintype Label]
  main : Label
  op : Label → Op Γ Δ Label

/-- Independent configurations for the builder language. -/
structure BuilderCfg {Γ Δ : Type} (P : Program Γ Δ) where
  label : Option P.Label
  buffer₁ : Option Γ
  buffer₂ : Option Γ
  test : Bool
  input : List Γ
  output : List Δ
  work₁ : List Γ
  work₂ : List Γ
  counter₁ : List Unit
  counter₂ : List Unit
  counter₃ : List Unit

/-- Structural semantics of one instruction. -/
def stepOp {Γ Δ : Type} {P : Program Γ Δ} :
    Op Γ Δ P.Label → BuilderCfg P → BuilderCfg P
  | .pushOutput symbol next, c =>
      { c with label := some next, output := symbol :: c.output }
  | .moveInputWork₁ nextEmpty nextMoved, c =>
      match c.input with
      | [] => { c with label := some nextEmpty, buffer₁ := none }
      | symbol :: rest =>
          { c with
            label := some (nextMoved symbol)
            buffer₁ := some symbol
            input := rest
            work₁ := symbol :: c.work₁ }
  | .moveWork₁Input nextEmpty nextMoved, c =>
      match c.work₁ with
      | [] => { c with label := some nextEmpty, buffer₁ := none }
      | symbol :: rest =>
          { c with
            label := some (nextMoved symbol)
            buffer₁ := some symbol
            input := symbol :: c.input
            work₁ := rest }
  | .moveInputWork₂ nextEmpty nextMoved, c =>
      match c.input with
      | [] => { c with label := some nextEmpty, buffer₂ := none }
      | symbol :: rest =>
          { c with
            label := some (nextMoved symbol)
            buffer₂ := some symbol
            input := rest
            work₂ := symbol :: c.work₂ }
  | .moveWork₂Input nextEmpty nextMoved, c =>
      match c.work₂ with
      | [] => { c with label := some nextEmpty, buffer₂ := none }
      | symbol :: rest =>
          { c with
            label := some (nextMoved symbol)
            buffer₂ := some symbol
            input := symbol :: c.input
            work₂ := rest }
  | .moveWork₁Work₂ nextEmpty nextMoved, c =>
      match c.work₁ with
      | [] => { c with label := some nextEmpty, buffer₁ := none }
      | symbol :: rest =>
          { c with
            label := some (nextMoved symbol)
            buffer₁ := some symbol
            work₁ := rest
            work₂ := symbol :: c.work₂ }
  | .moveWork₂Work₁ nextEmpty nextMoved, c =>
      match c.work₂ with
      | [] => { c with label := some nextEmpty, buffer₂ := none }
      | symbol :: rest =>
          { c with
            label := some (nextMoved symbol)
            buffer₂ := some symbol
            work₁ := symbol :: c.work₁
            work₂ := rest }
  | .copyInputWorks nextEmpty nextCopied, c =>
      match c.input with
      | [] => { c with label := some nextEmpty, buffer₁ := none }
      | symbol :: rest =>
          { c with
            label := some (nextCopied symbol)
            buffer₁ := some symbol
            input := rest
            work₁ := symbol :: c.work₁
            work₂ := symbol :: c.work₂ }
  | .popInput nextEmpty nextSome, c =>
      match c.input with
      | [] => { c with label := some nextEmpty, buffer₁ := none }
      | symbol :: rest =>
          { c with
            label := some (nextSome symbol)
            buffer₁ := some symbol
            input := rest }
  | .popWork₁ nextEmpty nextSome, c =>
      match c.work₁ with
      | [] => { c with label := some nextEmpty, buffer₁ := none }
      | symbol :: rest =>
          { c with
            label := some (nextSome symbol)
            buffer₁ := some symbol
            work₁ := rest }
  | .popWork₂ nextEmpty nextSome, c =>
      match c.work₂ with
      | [] => { c with label := some nextEmpty, buffer₂ := none }
      | symbol :: rest =>
          { c with
            label := some (nextSome symbol)
            buffer₂ := some symbol
            work₂ := rest }
  | .inc₁ next, c =>
      { c with label := some next, counter₁ := () :: c.counter₁ }
  | .inc₂ next, c =>
      { c with label := some next, counter₂ := () :: c.counter₂ }
  | .inc₃ next, c =>
      { c with label := some next, counter₃ := () :: c.counter₃ }
  | .dec₁ nextZero nextSucc, c =>
      match c.counter₁ with
      | [] => { c with label := some nextZero, test := false }
      | _ :: rest =>
          { c with label := some nextSucc, test := true, counter₁ := rest }
  | .dec₂ nextZero nextSucc, c =>
      match c.counter₂ with
      | [] => { c with label := some nextZero, test := false }
      | _ :: rest =>
          { c with label := some nextSucc, test := true, counter₂ := rest }
  | .dec₃ nextZero nextSucc, c =>
      match c.counter₃ with
      | [] => { c with label := some nextZero, test := false }
      | _ :: rest =>
          { c with label := some nextSucc, test := true, counter₃ := rest }
  | .jump next, c => { c with label := some next }
  | .halt, c =>
      { c with label := none, buffer₁ := none, buffer₂ := none, test := false }

/-- Execute one builder step, or stop if the current label is already absent. -/
def step {Γ Δ : Type} (P : Program Γ Δ) (c : BuilderCfg P) :
    Option (BuilderCfg P) :=
  match c.label with
  | none => none
  | some label => some (stepOp (P.op label) c)

end CLRS.Chapter34.Turing.PolyBuilder
