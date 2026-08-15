import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Verified list reversal for bounded builders

Builder output stacks are prepend-only.  This small machine consumes the input
from left to right and prepends each consumed symbol to the output, producing
the exact list reverse in `2n + 2` steps.  It is the canonical finalization
phase for streaming encoders that naturally construct a reversed wire format.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite control for the direct reversal machine. -/
inductive ReverseLabel (Γ : Type)
  | pop
  | push (symbol : Γ)
  | halt
deriving DecidableEq, Fintype

/-- Direct prepend-based reversal program. -/
def reverseProgram (Γ : Type) [Fintype Γ] : Program Γ Γ := by
  classical
  exact
    { Label := ReverseLabel Γ
      main := .pop
      op
        | .pop => .popInput .halt .push
        | .push symbol => .pushOutput symbol .pop
        | .halt => .halt }

/-- Exact step count of the reversal program. -/
def reverseSteps {Γ : Type} (input : List Γ) : Nat :=
  2 * input.length + 2

private def reversePopCfg {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (input output : List Γ) :
    BuilderCfg (reverseProgram Γ) :=
  { initialCfg (reverseProgram Γ) input with
      buffer₁ := buffer
      output := output }

/-- Structural iteration equation for the pop/push phase. -/
private theorem reverse_popPushPhase_eval {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (input output : List Γ) :
    (flip Option.bind (step (reverseProgram Γ)))^[2 * input.length + 1]
      (some (reversePopCfg buffer input output)) =
        some { haltCfg (reverseProgram Γ) (input.reverse ++ output) with
          label := some .halt } := by
  induction input generalizing buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step (reverseProgram Γ)))^[2 * rest.length + 1]
          (some (reversePopCfg (some symbol) rest (symbol :: output))) =
            some { haltCfg (reverseProgram Γ)
              ((symbol :: rest).reverse ++ output) with
                label := some .halt }
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: output)

/-- The input is reversed onto the output and all scratch state is cleared
before the final halt instruction. -/
def reverse_popPushPhase {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (reverseProgram Γ))
      (initialCfg (reverseProgram Γ) input)
      (some { haltCfg (reverseProgram Γ) input.reverse with
        label := some .halt })
      (2 * input.length + 1) := by
  refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
  simpa [reversePopCfg, initialCfg] using
    reverse_popPushPhase_eval (Γ := Γ) none input []

@[simp] theorem reverse_popPushPhase_steps {Γ : Type} [Fintype Γ]
    (input : List Γ) :
    (reverse_popPushPhase input).steps = 2 * input.length + 1 := by
  rfl

/-- The final halt instruction takes one step. -/
def reverse_haltStep {Γ : Type} [Fintype Γ] (output : List Γ) :
    EvalsToInTime (step (reverseProgram Γ))
      { haltCfg (reverseProgram Γ) output with label := some .halt }
      (some (haltCfg (reverseProgram Γ) output)) 1 := by
  refine ⟨⟨1, rfl⟩, le_rfl⟩

@[simp] theorem reverse_haltStep_steps {Γ : Type} [Fintype Γ]
    (output : List Γ) :
    (reverse_haltStep output).steps = 1 := by
  rfl

/-- Canonical exact independent-semantics reversal run. -/
def reverse_run {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (reverseProgram Γ))
      (initialCfg (reverseProgram Γ) input)
      (some (haltCfg (reverseProgram Γ) input.reverse))
      (reverseSteps input) := by
  let full := EvalsToInTime.trans (step (reverseProgram Γ))
    (2 * input.length + 1) 1
    (initialCfg (reverseProgram Γ) input)
    { haltCfg (reverseProgram Γ) input.reverse with label := some .halt }
    (some (haltCfg (reverseProgram Γ) input.reverse))
    (reverse_popPushPhase input) (reverse_haltStep input.reverse)
  have hsteps : full.steps = reverseSteps input := by
    simp [full, reverseSteps]
    omega
  refine ⟨⟨reverseSteps input, ?_⟩, le_rfl⟩
  rw [← hsteps]
  exact full.evals_in_steps

@[simp] theorem reverse_run_steps {Γ : Type} [Fintype Γ]
    (input : List Γ) :
    (reverse_run input).steps = reverseSteps input := by
  rfl

/-- Independent builder output contract for list reversal. -/
theorem reverse_builderOutputs {Γ : Type} [Fintype Γ] :
    BuilderOutputs (reverseProgram Γ) List.reverse reverseSteps := by
  intro input
  exact ⟨reverse_run input⟩

/-- Compiled TM2 output contract for list reversal. -/
theorem reverse_outputs {Γ : Type} [Fintype Γ] :
    Outputs (reverseProgram Γ) List.reverse reverseSteps :=
  Outputs.of_builder_run reverse_builderOutputs

/-- Linear polynomial envelope for reversal. -/
noncomputable def reverse_polyBound {Γ : Type} :
    PolyBound (@reverseSteps Γ) where
  polynomial := 2 * Polynomial.X + 2
  bound input := by
    simp [reverseSteps, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]

/-- Concrete polynomial-time TM2 implementation of list reversal. -/
noncomputable def reverse_computableInPolyTime
    {Γ : Type} [Fintype Γ] :
    _root_.Turing.TM2ComputableInPolyTime id id (@List.reverse Γ) :=
  ComputableInPolyTime (reverseProgram Γ) List.reverse reverseSteps
    reverse_outputs reverse_polyBound

end CLRS.Chapter34.Turing.PolyBuilder
