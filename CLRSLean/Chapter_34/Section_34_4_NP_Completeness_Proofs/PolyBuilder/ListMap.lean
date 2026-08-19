import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Verified fixed symbol maps over lists

A two-state streaming transducer consumes the input from left to right and
prepends the image of every symbol.  Its direct output is the reversed mapped
list; composition with the verified reversal machine supplies the forward
`List.map` operation.  The symbol function is fixed finite control, while the
list length remains runtime data.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite control stores the symbol between the input pop and output push. -/
inductive ListMapLabel (Γ : Type)
  | pop
  | push (symbol : Γ)
  | halt
deriving DecidableEq, Fintype

/-- Prepend-output implementation of a fixed symbol map. -/
def listMapRevProgram {Γ Δ : Type} [Fintype Γ] (f : Γ → Δ) :
    Program Γ Δ := by
  classical
  exact
    { Label := ListMapLabel Γ
      main := .pop
      op
        | .pop => .popInput .halt .push
        | .push symbol => .pushOutput (f symbol) .pop
        | .halt => .halt }

/-- Exact runtime of the direct reversed map. -/
def listMapRevSteps {Γ : Type} (input : List Γ) : Nat :=
  2 * input.length + 2

private def listMapPopCfg {Γ Δ : Type} [Fintype Γ] (f : Γ → Δ)
    (buffer : Option Γ) (input : List Γ) (output : List Δ) :
    BuilderCfg (listMapRevProgram f) :=
  { initialCfg (listMapRevProgram f) input with
      buffer₁ := buffer
      output := output }

/-- Structural pop/push evaluation with an arbitrary existing output suffix. -/
private theorem listMap_popPushPhase_eval
    {Γ Δ : Type} [Fintype Γ] (f : Γ → Δ)
    (buffer : Option Γ) (input : List Γ) (output : List Δ) :
    (flip Option.bind (step (listMapRevProgram f)))^[2 * input.length + 1]
      (some (listMapPopCfg f buffer input output)) =
        some { haltCfg (listMapRevProgram f)
            ((input.map f).reverse ++ output) with
          label := some .halt } := by
  induction input generalizing buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step (listMapRevProgram f)))^[
            2 * rest.length + 1]
          (some (listMapPopCfg f (some symbol) rest
            (f symbol :: output))) =
          some { haltCfg (listMapRevProgram f)
              (((symbol :: rest).map f).reverse ++ output) with
            label := some .halt }
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (f symbol :: output)

/-- The direct transducer reverses the mapped list and clears its scratch
state before the final halt instruction. -/
def listMap_popPushPhase {Γ Δ : Type} [Fintype Γ] (f : Γ → Δ)
    (input : List Γ) :
    EvalsToInTime (step (listMapRevProgram f))
      (initialCfg (listMapRevProgram f) input)
      (some { haltCfg (listMapRevProgram f) (input.map f).reverse with
        label := some .halt })
      (2 * input.length + 1) := by
  refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
  simpa [listMapPopCfg, initialCfg] using
    listMap_popPushPhase_eval f none input []

/-- Final halt instruction of the direct map program. -/
def listMap_haltStep {Γ Δ : Type} [Fintype Γ] (f : Γ → Δ)
    (output : List Δ) :
    EvalsToInTime (step (listMapRevProgram f))
      { haltCfg (listMapRevProgram f) output with label := some .halt }
      (some (haltCfg (listMapRevProgram f) output)) 1 := by
  exact ⟨⟨1, rfl⟩, le_rfl⟩

/-- Exact independent-semantics run for the reversed symbol map. -/
def listMapRev_run {Γ Δ : Type} [Fintype Γ] (f : Γ → Δ)
    (input : List Γ) :
    EvalsToInTime (step (listMapRevProgram f))
      (initialCfg (listMapRevProgram f) input)
      (some (haltCfg (listMapRevProgram f) (input.map f).reverse))
      (listMapRevSteps input) := by
  let full := EvalsToInTime.trans (step (listMapRevProgram f))
    (2 * input.length + 1) 1
    (initialCfg (listMapRevProgram f) input)
    { haltCfg (listMapRevProgram f) (input.map f).reverse with
      label := some .halt }
    (some (haltCfg (listMapRevProgram f) (input.map f).reverse))
    (listMap_popPushPhase f input)
    (listMap_haltStep f (input.map f).reverse)
  have hsteps : full.steps = listMapRevSteps input := by
    change 1 + (2 * input.length + 1) = 2 * input.length + 2
    omega
  exact ⟨⟨listMapRevSteps input, hsteps ▸ full.evals_in_steps⟩, le_rfl⟩

/-- Builder output contract for the reversed fixed symbol map. -/
theorem listMapRev_builderOutputs {Γ Δ : Type} [Fintype Γ]
    (f : Γ → Δ) :
    BuilderOutputs (listMapRevProgram f)
      (fun input => (input.map f).reverse) listMapRevSteps := by
  intro input
  exact ⟨listMapRev_run f input⟩

/-- Compiled TM2 output contract for the reversed fixed symbol map. -/
theorem listMapRev_outputs {Γ Δ : Type} [Fintype Γ] (f : Γ → Δ) :
    Outputs (listMapRevProgram f)
      (fun input => (input.map f).reverse) listMapRevSteps :=
  Outputs.of_builder_run (listMapRev_builderOutputs f)

/-- Linear polynomial envelope of the direct map transducer. -/
noncomputable def listMapRev_polyBound {Γ : Type} :
    PolyBound (@listMapRevSteps Γ) where
  polynomial := 2 * Polynomial.X + 2
  bound input := by
    simp [listMapRevSteps, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]

/-- Concrete polynomial-time TM2 for the reversed fixed symbol map. -/
noncomputable def listMapRev_computableInPolyTime
    {Γ Δ : Type} [Fintype Γ] (f : Γ → Δ) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ => (input.map f).reverse) :=
  ComputableInPolyTime (listMapRevProgram f)
    (fun input => (input.map f).reverse) listMapRevSteps
    (listMapRev_outputs f) listMapRev_polyBound

/-- Reversal of the direct prepend-output stream produces ordinary
left-to-right `List.map` under one composed polynomial-time TM2. -/
noncomputable def listMap_computableInPolyTime
    {Γ Δ : Type} [Fintype Γ] [Fintype Δ] (f : Γ → Δ) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Γ => input.map f) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (listMapRev_computableInPolyTime f)
      (reverse_computableInPolyTime (Γ := Δ))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
