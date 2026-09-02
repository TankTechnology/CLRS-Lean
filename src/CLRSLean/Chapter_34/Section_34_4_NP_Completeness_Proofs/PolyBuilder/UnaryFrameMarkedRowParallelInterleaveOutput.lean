import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveFamily

/-!
# Output restoration for parallel marked-row interleaving

After aligned row merging, the semantic interleaving is stored in reverse on
the scratch stack.  This module proves the final empty-source transition and
the exact linear pass which reverses that scratch onto the combined output
stack and halts.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

namespace UnaryFrameMarkedRowParallelInterleave

variable {α Γ : Type} [Fintype Γ]
variable {encode : α → List Γ}
variable {leftFamily rightFamily : α → UnaryFrameMarkedRowFamily}
variable
  (M₁ : _root_.Turing.TM2ComputableInPolyTime encode
    encodeUnaryFrameMarkedRowFamily leftFamily)
  (M₂ : _root_.Turing.TM2ComputableInPolyTime encode
    encodeUnaryFrameMarkedRowFamily rightFamily)

/-- Halted combined configuration with an explicitly supplied stack family. -/
def restoredCfg
    (values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)) :
    (machine M₁ M₂).Cfg :=
  ⟨none, (M₁.tm.initialState, M₂.tm.initialState, ExtraState.initial), values⟩

/-- Once the left source is empty, one physical probe enters output
restoration without changing any stack. -/
lemma merge_finish_step
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    (state : ExtraState Γ)
    (hleft : values (firstOutputK M₁ M₂) = []) :
    (flip Option.bind (machine M₁ M₂).step)
        (some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state values)) =
      some (mergeCfg M₁ M₂ ExtraΛ.outputRestore
        ExtraState.mergeDone values) := by
  have hhead : (values (firstOutputK M₁ M₂)).head? = none := by
    rw [hleft]
    rfl
  have htail : (values (firstOutputK M₁ M₂)).tail = [] := by
    rw [hleft]
    rfl
  have hcollapse : Function.update values (firstOutputK M₁ M₂) [] =
      values := update_self M₁ M₂ _ _ hleft
  simp [mergeCfg, machine, program, extraProgram, flip, hhead, htail]
  rw [hcollapse]
  rfl

/-- The reverse scratch is moved onto the real output stack, one symbol per
step plus one final empty-scratch step which resets the state and halts. -/
lemma output_restore_phase
    {source : List UnaryFrameSym}
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    {output : List (M₂.tm.Γ M₂.tm.k₁)} (state : ExtraState Γ)
    (htemp : values (outputTempK M₁ M₂) = source)
    (houtput : values (outputK M₁ M₂) = output) :
    (flip Option.bind (machine M₁ M₂).step)^[source.length + 1]
        (some (mergeCfg M₁ M₂ ExtraΛ.outputRestore state values)) =
      some (restoredCfg M₁ M₂
        (Function.update
          (Function.update values (outputTempK M₁ M₂) [])
          (outputK M₁ M₂)
            ((List.map M₂.outputAlphabet.invFun source).reverse ++ output))) := by
  induction source generalizing values output state with
  | nil =>
      have hhead : (values (outputTempK M₁ M₂)).head? = none := by
        rw [htemp]
        rfl
      have htail : (values (outputTempK M₁ M₂)).tail = [] := by
        rw [htemp]
        rfl
      have hcollapse :
          Function.update
              (Function.update values (outputTempK M₁ M₂) [])
              (outputK M₁ M₂) output =
            Function.update values (outputTempK M₁ M₂) [] := by
        rw [update_swap M₁ M₂ (outputTempK M₁ M₂) (outputK M₁ M₂)
          ([] : List UnaryFrameSym) output (by simp)]
        rw [update_self M₁ M₂ (outputK M₁ M₂) output houtput]
      simp [mergeCfg, restoredCfg, machine, program, extraProgram, flip,
        hhead, htail]
      rw [hcollapse]
      rfl
  | cons symbol rest ih =>
      have hhead : (values (outputTempK M₁ M₂)).head? = some symbol := by
        rw [htemp]
        rfl
      have htail : (values (outputTempK M₁ M₂)).tail = rest := by
        rw [htemp]
        rfl
      have hone :
          (flip Option.bind (machine M₁ M₂).step)
              (some (mergeCfg M₁ M₂ ExtraΛ.outputRestore state values)) =
            some (mergeCfg M₁ M₂ ExtraΛ.outputRestore
              (ExtraState.outputSymbol symbol)
              (Function.update
                (Function.update values (outputTempK M₁ M₂) rest)
                (outputK M₁ M₂)
                  (M₂.outputAlphabet.invFun symbol :: output))) := by
        simp [mergeCfg, machine, program, extraProgram, flip, hhead, htail,
          houtput]
        rfl
      rw [show (symbol :: rest).length + 1 =
          (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply, hone]
      have hih := ih
        (state := ExtraState.outputSymbol symbol)
        (values := Function.update
          (Function.update values (outputTempK M₁ M₂) rest)
          (outputK M₁ M₂)
            (M₂.outputAlphabet.invFun symbol :: output))
        (output := M₂.outputAlphabet.invFun symbol :: output)
        (by simp [Function.update])
        (by simp [Function.update])
      have hcollapse :
          Function.update
              (Function.update
                (Function.update
                  (Function.update values (outputTempK M₁ M₂) rest)
                  (outputK M₁ M₂)
                    (M₂.outputAlphabet.invFun symbol :: output))
                (outputTempK M₁ M₂) [])
              (outputK M₁ M₂)
                ((List.map M₂.outputAlphabet.invFun rest).reverse ++
                  M₂.outputAlphabet.invFun symbol :: output) =
            Function.update
              (Function.update values (outputTempK M₁ M₂) [])
              (outputK M₁ M₂)
                ((List.map M₂.outputAlphabet.invFun
                  (symbol :: rest)).reverse ++ output) := by
        funext key
        by_cases h₁ : key = outputTempK M₁ M₂ <;>
          by_cases h₂ : key = outputK M₁ M₂ <;>
            simp [Function.update, h₁, h₂, List.reverse_cons,
              List.cons_append, List.append_assoc]
      exact hih.trans (congrArg
        (fun stackValues => some (restoredCfg M₁ M₂ stackValues))
        hcollapse)

end UnaryFrameMarkedRowParallelInterleave

end CLRS.Chapter34.Turing.PolyBuilder
