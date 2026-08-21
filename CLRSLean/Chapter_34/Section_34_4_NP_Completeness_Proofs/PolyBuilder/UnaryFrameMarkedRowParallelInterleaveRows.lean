import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveInput

/-!
# Single-row transfer for parallel marked-row interleaving

The physical merger alternates between the two embedded output stacks.  This
file proves the two local facts used by the family-level induction: a complete
delimiter-free row, followed by `frameEnd`, is consumed in exactly one step
per encoded symbol, prepended to the semantic output scratch, and hands
control to the other stack.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

namespace UnaryFrameMarkedRowParallelInterleave

variable {Γ : Type} [Fintype Γ] [Inhabited Γ]
variable {leftFamily rightFamily : List Γ → UnaryFrameMarkedRowFamily}
variable
  (M₁ : _root_.Turing.TM2ComputableInPolyTime id
    encodeUnaryFrameMarkedRowFamily leftFamily)
  (M₂ : _root_.Turing.TM2ComputableInPolyTime id
    encodeUnaryFrameMarkedRowFamily rightFamily)

/-- Configuration at one of the physical merge phases. -/
def mergeCfg (label : ExtraΛ) (state : ExtraState Γ)
    (values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)) :
    (machine M₁ M₂).Cfg :=
  ⟨some (Sum.inr label),
    (M₁.tm.initialState, M₂.tm.initialState, state), values⟩

/-- A delimiter-free row on the first output stack is moved to the scratch,
including its boundary marker, before control passes to the second stack. -/
lemma merge_left_row_phase
    {row tail : List UnaryFrameSym}
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    {temp : List UnaryFrameSym} (state : ExtraState Γ)
    (hfree : ∀ symbol ∈ row, symbol ≠ UnaryFrameSym.frameEnd)
    (hsource : values (firstOutputK M₁ M₂) =
      List.map M₁.outputAlphabet.invFun
        (row ++ UnaryFrameSym.frameEnd :: tail))
    (htemp : values (outputTempK M₁ M₂) = temp) :
    (flip Option.bind (machine M₁ M₂).step)^[row.length + 1]
        (some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state values)) =
      some (mergeCfg M₁ M₂ ExtraΛ.mergeRight
        (ExtraState.mergeSymbol UnaryFrameSym.frameEnd)
        (Function.update
          (Function.update values (firstOutputK M₁ M₂)
            (List.map M₁.outputAlphabet.invFun tail))
          (outputTempK M₁ M₂)
            ((row ++ [UnaryFrameSym.frameEnd]).reverse ++ temp))) := by
  induction row generalizing values temp state with
  | nil =>
      have hhead : (values (firstOutputK M₁ M₂)).head? =
          some (M₁.outputAlphabet.invFun UnaryFrameSym.frameEnd) := by
        rw [hsource]
        simp
      have htail : (values (firstOutputK M₁ M₂)).tail =
          List.map M₁.outputAlphabet.invFun tail := by
        rw [hsource]
        simp
      simp [mergeCfg, machine, program, extraProgram, flip, hhead, htail,
        htemp]
      rfl
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      have hhead : (values (firstOutputK M₁ M₂)).head? =
          some (M₁.outputAlphabet.invFun symbol) := by
        rw [hsource]
        simp
      have htail : (values (firstOutputK M₁ M₂)).tail =
          List.map M₁.outputAlphabet.invFun
            (rest ++ UnaryFrameSym.frameEnd :: tail) := by
        rw [hsource]
        simp
      have hone :
          (flip Option.bind (machine M₁ M₂).step)
              (some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state values)) =
            some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft
              (ExtraState.mergeSymbol symbol)
              (Function.update
                (Function.update values (firstOutputK M₁ M₂)
                  (List.map M₁.outputAlphabet.invFun
                    (rest ++ UnaryFrameSym.frameEnd :: tail)))
                (outputTempK M₁ M₂) (symbol :: temp))) := by
        simp [mergeCfg, machine, program, extraProgram, flip, hhead, htail,
          htemp, hsymbol]
        rfl
      rw [show (symbol :: rest).length + 1 =
          (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply, hone]
      have hih := ih
        (state := ExtraState.mergeSymbol symbol)
        (values := Function.update
          (Function.update values (firstOutputK M₁ M₂)
            (List.map M₁.outputAlphabet.invFun
              (rest ++ UnaryFrameSym.frameEnd :: tail)))
          (outputTempK M₁ M₂) (symbol :: temp))
        (temp := symbol :: temp) hrest
        (by simp [Function.update])
        (by simp [Function.update])
      have hcollapse :
          Function.update
              (Function.update
                (Function.update
                  (Function.update values (firstOutputK M₁ M₂)
                    (List.map M₁.outputAlphabet.invFun
                      (rest ++ UnaryFrameSym.frameEnd :: tail)))
                  (outputTempK M₁ M₂) (symbol :: temp))
                (firstOutputK M₁ M₂)
                  (List.map M₁.outputAlphabet.invFun tail))
              (outputTempK M₁ M₂)
                ((rest ++ [UnaryFrameSym.frameEnd]).reverse ++
                  symbol :: temp) =
            Function.update
              (Function.update values (firstOutputK M₁ M₂)
                (List.map M₁.outputAlphabet.invFun tail))
              (outputTempK M₁ M₂)
                (((symbol :: rest) ++
                  [UnaryFrameSym.frameEnd]).reverse ++ temp) := by
        funext key
        by_cases h₁ : key = firstOutputK M₁ M₂ <;>
          by_cases h₂ : key = outputTempK M₁ M₂ <;>
            simp [Function.update, h₁, h₂, List.reverse_cons,
              List.append_assoc]
      exact hih.trans (congrArg
        (fun stackValues => some (mergeCfg M₁ M₂ ExtraΛ.mergeRight
          (ExtraState.mergeSymbol UnaryFrameSym.frameEnd) stackValues))
        hcollapse)

/-- A delimiter-free row on the second output stack is moved to the scratch,
including its boundary marker, before control returns to the first stack. -/
lemma merge_right_row_phase
    {row tail : List UnaryFrameSym}
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    {temp : List UnaryFrameSym} (state : ExtraState Γ)
    (hfree : ∀ symbol ∈ row, symbol ≠ UnaryFrameSym.frameEnd)
    (hsource : values (outputK M₁ M₂) =
      List.map M₂.outputAlphabet.invFun
        (row ++ UnaryFrameSym.frameEnd :: tail))
    (htemp : values (outputTempK M₁ M₂) = temp) :
    (flip Option.bind (machine M₁ M₂).step)^[row.length + 1]
        (some (mergeCfg M₁ M₂ ExtraΛ.mergeRight state values)) =
      some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft
        (ExtraState.mergeSymbol UnaryFrameSym.frameEnd)
        (Function.update
          (Function.update values (outputK M₁ M₂)
            (List.map M₂.outputAlphabet.invFun tail))
          (outputTempK M₁ M₂)
            ((row ++ [UnaryFrameSym.frameEnd]).reverse ++ temp))) := by
  induction row generalizing values temp state with
  | nil =>
      have hhead : (values (outputK M₁ M₂)).head? =
          some (M₂.outputAlphabet.invFun UnaryFrameSym.frameEnd) := by
        rw [hsource]
        simp
      have htail : (values (outputK M₁ M₂)).tail =
          List.map M₂.outputAlphabet.invFun tail := by
        rw [hsource]
        simp
      simp [mergeCfg, machine, program, extraProgram, flip, hhead, htail,
        htemp]
      rfl
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      have hhead : (values (outputK M₁ M₂)).head? =
          some (M₂.outputAlphabet.invFun symbol) := by
        rw [hsource]
        simp
      have htail : (values (outputK M₁ M₂)).tail =
          List.map M₂.outputAlphabet.invFun
            (rest ++ UnaryFrameSym.frameEnd :: tail) := by
        rw [hsource]
        simp
      have hone :
          (flip Option.bind (machine M₁ M₂).step)
              (some (mergeCfg M₁ M₂ ExtraΛ.mergeRight state values)) =
            some (mergeCfg M₁ M₂ ExtraΛ.mergeRight
              (ExtraState.mergeSymbol symbol)
              (Function.update
                (Function.update values (outputK M₁ M₂)
                  (List.map M₂.outputAlphabet.invFun
                    (rest ++ UnaryFrameSym.frameEnd :: tail)))
                (outputTempK M₁ M₂) (symbol :: temp))) := by
        simp [mergeCfg, machine, program, extraProgram, flip, hhead, htail,
          htemp, hsymbol]
        rfl
      rw [show (symbol :: rest).length + 1 =
          (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply, hone]
      have hih := ih
        (state := ExtraState.mergeSymbol symbol)
        (values := Function.update
          (Function.update values (outputK M₁ M₂)
            (List.map M₂.outputAlphabet.invFun
              (rest ++ UnaryFrameSym.frameEnd :: tail)))
          (outputTempK M₁ M₂) (symbol :: temp))
        (temp := symbol :: temp) hrest
        (by simp [Function.update])
        (by simp [Function.update])
      have hcollapse :
          Function.update
              (Function.update
                (Function.update
                  (Function.update values (outputK M₁ M₂)
                    (List.map M₂.outputAlphabet.invFun
                      (rest ++ UnaryFrameSym.frameEnd :: tail)))
                  (outputTempK M₁ M₂) (symbol :: temp))
                (outputK M₁ M₂)
                  (List.map M₂.outputAlphabet.invFun tail))
              (outputTempK M₁ M₂)
                ((rest ++ [UnaryFrameSym.frameEnd]).reverse ++
                  symbol :: temp) =
            Function.update
              (Function.update values (outputK M₁ M₂)
                (List.map M₂.outputAlphabet.invFun tail))
              (outputTempK M₁ M₂)
                (((symbol :: rest) ++
                  [UnaryFrameSym.frameEnd]).reverse ++ temp) := by
        funext key
        by_cases h₁ : key = outputK M₁ M₂ <;>
          by_cases h₂ : key = outputTempK M₁ M₂ <;>
            simp [Function.update, h₁, h₂, List.reverse_cons,
              List.append_assoc]
      exact hih.trans (congrArg
        (fun stackValues => some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft
          (ExtraState.mergeSymbol UnaryFrameSym.frameEnd) stackValues))
        hcollapse)

end UnaryFrameMarkedRowParallelInterleave

end CLRS.Chapter34.Turing.PolyBuilder
