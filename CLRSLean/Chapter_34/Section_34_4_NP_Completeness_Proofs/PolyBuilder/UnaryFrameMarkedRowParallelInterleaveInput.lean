import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveSimulation

/-!
# Input duplication for parallel marked-row interleaving

The combined machine first moves the raw input through a semantic scratch
stack and restores it onto both embedded input stacks.  This file proves the
two exact passes and their `2 * |x| + 2` composite bound.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

namespace UnaryFrameMarkedRowParallelInterleave

variable {Γ : Type} [Fintype Γ]
variable {leftFamily rightFamily : List Γ → UnaryFrameMarkedRowFamily}
variable
  (M₁ : _root_.Turing.TM2ComputableInPolyTime id
    encodeUnaryFrameMarkedRowFamily leftFamily)
  (M₂ : _root_.Turing.TM2ComputableInPolyTime id
    encodeUnaryFrameMarkedRowFamily rightFamily)

/-- Updating two distinct dependent stack keys commutes. -/
lemma update_swap
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    (first second : K M₁ M₂)
    (firstValue : List (StackAlphabet M₁ M₂ first))
    (secondValue : List (StackAlphabet M₁ M₂ second))
    (hne : first ≠ second) :
    Function.update (Function.update values first firstValue)
        second secondValue =
      Function.update (Function.update values second secondValue)
        first firstValue := by
  funext key
  by_cases hfirst : key = first
  · subst key
    simp [Function.update, hne]
  · by_cases hsecond : key = second
    · subst key
      simp [Function.update, hfirst]
    · simp [Function.update, hfirst, hsecond]

/-- Updating a stack with its current value is a no-op. -/
lemma update_self
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    (key : K M₁ M₂) (value : List (StackAlphabet M₁ M₂ key))
    (hvalue : values key = value) :
    Function.update values key value = values := by
  funext other
  by_cases h : other = key
  · subst other
    simp [Function.update, hvalue]
  · simp [Function.update, h]

/-- Copy-out phase: move the first input onto the scratch in reverse order. -/
lemma duplicate_copyout_phase
    {input : List Γ}
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    {temp : List Γ} (state : ExtraState Γ)
    (hinput : values (inputK M₁ M₂) =
      List.map M₁.inputAlphabet.invFun input)
    (htemp : values (inputTempK M₁ M₂) = temp) :
    (flip Option.bind (machine M₁ M₂).step)^[input.length + 1]
        (some
          (⟨some (Sum.inr ExtraΛ.duplicateScan),
            (M₁.tm.initialState, M₂.tm.initialState, state), values⟩ :
              (machine M₁ M₂).Cfg)) =
      some
        (⟨some (Sum.inr ExtraΛ.duplicateRestore),
          (M₁.tm.initialState, M₂.tm.initialState,
            ExtraState.duplicateDone),
          Function.update
            (Function.update values (inputK M₁ M₂) [])
            (inputTempK M₁ M₂) (input.reverse ++ temp)⟩ :
              (machine M₁ M₂).Cfg) := by
  induction input generalizing values temp state with
  | nil =>
      have hhead : (values (inputK M₁ M₂)).head? = none := by
        rw [hinput]
        simp
      have htail : (values (inputK M₁ M₂)).tail = [] := by
        rw [hinput]
        simp
      have hcollapse :
          Function.update
              (Function.update values (inputK M₁ M₂) [])
              (inputTempK M₁ M₂) temp =
            Function.update values (inputK M₁ M₂) [] := by
        rw [update_swap M₁ M₂ (inputK M₁ M₂) (inputTempK M₁ M₂)
          ([] : List (M₁.tm.Γ M₁.tm.k₀)) temp (by simp)]
        rw [update_self M₁ M₂ (inputTempK M₁ M₂) temp htemp]
      by_cases hnonempty : Nonempty Γ
      · simp [machine, program, extraProgram, flip, hnonempty, hhead, htail]
        rw [hcollapse]
      · simp [machine, program, extraProgram, flip, hnonempty, hhead, htail]
        rw [hcollapse]
  | cons symbol rest ih =>
      have hhead : (values (inputK M₁ M₂)).head? =
          some (M₁.inputAlphabet.invFun symbol) := by
        rw [hinput]
        simp
      have htail : (values (inputK M₁ M₂)).tail =
          List.map M₁.inputAlphabet.invFun rest := by
        rw [hinput]
        simp
      have hone :
          (flip Option.bind (machine M₁ M₂).step)
              (some
                (⟨some (Sum.inr ExtraΛ.duplicateScan),
                  (M₁.tm.initialState, M₂.tm.initialState, state), values⟩ :
                    (machine M₁ M₂).Cfg)) =
            some
              (⟨some (Sum.inr ExtraΛ.duplicateScan),
                (M₁.tm.initialState, M₂.tm.initialState,
                  ExtraState.duplicateSymbol symbol),
                Function.update
                  (Function.update values (inputK M₁ M₂)
                    (List.map M₁.inputAlphabet.invFun rest))
                  (inputTempK M₁ M₂) (symbol :: temp)⟩ :
                    (machine M₁ M₂).Cfg) := by
        have hnonempty : Nonempty Γ := ⟨symbol⟩
        simp [machine, program, extraProgram, flip, hnonempty, hhead, htail,
          htemp]
      rw [show (symbol :: rest).length + 1 =
          (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply, hone]
      have hih := ih
        (state := ExtraState.duplicateSymbol symbol)
        (values := Function.update
          (Function.update values (inputK M₁ M₂)
            (List.map M₁.inputAlphabet.invFun rest))
          (inputTempK M₁ M₂) (symbol :: temp))
        (temp := symbol :: temp)
        (by simp [Function.update])
        (by simp [Function.update])
      have hcollapse :
          Function.update
              (Function.update
                (Function.update
                  (Function.update values (inputK M₁ M₂)
                    (List.map M₁.inputAlphabet.invFun rest))
                  (inputTempK M₁ M₂) (symbol :: temp))
                (inputK M₁ M₂) [])
              (inputTempK M₁ M₂) (rest.reverse ++ symbol :: temp) =
            Function.update
              (Function.update values (inputK M₁ M₂) [])
              (inputTempK M₁ M₂)
                ((symbol :: rest).reverse ++ temp) := by
        funext key
        by_cases h₁ : key = inputK M₁ M₂ <;>
          by_cases h₂ : key = inputTempK M₁ M₂ <;>
            simp [Function.update, h₁, h₂, List.reverse_cons,
              List.cons_append, List.append_assoc]
      exact hih.trans (congrArg
        (fun stackValues => some
          (⟨some (Sum.inr ExtraΛ.duplicateRestore),
            (M₁.tm.initialState, M₂.tm.initialState,
              ExtraState.duplicateDone), stackValues⟩ :
                (machine M₁ M₂).Cfg)) hcollapse)

/-- Copy-back phase: restore the semantic scratch onto both input stacks. -/
lemma duplicate_restore_phase
    {input : List Γ}
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    (state : ExtraState Γ)
    {first : List (M₁.tm.Γ M₁.tm.k₀)}
    {second : List (M₂.tm.Γ M₂.tm.k₀)}
    (htemp : values (inputTempK M₁ M₂) = input)
    (hfirst : values (inputK M₁ M₂) = first)
    (hsecond : values (secondInputK M₁ M₂) = second) :
    (flip Option.bind (machine M₁ M₂).step)^[input.length + 1]
        (some
          (⟨some (Sum.inr ExtraΛ.duplicateRestore),
            (M₁.tm.initialState, M₂.tm.initialState, state), values⟩ :
              (machine M₁ M₂).Cfg)) =
      some
        (⟨some (Sum.inl (Sum.inl M₁.tm.main)),
          (M₁.tm.initialState, M₂.tm.initialState, ExtraState.initial),
          Function.update
            (Function.update
              (Function.update values (inputTempK M₁ M₂) [])
              (inputK M₁ M₂)
                ((List.map M₁.inputAlphabet.invFun input).reverse ++ first))
            (secondInputK M₁ M₂)
              ((List.map M₂.inputAlphabet.invFun input).reverse ++ second)⟩ :
                (machine M₁ M₂).Cfg) := by
  induction input generalizing values first second state with
  | nil =>
      have hhead : (values (inputTempK M₁ M₂)).head? = none := by
        rw [htemp]
        simp
      have htail : (values (inputTempK M₁ M₂)).tail = [] := by
        rw [htemp]
        simp
      have hcollapse :
          Function.update
              (Function.update
                (Function.update values (inputTempK M₁ M₂) [])
                (inputK M₁ M₂) first)
              (secondInputK M₁ M₂) second =
            Function.update values (inputTempK M₁ M₂) [] := by
        funext key
        by_cases h₁ : key = inputK M₁ M₂
        · subst key
          simp [Function.update, hfirst]
        · by_cases h₂ : key = secondInputK M₁ M₂
          · subst key
            simp [Function.update, hsecond]
          · by_cases h₃ : key = inputTempK M₁ M₂
            · subst key
              simp [Function.update]
            · simp [Function.update, h₁, h₂, h₃]
      by_cases hnonempty : Nonempty Γ
      · simp [machine, program, extraProgram, flip, hnonempty, hhead, htail]
        rw [hcollapse]
      · simp [machine, program, extraProgram, flip, hnonempty, hhead, htail]
        rw [hcollapse]
  | cons symbol rest ih =>
      have hhead : (values (inputTempK M₁ M₂)).head? = some symbol := by
        rw [htemp]
        simp
      have htail : (values (inputTempK M₁ M₂)).tail = rest := by
        rw [htemp]
        simp
      have hone :
          (flip Option.bind (machine M₁ M₂).step)
              (some
                (⟨some (Sum.inr ExtraΛ.duplicateRestore),
                  (M₁.tm.initialState, M₂.tm.initialState, state), values⟩ :
                    (machine M₁ M₂).Cfg)) =
            some
              (⟨some (Sum.inr ExtraΛ.duplicateRestore),
                (M₁.tm.initialState, M₂.tm.initialState,
                  ExtraState.restoreSymbol symbol),
                Function.update
                  (Function.update
                    (Function.update values (inputTempK M₁ M₂) rest)
                    (inputK M₁ M₂)
                      (M₁.inputAlphabet.invFun symbol :: first))
                  (secondInputK M₁ M₂)
                    (M₂.inputAlphabet.invFun symbol :: second)⟩ :
                    (machine M₁ M₂).Cfg) := by
        have hnonempty : Nonempty Γ := ⟨symbol⟩
        simp [machine, program, extraProgram, flip, hnonempty, hhead, htail,
          hfirst, hsecond]
      rw [show (symbol :: rest).length + 1 =
          (rest.length + 1) + 1 by simp,
        Function.iterate_succ_apply, hone]
      have hih := ih
        (state := ExtraState.restoreSymbol symbol)
        (values := Function.update
          (Function.update
            (Function.update values (inputTempK M₁ M₂) rest)
            (inputK M₁ M₂)
              (M₁.inputAlphabet.invFun symbol :: first))
          (secondInputK M₁ M₂)
            (M₂.inputAlphabet.invFun symbol :: second))
        (first := M₁.inputAlphabet.invFun symbol :: first)
        (second := M₂.inputAlphabet.invFun symbol :: second)
        (by simp [Function.update])
        (by simp [Function.update])
        (by simp [Function.update])
      have hcollapse :
          Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update
                      (Function.update values (inputTempK M₁ M₂) rest)
                      (inputK M₁ M₂)
                        (M₁.inputAlphabet.invFun symbol :: first))
                    (secondInputK M₁ M₂)
                      (M₂.inputAlphabet.invFun symbol :: second))
                  (inputTempK M₁ M₂) [])
                (inputK M₁ M₂)
                  ((List.map M₁.inputAlphabet.invFun rest).reverse ++
                    M₁.inputAlphabet.invFun symbol :: first))
              (secondInputK M₁ M₂)
                ((List.map M₂.inputAlphabet.invFun rest).reverse ++
                  M₂.inputAlphabet.invFun symbol :: second) =
            Function.update
              (Function.update
                (Function.update values (inputTempK M₁ M₂) [])
                (inputK M₁ M₂)
                  ((List.map M₁.inputAlphabet.invFun
                    (symbol :: rest)).reverse ++ first))
              (secondInputK M₁ M₂)
                ((List.map M₂.inputAlphabet.invFun
                  (symbol :: rest)).reverse ++ second) := by
        funext key
        by_cases h₁ : key = inputTempK M₁ M₂ <;>
          by_cases h₂ : key = inputK M₁ M₂ <;>
            by_cases h₃ : key = secondInputK M₁ M₂ <;>
              simp [Function.update, h₁, h₂, h₃, List.reverse_cons,
                List.cons_append, List.append_assoc]
      exact hih.trans (congrArg
        (fun stackValues => some
          (⟨some (Sum.inl (Sum.inl M₁.tm.main)),
            (M₁.tm.initialState, M₂.tm.initialState, ExtraState.initial),
            stackValues⟩ : (machine M₁ M₂).Cfg)) hcollapse)

/-- The second transducer's duplicated input stack family. -/
def duplicatedSecondInput (input : List Γ) :
    ∀ k : M₂.tm.K, List (M₂.tm.Γ k) :=
  (_root_.Turing.initList M₂.tm
    (List.map M₂.inputAlphabet.invFun input)).stk

/-- The complete duplication phase restores the input to both transducers. -/
lemma duplicate_phase (input : List Γ) :
    (flip Option.bind (machine M₁ M₂).step)^[2 * input.length + 2]
        (some (_root_.Turing.initList (machine M₁ M₂)
          (List.map M₁.inputAlphabet.invFun input))) =
      some (mapCfg₁ M₁ M₂
        (_root_.Turing.initList M₁.tm
          (List.map M₁.inputAlphabet.invFun input))
        (duplicatedSecondInput M₂ input)) := by
  have hcopy := duplicate_copyout_phase M₁ M₂
    (input := input) (state := ExtraState.initial)
    (values := (_root_.Turing.initList (machine M₁ M₂)
      (List.map M₁.inputAlphabet.invFun input)).stk)
    (temp := [])
    (by
      simpa only using
        (_root_.Turing.TM2Comp.initList_stk₀ (machine M₁ M₂)
          (List.map M₁.inputAlphabet.invFun input)))
    (by simp [machine, inputTempK])
  have hrestore := duplicate_restore_phase M₁ M₂
    (input := input.reverse) (state := ExtraState.duplicateDone)
    (values := Function.update
      (Function.update
        (_root_.Turing.initList (machine M₁ M₂)
          (List.map M₁.inputAlphabet.invFun input)).stk
        (inputK M₁ M₂) [])
      (inputTempK M₁ M₂) (input.reverse ++ []))
    (first := []) (second := [])
    (by simp [inputTempK, Function.update])
    (by simp [inputK, Function.update])
    (by simp [secondInputK, Function.update])
  change
    (flip Option.bind (machine M₁ M₂).step)^[2 * input.length + 2]
        (some
          (⟨some (Sum.inr ExtraΛ.duplicateScan),
            (M₁.tm.initialState, M₂.tm.initialState, ExtraState.initial),
            (_root_.Turing.initList (machine M₁ M₂)
              (List.map M₁.inputAlphabet.invFun input)).stk⟩ :
                (machine M₁ M₂).Cfg)) = _
  rw [show 2 * input.length + 2 =
      (input.reverse.length + 1) + (input.length + 1) by simp; omega,
    Function.iterate_add_apply]
  refine (congrArg
    (fun cfg =>
      (flip Option.bind (machine M₁ M₂).step)^[input.reverse.length + 1]
        cfg) hcopy).trans ?_
  refine hrestore.trans ?_
  apply congrArg some
  apply _root_.Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext key
    cases key with
    | inl bank =>
        cases bank with
        | inl firstIndex =>
            by_cases h : firstIndex = M₁.tm.k₀
            · subst firstIndex
              simp [mapCfg₁, combinedStacks, duplicatedSecondInput,
                _root_.Turing.initList, Function.update, List.map_reverse]
            · simp [mapCfg₁, combinedStacks, duplicatedSecondInput,
                _root_.Turing.initList, Function.update, h]
        | inr secondIndex =>
            by_cases h : secondIndex = M₂.tm.k₀
            · subst secondIndex
              simp [mapCfg₁, combinedStacks, duplicatedSecondInput,
                _root_.Turing.initList, Function.update, List.map_reverse]
            · simp [mapCfg₁, combinedStacks, duplicatedSecondInput,
                _root_.Turing.initList, Function.update, h]
    | inr extra =>
        cases extra <;>
          simp [mapCfg₁, combinedStacks, duplicatedSecondInput,
            _root_.Turing.initList, Function.update]

end UnaryFrameMarkedRowParallelInterleave

end CLRS.Chapter34.Turing.PolyBuilder
