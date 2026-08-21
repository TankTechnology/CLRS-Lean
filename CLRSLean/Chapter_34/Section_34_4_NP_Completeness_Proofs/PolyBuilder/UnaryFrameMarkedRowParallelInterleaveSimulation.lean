import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveBase

/-!
# Embedded-transducer simulations for marked-row interleaving

The two source machines occupy disjoint stack banks.  This module proves that
their translated statements and whole steps commute with the corresponding
configuration embeddings.  Input duplication and output interleaving are
handled separately.
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

/-- Updating a first-bank stack commutes with the combined embedding. -/
lemma update_combinedStacks₁
    (first : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
    (second : ∀ k : M₂.tm.K, List (M₂.tm.Γ k))
    (k : M₁.tm.K) (value : List (M₁.tm.Γ k)) :
    Function.update (combinedStacks M₁ M₂ first second)
        (Sum.inl (Sum.inl k)) value =
      combinedStacks M₁ M₂ (Function.update first k value) second := by
  funext index
  cases index with
  | inl bank =>
      cases bank with
      | inl firstIndex =>
          by_cases h : firstIndex = k
          · subst firstIndex
            simp [combinedStacks, Function.update]
          · simp [combinedStacks, Function.update, h]
      | inr secondIndex =>
          simp [combinedStacks, Function.update]
  | inr extra =>
      cases extra <;> simp [combinedStacks, Function.update]

/-- Updating a second-bank stack commutes with the combined embedding. -/
lemma update_combinedStacks₂
    (first : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
    (second : ∀ k : M₂.tm.K, List (M₂.tm.Γ k))
    (k : M₂.tm.K) (value : List (M₂.tm.Γ k)) :
    Function.update (combinedStacks M₁ M₂ first second)
        (Sum.inl (Sum.inr k)) value =
      combinedStacks M₁ M₂ first (Function.update second k value) := by
  funext index
  cases index with
  | inl bank =>
      cases bank with
      | inl firstIndex =>
          simp [combinedStacks, Function.update]
      | inr secondIndex =>
          by_cases h : secondIndex = k
          · subst secondIndex
            simp [combinedStacks, Function.update]
          · simp [combinedStacks, Function.update, h]
  | inr extra =>
      cases extra <;> simp [combinedStacks, Function.update]

/-- Executing a translated first-machine statement mirrors the original
statement while freezing the second stack bank. -/
lemma stepAux_mapStmt₁
    (statement : _root_.Turing.TM2.Stmt M₁.tm.Γ M₁.tm.Λ M₁.tm.σ) :
    ∀ (state : M₁.tm.σ)
      (first : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
      (second : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)),
      _root_.Turing.TM2.stepAux (mapStmt₁ M₁ M₂ statement)
          (state, M₂.tm.initialState, ExtraState.initial)
          (combinedStacks M₁ M₂ first second) =
        mapCfg₁ M₁ M₂
          (_root_.Turing.TM2.stepAux statement state first) second := by
  induction statement with
  | push k f q ih =>
      intro state first second
      simp [mapStmt₁, combinedStacks, _root_.Turing.TM2.stepAux]
      rw [update_combinedStacks₁ M₁ M₂ first second k
        (f state :: first k)]
      exact ih state (Function.update first k (f state :: first k)) second
  | peek k f q ih =>
      intro state first second
      simp [mapStmt₁, combinedStacks, _root_.Turing.TM2.stepAux]
      exact ih (f state (first k).head?) first second
  | pop k f q ih =>
      intro state first second
      simp [mapStmt₁, combinedStacks, _root_.Turing.TM2.stepAux]
      rw [update_combinedStacks₁ M₁ M₂ first second k (first k).tail]
      exact ih (f state (first k).head?)
        (Function.update first k (first k).tail) second
  | load f q ih =>
      intro state first second
      simp [mapStmt₁, _root_.Turing.TM2.stepAux]
      exact ih (f state) first second
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro state first second
      simp [mapStmt₁, _root_.Turing.TM2.stepAux]
      by_cases h : f state <;>
        simp [h, ih₁ state first second, ih₂ state first second]
  | goto f =>
      intro state first second
      simp [mapStmt₁, _root_.Turing.TM2.stepAux, mapCfg₁]
  | halt =>
      intro state first second
      simp [mapStmt₁, _root_.Turing.TM2.stepAux, mapCfg₁]

/-- Executing a translated second-machine statement mirrors the original
statement while freezing the first stack bank. -/
lemma stepAux_mapStmt₂
    (statement : _root_.Turing.TM2.Stmt M₂.tm.Γ M₂.tm.Λ M₂.tm.σ) :
    ∀ (state : M₂.tm.σ)
      (first : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
      (second : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)),
      _root_.Turing.TM2.stepAux (mapStmt₂ M₁ M₂ statement)
          (M₁.tm.initialState, state, ExtraState.initial)
          (combinedStacks M₁ M₂ first second) =
        mapCfg₂ M₁ M₂
          (_root_.Turing.TM2.stepAux statement state second) first := by
  induction statement with
  | push k f q ih =>
      intro state first second
      simp [mapStmt₂, combinedStacks, _root_.Turing.TM2.stepAux]
      rw [update_combinedStacks₂ M₁ M₂ first second k
        (f state :: second k)]
      exact ih state first (Function.update second k (f state :: second k))
  | peek k f q ih =>
      intro state first second
      simp [mapStmt₂, combinedStacks, _root_.Turing.TM2.stepAux]
      exact ih (f state (second k).head?) first second
  | pop k f q ih =>
      intro state first second
      simp [mapStmt₂, combinedStacks, _root_.Turing.TM2.stepAux]
      rw [update_combinedStacks₂ M₁ M₂ first second k (second k).tail]
      exact ih (f state (second k).head?) first
        (Function.update second k (second k).tail)
  | load f q ih =>
      intro state first second
      simp [mapStmt₂, _root_.Turing.TM2.stepAux]
      exact ih (f state) first second
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro state first second
      simp [mapStmt₂, _root_.Turing.TM2.stepAux]
      by_cases h : f state <;>
        simp [h, ih₁ state first second, ih₂ state first second]
  | goto f =>
      intro state first second
      simp [mapStmt₂, _root_.Turing.TM2.stepAux, mapCfg₂]
  | halt =>
      intro state first second
      simp [mapStmt₂, _root_.Turing.TM2.stepAux, mapCfg₂]

private lemma step_ne_none_iff
    {K : Type} [DecidableEq K]
    {Γ : K → Type} {Λ σ : Type}
    (program : Λ → _root_.Turing.TM2.Stmt Γ Λ σ)
    (cfg : _root_.Turing.TM2.Cfg Γ Λ σ) :
    _root_.Turing.TM2.step program cfg ≠ none ↔ cfg.l ≠ none := by
  constructor
  · intro h hlabel
    rcases cfg with ⟨label, state, stackValues⟩
    cases label
    · simp [_root_.Turing.TM2.step] at h
    · cases hlabel
  · intro hlabel
    rcases cfg with ⟨label, state, stackValues⟩
    cases label
    · exact (hlabel rfl).elim
    · simp [_root_.Turing.TM2.step]

/-- One combined step simulates a non-halted first-machine step. -/
lemma step₁_sim
    (cfg : _root_.Turing.TM2.Cfg M₁.tm.Γ M₁.tm.Λ M₁.tm.σ)
    (hcfg : cfg.l ≠ none)
    (second : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)) :
    (machine M₁ M₂).step (mapCfg₁ M₁ M₂ cfg second) =
      Option.map (mapCfg₁ M₁ M₂ · second) (M₁.tm.step cfg) := by
  rcases cfg with ⟨label, state, first⟩
  cases label with
  | none => exact False.elim (hcfg rfl)
  | some label =>
      simp [_root_.Turing.FinTM2.step, _root_.Turing.TM2.step, mapCfg₁]
      change some (_root_.Turing.TM2.stepAux
          (mapStmt₁ M₁ M₂ (M₁.tm.m label))
          (state, M₂.tm.initialState, ExtraState.initial)
          (combinedStacks M₁ M₂ first second)) =
        some (mapCfg₁ M₁ M₂
          (_root_.Turing.TM2.stepAux (M₁.tm.m label) state first) second)
      exact congrArg some
        (stepAux_mapStmt₁ M₁ M₂ (M₁.tm.m label) state first second)

/-- One combined step simulates a non-halted second-machine step. -/
lemma step₂_sim
    (cfg : _root_.Turing.TM2.Cfg M₂.tm.Γ M₂.tm.Λ M₂.tm.σ)
    (hcfg : cfg.l ≠ none)
    (first : ∀ k : M₁.tm.K, List (M₁.tm.Γ k)) :
    (machine M₁ M₂).step (mapCfg₂ M₁ M₂ cfg first) =
      Option.map (mapCfg₂ M₁ M₂ · first) (M₂.tm.step cfg) := by
  rcases cfg with ⟨label, state, second⟩
  cases label with
  | none => exact False.elim (hcfg rfl)
  | some label =>
      simp [_root_.Turing.FinTM2.step, _root_.Turing.TM2.step, mapCfg₂]
      change some (_root_.Turing.TM2.stepAux
          (mapStmt₂ M₁ M₂ (M₂.tm.m label))
          (M₁.tm.initialState, state, ExtraState.initial)
          (combinedStacks M₁ M₂ first second)) =
        some (mapCfg₂ M₁ M₂
          (_root_.Turing.TM2.stepAux (M₂.tm.m label) state second) first)
      exact congrArg some
        (stepAux_mapStmt₂ M₁ M₂ (M₂.tm.m label) state first second)

/-- Simulation form expected by `evalsToInTime_lift`. -/
lemma stepC_sim₁
    (second : ∀ k : M₂.tm.K, List (M₂.tm.Γ k))
    (cfg : _root_.Turing.TM2.Cfg M₁.tm.Γ M₁.tm.Λ M₁.tm.σ) :
    M₁.tm.step cfg ≠ none →
      (machine M₁ M₂).step (mapCfg₁ M₁ M₂ cfg second) =
        Option.map (mapCfg₁ M₁ M₂ · second) (M₁.tm.step cfg) :=
  fun hstep => step₁_sim M₁ M₂ cfg
    ((step_ne_none_iff M₁.tm.m cfg).1 hstep) second

/-- Simulation form expected by `evalsToInTime_lift`. -/
lemma stepC_sim₂
    (first : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
    (cfg : _root_.Turing.TM2.Cfg M₂.tm.Γ M₂.tm.Λ M₂.tm.σ) :
    M₂.tm.step cfg ≠ none →
      (machine M₁ M₂).step (mapCfg₂ M₁ M₂ cfg first) =
        Option.map (mapCfg₂ M₁ M₂ · first) (M₂.tm.step cfg) :=
  fun hstep => step₂_sim M₁ M₂ cfg
    ((step_ne_none_iff M₂.tm.m cfg).1 hstep) first

end UnaryFrameMarkedRowParallelInterleave

end CLRS.Chapter34.Turing.PolyBuilder
