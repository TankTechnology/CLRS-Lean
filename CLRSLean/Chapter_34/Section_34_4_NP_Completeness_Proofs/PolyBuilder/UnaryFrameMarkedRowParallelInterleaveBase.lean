import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowInterleave
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Machine skeleton for parallel marked-row interleaving

Two polynomial-time transducers receive the same input.  The combined machine
duplicates that input, executes the transducers sequentially on disjoint stack
banks, alternates complete `frameEnd`-delimited rows from their output stacks,
and reverses the temporary prepend-order result onto the final output stack.

This file contains only the finite machine and its configuration embeddings.
Step simulations, exact merge semantics, and the polynomial runtime theorem
are intentionally split into later modules.
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

/-- Scratch stacks for input duplication and prepend-order output merging. -/
inductive ExtraK
  | inputTemp
  | outputTemp
deriving DecidableEq, Fintype, Inhabited

/-- Finite control phases outside the two embedded transducers. -/
inductive ExtraΛ
  | duplicateScan
  | duplicateRestore
  | mergeLeft
  | mergeRight
  | outputRestore
deriving DecidableEq, Fintype, Inhabited

/-- Extra finite state used while copying input and transferring output
symbols. -/
inductive ExtraState (Γ : Type)
  | initial
  | duplicateSymbol (symbol : Γ)
  | duplicateDone
  | restoreSymbol (symbol : Γ)
  | restoreDone
  | mergeSymbol (symbol : UnaryFrameSym)
  | mergeDone
  | outputSymbol (symbol : UnaryFrameSym)
  | outputDone
deriving DecidableEq, Fintype, Inhabited

/-- Combined stack bank: both transducers plus two scratch stacks. -/
abbrev K := Sum (Sum M₁.tm.K M₂.tm.K) ExtraK

/-- Dependent alphabet of every combined stack. -/
abbrev StackAlphabet : K M₁ M₂ → Type
  | Sum.inl (Sum.inl k₁) => M₁.tm.Γ k₁
  | Sum.inl (Sum.inr k₂) => M₂.tm.Γ k₂
  | Sum.inr ExtraK.inputTemp => Γ
  | Sum.inr ExtraK.outputTemp => UnaryFrameSym

/-- Combined program labels and state. -/
abbrev Λ := Sum (Sum M₁.tm.Λ M₂.tm.Λ) ExtraΛ
abbrev σ := M₁.tm.σ × M₂.tm.σ × ExtraState Γ

abbrev inputK : K M₁ M₂ := Sum.inl (Sum.inl M₁.tm.k₀)
abbrev secondInputK : K M₁ M₂ := Sum.inl (Sum.inr M₂.tm.k₀)
abbrev firstOutputK : K M₁ M₂ := Sum.inl (Sum.inl M₁.tm.k₁)
abbrev outputK : K M₁ M₂ := Sum.inl (Sum.inr M₂.tm.k₁)
abbrev inputTempK : K M₁ M₂ := Sum.inr ExtraK.inputTemp
abbrev outputTempK : K M₁ M₂ := Sum.inr ExtraK.outputTemp

def kDecidableEq : DecidableEq (K M₁ M₂) := by
  letI : DecidableEq M₁.tm.K := M₁.tm.kDecidableEq
  letI : DecidableEq M₂.tm.K := M₂.tm.kDecidableEq
  infer_instance

def kFintype : Fintype (K M₁ M₂) := by
  letI : Fintype M₁.tm.K := M₁.tm.kFin
  letI : Fintype M₂.tm.K := M₂.tm.kFin
  infer_instance

def labelFintype : Fintype (Λ M₁ M₂) := by
  letI : Fintype M₁.tm.Λ := M₁.tm.ΛFin
  letI : Fintype M₂.tm.Λ := M₂.tm.ΛFin
  infer_instance

def stateFintype : Fintype (σ M₁ M₂) := by
  letI : Fintype M₁.tm.σ := M₁.tm.σFin
  letI : Fintype M₂.tm.σ := M₂.tm.σFin
  infer_instance

def inputAlphabetFintype :
    Fintype (StackAlphabet M₁ M₂ (inputK M₁ M₂)) :=
  M₁.tm.Γk₀Fin

instance kInst : DecidableEq (K M₁ M₂) := kDecidableEq M₁ M₂
instance kFinInst : Fintype (K M₁ M₂) := kFintype M₁ M₂

/-- Embed the first transducer's program.  Halting starts the second
transducer. -/
def mapStmt₁ :
    _root_.Turing.TM2.Stmt M₁.tm.Γ M₁.tm.Λ M₁.tm.σ →
      _root_.Turing.TM2.Stmt (StackAlphabet M₁ M₂) (Λ M₁ M₂) (σ M₁ M₂)
  | .push k f q =>
      .push (Sum.inl (Sum.inl k)) (fun state => f state.1)
        (mapStmt₁ q)
  | .peek k f q =>
      .peek (Sum.inl (Sum.inl k))
        (fun state value => (f state.1 value, state.2.1, state.2.2))
        (mapStmt₁ q)
  | .pop k f q =>
      .pop (Sum.inl (Sum.inl k))
        (fun state value => (f state.1 value, state.2.1, state.2.2))
        (mapStmt₁ q)
  | .load f q =>
      .load (fun state => (f state.1, state.2.1, state.2.2))
        (mapStmt₁ q)
  | .branch f q₁ q₂ =>
      .branch (fun state => f state.1) (mapStmt₁ q₁) (mapStmt₁ q₂)
  | .goto f => .goto (fun state => Sum.inl (Sum.inl (f state.1)))
  | .halt => .goto (fun _ => Sum.inl (Sum.inr M₂.tm.main))

/-- Embed the second transducer's program.  Halting starts physical row
interleaving. -/
def mapStmt₂ :
    _root_.Turing.TM2.Stmt M₂.tm.Γ M₂.tm.Λ M₂.tm.σ →
      _root_.Turing.TM2.Stmt (StackAlphabet M₁ M₂) (Λ M₁ M₂) (σ M₁ M₂)
  | .push k f q =>
      .push (Sum.inl (Sum.inr k)) (fun state => f state.2.1)
        (mapStmt₂ q)
  | .peek k f q =>
      .peek (Sum.inl (Sum.inr k))
        (fun state value => (state.1, f state.2.1 value, state.2.2))
        (mapStmt₂ q)
  | .pop k f q =>
      .pop (Sum.inl (Sum.inr k))
        (fun state value => (state.1, f state.2.1 value, state.2.2))
        (mapStmt₂ q)
  | .load f q =>
      .load (fun state => (state.1, f state.2.1, state.2.2))
        (mapStmt₂ q)
  | .branch f q₁ q₂ =>
      .branch (fun state => f state.2.1) (mapStmt₂ q₁) (mapStmt₂ q₂)
  | .goto f => .goto (fun state => Sum.inl (Sum.inr (f state.2.1)))
  | .halt => .goto (fun _ => Sum.inr ExtraΛ.mergeLeft)

private def inputDefault [Inhabited Γ] :
    Inhabited (M₁.tm.Γ M₁.tm.k₀) :=
  ⟨M₁.inputAlphabet.invFun default⟩

private def secondInputDefault [Inhabited Γ] :
    Inhabited (M₂.tm.Γ M₂.tm.k₀) :=
  ⟨M₂.inputAlphabet.invFun default⟩

private def outputDefault : Inhabited (M₂.tm.Γ M₂.tm.k₁) :=
  ⟨M₂.outputAlphabet.invFun .frameEnd⟩

/-- Extra program implementing duplication, alternating row transfer, and
final output restoration. -/
def extraProgram : ExtraΛ →
    _root_.Turing.TM2.Stmt (StackAlphabet M₁ M₂) (Λ M₁ M₂) (σ M₁ M₂) := by
  classical
  exact fun label =>
    letI : Inhabited (M₂.tm.Γ M₂.tm.k₁) := outputDefault M₂
    match label with
    | .duplicateScan =>
        if h : Nonempty Γ then
          letI : Inhabited Γ := ⟨Classical.choice h⟩
          .pop (inputK M₁ M₂)
            (fun state value => (state.1, state.2.1,
              match value with
              | some symbol => .duplicateSymbol (M₁.inputAlphabet symbol)
              | none => .duplicateDone))
            (.branch
              (fun state => match state.2.2 with
                | .duplicateSymbol _ => true
                | _ => false)
              (.push (inputTempK M₁ M₂)
                (fun state => match state.2.2 with
                  | .duplicateSymbol symbol => symbol
                  | _ => default)
                (.goto fun _ => Sum.inr .duplicateScan))
              (.goto fun _ => Sum.inr .duplicateRestore))
        else
          .pop (inputK M₁ M₂)
            (fun state value => (state.1, state.2.1,
              match value with
              | some symbol => .duplicateSymbol (M₁.inputAlphabet symbol)
              | none => .duplicateDone))
            (.goto fun _ => Sum.inr .duplicateRestore)
    | .duplicateRestore =>
        if h : Nonempty Γ then
          letI : Inhabited Γ := ⟨Classical.choice h⟩
          letI : Inhabited (M₁.tm.Γ M₁.tm.k₀) := inputDefault M₁
          letI : Inhabited (M₂.tm.Γ M₂.tm.k₀) := secondInputDefault M₂
          .pop (inputTempK M₁ M₂)
            (fun state value => (state.1, state.2.1,
              match value with
              | some symbol => .restoreSymbol symbol
              | none => .restoreDone))
            (.branch
              (fun state => match state.2.2 with
                | .restoreSymbol _ => true
                | _ => false)
              (.push (inputK M₁ M₂)
                (fun state => match state.2.2 with
                  | .restoreSymbol symbol => M₁.inputAlphabet.invFun symbol
                  | _ => default)
                (.push (secondInputK M₁ M₂)
                  (fun state => match state.2.2 with
                    | .restoreSymbol symbol => M₂.inputAlphabet.invFun symbol
                    | _ => default)
                  (.goto fun _ => Sum.inr .duplicateRestore)))
              (.load
                (fun _ => (M₁.tm.initialState, M₂.tm.initialState,
                  ExtraState.initial))
                (.goto fun _ => Sum.inl (Sum.inl M₁.tm.main))))
        else
          .pop (inputTempK M₁ M₂)
            (fun state value => (state.1, state.2.1,
              match value with
              | some symbol => .restoreSymbol symbol
              | none => .restoreDone))
            (.load
              (fun _ => (M₁.tm.initialState, M₂.tm.initialState,
                ExtraState.initial))
              (.goto fun _ => Sum.inl (Sum.inl M₁.tm.main)))
    | .mergeLeft =>
        .pop (firstOutputK M₁ M₂)
          (fun state value => (state.1, state.2.1,
            match value with
            | some symbol => .mergeSymbol (M₁.outputAlphabet symbol)
            | none => .mergeDone))
          (.branch
            (fun state => match state.2.2 with
              | .mergeSymbol _ => true
              | _ => false)
            (.push (outputTempK M₁ M₂)
              (fun state => match state.2.2 with
                | .mergeSymbol symbol => symbol
                | _ => .frameEnd)
              (.branch
                (fun state => match state.2.2 with
                  | .mergeSymbol .frameEnd => true
                  | _ => false)
                (.goto fun _ => Sum.inr .mergeRight)
                (.goto fun _ => Sum.inr .mergeLeft)))
            (.goto fun _ => Sum.inr .outputRestore))
    | .mergeRight =>
        .pop (outputK M₁ M₂)
          (fun state value => (state.1, state.2.1,
            match value with
            | some symbol => .mergeSymbol (M₂.outputAlphabet symbol)
            | none => .mergeDone))
          (.branch
            (fun state => match state.2.2 with
              | .mergeSymbol _ => true
              | _ => false)
            (.push (outputTempK M₁ M₂)
              (fun state => match state.2.2 with
                | .mergeSymbol symbol => symbol
                | _ => .frameEnd)
              (.branch
                (fun state => match state.2.2 with
                  | .mergeSymbol .frameEnd => true
                  | _ => false)
                (.goto fun _ => Sum.inr .mergeLeft)
                (.goto fun _ => Sum.inr .mergeRight)))
            (.goto fun _ => Sum.inr .outputRestore))
    | .outputRestore =>
        .pop (outputTempK M₁ M₂)
          (fun state value => (state.1, state.2.1,
            match value with
            | some symbol => .outputSymbol symbol
            | none => .outputDone))
          (.branch
            (fun state => match state.2.2 with
              | .outputSymbol _ => true
              | _ => false)
            (.push (outputK M₁ M₂)
              (fun state => match state.2.2 with
                | .outputSymbol symbol => M₂.outputAlphabet.invFun symbol
                | _ => default)
              (.goto fun _ => Sum.inr .outputRestore))
            (.load
              (fun _ => (M₁.tm.initialState, M₂.tm.initialState,
                ExtraState.initial))
              .halt))

def program : Λ M₁ M₂ →
    _root_.Turing.TM2.Stmt (StackAlphabet M₁ M₂) (Λ M₁ M₂) (σ M₁ M₂)
  | Sum.inl (Sum.inl label) => mapStmt₁ M₁ M₂ (M₁.tm.m label)
  | Sum.inl (Sum.inr label) => mapStmt₂ M₁ M₂ (M₂.tm.m label)
  | Sum.inr label => extraProgram M₁ M₂ label

/-- The bundled same-input row-interleaving machine. -/
abbrev machine : _root_.Turing.FinTM2 :=
  @_root_.Turing.FinTM2.mk (K M₁ M₂) (kDecidableEq M₁ M₂)
    (kFintype M₁ M₂) (inputK M₁ M₂) (outputK M₁ M₂)
    (StackAlphabet M₁ M₂) (Λ M₁ M₂)
    (Sum.inr ExtraΛ.duplicateScan) (labelFintype M₁ M₂) (σ M₁ M₂)
    (M₁.tm.initialState, M₂.tm.initialState, ExtraState.initial)
    (stateFintype M₁ M₂) (inputAlphabetFintype M₁ M₂) (program M₁ M₂)

def inputAlphabet : (machine M₁ M₂).Γ (machine M₁ M₂).k₀ ≃ Γ :=
  M₁.inputAlphabet

def outputAlphabet :
    (machine M₁ M₂).Γ (machine M₁ M₂).k₁ ≃ UnaryFrameSym :=
  M₂.outputAlphabet

/-- Embed both transducer stack banks and keep both scratch stacks empty. -/
def combinedStacks
    (first : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
    (second : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)) :
    ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)
  | Sum.inl (Sum.inl k) => first k
  | Sum.inl (Sum.inr k) => second k
  | Sum.inr ExtraK.inputTemp => []
  | Sum.inr ExtraK.outputTemp => []

/-- First-machine configurations embedded while the second input is frozen. -/
def mapCfg₁
    (cfg : _root_.Turing.TM2.Cfg M₁.tm.Γ M₁.tm.Λ M₁.tm.σ)
    (second : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)) :
    (machine M₁ M₂).Cfg :=
  { l := match cfg.l with
      | some label => some (Sum.inl (Sum.inl label))
      | none => some (Sum.inl (Sum.inr M₂.tm.main))
    var := (cfg.var, M₂.tm.initialState, ExtraState.initial)
    stk := combinedStacks M₁ M₂ cfg.stk second }

/-- Second-machine configurations embedded while the first result is frozen.
-/
def mapCfg₂
    (cfg : _root_.Turing.TM2.Cfg M₂.tm.Γ M₂.tm.Λ M₂.tm.σ)
    (first : ∀ k : M₁.tm.K, List (M₁.tm.Γ k)) :
    (machine M₁ M₂).Cfg :=
  { l := match cfg.l with
      | some label => some (Sum.inl (Sum.inr label))
      | none => some (Sum.inr ExtraΛ.mergeLeft)
    var := (M₁.tm.initialState, cfg.var, ExtraState.initial)
    stk := combinedStacks M₁ M₂ first cfg.stk }

end UnaryFrameMarkedRowParallelInterleave

end CLRS.Chapter34.Turing.PolyBuilder
