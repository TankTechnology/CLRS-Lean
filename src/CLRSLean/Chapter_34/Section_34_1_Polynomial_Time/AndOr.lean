import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Parallel decision of two polynomial-time deciders (AND/OR combine)

A TM2 machine computing `x ↦ [op (f₁ x) (f₂ x)]` for two polynomial-time
decision functions `f₁`, `f₂` and `op ∈ {and, or}`.  This is the construction
behind the closure of the complexity class **P** under union and intersection
(CLRS §34.1).

Main results:

- Construction `andOrMachine`: four phases — `dupScan`/`dupRestore` duplicate
  the input onto both deciders' input stacks; phase 1 runs `M₁`'s program,
  phase 2 runs `M₂`'s program; `combine` pops the two `Bool` results and pushes
  `op b₁ b₂` onto the output stack.
- Simulations `step₁_sim`/`step₂_sim` and transports `evalsTo_lift`.
- Configuration bridges `mapCfg₁to₂` and `combine_step`.
- Time bound `andOrTime`.
- Theorems `andOrComputableInPolyTime`: `(op ∘ (f₁, f₂))` is polytime.

Design (duplicate-then-sequential, shared output stack):

- Stacks `Sum (Sum K₁ K₂) dupTemp`: `inl (inl k₁)` are `M₁`'s stacks,
  `inl (inr k₂)` are `M₂`'s stacks, `inr dupTemp` is a scratch stack of type
  `Γ` used to duplicate the input.
- Phase 0 duplicates the input `x` from `inl (inl M₁.k₀)` onto
  `inl (inr M₂.k₀)` (via `inr dupTemp`, a LIFO double pass).
- Phase 1 runs `M₁`'s program (`mapStmt₁`); `halt` becomes `goto` into `M₂`'s
  main.  `M₂`'s stacks are frozen at the duplicated input.
- Phase 2 runs `M₂`'s program (`mapStmt₂`); `halt` becomes `goto` into the
  `combine` label.  `M₁`'s stacks are frozen at their post-phase-1 values.
- Phase 3 (`combine`) pops `b₁` from `inl (inl M₁.k₁)` and `b₂` from
  `inl (inr M₂.k₁)`, pushes `op b₁ b₂` (via `M₂.outputAlphabet`) onto
  `inl (inr M₂.k₁)` — which is the combined output stack — resets the state
  and halts.

Because both deciders halt in the `haltList` configuration, the frozen halves
are exactly the `haltList`/`initList` stacks, so the bridges are equalities of
configurations.

Time bound: phase 0 takes `2|x| + 2` steps, phase 3 takes `1` step, so
`andOrTime := M₁.time + M₂.time + (2 * Polynomial.X + 3)`.
-/

noncomputable section

open Computability StateTransition

namespace Turing

namespace TM2AndOr

variable {α Γ : Type} [Fintype Γ] [Inhabited Γ]
variable {encode : α → List Γ} {f₁ f₂ : α → Bool}
variable (M₁ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₁)
variable (M₂ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₂)

/-- The extra stack: a scratch used to duplicate the input. -/
inductive AndOrExtraK : Type
  | dupTemp
deriving DecidableEq, Fintype, Inhabited

/-- The extra labels: the duplicate phase (scan + two restore steps) and the
combine phase. -/
inductive AndOrExtraΛ : Type
  | dupScan
  | dupRestore
  | dupRestore₂
  | combine
deriving DecidableEq, Fintype, Inhabited

/-- The extra state, carrying the symbol being copied or the two Boolean
results being combined. -/
inductive AndOrSt (Γ : Type) : Type
  | initial
  | dupSym (a : Γ)
  | dupDone
  | restSym (a : Γ)
  | restDone
  | comb₁ (b₁ : Bool)
  | comb₂ (b₁ b₂ : Bool)
deriving DecidableEq, Fintype, Inhabited

/-- Combined stack index type: `M₁`'s stacks, `M₂`'s stacks, and the scratch. -/
abbrev AndOrK := Sum (Sum M₁.tm.K M₂.tm.K) AndOrExtraK

/-- Combined stack types. -/
abbrev AndOrΓ : AndOrK M₁ M₂ → Type
  | Sum.inl (Sum.inl k₁) => M₁.tm.Γ k₁
  | Sum.inl (Sum.inr k₂) => M₂.tm.Γ k₂
  | Sum.inr AndOrExtraK.dupTemp => Γ

/-- Combined label type. -/
abbrev AndOrΛ := Sum (Sum M₁.tm.Λ M₂.tm.Λ) AndOrExtraΛ

/-- Combined state: `M₁`'s, `M₂`'s, and the extra state. -/
abbrev AndOrσ := M₁.tm.σ × M₂.tm.σ × AndOrSt Γ

/-- `M₁`'s input stack (also the combined input stack). -/
abbrev inK {M₁ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₁}
    {M₂ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₂} : AndOrK M₁ M₂ :=
  Sum.inl (Sum.inl M₁.tm.k₀)

/-- `M₂`'s input stack (holds the duplicated copy of the input). -/
abbrev in2K {M₁ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₁}
    {M₂ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₂} : AndOrK M₁ M₂ :=
  Sum.inl (Sum.inr M₂.tm.k₀)

/-- The combined output stack: `M₂`'s output stack. -/
abbrev outK {M₁ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₁}
    {M₂ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₂} : AndOrK M₁ M₂ :=
  Sum.inl (Sum.inr M₂.tm.k₁)

/-- The scratch stack, holding `Γ` elements. -/
abbrev tmpK {M₁ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₁}
    {M₂ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₂} : AndOrK M₁ M₂ :=
  Sum.inr AndOrExtraK.dupTemp

/-- The combined index type is decidable. -/
def andOrKDecidableEq : DecidableEq (AndOrK M₁ M₂) := by
  letI : DecidableEq M₁.tm.K := M₁.tm.kDecidableEq
  letI : DecidableEq M₂.tm.K := M₂.tm.kDecidableEq
  infer_instance

/-- The combined index type is finite. -/
def andOrKFintype : Fintype (AndOrK M₁ M₂) := by
  letI : Fintype M₁.tm.K := M₁.tm.kFin
  letI : Fintype M₂.tm.K := M₂.tm.kFin
  infer_instance

/-- The combined label type is finite. -/
def andOrΛFintype : Fintype (AndOrΛ M₁ M₂) := by
  letI : Fintype M₁.tm.Λ := M₁.tm.ΛFin
  letI : Fintype M₂.tm.Λ := M₂.tm.ΛFin
  infer_instance

/-- The combined state type is finite. -/
def andOrσFintype : Fintype (AndOrσ M₁ M₂) := by
  letI : Fintype M₁.tm.σ := M₁.tm.σFin
  letI : Fintype M₂.tm.σ := M₂.tm.σFin
  infer_instance

/-- The combined input alphabet is finite. -/
def andOrΓk₀Fintype : Fintype (AndOrΓ M₁ M₂ inK) :=
  M₁.tm.Γk₀Fin

instance andOrKInst (M₁ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₁)
    (M₂ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₂) :
    DecidableEq (AndOrK M₁ M₂) :=
  andOrKDecidableEq M₁ M₂

instance andOrKFinInst (M₁ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₁)
    (M₂ : TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding f₂) :
    Fintype (AndOrK M₁ M₂) :=
  andOrKFintype M₁ M₂

/-- Translate `M₁`'s program to the combined machine.  `halt` jumps into
`M₂`'s main.  The `σ₂` and extra components are frozen. -/
def mapStmt₁ : TM2.Stmt M₁.tm.Γ M₁.tm.Λ M₁.tm.σ →
    TM2.Stmt (AndOrΓ M₁ M₂) (AndOrΛ M₁ M₂) (AndOrσ M₁ M₂)
  | TM2.Stmt.push k f q => TM2.Stmt.push (Sum.inl (Sum.inl k)) (fun v => f v.1) (mapStmt₁ q)
  | TM2.Stmt.peek k f q =>
      TM2.Stmt.peek (Sum.inl (Sum.inl k)) (fun v x => (f v.1 x, v.2.1, v.2.2)) (mapStmt₁ q)
  | TM2.Stmt.pop k f q =>
      TM2.Stmt.pop (Sum.inl (Sum.inl k)) (fun v x => (f v.1 x, v.2.1, v.2.2)) (mapStmt₁ q)
  | TM2.Stmt.load f q => TM2.Stmt.load (fun v => (f v.1, v.2.1, v.2.2)) (mapStmt₁ q)
  | TM2.Stmt.branch f q₁ q₂ =>
      TM2.Stmt.branch (fun v => f v.1) (mapStmt₁ q₁) (mapStmt₁ q₂)
  | TM2.Stmt.goto f => TM2.Stmt.goto (fun v => Sum.inl (Sum.inl (f v.1)))
  | TM2.Stmt.halt => TM2.Stmt.goto (fun _ => Sum.inl (Sum.inr M₂.tm.main))

/-- Translate `M₂`'s program to the combined machine.  `halt` jumps into the
`combine` label.  The `σ₁` and extra components are frozen. -/
def mapStmt₂ : TM2.Stmt M₂.tm.Γ M₂.tm.Λ M₂.tm.σ →
    TM2.Stmt (AndOrΓ M₁ M₂) (AndOrΛ M₁ M₂) (AndOrσ M₁ M₂)
  | TM2.Stmt.push k f q => TM2.Stmt.push (Sum.inl (Sum.inr k)) (fun v => f v.2.1) (mapStmt₂ q)
  | TM2.Stmt.peek k f q =>
      TM2.Stmt.peek (Sum.inl (Sum.inr k)) (fun v x => (v.1, f v.2.1 x, v.2.2)) (mapStmt₂ q)
  | TM2.Stmt.pop k f q =>
      TM2.Stmt.pop (Sum.inl (Sum.inr k)) (fun v x => (v.1, f v.2.1 x, v.2.2)) (mapStmt₂ q)
  | TM2.Stmt.load f q => TM2.Stmt.load (fun v => (v.1, f v.2.1, v.2.2)) (mapStmt₂ q)
  | TM2.Stmt.branch f q₁ q₂ =>
      TM2.Stmt.branch (fun v => f v.2.1) (mapStmt₂ q₁) (mapStmt₂ q₂)
  | TM2.Stmt.goto f => TM2.Stmt.goto (fun v => Sum.inl (Sum.inr (f v.2.1)))
  | TM2.Stmt.halt => TM2.Stmt.goto (fun _ => Sum.inr AndOrExtraΛ.combine)

/-- Inhabited instances for the stack alphabets, derived from `Inhabited Γ` and
`Inhabited Bool` through the machine alphabets (for the `default` fallthroughs
in the extra program). -/
def inh₁ : Inhabited (M₁.tm.Γ M₁.tm.k₀) :=
  ⟨M₁.inputAlphabet.invFun (default : Γ)⟩

def inh₂₀ : Inhabited (M₂.tm.Γ M₂.tm.k₀) :=
  ⟨M₂.inputAlphabet.invFun (default : Γ)⟩

def inh₂₁ : Inhabited (M₂.tm.Γ M₂.tm.k₁) :=
  ⟨M₂.outputAlphabet.invFun false⟩

/-- The extra program: the duplicate phase and the combine phase.  Every
`pop`'s continuation carries the rest of the work, so each phase takes one
machine step per symbol (plus a final empty-pop step). -/
def extraProgram (op : Bool → Bool → Bool) : AndOrExtraΛ →
    TM2.Stmt (AndOrΓ M₁ M₂) (AndOrΛ M₁ M₂) (AndOrσ M₁ M₂) :=
  fun l =>
    letI : Inhabited (M₁.tm.Γ M₁.tm.k₀) := inh₁ M₁
    letI : Inhabited (M₂.tm.Γ M₂.tm.k₀) := inh₂₀ M₂
    letI : Inhabited (M₂.tm.Γ M₂.tm.k₁) := inh₂₁ M₂
    match l with
    | AndOrExtraΛ.dupScan =>
        TM2.Stmt.pop inK (fun v x => (v.1, v.2.1,
          match x with
          | some a => AndOrSt.dupSym (M₁.inputAlphabet a)
          | none => AndOrSt.dupDone))
          (TM2.Stmt.branch (fun v => match v.2.2 with | AndOrSt.dupSym _ => true | _ => false)
            (TM2.Stmt.push tmpK (fun v => match v.2.2 with | AndOrSt.dupSym a => a | _ => default)
              (TM2.Stmt.goto (fun _ => Sum.inr AndOrExtraΛ.dupScan)))
            (TM2.Stmt.goto (fun _ => Sum.inr AndOrExtraΛ.dupRestore)))
    | AndOrExtraΛ.dupRestore =>
        TM2.Stmt.pop tmpK (fun v x => (v.1, v.2.1,
          match x with
          | some a => AndOrSt.restSym a
          | none => AndOrSt.restDone))
          (TM2.Stmt.branch (fun v => match v.2.2 with | AndOrSt.restSym _ => true | _ => false)
            (TM2.Stmt.push inK (fun v => match v.2.2 with | AndOrSt.restSym a => M₁.inputAlphabet.invFun a | _ => default)
              (TM2.Stmt.push in2K (fun v => match v.2.2 with | AndOrSt.restSym a => M₂.inputAlphabet.invFun a | _ => default)
                (TM2.Stmt.goto (fun _ => Sum.inr AndOrExtraΛ.dupRestore))))
            (TM2.Stmt.load (fun _ => (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.initial))
              (TM2.Stmt.goto (fun _ => Sum.inl (Sum.inl M₁.tm.main)))))
    | AndOrExtraΛ.dupRestore₂ =>
        TM2.Stmt.push in2K (fun v => match v.2.2 with | AndOrSt.restSym a => M₂.inputAlphabet.invFun a | _ => default)
          (TM2.Stmt.goto (fun _ => Sum.inr AndOrExtraΛ.dupRestore))
    | AndOrExtraΛ.combine =>
        TM2.Stmt.pop (Sum.inl (Sum.inl M₁.tm.k₁)) (fun v x => (v.1, v.2.1,
          match x with
          | some b₁ => AndOrSt.comb₁ (M₁.outputAlphabet b₁)
          | none => AndOrSt.comb₁ false))
          (TM2.Stmt.pop (Sum.inl (Sum.inr M₂.tm.k₁)) (fun v x => (v.1, v.2.1,
            match v.2.2, x with
            | AndOrSt.comb₁ b₁, some b₂ => AndOrSt.comb₂ b₁ (M₂.outputAlphabet b₂)
            | _, _ => AndOrSt.comb₂ false false))
            (TM2.Stmt.push (Sum.inl (Sum.inr M₂.tm.k₁)) (fun v =>
                match v.2.2 with
                | AndOrSt.comb₂ b₁ b₂ => M₂.outputAlphabet.invFun (op b₁ b₂)
                | _ => default)
              (TM2.Stmt.load (fun _ => (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.initial))
                TM2.Stmt.halt)))

/-- The combined program. -/
def andOrProgram (op : Bool → Bool → Bool) : AndOrΛ M₁ M₂ →
    TM2.Stmt (AndOrΓ M₁ M₂) (AndOrΛ M₁ M₂) (AndOrσ M₁ M₂)
  | Sum.inl (Sum.inl l₁) => mapStmt₁ M₁ M₂ (M₁.tm.m l₁)
  | Sum.inl (Sum.inr l₂) => mapStmt₂ M₁ M₂ (M₂.tm.m l₂)
  | Sum.inr extra => extraProgram M₁ M₂ op extra

/-- The combined bundled machine. -/
abbrev andOrMachine (op : Bool → Bool → Bool) : FinTM2 :=
  @FinTM2.mk (AndOrK M₁ M₂) (andOrKDecidableEq M₁ M₂) (andOrKFintype M₁ M₂)
    inK outK (AndOrΓ M₁ M₂) (AndOrΛ M₁ M₂) (Sum.inr AndOrExtraΛ.dupScan)
    (andOrΛFintype M₁ M₂) (AndOrσ M₁ M₂)
    (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.initial)
    (andOrσFintype M₁ M₂) (andOrΓk₀Fintype M₁ M₂) (andOrProgram M₁ M₂ op)

/-- The combined input alphabet: `M₁`'s. -/
def andOrInputAlphabet : (andOrMachine M₁ M₂ op).Γ (andOrMachine M₁ M₂ op).k₀ ≃ Γ :=
  M₁.inputAlphabet

/-- The combined output alphabet: `M₂`'s. -/
def andOrOutputAlphabet : (andOrMachine M₁ M₂ op).Γ (andOrMachine M₁ M₂ op).k₁ ≃ Bool :=
  M₂.outputAlphabet

/-- The duplicated copy of the input on `M₂`'s input stack. -/
def dupInput (x : List Γ) : ∀ k : M₂.tm.K, List (M₂.tm.Γ k) :=
  (initList M₂.tm (List.map M₂.inputAlphabet.invFun x)).stk

/-- `M₁`'s stacks frozen after phase 1: the `haltList` stacks for output `[f₁ x]`. -/
def halt₁stk (x : α) : ∀ k : M₁.tm.K, List (M₁.tm.Γ k) :=
  (haltList M₁.tm (List.map M₁.outputAlphabet.invFun [f₁ x])).stk

/-- Embedding both machines' stacks in the combined machine. -/
def stk (S₁ : ∀ k : M₁.tm.K, List (M₁.tm.Γ k)) (S₂ : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)) :
    ∀ k : AndOrK M₁ M₂, List (AndOrΓ M₁ M₂ k) :=
  fun k => match k with
  | Sum.inl (Sum.inl k₁) => S₁ k₁
  | Sum.inl (Sum.inr k₂) => S₂ k₂
  | Sum.inr AndOrExtraK.dupTemp => []

/-- `M₁`'s configurations embedded in the combined machine (phase 1).  The
halted configuration of `M₁` maps to the start of phase 2. -/
def mapCfg₁ (c₁ : TM2.Cfg M₁.tm.Γ M₁.tm.Λ M₁.tm.σ)
    (S₂ : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)) :
    TM2.Cfg (AndOrΓ M₁ M₂) (AndOrΛ M₁ M₂) (AndOrσ M₁ M₂) :=
  { l := match c₁.l with
      | some l₁ => some (Sum.inl (Sum.inl l₁))
      | none => some (Sum.inl (Sum.inr M₂.tm.main))
    var := (c₁.var, M₂.tm.initialState, AndOrSt.initial)
    stk := stk M₁ M₂ c₁.stk S₂ }

/-- `M₂`'s configurations embedded in the combined machine (phase 2).  The
halted configuration of `M₂` maps to the `combine` label. -/
def mapCfg₂ (c₂ : TM2.Cfg M₂.tm.Γ M₂.tm.Λ M₂.tm.σ)
    (S₁ : ∀ k : M₁.tm.K, List (M₁.tm.Γ k)) :
    TM2.Cfg (AndOrΓ M₁ M₂) (AndOrΛ M₁ M₂) (AndOrσ M₁ M₂) :=
  { l := match c₂.l with
      | some l₂ => some (Sum.inl (Sum.inr l₂))
      | none => some (Sum.inr AndOrExtraΛ.combine)
    var := (M₁.tm.initialState, c₂.var, AndOrSt.initial)
    stk := stk M₁ M₂ S₁ c₂.stk }

/-- Updating `M₁`'s stack `k` commutes with the embedding. -/
lemma update_stk₁ (S₁ : ∀ k : M₁.tm.K, List (M₁.tm.Γ k)) (S₂ : ∀ k : M₂.tm.K, List (M₂.tm.Γ k))
    (k : M₁.tm.K) (L : List (M₁.tm.Γ k)) :
    Function.update (stk M₁ M₂ S₁ S₂) (Sum.inl (Sum.inl k)) L = stk M₁ M₂ (Function.update S₁ k L) S₂ := by
  funext k'
  cases k' with
  | inl k₁ =>
      cases k₁ with
      | inl k₁' =>
          by_cases h : k₁' = k
          · subst k₁'
            simp [stk, Function.update]
          · simp [stk, Function.update, h]
      | inr k₂' =>
          simp [stk, Function.update]
  | inr AndOrExtraK.dupTemp =>
      simp [stk, Function.update]

/-- Updating `M₂`'s stack `k` commutes with the embedding. -/
lemma update_stk₂ (S₁ : ∀ k : M₁.tm.K, List (M₁.tm.Γ k)) (S₂ : ∀ k : M₂.tm.K, List (M₂.tm.Γ k))
    (k : M₂.tm.K) (L : List (M₂.tm.Γ k)) :
    Function.update (stk M₁ M₂ S₁ S₂) (Sum.inl (Sum.inr k)) L = stk M₁ M₂ S₁ (Function.update S₂ k L) := by
  funext k'
  cases k' with
  | inl k₁ =>
      cases k₁ with
      | inl k₁' =>
          simp [stk, Function.update]
      | inr k₂' =>
          by_cases h : k₂' = k
          · subst k₂'
            simp [stk, Function.update]
          · simp [stk, Function.update, h]
  | inr AndOrExtraK.dupTemp =>
      simp [stk, Function.update]

/-- Executing `mapStmt₁ s` from the phase-1 state mirrors executing `s` in `M₁`. -/
lemma stepAux_mapStmt₁ (s : TM2.Stmt M₁.tm.Γ M₁.tm.Λ M₁.tm.σ) :
    ∀ (v : M₁.tm.σ) (S₁ : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
      (S₂ : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)),
      TM2.stepAux (mapStmt₁ M₁ M₂ s) (v, M₂.tm.initialState, AndOrSt.initial) (stk M₁ M₂ S₁ S₂)
        = mapCfg₁ M₁ M₂ (TM2.stepAux s v S₁) S₂ := by
  induction s with
  | push k f q ih =>
      intro v S₁ S₂
      simp [mapStmt₁, stk, TM2.stepAux]
      rw [update_stk₁ M₁ M₂ S₁ S₂ k (f v :: S₁ k)]
      exact ih v (Function.update S₁ k (f v :: S₁ k)) S₂
  | peek k f q ih =>
      intro v S₁ S₂
      simp [mapStmt₁, stk, TM2.stepAux]
      exact ih (f v (S₁ k).head?) S₁ S₂
  | pop k f q ih =>
      intro v S₁ S₂
      simp [mapStmt₁, stk, TM2.stepAux]
      rw [update_stk₁ M₁ M₂ S₁ S₂ k (S₁ k).tail]
      exact ih (f v (S₁ k).head?) (Function.update S₁ k (S₁ k).tail) S₂
  | load f q ih =>
      intro v S₁ S₂
      simp [mapStmt₁, TM2.stepAux]
      exact ih (f v) S₁ S₂
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v S₁ S₂
      simp [mapStmt₁, TM2.stepAux]
      by_cases h : f v <;> simp [h, ih₁ v S₁ S₂, ih₂ v S₁ S₂]
  | goto f =>
      intro v S₁ S₂
      simp [mapStmt₁, TM2.stepAux, mapCfg₁]
  | halt =>
      intro v S₁ S₂
      simp [mapStmt₁, TM2.stepAux, mapCfg₁]

/-- Executing `mapStmt₂ s` from the phase-2 state mirrors executing `s` in `M₂`. -/
lemma stepAux_mapStmt₂ (s : TM2.Stmt M₂.tm.Γ M₂.tm.Λ M₂.tm.σ) :
    ∀ (v : M₂.tm.σ) (S₁ : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
      (S₂ : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)),
      TM2.stepAux (mapStmt₂ M₁ M₂ s) (M₁.tm.initialState, v, AndOrSt.initial) (stk M₁ M₂ S₁ S₂)
        = mapCfg₂ M₁ M₂ (TM2.stepAux s v S₂) S₁ := by
  induction s with
  | push k f q ih =>
      intro v S₁ S₂
      simp [mapStmt₂, stk, TM2.stepAux]
      rw [update_stk₂ M₁ M₂ S₁ S₂ k (f v :: S₂ k)]
      exact ih v S₁ (Function.update S₂ k (f v :: S₂ k))
  | peek k f q ih =>
      intro v S₁ S₂
      simp [mapStmt₂, stk, TM2.stepAux]
      exact ih (f v (S₂ k).head?) S₁ S₂
  | pop k f q ih =>
      intro v S₁ S₂
      simp [mapStmt₂, stk, TM2.stepAux]
      rw [update_stk₂ M₁ M₂ S₁ S₂ k (S₂ k).tail]
      exact ih (f v (S₂ k).head?) S₁ (Function.update S₂ k (S₂ k).tail)
  | load f q ih =>
      intro v S₁ S₂
      simp [mapStmt₂, TM2.stepAux]
      exact ih (f v) S₁ S₂
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v S₁ S₂
      simp [mapStmt₂, TM2.stepAux]
      by_cases h : f v <;> simp [h, ih₁ v S₁ S₂, ih₂ v S₁ S₂]
  | goto f =>
      intro v S₁ S₂
      simp [mapStmt₂, TM2.stepAux, mapCfg₂]
  | halt =>
      intro v S₁ S₂
      simp [mapStmt₂, TM2.stepAux, mapCfg₂]

/-- `M₁`'s step is non-`none` exactly on non-halted configurations. -/
lemma step₁_ne_iff (c₁ : TM2.Cfg M₁.tm.Γ M₁.tm.Λ M₁.tm.σ) :
    M₁.tm.step c₁ ≠ none ↔ c₁.l ≠ none := by
  constructor
  · intro h hcl
    rcases c₁ with ⟨l, v, S⟩
    cases l
    · simp [TM2.step] at h
      exact h rfl
    · cases hcl
  · intro hcl
    rcases c₁ with ⟨l, v, S⟩
    cases l
    · exact (hcl rfl).elim
    · simp [TM2.step]

/-- `M₂`'s step is non-`none` exactly on non-halted configurations. -/
lemma step₂_ne_iff (c₂ : TM2.Cfg M₂.tm.Γ M₂.tm.Λ M₂.tm.σ) :
    M₂.tm.step c₂ ≠ none ↔ c₂.l ≠ none := by
  constructor
  · intro h hcl
    rcases c₂ with ⟨l, v, S⟩
    cases l
    · simp [TM2.step] at h
      exact h rfl
    · cases hcl
  · intro hcl
    rcases c₂ with ⟨l, v, S⟩
    cases l
    · exact (hcl rfl).elim
    · simp [TM2.step]

/-- Phase-1 steps mirror `M₁`'s steps, for every non-halted `M₁` config. -/
lemma step₁_sim (c₁ : TM2.Cfg M₁.tm.Γ M₁.tm.Λ M₁.tm.σ) (hc₁ : c₁.l ≠ none)
    (S₂ : ∀ k : M₂.tm.K, List (M₂.tm.Γ k)) :
    (andOrMachine M₁ M₂ op).step (mapCfg₁ M₁ M₂ c₁ S₂) = Option.map (mapCfg₁ M₁ M₂ · S₂) (M₁.tm.step c₁) := by
  rcases c₁ with ⟨l, v, S₁⟩
  cases l with
  | none =>
      exfalso
      exact hc₁ rfl
  | some l₁ =>
      simp [FinTM2.step, TM2.step, mapCfg₁]
      change some (TM2.stepAux (mapStmt₁ M₁ M₂ (M₁.tm.m l₁)) (v, M₂.tm.initialState, AndOrSt.initial)
          (stk M₁ M₂ S₁ S₂)) =
        some (mapCfg₁ M₁ M₂ (TM2.stepAux (M₁.tm.m l₁) v S₁) S₂)
      exact congrArg some (stepAux_mapStmt₁ M₁ M₂ (M₁.tm.m l₁) v S₁ S₂)

/-- Phase-2 steps mirror `M₂`'s steps, for every non-halted `M₂` config. -/
lemma step₂_sim (c₂ : TM2.Cfg M₂.tm.Γ M₂.tm.Λ M₂.tm.σ) (hc₂ : c₂.l ≠ none)
    (S₁ : ∀ k : M₁.tm.K, List (M₁.tm.Γ k)) :
    (andOrMachine M₁ M₂ op).step (mapCfg₂ M₁ M₂ c₂ S₁) = Option.map (mapCfg₂ M₁ M₂ · S₁) (M₂.tm.step c₂) := by
  rcases c₂ with ⟨l, v, S₂⟩
  cases l with
  | none =>
      exfalso
      exact hc₂ rfl
  | some l₂ =>
      simp [FinTM2.step, TM2.step, mapCfg₂]
      change some (TM2.stepAux (mapStmt₂ M₁ M₂ (M₂.tm.m l₂)) (M₁.tm.initialState, v, AndOrSt.initial)
          (stk M₁ M₂ S₁ S₂)) =
        some (mapCfg₂ M₁ M₂ (TM2.stepAux (M₂.tm.m l₂) v S₂) S₁)
      exact congrArg some (stepAux_mapStmt₂ M₁ M₂ (M₂.tm.m l₂) v S₁ S₂)

/-- The combined step simulates `M₁` on every non-halted configuration. -/
lemma stepC_sim₁ (S₂ : ∀ k : M₂.tm.K, List (M₂.tm.Γ k))
    (c₁ : TM2.Cfg M₁.tm.Γ M₁.tm.Λ M₁.tm.σ) :
    M₁.tm.step c₁ ≠ none →
      (andOrMachine M₁ M₂ op).step (mapCfg₁ M₁ M₂ c₁ S₂) = Option.map (mapCfg₁ M₁ M₂ · S₂) (M₁.tm.step c₁) :=
  fun hc => step₁_sim M₁ M₂ c₁ ((step₁_ne_iff M₁ c₁).1 hc) S₂

/-- The combined step simulates `M₂` on every non-halted configuration. -/
lemma stepC_sim₂ (S₁ : ∀ k : M₁.tm.K, List (M₁.tm.Γ k))
    (c₂ : TM2.Cfg M₂.tm.Γ M₂.tm.Λ M₂.tm.σ) :
    M₂.tm.step c₂ ≠ none →
      (andOrMachine M₁ M₂ op).step (mapCfg₂ M₁ M₂ c₂ S₁) = Option.map (mapCfg₂ M₁ M₂ · S₁) (M₂.tm.step c₂) :=
  fun hc => step₂_sim M₁ M₂ c₂ ((step₂_ne_iff M₂ c₂).1 hc) S₁

/-- Updating a key, then updating a different key with the same content, is
commutative. -/
lemma update_swap {S : ∀ k : AndOrK M₁ M₂, List (AndOrΓ M₁ M₂ k)} (a b : AndOrK M₁ M₂)
    (va : List (AndOrΓ M₁ M₂ a)) (vb : List (AndOrΓ M₁ M₂ b)) (h : a ≠ b) :
    Function.update (Function.update S a va) b vb = Function.update (Function.update S b vb) a va := by
  funext k
  by_cases h₁ : k = a
  · subst k
    simp [Function.update, h]
  · by_cases h₂ : k = b
    · subst k
      simp [Function.update, h₁]
    · simp [Function.update, h₁, h₂]

/-- Updating a key with its current content is a no-op. -/
lemma update_self {S : ∀ k : AndOrK M₁ M₂, List (AndOrΓ M₁ M₂ k)} (a : AndOrK M₁ M₂)
    (va : List (AndOrΓ M₁ M₂ a)) (h : S a = va) :
    Function.update S a va = S := by
  funext k
  by_cases hk : k = a
  · subst k
    simp [Function.update, h]
  · simp [Function.update, hk]

/-- The copy-out phase: pop the input onto the scratch (reversing it), one step
per symbol plus a final empty-pop step.  Ends at `dupRestore` with the input
empty and the scratch holding `x.reverse ++ T`. -/
lemma dup_copyout_phase {x : List Γ} {S : ∀ k : AndOrK M₁ M₂, List (AndOrΓ M₁ M₂ k)} {T : List Γ}
    (s : AndOrSt Γ)
    (h : S inK = List.map M₁.inputAlphabet.invFun x)
    (ht : S tmpK = T) :
    (flip bind (andOrMachine M₁ M₂ op).step)^[x.length + 1]
        (some (⟨some (Sum.inr AndOrExtraΛ.dupScan), (M₁.tm.initialState, M₂.tm.initialState, s), S⟩ : (andOrMachine M₁ M₂ op).Cfg))
      = some (⟨some (Sum.inr AndOrExtraΛ.dupRestore), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.dupDone),
          Function.update (Function.update S inK []) tmpK (x.reverse ++ T)⟩ : (andOrMachine M₁ M₂ op).Cfg) := by
  induction x generalizing S T s with
  | nil =>
      have hhead : (S inK).head? = none := by rw [h]; simp
      have htail : (S inK).tail = [] := by rw [h]; simp
      have hcollapse : Function.update (Function.update S inK []) tmpK T = Function.update S inK [] := by
        rw [update_swap M₁ M₂ inK tmpK ([] : List (M₁.tm.Γ M₁.tm.k₀)) T (by simp [inK, tmpK])]
        rw [update_self M₁ M₂ tmpK T ht]
      simp [andOrMachine, andOrProgram, extraProgram, flip, hhead, htail]
      rw [hcollapse]
  | cons a x' ih =>
      have hhead : (S inK).head? = some (M₁.inputAlphabet.invFun a) := by rw [h]; simp
      have htail : (S inK).tail = List.map M₁.inputAlphabet.invFun x' := by rw [h]; simp
      have hone : (flip bind (andOrMachine M₁ M₂ op).step) (some (⟨some (Sum.inr AndOrExtraΛ.dupScan),
          (M₁.tm.initialState, M₂.tm.initialState, s), S⟩ : (andOrMachine M₁ M₂ op).Cfg))
          = some (⟨some (Sum.inr AndOrExtraΛ.dupScan), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.dupSym a),
              Function.update (Function.update S inK (List.map M₁.inputAlphabet.invFun x')) tmpK (a :: T)⟩ : (andOrMachine M₁ M₂ op).Cfg) := by
        simp [andOrMachine, andOrProgram, extraProgram, flip, hhead, htail, ht]
      rw [show (a :: x').length + 1 = (x'.length + 1) + 1 by simp [List.length_cons, Nat.add_assoc]]
      rw [Function.iterate_succ_apply]
      rw [hone]
      have hih := ih (s := AndOrSt.dupSym a)
        (S := Function.update (Function.update S inK (List.map M₁.inputAlphabet.invFun x')) tmpK (a :: T))
        (T := a :: T)
        (by simp [Function.update])
        (by simp [Function.update])
      have hcollapse : Function.update (Function.update
          (Function.update (Function.update S inK (List.map M₁.inputAlphabet.invFun x')) tmpK (a :: T))
          inK []) tmpK (x'.reverse ++ (a :: T))
        = Function.update (Function.update S inK []) tmpK ((a :: x').reverse ++ T) := by
        funext k
        by_cases h₁ : k = inK <;> by_cases h₂ : k = tmpK <;>
          simp [Function.update, h₁, h₂, List.reverse_cons, List.cons_append, List.append_assoc]
      calc
        (flip bind (andOrMachine M₁ M₂ op).step)^[x'.length + 1]
            (some (⟨some (Sum.inr AndOrExtraΛ.dupScan), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.dupSym a),
              Function.update (Function.update S inK (List.map M₁.inputAlphabet.invFun x')) tmpK (a :: T)⟩ : (andOrMachine M₁ M₂ op).Cfg))
          = some (⟨some (Sum.inr AndOrExtraΛ.dupRestore), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.dupDone),
              Function.update (Function.update
                (Function.update (Function.update S inK (List.map M₁.inputAlphabet.invFun x')) tmpK (a :: T))
                inK []) tmpK (x'.reverse ++ (a :: T))⟩ : (andOrMachine M₁ M₂ op).Cfg) := hih
        _ = some (⟨some (Sum.inr AndOrExtraΛ.dupRestore), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.dupDone),
              Function.update (Function.update S inK []) tmpK ((a :: x').reverse ++ T)⟩ : (andOrMachine M₁ M₂ op).Cfg) := by
          exact congrArg (fun stk => some (⟨some (Sum.inr AndOrExtraΛ.dupRestore),
              (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.dupDone), stk⟩ : (andOrMachine M₁ M₂ op).Cfg)) hcollapse

/-- The copy-back phase: pop the scratch onto both input stacks (restoring the
order), one step per symbol plus a final empty-pop step.  Ends at `M₁.main`
with the input restored on both stacks and the scratch empty. -/
lemma dup_restore_phase {x : List Γ} {S : ∀ k : AndOrK M₁ M₂, List (AndOrΓ M₁ M₂ k)}
    (s : AndOrSt Γ) {A : List (M₁.tm.Γ M₁.tm.k₀)} {B : List (M₂.tm.Γ M₂.tm.k₀)}
    (ht : S tmpK = x) (hin : S inK = A) (hin2 : S in2K = B) :
    (flip bind (andOrMachine M₁ M₂ op).step)^[x.length + 1]
        (some (⟨some (Sum.inr AndOrExtraΛ.dupRestore), (M₁.tm.initialState, M₂.tm.initialState, s), S⟩ : (andOrMachine M₁ M₂ op).Cfg))
      = some (⟨some (Sum.inl (Sum.inl M₁.tm.main)), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.initial),
          Function.update (Function.update (Function.update S tmpK []) inK ((List.map M₁.inputAlphabet.invFun x).reverse ++ A)) in2K ((List.map M₂.inputAlphabet.invFun x).reverse ++ B)⟩ : (andOrMachine M₁ M₂ op).Cfg) := by
  induction x generalizing S A B s with
  | nil =>
      have hhead : (S tmpK).head? = none := by rw [ht]; simp
      have htail : (S tmpK).tail = [] := by rw [ht]; simp
      have hcollapse : Function.update (Function.update (Function.update S tmpK []) inK A) in2K B = Function.update S tmpK [] := by
        funext k
        by_cases h₁ : k = inK
        · subst k
          simp [Function.update, hin]
        · by_cases h₂ : k = in2K
          · subst k
            simp [Function.update, hin2]
          · by_cases h₃ : k = tmpK
            · subst k
              simp [Function.update]
            · simp [Function.update, h₁, h₂, h₃]
      simp [andOrMachine, andOrProgram, extraProgram, flip, hhead, htail]
      rw [hcollapse]
  | cons a x' ih =>
      have hhead : (S tmpK).head? = some a := by rw [ht]; simp
      have htail : (S tmpK).tail = x' := by rw [ht]; simp
      have hone : (flip bind (andOrMachine M₁ M₂ op).step) (some (⟨some (Sum.inr AndOrExtraΛ.dupRestore),
          (M₁.tm.initialState, M₂.tm.initialState, s), S⟩ : (andOrMachine M₁ M₂ op).Cfg))
          = some (⟨some (Sum.inr AndOrExtraΛ.dupRestore), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.restSym a),
              Function.update (Function.update (Function.update S tmpK x') inK (M₁.inputAlphabet.invFun a :: A)) in2K (M₂.inputAlphabet.invFun a :: B)⟩ : (andOrMachine M₁ M₂ op).Cfg) := by
        simp [andOrMachine, andOrProgram, extraProgram, flip, hhead, htail, hin, hin2]
      rw [show (a :: x').length + 1 = (x'.length + 1) + 1 by simp [List.length_cons, Nat.add_assoc]]
      rw [Function.iterate_succ_apply]
      rw [hone]
      have hih := ih (s := AndOrSt.restSym a)
        (S := Function.update (Function.update (Function.update S tmpK x') inK (M₁.inputAlphabet.invFun a :: A)) in2K (M₂.inputAlphabet.invFun a :: B))
        (A := M₁.inputAlphabet.invFun a :: A)
        (B := M₂.inputAlphabet.invFun a :: B)
        (by simp [Function.update])
        (by simp [Function.update])
        (by simp [Function.update])
      have hcollapse : Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update S tmpK x') inK (M₁.inputAlphabet.invFun a :: A)) in2K (M₂.inputAlphabet.invFun a :: B))
          tmpK []) inK ((List.map M₁.inputAlphabet.invFun x').reverse ++ (M₁.inputAlphabet.invFun a :: A)))
          in2K ((List.map M₂.inputAlphabet.invFun x').reverse ++ (M₂.inputAlphabet.invFun a :: B))
        = Function.update (Function.update (Function.update S tmpK []) inK ((List.map M₁.inputAlphabet.invFun (a :: x')).reverse ++ A)) in2K ((List.map M₂.inputAlphabet.invFun (a :: x')).reverse ++ B) := by
        funext k
        by_cases h₁ : k = tmpK <;> by_cases h₂ : k = inK <;> by_cases h₃ : k = in2K <;>
          simp [Function.update, h₁, h₂, h₃, List.reverse_cons, List.cons_append, List.append_assoc]
      calc
        (flip bind (andOrMachine M₁ M₂ op).step)^[x'.length + 1]
            (some (⟨some (Sum.inr AndOrExtraΛ.dupRestore), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.restSym a),
              Function.update (Function.update (Function.update S tmpK x') inK (M₁.inputAlphabet.invFun a :: A)) in2K (M₂.inputAlphabet.invFun a :: B)⟩ : (andOrMachine M₁ M₂ op).Cfg))
          = some (⟨some (Sum.inl (Sum.inl M₁.tm.main)), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.initial),
              Function.update (Function.update (Function.update
                (Function.update (Function.update (Function.update S tmpK x') inK (M₁.inputAlphabet.invFun a :: A)) in2K (M₂.inputAlphabet.invFun a :: B))
                tmpK []) inK ((List.map M₁.inputAlphabet.invFun x').reverse ++ (M₁.inputAlphabet.invFun a :: A)))
                in2K ((List.map M₂.inputAlphabet.invFun x').reverse ++ (M₂.inputAlphabet.invFun a :: B))⟩ : (andOrMachine M₁ M₂ op).Cfg) := hih
        _ = some (⟨some (Sum.inl (Sum.inl M₁.tm.main)), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.initial),
              Function.update (Function.update (Function.update S tmpK []) inK ((List.map M₁.inputAlphabet.invFun (a :: x')).reverse ++ A)) in2K ((List.map M₂.inputAlphabet.invFun (a :: x')).reverse ++ B)⟩ : (andOrMachine M₁ M₂ op).Cfg) := by
          exact congrArg (fun stk => some (⟨some (Sum.inl (Sum.inl M₁.tm.main)),
              (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.initial), stk⟩ : (andOrMachine M₁ M₂ op).Cfg)) hcollapse

/-- The phase-1 start configuration after the duplicate phase: both deciders'
input stacks carry the input, the scratch is empty. -/
lemma dup_phase (x : List Γ) :
    (flip bind (andOrMachine M₁ M₂ op).step)^[2 * x.length + 2]
        (some (initList (andOrMachine M₁ M₂ op) (List.map M₁.inputAlphabet.invFun x)))
      = some (mapCfg₁ M₁ M₂ (initList M₁.tm (List.map M₁.inputAlphabet.invFun x)) (dupInput M₂ x)) := by
  -- copy the input out to the scratch (reversing it), one step per symbol plus
  -- a final empty-pop step
  have hcopy : (flip bind (andOrMachine M₁ M₂ op).step)^[x.length + 1]
        (some (initList (andOrMachine M₁ M₂ op) (List.map M₁.inputAlphabet.invFun x)))
      = some (⟨some (Sum.inr AndOrExtraΛ.dupRestore), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.dupDone),
          Function.update (Function.update (initList (andOrMachine M₁ M₂ op) (List.map M₁.inputAlphabet.invFun x)).stk inK []) tmpK (x.reverse ++ [])⟩ : (andOrMachine M₁ M₂ op).Cfg) := by
    apply dup_copyout_phase M₁ M₂ AndOrSt.initial
    · simp [inK]
    · simp [tmpK]
  -- copy the input back from the scratch onto both input stacks, one step per
  -- symbol plus a final empty-pop step, ending at `M₁.main`
  have hrestore : (flip bind (andOrMachine M₁ M₂ op).step)^[x.reverse.length + 1]
        (some (⟨some (Sum.inr AndOrExtraΛ.dupRestore), (M₁.tm.initialState, M₂.tm.initialState, AndOrSt.dupDone),
            Function.update (Function.update (initList (andOrMachine M₁ M₂ op) (List.map M₁.inputAlphabet.invFun x)).stk inK []) tmpK (x.reverse ++ [])⟩ : (andOrMachine M₁ M₂ op).Cfg))
      = some (mapCfg₁ M₁ M₂ (initList M₁.tm (List.map M₁.inputAlphabet.invFun x)) (dupInput M₂ x)) := by
    have hphase := dup_restore_phase M₁ M₂ AndOrSt.dupDone
      (x := x.reverse) (op := op)
      (S := Function.update (Function.update (initList (andOrMachine M₁ M₂ op) (List.map M₁.inputAlphabet.invFun x)).stk inK []) tmpK (x.reverse ++ []))
      (A := []) (B := [])
      (by simp [tmpK, Function.update])
      (by simp [inK, Function.update])
      (by simp [in2K, Function.update])
    rw [hphase]
    apply congrArg some
    apply Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext k
      cases k with
      | inl k₁ =>
          cases k₁ with
          | inl k₁' =>
              by_cases h : k₁' = M₁.tm.k₀
              · subst k₁'
                simp [mapCfg₁, stk, dupInput, initList, Function.update, List.map_reverse, List.reverse_reverse]
              · simp [mapCfg₁, stk, dupInput, initList, Function.update, h]
          | inr k₂' =>
              by_cases h : k₂' = M₂.tm.k₀
              · subst k₂'
                simp [mapCfg₁, stk, dupInput, initList, Function.update, List.map_reverse, List.reverse_reverse]
              · simp [mapCfg₁, stk, dupInput, initList, Function.update, h]
      | inr AndOrExtraK.dupTemp =>
          simp [mapCfg₁, stk, dupInput, initList, Function.update, List.map_reverse, List.reverse_reverse]
  have hlen : x.reverse.length = x.length := by simp
  rw [show 2 * x.length + 2 = (x.reverse.length + 1) + (x.length + 1) by rw [hlen]; omega]
  rw [Function.iterate_add_apply]
  rw [hcopy]
  exact hrestore

/-- The phase-1 halt configuration is the phase-2 start configuration: `M₁`'s
output `[f₁ x]` is `M₂`'s input and the duplicated copy of the input is already
on `M₂`'s input stack. -/
lemma mapCfg₁to₂ (x : α) :
    mapCfg₁ M₁ M₂ (haltList M₁.tm (List.map M₁.outputAlphabet.invFun [f₁ x]))
        (dupInput M₂ (encode x)) =
      mapCfg₂ M₁ M₂
        (initList M₂.tm (List.map M₂.inputAlphabet.invFun (encode x)))
        (halt₁stk M₁ x) := by
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k₁ =>
        cases k₁ with
        | inl k₁' =>
            by_cases h : k₁' = M₁.tm.k₁
            · subst k₁'
              simp [mapCfg₁, mapCfg₂, stk, dupInput, halt₁stk, haltList]
            · simp [mapCfg₁, mapCfg₂, stk, dupInput, halt₁stk, haltList, h]
        | inr k₂' =>
            by_cases h : k₂' = M₂.tm.k₀
            · subst k₂'
              simp [mapCfg₁, mapCfg₂, stk, dupInput, halt₁stk, haltList]
            · simp [mapCfg₁, mapCfg₂, stk, dupInput, halt₁stk, haltList, h]
    | inr AndOrExtraK.dupTemp =>
        simp [mapCfg₁, mapCfg₂, stk, dupInput, halt₁stk, haltList]

/-- The combine phase: one step pops `b₁` from `M₁`'s output, pops `b₂` from
`M₂`'s output, pushes `op b₁ b₂` onto the combined output stack, resets the
state and halts. -/
lemma combine_step (x : α) :
    (flip bind (andOrMachine M₁ M₂ op).step)
        (some (mapCfg₂ M₁ M₂ (haltList M₂.tm (List.map M₂.outputAlphabet.invFun [f₂ x])) (halt₁stk M₁ x)))
      = some (haltList (andOrMachine M₁ M₂ op) (List.map M₂.outputAlphabet.invFun [op (f₁ x) (f₂ x)])) := by
  apply congrArg some
  apply Turing.TM2Comp.Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k₁ =>
        cases k₁ with
        | inl k₁' =>
            by_cases h : k₁' = M₁.tm.k₁
            · subst k₁'
              simp [andOrMachine, andOrProgram, extraProgram, mapCfg₂, stk, halt₁stk,
                Equiv.apply_invFun_apply]
            · simp [andOrMachine, andOrProgram, extraProgram, mapCfg₂, stk, halt₁stk,
                Equiv.apply_invFun_apply, h]
        | inr k₂' =>
            by_cases h : k₂' = M₂.tm.k₁
            · subst k₂'
              simp [andOrMachine, andOrProgram, extraProgram, mapCfg₂, stk, halt₁stk,
                Equiv.apply_invFun_apply]
              rw [Turing.TM2Comp.haltList_stk₁]
            · simp [andOrMachine, andOrProgram, extraProgram, mapCfg₂, stk, halt₁stk,
                Equiv.apply_invFun_apply, h]
    | inr AndOrExtraK.dupTemp =>
        simp [andOrMachine, andOrProgram, extraProgram, mapCfg₂, stk, halt₁stk,
          Equiv.apply_invFun_apply]

/-- The combined time bound: the duplicate phase takes `2|x| + 2` steps, the
combine phase takes `1` step. -/
def andOrTime : Polynomial ℕ := M₁.time + M₂.time + (2 * Polynomial.X + 3)

/-- The combined machine's `outputsFun`: duplicate the input, run `M₁`, run
`M₂`, combine the two Boolean results with `op`. -/
def andOr_outputsFun (op : Bool → Bool → Bool) (x : α) :
    TM2OutputsInTime (andOrMachine M₁ M₂ op)
      (List.map (andOrInputAlphabet M₁ M₂).invFun (encode x))
      (some (List.map (andOrOutputAlphabet M₁ M₂).invFun (Turing.TM2Comp.boolEncoding (op (f₁ x) (f₂ x)))))
      ((andOrTime M₁ M₂).eval (encode x).length) := by
  let input := encode x
  let n := input.length
  let m₁ := (M₁.time).eval n
  let m₂ := (M₂.time).eval n
  let initC := initList (andOrMachine M₁ M₂ op)
    (List.map M₁.inputAlphabet.invFun input)
  let init₁ := initList M₁.tm (List.map M₁.inputAlphabet.invFun input)
  let halt₁ := haltList M₁.tm (List.map M₁.outputAlphabet.invFun [f₁ x])
  let init₂ := initList M₂.tm (List.map M₂.inputAlphabet.invFun input)
  let halt₂ := haltList M₂.tm (List.map M₂.outputAlphabet.invFun [f₂ x])
  let C₁ := mapCfg₁ M₁ M₂ init₁ (dupInput M₂ input)
  let C₃ := mapCfg₂ M₁ M₂ init₂ (halt₁stk M₁ x)
  let C₄ := mapCfg₂ M₁ M₂ halt₂ (halt₁stk M₁ x)
  let haltC := haltList (andOrMachine M₁ M₂ op) (List.map M₂.outputAlphabet.invFun [op (f₁ x) (f₂ x)])
  change EvalsToInTime (andOrMachine M₁ M₂ op).step initC (some haltC) ((andOrTime M₁ M₂).eval n)

  -- duplicate phase
  have hdupIt : EvalsToInTime (andOrMachine M₁ M₂ op).step initC
      (some C₁) (2 * input.length + 2) := by
    refine ⟨⟨2 * input.length + 2, ?_⟩, le_rfl⟩
    change (flip bind (andOrMachine M₁ M₂ op).step)^[2 * input.length + 2]
      (some initC) = some C₁
    exact dup_phase M₁ M₂ input

  -- phase 1
  have h₁run : EvalsToInTime M₁.tm.step init₁ (some halt₁) m₁ := by
    have hh := M₁.outputsFun x
    simpa [input, n, m₁, init₁, Turing.TM2Comp.boolEncoding, halt₁,
      TM2OutputsInTime] using hh
  have hstop₁ : M₁.tm.step halt₁ = none := rfl
  have hlift₁ : EvalsToInTime (andOrMachine M₁ M₂ op).step
        (mapCfg₁ M₁ M₂ init₁ (dupInput M₂ input))
        (some (mapCfg₁ M₁ M₂ halt₁ (dupInput M₂ input))) m₁ :=
    Turing.TM2Comp.evalsToInTime_lift
      (fun c₁ => mapCfg₁ M₁ M₂ c₁ (dupInput M₂ input)) h₁run hstop₁
      (stepC_sim₁ M₁ M₂ (dupInput M₂ input))
  have hbridge₁ : mapCfg₁ M₁ M₂ halt₁ (dupInput M₂ input) = C₃ := by
    simpa [input, halt₁, init₂, C₃] using mapCfg₁to₂ M₁ M₂ x
  have h₁ : EvalsToInTime (andOrMachine M₁ M₂ op).step C₁ (some C₃) m₁ := by
    simpa [C₁, C₃] using (by rwa [hbridge₁] at hlift₁)

  -- phase 2
  have h₂run : EvalsToInTime M₂.tm.step init₂ (some halt₂) m₂ := by
    have hh := M₂.outputsFun x
    simpa [input, n, m₂, init₂, Turing.TM2Comp.boolEncoding, halt₂,
      TM2OutputsInTime] using hh
  have hstop₂ : M₂.tm.step halt₂ = none := rfl
  have hlift₂ : EvalsToInTime (andOrMachine M₁ M₂ op).step (mapCfg₂ M₁ M₂ init₂ (halt₁stk M₁ x))
        (some (mapCfg₂ M₁ M₂ halt₂ (halt₁stk M₁ x))) m₂ :=
    Turing.TM2Comp.evalsToInTime_lift (fun c₂ => mapCfg₂ M₁ M₂ c₂ (halt₁stk M₁ x)) h₂run hstop₂
      (stepC_sim₂ M₁ M₂ (halt₁stk M₁ x))
  have h₂ : EvalsToInTime (andOrMachine M₁ M₂ op).step C₃ (some C₄) m₂ := by
    simpa [C₃, C₄] using hlift₂

  -- combine phase
  have hcombIt : EvalsToInTime (andOrMachine M₁ M₂ op).step C₄ (some haltC) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind (andOrMachine M₁ M₂ op).step) (some C₄) = some haltC
    exact combine_step M₁ M₂ x

  -- chain the phases
  have h₁₂It : EvalsToInTime (andOrMachine M₁ M₂ op).step initC
      (some C₃) (m₁ + (2 * input.length + 2)) :=
    EvalsToInTime.trans (andOrMachine M₁ M₂ op).step
      (2 * input.length + 2) m₁ initC C₁ (some C₃) hdupIt h₁
  have h₁₂₃It : EvalsToInTime (andOrMachine M₁ M₂ op).step initC
      (some C₄) (m₂ + (m₁ + (2 * input.length + 2))) :=
    EvalsToInTime.trans (andOrMachine M₁ M₂ op).step
      (m₁ + (2 * input.length + 2)) m₂ initC C₃ (some C₄) h₁₂It h₂
  have hchain : EvalsToInTime (andOrMachine M₁ M₂ op).step initC (some haltC)
        (1 + (m₂ + (m₁ + (2 * input.length + 2)))) :=
    EvalsToInTime.trans (andOrMachine M₁ M₂ op).step
      (m₂ + (m₁ + (2 * input.length + 2))) 1 initC C₄
      (some haltC) h₁₂₃It hcombIt

  -- time bound
  have htime : (andOrTime M₁ M₂).eval n =
      m₁ + m₂ + (2 * input.length + 3) := by
    simp [n, m₁, m₂, andOrTime, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_natCast]
  have hbound : 1 + (m₂ + (m₁ + (2 * input.length + 2))) ≤
      (andOrTime M₁ M₂).eval n := by
    rw [htime]
    omega
  exact { hchain with steps_le_m := le_trans hchain.steps_le_m hbound }

/-- The combination of two polytime deciders is polytime: `x ↦ [op (f₁ x) (f₂ x)]`
is computed by the combined machine. -/
def andOrComputableInPolyTime (op : Bool → Bool → Bool) :
    TM2ComputableInPolyTime encode Turing.TM2Comp.boolEncoding
      (fun x => op (f₁ x) (f₂ x)) where
  tm := andOrMachine M₁ M₂ op
  inputAlphabet := andOrInputAlphabet M₁ M₂
  outputAlphabet := andOrOutputAlphabet M₁ M₂
  time := andOrTime M₁ M₂
  outputsFun := andOr_outputsFun M₁ M₂ op

end TM2AndOr

end Turing

end
