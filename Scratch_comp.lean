import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-!
# Scratch: prove `Turing.TM2ComputableInPolyTime.comp`

Composition of polynomial-time TM2 machines is polynomial-time.

Design (shared-stack, two-phase):

- The combined machine has stacks `Sum K₁ K₂`: `inl k` are `h1`'s stacks,
  `inr k` are `h2`'s stacks.
- Phase 1 runs `h1`'s program (`mapStmt₁` reindexes stacks `k ↦ inl k` and
  carries the state in the first projection; `halt` becomes `goto` into `h2`'s
  main).
- Phase 2 runs `h2`'s program (`mapStmt₂` maps `h2`'s input stack `k₀₂` onto
  `h1`'s output stack `inl k₁₁`, converting elements through the alphabet
  equivalence `Γ₁ k₁₁ ≃ βΓ ≃ Γ₂ k₀₂`; every other `h2` stack is `inr k`).
  Since both machines halt in the `haltList` configuration (empty non-output
  stacks, `initialState` variables), the combined machine also halts exactly
  in `haltList` with the right output on `k₁C := if k₀₂ = k₁₂ then inl k₁₁
  else inr k₁₂`.

Time bound: phase 1 ≤ `p(n)`, phase 2 ≤ `q(out₁.length)` where
`out₁.length ≤ n + p(n)` (the output stack starts empty unless it *is* the
input stack, in which case it starts with `n` elements).  So
`timeC := h1.time + h2.time.comp (Polynomial.X + h1.time)`.
-/

noncomputable section

open Computability StateTransition

namespace Turing

namespace ScratchComp

-- Combinator for the combined-machine indices and types.
variable {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
variable {f : α → β} {g : β → γ}

variable (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g)

/-- Combined stack index type: `h1`'s stacks on the left, `h2`'s on the right. -/
abbrev CompK := Sum (h1.tm).K (h2.tm).K

/-- Combined stack types. -/
abbrev CompΓ : CompK h1 h2 → Type := Sum.elim (h1.tm).Γ (h2.tm).Γ

/-- Combined label type. -/
abbrev CompΛ := Sum (h1.tm).Λ (h2.tm).Λ

/-- Combined state: `h1`'s state in the first component, `h2`'s in the second. -/
abbrev Compσ := (h1.tm).σ × (h2.tm).σ

/-- Combined input stack: `h1`'s input stack. -/
def compk₀ : CompK h1 h2 := Sum.inl (h1.tm).k₀

/-- Combined output stack: `h2`'s output stack, or `h1`'s output stack when
`h2` reuses its input stack as its output stack. -/
def compk₁ : CompK h1 h2 :=
  if (h2.tm).k₀ = (h2.tm).k₁ then Sum.inl (h1.tm).k₁ else Sum.inr (h2.tm).k₁

/-- The `h1` output stack carries `h2`'s input: elements of `Γ₁ k₁₁` are
converted to `Γ₂ k₀₂` through the alphabet equivalence `βΓ`. -/
def convIn (x : (h1.tm).Γ (h1.tm).k₁) : (h2.tm).Γ (h2.tm).k₀ :=
  h2.inputAlphabet.invFun (h1.outputAlphabet x)

/-- The inverse conversion for pushing `h2`'s input elements. -/
def convOut (y : (h2.tm).Γ (h2.tm).k₀) : (h1.tm).Γ (h1.tm).k₁ :=
  h1.outputAlphabet.invFun (h2.inputAlphabet y)
@[simp] lemma convIn_convOut (y : (h2.tm).Γ (h2.tm).k₀) :
    convIn h1 h2 (convOut h1 h2 y) = y := by
  simp [convIn, convOut, Equiv.apply_symm_apply]

@[simp] lemma convOut_convIn (x : (h1.tm).Γ (h1.tm).k₁) :
    convOut h1 h2 (convIn h1 h2 x) = x := by
  simp [convIn, convOut, Equiv.apply_symm_apply]


/-- Translate `h1`'s program to the combined machine.  `halt` jumps into
`h2`'s main. -/
def mapStmt₁ : Turing.TM2.Stmt (h1.tm).Γ (h1.tm).Λ (h1.tm).σ →
    Turing.TM2.Stmt (CompΓ h1 h2) (CompΛ h1 h2) (Compσ h1 h2)
  | Turing.TM2.Stmt.push k f q => Turing.TM2.Stmt.push (Sum.inl k) (fun v => f v.1) (mapStmt₁ q)
  | Turing.TM2.Stmt.peek k f q =>
      Turing.TM2.Stmt.peek (Sum.inl k) (fun v x => (f v.1 x, v.2)) (mapStmt₁ q)
  | Turing.TM2.Stmt.pop k f q =>
      Turing.TM2.Stmt.pop (Sum.inl k) (fun v x => (f v.1 x, v.2)) (mapStmt₁ q)
  | Turing.TM2.Stmt.load f q => Turing.TM2.Stmt.load (fun v => (f v.1, v.2)) (mapStmt₁ q)
  | Turing.TM2.Stmt.branch f q₁ q₂ =>
      Turing.TM2.Stmt.branch (fun v => f v.1) (mapStmt₁ q₁) (mapStmt₁ q₂)
  | Turing.TM2.Stmt.goto f => Turing.TM2.Stmt.goto (fun v => Sum.inl (f v.1))
  | Turing.TM2.Stmt.halt => Turing.TM2.Stmt.goto (fun _ => Sum.inr (h2.tm).main)

/-- Translate `h2`'s program to the combined machine.  `halt` is the final halt.
`h2`'s input stack `k₀` is implemented by `h1`'s output stack `inl k₁`, with
elements converted through the alphabet equivalence. -/
def mapStmt₂ : Turing.TM2.Stmt (h2.tm).Γ (h2.tm).Λ (h2.tm).σ →
    Turing.TM2.Stmt (CompΓ h1 h2) (CompΛ h1 h2) (Compσ h1 h2)
  | Turing.TM2.Stmt.push k f q =>
      if h : k = (h2.tm).k₀ then
        Turing.TM2.Stmt.push (Sum.inl (h1.tm).k₁)
          (fun v => convOut h1 h2 (Eq.ndrec (motive := fun t => (h2.tm).Γ t) (f v.2) h)) (mapStmt₂ q)
      else
        Turing.TM2.Stmt.push (Sum.inr k) (fun v => f v.2) (mapStmt₂ q)
  | Turing.TM2.Stmt.peek k f q =>
      if h : k = (h2.tm).k₀ then
        Turing.TM2.Stmt.peek (Sum.inl (h1.tm).k₁)
          (fun v x => (v.1, f v.2 (Eq.ndrec (motive := fun t => Option ((h2.tm).Γ t))
            (x.map (convIn h1 h2)) h.symm))) (mapStmt₂ q)
      else
        Turing.TM2.Stmt.peek (Sum.inr k) (fun v x => (v.1, f v.2 x)) (mapStmt₂ q)
  | Turing.TM2.Stmt.pop k f q =>
      if h : k = (h2.tm).k₀ then
        Turing.TM2.Stmt.pop (Sum.inl (h1.tm).k₁)
          (fun v x => (v.1, f v.2 (Eq.ndrec (motive := fun t => Option ((h2.tm).Γ t))
            (x.map (convIn h1 h2)) h.symm))) (mapStmt₂ q)
      else
        Turing.TM2.Stmt.pop (Sum.inr k) (fun v x => (v.1, f v.2 x)) (mapStmt₂ q)
  | Turing.TM2.Stmt.load f q => Turing.TM2.Stmt.load (fun v => (v.1, f v.2)) (mapStmt₂ q)
  | Turing.TM2.Stmt.branch f q₁ q₂ =>
      Turing.TM2.Stmt.branch (fun v => f v.2) (mapStmt₂ q₁) (mapStmt₂ q₂)
  | Turing.TM2.Stmt.goto f => Turing.TM2.Stmt.goto (fun v => Sum.inr (f v.2))
  | Turing.TM2.Stmt.halt => Turing.TM2.Stmt.halt

/-- The combined program. -/
def compProgram (l : CompΛ h1 h2) : Turing.TM2.Stmt (CompΓ h1 h2) (CompΛ h1 h2) (Compσ h1 h2) :=
  match l with
  | Sum.inl l₁ => mapStmt₁ h1 h2 ((h1.tm).m l₁)
  | Sum.inr l₂ => mapStmt₂ h1 h2 ((h2.tm).m l₂)

/-- The `h1`/`h2` instance fields do not project through `h1.tm`/`h2.tm`, so the
combined machine's finiteness instances are built explicitly. -/
def compKDecidableEq : DecidableEq (CompK h1 h2) := by
  letI : DecidableEq (h1.tm).K := h1.tm.kDecidableEq
  letI : DecidableEq (h2.tm).K := h2.tm.kDecidableEq
  infer_instance

/-- The combined index type is finite. -/
def compKFintype : Fintype (CompK h1 h2) := by
  letI : Fintype (h1.tm).K := h1.tm.kFin
  letI : Fintype (h2.tm).K := h2.tm.kFin
  infer_instance

/-- The combined label type is finite. -/
def compΛFintype : Fintype (CompΛ h1 h2) := by
  letI : Fintype (h1.tm).Λ := h1.tm.ΛFin
  letI : Fintype (h2.tm).Λ := h2.tm.ΛFin
  infer_instance

/-- The combined state type is finite. -/
def compσFintype : Fintype (Compσ h1 h2) := by
  letI : Fintype (h1.tm).σ := h1.tm.σFin
  letI : Fintype (h2.tm).σ := h2.tm.σFin
  infer_instance

/-- The combined input alphabet is finite. -/
def compΓk₀Fintype : Fintype (CompΓ h1 h2 (Sum.inl (h1.tm).k₀)) :=
  h1.tm.Γk₀Fin

/-- The combined bundled machine. -/
abbrev compMachine (h1 : TM2ComputableInPolyTime eα eβ f)
    (h2 : TM2ComputableInPolyTime eβ eγ g) : FinTM2 :=
  @FinTM2.mk (CompK h1 h2) (compKDecidableEq h1 h2) (compKFintype h1 h2)
    (compk₀ h1 h2) (compk₁ h1 h2) (CompΓ h1 h2) (CompΛ h1 h2) (Sum.inl (h1.tm).main)
    (compΛFintype h1 h2) (Compσ h1 h2) ((h1.tm).initialState, (h2.tm).initialState)
    (compσFintype h1 h2) (compΓk₀Fintype h1 h2) (compProgram h1 h2)

/-- The combined input alphabet: `h1`'s. -/
def compInputAlphabet : (compMachine h1 h2).Γ (compMachine h1 h2).k₀ ≃ αΓ :=
  h1.inputAlphabet

@[simp] lemma eq_ndrec_round_trip {α : Type} {a b : α} {M : α → Sort*}
    (x : M a) (h : a = b) : Eq.ndrec (motive := M) (Eq.ndrec (motive := M) x h) h.symm = x := by
  cases h
  simp

@[simp] lemma cast_congrArg_List_map {α β : Type} {e : α = β} (l : List α) :
    cast (congrArg List e) l = List.map (cast e) l := by
  cases e
  induction l with
  | nil => rfl
  | cons x xs ih =>
      change x :: xs = List.map (fun x : α => x) (x :: xs)
      simp

@[simp] lemma cast_congrArg_eq_ndrec {α : Type} {a b : α} {M : α → Type}
    {e : a = b} (x : M a) : cast (congrArg M e) x = Eq.ndrec (motive := M) x e := by
  cases e
  simp

@[simp] lemma cast_cast {α β γ : Type} (e₁ : α = β) (e₂ : β = γ) (x : α) :
    cast e₂ (cast e₁ x) = cast (e₁.trans e₂) x := by
  cases e₁
  cases e₂
  rfl

@[simp] lemma eq_symm_trans_self {α : Type} {a b : α} (h : a = b) : h.symm.trans h = rfl := by
  cases h
  rfl

/-- Casting to `β` and back to `α` is the identity (proofs of the type equalities
are proof-irrelevant). -/
@[simp] lemma cast_symm_cancel {α β : Type} {p : α = β} (q : β = α) (x : α) :
    q ▸ (cast p x) = x := by
  cases p
  cases q
  rfl

/-- The combined output alphabet: `h2`'s, or the composite when `h2` reuses
its input stack as output.  The `k₀ = k₁` branch is an explicit `Equiv` whose
`invFun` is definitionally `convOut ∘ (Eq.ndrec …)`, and the domain recast is
carried by `Equiv.cast` so that `.symm` reduces via `Equiv.cast_symm`. -/
def compOutputAlphabet : (compMachine h1 h2).Γ (compMachine h1 h2).k₁ ≃ γΓ :=
  if h : (h2.tm).k₀ = (h2.tm).k₁ then
    (Equiv.cast (show CompΓ h1 h2 (compk₁ h1 h2) = (h1.tm).Γ (h1.tm).k₁ by simp [compk₁, h])).trans
      { toFun := fun x : (h1.tm).Γ (h1.tm).k₁ =>
          h2.outputAlphabet
            (Eq.ndrec (motive := fun k : (h2.tm).K => (h2.tm).Γ k) (convIn h1 h2 x) h)
        invFun := fun y : γΓ =>
          convOut h1 h2
            (Eq.ndrec (motive := fun k : (h2.tm).K => (h2.tm).Γ k) (h2.outputAlphabet.invFun y) h.symm)
        left_inv := by
          intro x
          change convOut h1 h2 (Eq.ndrec (motive := fun k : (h2.tm).K => (h2.tm).Γ k)
            (h2.outputAlphabet.symm (h2.outputAlphabet (Eq.ndrec (motive := fun k : (h2.tm).K => (h2.tm).Γ k) (convIn h1 h2 x) h))) h.symm) = x
          simp [convIn, convOut, Equiv.apply_symm_apply, Equiv.symm_apply_apply, eq_ndrec_round_trip]
        right_inv := by
          intro y
          change h2.outputAlphabet (Eq.ndrec (motive := fun k : (h2.tm).K => (h2.tm).Γ k)
            (convIn h1 h2 (convOut h1 h2 (Eq.ndrec (motive := fun k : (h2.tm).K => (h2.tm).Γ k) (h2.outputAlphabet.symm y) h.symm))) h) = y
          simp [convIn, convOut, Equiv.apply_symm_apply, Equiv.symm_apply_apply, eq_ndrec_round_trip] }
  else
    (Equiv.cast (show CompΓ h1 h2 (compk₁ h1 h2) = (h2.tm).Γ (h2.tm).k₁ by simp [compk₁, h])).trans h2.outputAlphabet

lemma list_map_tail {α β : Type} (f : α → β) (l : List α) :
    (List.map f l).tail = List.map f l.tail := by
  cases l <;> simp

@[simp] lemma list_head?_map {α β : Type} (f : α → β) (l : List α) :
    (List.map f l).head? = l.head?.map f := by
  cases l <;> simp

@[simp] lemma convIn_comp_convOut : (convIn h1 h2 ∘ convOut h1 h2) = id := by
  funext y
  simp

/-- `h1`'s stacks embedded in the combined machine (phase 1). -/
def stk₁ (S : ∀ k : (h1.tm).K, List ((h1.tm).Γ k)) :
    ∀ k : CompK h1 h2, List (CompΓ h1 h2 k) :=
  fun k => match k with | Sum.inl k' => S k' | Sum.inr _ => []

/-- `h2`'s stacks embedded in the combined machine (phase 2). -/
def stk₂ (S : ∀ k : (h2.tm).K, List ((h2.tm).Γ k)) :
    ∀ k : CompK h1 h2, List (CompΓ h1 h2 k) := by
  intro k
  cases k with
  | inl k' =>
      by_cases h : k' = (h1.tm).k₁
      · subst k'
        exact List.map (convOut h1 h2) (S (h2.tm).k₀)
      · exact []
  | inr k' =>
      by_cases h : k' = (h2.tm).k₀
      · subst k'
        exact []
      · exact S k'

/-- Updating `h1`'s stack `k` commutes with the phase-1 embedding. -/
lemma update_stk₁ (S : ∀ k : (h1.tm).K, List ((h1.tm).Γ k)) (k : (h1.tm).K)
    (L : List ((h1.tm).Γ k)) :
    Function.update (stk₁ h1 h2 S) (Sum.inl k) L = stk₁ h1 h2 (Function.update S k L) := by
  funext k'
  cases k' with
  | inl k'' =>
      by_cases h : k'' = k
      · subst k''
        simp [stk₁, Function.update]
      · simp [stk₁, Function.update, h]
  | inr k'' =>
      simp [stk₁, Function.update]

/-- `h1`'s configurations embedded in the combined machine.  The halted
configuration of `h1` maps to the start of phase 2. -/
def mapCfg₁ (c : Turing.TM2.Cfg (h1.tm).Γ (h1.tm).Λ (h1.tm).σ) :
    Turing.TM2.Cfg (CompΓ h1 h2) (CompΛ h1 h2) (Compσ h1 h2) :=
  { l := match c.l with
      | some l₁ => some (Sum.inl l₁)
      | none => some (Sum.inr (h2.tm).main)
    var := (c.var, (h2.tm).initialState)
    stk := stk₁ h1 h2 c.stk }

/-- `h2`'s configurations embedded in the combined machine (phase 2). -/
def mapCfg₂ (c : Turing.TM2.Cfg (h2.tm).Γ (h2.tm).Λ (h2.tm).σ) :
    Turing.TM2.Cfg (CompΓ h1 h2) (CompΛ h1 h2) (Compσ h1 h2) :=
  { l := Option.map Sum.inr c.l
    var := ((h1.tm).initialState, c.var)
    stk := stk₂ h1 h2 c.stk }

/-- Executing `mapStmt₁ s` from the phase-1 state mirrors executing `s` in `h1`. -/
lemma stepAux_mapStmt₁ (s : Turing.TM2.Stmt (h1.tm).Γ (h1.tm).Λ (h1.tm).σ) :
    ∀ (v : (h1.tm).σ) (S : ∀ k : (h1.tm).K, List ((h1.tm).Γ k)),
      Turing.TM2.stepAux (mapStmt₁ h1 h2 s) (v, (h2.tm).initialState) (stk₁ h1 h2 S)
        = mapCfg₁ h1 h2 (Turing.TM2.stepAux s v S) := by
  induction s with
  | push k f q ih =>
      intro v S
      simp [mapStmt₁, stk₁, Turing.TM2.stepAux]
      rw [update_stk₁]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      intro v S
      simp [mapStmt₁, stk₁, Turing.TM2.stepAux]
      exact ih (f v (S k).head?) S
  | pop k f q ih =>
      intro v S
      simp [mapStmt₁, stk₁, Turing.TM2.stepAux]
      rw [update_stk₁]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      intro v S
      simp [mapStmt₁, Turing.TM2.stepAux]
      exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v S
      simp [mapStmt₁, Turing.TM2.stepAux]
      by_cases h : f v
      · simp [h, ih₁ v S]
      · simp [h, ih₂ v S]
  | goto f =>
      intro v S
      simp [mapStmt₁, stk₁, Turing.TM2.stepAux, mapCfg₁]
  | halt =>
      intro v S
      simp [mapStmt₁, stk₁, Turing.TM2.stepAux, mapCfg₁]

/-- Phase-1 steps mirror `h1`'s steps, for every non-halted `h1` config. -/
lemma step₁_sim (c₁ : Turing.TM2.Cfg (h1.tm).Γ (h1.tm).Λ (h1.tm).σ)
    (hc₁ : c₁.l ≠ none) :
    (compMachine h1 h2).step (mapCfg₁ h1 h2 c₁) = Option.map (mapCfg₁ h1 h2) ((h1.tm).step c₁) := by
  rcases c₁ with ⟨l, v, S⟩
  cases l with
  | none =>
      exfalso
      exact hc₁ rfl
  | some l₁ =>
      simp [FinTM2.step, Turing.TM2.step, mapCfg₁]
      change some (Turing.TM2.stepAux (mapStmt₁ h1 h2 ((h1.tm).m l₁)) (v, (h2.tm).initialState)
          (stk₁ h1 h2 S)) =
        some (mapCfg₁ h1 h2 (Turing.TM2.stepAux ((h1.tm).m l₁) v S))
      exact congrArg some (stepAux_mapStmt₁ h1 h2 ((h1.tm).m l₁) v S)

/-- Updating `h2`'s input stack (embedded as `h1`'s output stack) with the
converted list `L` commutes with the phase-2 embedding. -/
lemma update_stk₂_inl (S : ∀ k : (h2.tm).K, List ((h2.tm).Γ k))
    (L : List ((h2.tm).Γ (h2.tm).k₀)) :
    Function.update (stk₂ h1 h2 S) (Sum.inl (h1.tm).k₁) (List.map (convOut h1 h2) L) =
      stk₂ h1 h2 (Function.update S (h2.tm).k₀ L) := by
  funext k'
  cases k' with
  | inl k'' =>
      by_cases h : k'' = (h1.tm).k₁
      · subst k''
        simp [stk₂, Function.update]
      · simp [stk₂, Function.update, h]
  | inr k'' =>
      by_cases h : k'' = (h2.tm).k₀
      · subst k''
        simp [stk₂, Function.update]
      · simp [stk₂, Function.update, h]

/-- Pushing `L` onto a non-input `h2` stack commutes with the phase-2 embedding. -/
lemma update_stk₂_inr (S : ∀ k : (h2.tm).K, List ((h2.tm).Γ k)) (k : (h2.tm).K)
    (hk : k ≠ (h2.tm).k₀) (L : List ((h2.tm).Γ k)) :
    Function.update (stk₂ h1 h2 S) (Sum.inr k) L = stk₂ h1 h2 (Function.update S k L) := by
  funext k'
  cases k' with
  | inl k'' =>
      by_cases h : k'' = (h1.tm).k₁
      · subst k''
        simp [stk₂, Function.update, hk.symm]
      · simp [stk₂, Function.update, h]
  | inr k'' =>
      by_cases h : k'' = k
      · subst k''
        simp [stk₂, Function.update, hk]
      · by_cases h₂ : k'' = (h2.tm).k₀
        · subst k''
          simp [stk₂, Function.update, hk.symm]
        · simp [stk₂, Function.update, h, h₂]

/-- Executing `mapStmt₂ s` from the phase-2 state mirrors executing `s` in `h2`. -/
lemma stepAux_mapStmt₂ (s : Turing.TM2.Stmt (h2.tm).Γ (h2.tm).Λ (h2.tm).σ) :
    ∀ (v : (h2.tm).σ) (S : ∀ k : (h2.tm).K, List ((h2.tm).Γ k)),
      Turing.TM2.stepAux (mapStmt₂ h1 h2 s) ((h1.tm).initialState, v) (stk₂ h1 h2 S)
        = mapCfg₂ h1 h2 (Turing.TM2.stepAux s v S) := by
  induction s with
  | push k f q ih =>
      intro v S
      simp [mapStmt₂, Turing.TM2.stepAux]
      by_cases h : k = (h2.tm).k₀
      · subst k
        simp [stk₂]
        rw [← List.map_cons]
        exact (congrArg
          (fun s => Turing.TM2.stepAux (mapStmt₂ h1 h2 q) ((h1.tm).initialState, v) s)
          (update_stk₂_inl h1 h2 S (f v :: S (h2.tm).k₀))).trans
          (ih v (Function.update S (h2.tm).k₀ (f v :: S (h2.tm).k₀)))
      · simp [stk₂, h]
        rw [update_stk₂_inr h1 h2 S k h (f v :: S k)]
        exact ih v (Function.update S k (f v :: S k))
  | peek k f q ih =>
      intro v S
      simp [mapStmt₂, Turing.TM2.stepAux]
      by_cases h : k = (h2.tm).k₀
      · subst k
        simp [stk₂, list_head?_map, convIn_convOut]
        exact ih (f v (S (h2.tm).k₀).head?) S
      · simp [stk₂, h]
        exact ih (f v (S k).head?) S
  | pop k f q ih =>
      intro v S
      simp [mapStmt₂, Turing.TM2.stepAux]
      by_cases h : k = (h2.tm).k₀
      · subst k
        simp [stk₂, list_head?_map, convIn_convOut]
        have htail : (List.map (convOut h1 h2) (S (h2.tm).k₀)).tail =
            List.map (convOut h1 h2) ((S (h2.tm).k₀).tail) :=
          list_map_tail (convOut h1 h2) (S (h2.tm).k₀)
        have hstack : Function.update (stk₂ h1 h2 S) (Sum.inl (h1.tm).k₁)
              ((List.map (convOut h1 h2) (S (h2.tm).k₀)).tail) =
            stk₂ h1 h2 (Function.update S (h2.tm).k₀ ((S (h2.tm).k₀).tail)) := by
          rw [htail]
          exact update_stk₂_inl h1 h2 S (S (h2.tm).k₀).tail
        exact (congrArg
          (fun s => Turing.TM2.stepAux (mapStmt₂ h1 h2 q) ((h1.tm).initialState, f v (S (h2.tm).k₀).head?) s)
          hstack).trans
          (ih (f v (S (h2.tm).k₀).head?) (Function.update S (h2.tm).k₀ ((S (h2.tm).k₀).tail)))
      · simp [stk₂, h]
        rw [update_stk₂_inr h1 h2 S k h (S k).tail]
        exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f q ih =>
      intro v S
      simp [mapStmt₂, Turing.TM2.stepAux]
      exact ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v S
      simp [mapStmt₂, Turing.TM2.stepAux]
      by_cases h : f v
      · simp [h, ih₁ v S]
      · simp [h, ih₂ v S]
  | goto f =>
      intro v S
      simp [mapStmt₂, stk₂, Turing.TM2.stepAux, mapCfg₂]
  | halt =>
      intro v S
      simp [mapStmt₂, stk₂, Turing.TM2.stepAux, mapCfg₂]

/-- Phase-2 steps mirror `h2`'s steps. -/
lemma step₂_sim (c₂ : Turing.TM2.Cfg (h2.tm).Γ (h2.tm).Λ (h2.tm).σ) :
    (compMachine h1 h2).step (mapCfg₂ h1 h2 c₂) = Option.map (mapCfg₂ h1 h2) ((h2.tm).step c₂) := by
  rcases c₂ with ⟨l, v, S⟩
  cases l with
  | none =>
      rfl
  | some l₂ =>
      simp [FinTM2.step, Turing.TM2.step, mapCfg₂]
      change some (Turing.TM2.stepAux (mapStmt₂ h1 h2 ((h2.tm).m l₂)) ((h1.tm).initialState, v)
          (stk₂ h1 h2 S)) =
        some (mapCfg₂ h1 h2 (Turing.TM2.stepAux ((h2.tm).m l₂) v S))
      exact congrArg some (stepAux_mapStmt₂ h1 h2 ((h2.tm).m l₂) v S)

/-- `h1`'s step is non-`none` exactly on non-halted configurations. -/
lemma step₁_ne_iff (c₁ : Turing.TM2.Cfg (h1.tm).Γ (h1.tm).Λ (h1.tm).σ) :
    (h1.tm).step c₁ ≠ none ↔ c₁.l ≠ none := by
  constructor
  · intro h hcl
    rcases c₁ with ⟨l, v, S⟩
    cases l
    · simp [Turing.TM2.step, hcl] at h
      exact h rfl
    · cases hcl
  · intro hcl
    rcases c₁ with ⟨l, v, S⟩
    cases l
    · exact (hcl rfl).elim
    · simp [Turing.TM2.step]

/-- `h2`'s step is non-`none` exactly on non-halted configurations. -/
lemma step₂_ne_iff (c₂ : Turing.TM2.Cfg (h2.tm).Γ (h2.tm).Λ (h2.tm).σ) :
    (h2.tm).step c₂ ≠ none ↔ c₂.l ≠ none := by
  constructor
  · intro h hcl
    rcases c₂ with ⟨l, v, S⟩
    cases l
    · simp [Turing.TM2.step, hcl] at h
      exact h rfl
    · cases hcl
  · intro hcl
    rcases c₂ with ⟨l, v, S⟩
    cases l
    · exact (hcl rfl).elim
    · simp [Turing.TM2.step]

/-- The combined step simulates `h1` on every non-halted configuration. -/
lemma stepC_sim₁ (c₁ : Turing.TM2.Cfg (h1.tm).Γ (h1.tm).Λ (h1.tm).σ) :
    (h1.tm).step c₁ ≠ none →
      (compMachine h1 h2).step (mapCfg₁ h1 h2 c₁) = Option.map (mapCfg₁ h1 h2) ((h1.tm).step c₁) :=
  fun hc => step₁_sim h1 h2 c₁ ((step₁_ne_iff h1 c₁).1 hc)

/-- The combined step simulates `h2` on every configuration. -/
lemma stepC_sim₂ (c₂ : Turing.TM2.Cfg (h2.tm).Γ (h2.tm).Λ (h2.tm).σ) :
    (h2.tm).step c₂ ≠ none →
      (compMachine h1 h2).step (mapCfg₂ h1 h2 c₂) = Option.map (mapCfg₂ h1 h2) ((h2.tm).step c₂) :=
  fun _ => step₂_sim h1 h2 c₂

/-- Applying a bind step to `none` stays `none`. -/
lemma iterate_bind_none {σ : Type} (f : σ → Option σ) :
    ∀ n : ℕ, (flip bind f)^[n] none = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (flip bind f)^[n] (bind none f) = none
      simpa using ih

/-- Transport an iterated evaluation through a step simulation. -/
lemma iterate_bind_lift {σ₁ σ₂ : Type} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {a₁ b₁ : σ₁} (tr : σ₁ → σ₂) (hb : f₁ b₁ = none)
    (H : ∀ c₁, f₁ c₁ ≠ none → f₂ (tr c₁) = Option.map tr (f₁ c₁)) :
    ∀ n : ℕ, (flip bind f₁)^[n] (some a₁) = some b₁ →
      (flip bind f₂)^[n] (some (tr a₁)) = some (tr b₁) := by
  intro n
  induction n generalizing a₁ with
  | zero =>
      intro h
      injection h with h₀
      simpa [h₀]
  | succ n ih =>
      intro h
      rw [Function.iterate_succ_apply] at h
      change (flip bind f₁)^[n] (f₁ a₁) = some b₁ at h
      cases hca : f₁ a₁ with
      | none =>
          rw [hca] at h
          rw [iterate_bind_none f₁ n] at h
          cases h
      | some c₁ =>
          rw [hca] at h
          have hH : f₂ (tr a₁) = some (tr c₁) := by
            rw [H a₁ (by rw [hca]; simp)]
            rw [hca]
            simp
          change (flip bind f₂)^[n] (f₂ (tr a₁)) = some (tr b₁)
          rw [hH]
          exact ih (a₁ := c₁) h

/-- Transport an `EvalsTo` through a step simulation. -/
def evalsTo_lift {σ₁ σ₂ : Type} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {a₁ b₁ : σ₁} (tr : σ₁ → σ₂) (h : StateTransition.EvalsTo f₁ a₁ (some b₁))
    (hb : f₁ b₁ = none)
    (H : ∀ c₁, f₁ c₁ ≠ none → f₂ (tr c₁) = Option.map tr (f₁ c₁)) :
    StateTransition.EvalsTo f₂ (tr a₁) (some (tr b₁)) :=
  ⟨h.steps, iterate_bind_lift tr hb H h.steps h.evals_in_steps⟩

/-- Transport an `EvalsToInTime` through a step simulation. -/
def evalsToInTime_lift {σ₁ σ₂ : Type} {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂}
    {a₁ b₁ : σ₁} {m : ℕ} (tr : σ₁ → σ₂)
    (h : StateTransition.EvalsToInTime f₁ a₁ (some b₁) m)
    (hb : f₁ b₁ = none)
    (H : ∀ c₁, f₁ c₁ ≠ none → f₂ (tr c₁) = Option.map tr (f₁ c₁)) :
    StateTransition.EvalsToInTime f₂ (tr a₁) (some (tr b₁)) m :=
  { toEvalsTo := evalsTo_lift tr h.toEvalsTo hb H,
    steps_le_m := by
      change h.toEvalsTo.steps ≤ m
      exact h.steps_le_m }

/-- The number of `push` operations a statement can perform. -/
def pushCount {K : Type} {Γ : K → Type} {Λ : Type} {σ : Type} : Turing.TM2.Stmt Γ Λ σ → ℕ
  | Turing.TM2.Stmt.push _ _ q => 1 + pushCount q
  | Turing.TM2.Stmt.peek _ _ q => pushCount q
  | Turing.TM2.Stmt.pop _ _ q => pushCount q
  | Turing.TM2.Stmt.load _ q => pushCount q
  | Turing.TM2.Stmt.branch _ q₁ q₂ => max (pushCount q₁) (pushCount q₂)
  | Turing.TM2.Stmt.goto _ => 0
  | Turing.TM2.Stmt.halt => 0

/-- Executing a statement grows any single stack by at most the number of
pushes in that statement. -/
lemma stepAux_stk_len_pushCount {K : Type} [DecidableEq K] {Γ : K → Type} {Λ : Type}
    {σ : Type} (s : Turing.TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (S : ∀ k : K, List (Γ k)) (k : K),
      ((Turing.TM2.stepAux s v S).stk k).length ≤ (S k).length + pushCount s := by
  induction s with
  | push k' f q ih =>
      intro v S k
      rw [Turing.TM2.stepAux]
      have h₁ := ih v (Function.update S k' (f v :: S k')) k
      have h₂ : ((Function.update S k' (f v :: S k')) k).length ≤ (S k).length + 1 := by
        by_cases hk : k = k'
        · subst k'
          simp [Function.update]
        · simp [Function.update, hk]
      have hpc : pushCount (Turing.TM2.Stmt.push k' f q) = 1 + pushCount q := by
        simp [pushCount]
      nlinarith [h₁, h₂, hpc]
  | peek k' f q ih =>
      intro v S k
      rw [Turing.TM2.stepAux]
      exact ih (f v (S k').head?) S k
  | pop k' f q ih =>
      intro v S k
      rw [Turing.TM2.stepAux]
      have h₁ := ih (f v (S k').head?) (Function.update S k' (S k').tail) k
      have h₂ : ((Function.update S k' (S k').tail) k).length ≤ (S k).length := by
        by_cases hk : k = k'
        · subst k'
          simp [Function.update]
        · simp [Function.update, hk]
      have hpc : pushCount (Turing.TM2.Stmt.pop k' f q) = pushCount q := by
        simp [pushCount]
      nlinarith [h₁, h₂, hpc]
  | load f q ih =>
      intro v S k
      rw [Turing.TM2.stepAux]
      exact ih (f v) S k
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v S k
      rw [Turing.TM2.stepAux]
      by_cases h : f v
      · have h₁ := ih₁ v S k
        have hpc : pushCount (Turing.TM2.Stmt.branch f q₁ q₂) = max (pushCount q₁) (pushCount q₂) := by
          simp [pushCount]
        simp [h]
        nlinarith [h₁, hpc, Nat.le_max_left (pushCount q₁) (pushCount q₂)]
      · have h₂ := ih₂ v S k
        have hpc : pushCount (Turing.TM2.Stmt.branch f q₁ q₂) = max (pushCount q₁) (pushCount q₂) := by
          simp [pushCount]
        simp [h]
        nlinarith [h₂, hpc, Nat.le_max_right (pushCount q₁) (pushCount q₂)]
  | goto f =>
      intro v S k
      simp [Turing.TM2.stepAux]
  | halt =>
      intro v S k
      simp [Turing.TM2.stepAux]

/-- The maximum number of pushes in any of `h1`'s statements. -/
def maxPushCount₁ : ℕ := by
  letI : Fintype (h1.tm).Λ := h1.tm.ΛFin
  exact @Finset.sup ℕ (h1.tm).Λ (inferInstance : SemilatticeSup ℕ) (inferInstance : OrderBot ℕ)
    Finset.univ (fun l : (h1.tm).Λ => pushCount ((h1.tm).m l))

lemma pushCount₁_le (l : (h1.tm).Λ) : pushCount ((h1.tm).m l) ≤ maxPushCount₁ h1 := by
  letI : Fintype (h1.tm).Λ := h1.tm.ΛFin
  exact @Finset.le_sup ℕ (h1.tm).Λ (inferInstance : SemilatticeSup ℕ) (inferInstance : OrderBot ℕ)
    Finset.univ (fun l : (h1.tm).Λ => pushCount ((h1.tm).m l)) l (Finset.mem_univ l)

/-- Along any run, a stack that grows by at most `M` per step is bounded by
its initial length plus `M` times the number of steps. -/
lemma evalsTo_stk_len_le {tm : FinTM2} {c₀ : tm.Cfg} (k : tm.K) (M : ℕ)
    (hstep : ∀ c d : tm.Cfg, tm.step c = some d → (d.stk k).length ≤ (c.stk k).length + M)
    {b : tm.Cfg} (h : StateTransition.EvalsTo tm.step c₀ (some b)) :
    (b.stk k).length ≤ (c₀.stk k).length + M * h.steps := by
  -- Prove by induction on the iterated run.
  have hmain : ∀ (c₀ : tm.Cfg) (n : ℕ), (flip bind tm.step)^[n] (some c₀) = some b →
      (b.stk k).length ≤ (c₀.stk k).length + M * n := by
    intro c₀ n
    revert c₀
    induction n with
    | zero =>
        intro c₀ hb
        injection hb with h₀
        subst b
        simp
    | succ n ih =>
        intro c₀ hb
        rw [Function.iterate_succ_apply] at hb
        change (flip bind tm.step)^[n] (tm.step c₀) = some b at hb
        cases hc : tm.step c₀ with
        | none =>
            rw [hc] at hb
            rw [iterate_bind_none tm.step n] at hb
            cases hb
        | some d =>
            rw [hc] at hb
            have h₁ := ih d hb
            have h₂ := hstep c₀ d hc
            rw [Nat.mul_succ]
            omega
  exact hmain c₀ h.steps h.evals_in_steps

/-- Along `h1`'s run, its output stack is bounded by the input length plus a
constant multiple of the step count. -/
lemma evalsTo_out_len_le (a : α) :
    (List.map h1.outputAlphabet.invFun (eβ (f a))).length ≤
      (eα a).length + maxPushCount₁ h1 * (h1.outputsFun a).toEvalsTo.steps := by
  have hstep : ∀ c d : (h1.tm).Cfg, (h1.tm).step c = some d →
      (d.stk (h1.tm).k₁).length ≤ (c.stk (h1.tm).k₁).length + maxPushCount₁ h1 := by
    intro c d hcd
    rcases c with ⟨l, v, S⟩
    cases l with
    | none =>
        simp [Turing.TM2.step] at hcd
    | some l₀ =>
        change some (Turing.TM2.stepAux ((h1.tm).m l₀) v S) = some d at hcd
        injection hcd with hd
        subst d
        have hlen := stepAux_stk_len_pushCount ((h1.tm).m l₀) v S (h1.tm).k₁
        have hle := pushCount₁_le h1 l₀
        simp
        omega
  have hrun := evalsTo_stk_len_le (tm := (h1.tm)) (k := (h1.tm).k₁) (M := maxPushCount₁ h1)
      hstep (h1.outputsFun a).toEvalsTo
  -- hrun : (haltList tm₁ out₁).stk k₁₁ .length ≤ (initList tm₁ in₁).stk k₁₁ .length + M * steps
  have hinit : ((initList (h1.tm) (List.map h1.inputAlphabet.invFun (eα a))).stk (h1.tm).k₁).length
      ≤ (eα a).length := by
    by_cases h : (h1.tm).k₁ = (h1.tm).k₀
    · rw [h]
      simp [initList]
    · simp [initList, h]
  -- out₁.length = (haltList out₁).stk k₁₁ .length
  have hout : (List.map h1.outputAlphabet.invFun (eβ (f a))).length =
      ((haltList (h1.tm) (List.map h1.outputAlphabet.invFun (eβ (f a)))).stk (h1.tm).k₁).length := by
    simp [haltList]
  rw [hout]
  omega

/-- Phase 2's time bound, as a function of phase 1's input length. -/
def compTime : Polynomial ℕ :=
  h1.time + (h2.time.comp (Polynomial.X + (maxPushCount₁ h1 : Polynomial ℕ) * h1.time))

@[ext] theorem Cfg_ext {K : Type} {Γ : K → Type} {Λ σ : Type}
    {c d : Turing.TM2.Cfg Γ Λ σ}
    (h₁ : c.l = d.l) (h₂ : c.var = d.var) (h₃ : c.stk = d.stk) : c = d := by
  cases c with
  | mk l₁ v₁ S₁ =>
      cases d with
      | mk l₂ v₂ S₂ =>
          simp_all

/-- `h1`'s output equals `h2`'s input, transported through the alphabet
equivalence. -/
lemma out₁_eq (a : α) :
    List.map h1.outputAlphabet.invFun (eβ (f a)) =
      List.map (convOut h1 h2) (List.map h2.inputAlphabet.invFun (eβ (f a))) := by
  rw [List.map_map]
  congr 1
  funext z
  simp [convOut, Equiv.apply_invFun_apply]

@[simp] lemma initList_stk₀ (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk tm.k₀ = s := by
  simp [initList]

@[simp] lemma initList_stk_of_ne (tm : FinTM2) {k : tm.K} (h : k ≠ tm.k₀)
    (s : List (tm.Γ tm.k₀)) : (initList tm s).stk k = [] := by
  simp [initList, h]

@[simp] lemma haltList_stk₁ (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk tm.k₁ = s := by
  simp [haltList]

@[simp] lemma haltList_stk_of_ne (tm : FinTM2) {k : tm.K} (h : k ≠ tm.k₁)
    (s : List (tm.Γ tm.k₁)) : (haltList tm s).stk k = [] := by
  simp [haltList, h]

@[simp] lemma compk₀_eq : (compMachine h1 h2).k₀ = Sum.inl (h1.tm).k₀ := rfl

@[simp] lemma compk₁_eq (h : (h2.tm).k₀ = (h2.tm).k₁) :
    (compMachine h1 h2).k₁ = Sum.inl (h1.tm).k₁ := by
  simp [compk₁, h]

@[simp] lemma compk₁_eq_ne (h : (h2.tm).k₀ ≠ (h2.tm).k₁) :
    (compMachine h1 h2).k₁ = Sum.inr (h2.tm).k₁ := by
  simp [compk₁, h]

/-!
**Status**: the composite-alphabet cast is closed.  `mapCfg₂_halt_eq` is proved
(axiom-clean).  The blocker was `compMachine` being an opaque `def`: at `rw`'s
reducible transparency the type `(compMachine h1 h2).Γ (compMachine h1 h2).k₁`
does not unfold to `CompΓ h1 h2 (compk₁ h1 h2)`, so the outer `⋯ ▸` cast on the
element-wise goal could not unify.  Making `compMachine` an `abbrev` (reducible)
lets `rw [compOutputAlphabet]` and the element-wise chain
`Equiv.invFun_as_coe` → `Equiv.symm_trans` → `Equiv.cast_symm` → `cast_symm_cancel`
all fire.  The two alphabet cases are isolated as
`compOutputAlphabet_invFun_reuse` (`k₀₂ = k₁₂`, round-trips to `convOut`) and
`compOutputAlphabet_invFun_no_reuse` (`k₀₂ ≠ k₁₂`, round-trips to
`outputAlphabet₂.symm`).

**Done**: `comp_outputsFun` assembles the run (phase 1 via `mapCfg₁`, meeting
`mapCfg₁_halt_eq`, phase 2 via `mapCfg₂`, closing with `mapCfg₂_halt_eq`,
chained by `EvalsToInTime.trans`) and bounds the total time by `compTime` using
`Polynomial.eval_mono_nat` (new: `eval` on `Polynomial ℕ` is monotone) plus
`evalsTo_out_len_le`.  `TM2ComputableInPolyTime.comp_scratch` proves Mathlib's
`proof_wanted TM2ComputableInPolyTime.comp` (axiom-clean).
-/

/-- The phase-1 start configuration. -/
lemma mapCfg₁_init (a : α) :
    mapCfg₁ h1 h2 (initList (h1.tm) (List.map h1.inputAlphabet.invFun (eα a))) =
      initList (compMachine h1 h2) (List.map (compInputAlphabet h1 h2).invFun (eα a)) := by
  apply Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k' =>
        by_cases h : k' = (h1.tm).k₀
        · subst k'
          simp [mapCfg₁, stk₁, compk₀, compInputAlphabet, initList]
        · have hl : (initList (h1.tm) (List.map h1.inputAlphabet.invFun (eα a))).stk k' = [] :=
            initList_stk_of_ne (h1.tm) h (List.map h1.inputAlphabet.invFun (eα a))
          have hr : (initList (compMachine h1 h2) (List.map (compInputAlphabet h1 h2).invFun (eα a))).stk (Sum.inl k') = [] :=
            initList_stk_of_ne (compMachine h1 h2) (by
              intro hk
              exact h (Sum.inl.inj hk)) (List.map (compInputAlphabet h1 h2).invFun (eα a))
          exact hl.trans hr.symm
    | inr k' =>
        simp [mapCfg₁, stk₁, compk₀, compInputAlphabet, initList]

/-- `h1`'s halted configuration is `h2`'s initial configuration. -/
lemma mapCfg₁_halt_eq (a : α) :
    mapCfg₁ h1 h2 (haltList (h1.tm) (List.map h1.outputAlphabet.invFun (eβ (f a)))) =
      mapCfg₂ h1 h2 (initList (h2.tm) (List.map h2.inputAlphabet.invFun (eβ (f a)))) := by
  apply Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k' =>
        by_cases h : k' = (h1.tm).k₁
        · subst k'
          have hl : (mapCfg₁ h1 h2 (haltList (h1.tm) (List.map h1.outputAlphabet.invFun (eβ (f a))))).stk (Sum.inl (h1.tm).k₁)
              = List.map h1.outputAlphabet.invFun (eβ (f a)) := by
            simp [mapCfg₁, stk₁]
          have hr : (mapCfg₂ h1 h2 (initList (h2.tm) (List.map h2.inputAlphabet.invFun (eβ (f a))))).stk (Sum.inl (h1.tm).k₁)
              = List.map (convOut h1 h2) (List.map h2.inputAlphabet.invFun (eβ (f a))) := by
            simp [mapCfg₂, stk₂]
          exact hl.trans ((out₁_eq h1 h2 a).trans hr.symm)
        · simp [mapCfg₁, mapCfg₂, stk₁, stk₂, h]
    | inr k' =>
        by_cases h : k' = (h2.tm).k₀
        · subst k'
          simp [mapCfg₁, mapCfg₂, stk₁, stk₂]
        · simp [mapCfg₁, mapCfg₂, stk₁, stk₂, h]

/-- `compOutputAlphabet`'s inverse on the reuse branch (`k₀ = k₁`), recast to
`h1`'s output alphabet.  The cast round-trip `⋯ ▸ (cast recast.symm w) = w` is
the composite-alphabet cast from `e89de6f`, now closed via the reducible
`compMachine` + `cast_symm_cancel`. -/
lemma compOutputAlphabet_invFun_reuse (h : (h2.tm).k₀ = (h2.tm).k₁) (z : γΓ) :
    (show (compMachine h1 h2).Γ (compMachine h1 h2).k₁ = (h1.tm).Γ (h1.tm).k₁ by
      simp [compk₁, h]) ▸ (compOutputAlphabet h1 h2).invFun z
    = convOut h1 h2 (Eq.ndrec (motive := fun k : (h2.tm).K => (h2.tm).Γ k) (h2.outputAlphabet.invFun z) h.symm) := by
  rw [compOutputAlphabet]
  rw [dif_pos h]
  set w : (h1.tm).Γ (h1.tm).k₁ :=
    convOut h1 h2 (Eq.ndrec (motive := fun k : (h2.tm).K => (h2.tm).Γ k) (h2.outputAlphabet.invFun z) h.symm)
  change (show (compMachine h1 h2).Γ (compMachine h1 h2).k₁ = (h1.tm).Γ (h1.tm).k₁ by
      simp [compk₁, h]) ▸
      cast (show CompΓ h1 h2 (compk₁ h1 h2) = (h1.tm).Γ (h1.tm).k₁ by simp [compk₁, h]).symm w = w
  rw [cast_symm_cancel]

/-- `compOutputAlphabet`'s inverse on the non-reuse branch (`k₀ ≠ k₁`), recast
to `h2`'s output alphabet. -/
lemma compOutputAlphabet_invFun_no_reuse (h : (h2.tm).k₀ ≠ (h2.tm).k₁) (z : γΓ) :
    h2.outputAlphabet.invFun z
      = (show (compMachine h1 h2).Γ (compMachine h1 h2).k₁ = (h2.tm).Γ (h2.tm).k₁ by
          simp [compk₁, h]) ▸ (compOutputAlphabet h1 h2).invFun z := by
  rw [compOutputAlphabet]
  rw [dif_neg h]
  set w : (h2.tm).Γ (h2.tm).k₁ := h2.outputAlphabet.invFun z
  change w = (show (compMachine h1 h2).Γ (compMachine h1 h2).k₁ = (h2.tm).Γ (h2.tm).k₁ by
      simp [compk₁, h]) ▸
      cast (show CompΓ h1 h2 (compk₁ h1 h2) = (h2.tm).Γ (h2.tm).k₁ by simp [compk₁, h]).symm w
  rw [cast_symm_cancel]

/-- `h2`'s halted configuration is the combined machine's halted configuration. -/
lemma mapCfg₂_halt_eq (a : α) :
    mapCfg₂ h1 h2 (haltList (h2.tm) (List.map h2.outputAlphabet.invFun (eγ (g (f a))))) =
      haltList (compMachine h1 h2) (List.map (compOutputAlphabet h1 h2).invFun (eγ (g (f a)))) := by
  apply Cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k' =>
        by_cases h : (h2.tm).k₀ = (h2.tm).k₁
        · by_cases hk : k' = (h1.tm).k₁
          · subst k'
            simp [mapCfg₂, stk₂, compk₁, h, haltList]
            intro a₁ _
            exact (compOutputAlphabet_invFun_reuse h1 h2 h a₁).symm
          · simp [mapCfg₂, stk₂, compk₁, h, hk, haltList]
        · by_cases hk : k' = (h1.tm).k₁
          · subst k'
            simp [mapCfg₂, stk₂, compk₁, h, haltList]
          · simp [mapCfg₂, stk₂, compk₁, h, hk, haltList]
    | inr k' =>
        by_cases h : (h2.tm).k₀ = (h2.tm).k₁
        · by_cases hk : k' = (h2.tm).k₀
          · subst k'
            simp [mapCfg₂, stk₂, compk₁, h, haltList]
          · by_cases hk2 : k' = (h2.tm).k₁
            · subst k'
              exfalso
              exact hk h.symm
            · simp [mapCfg₂, stk₂, compk₁, h, hk, hk2, haltList]
        · by_cases hk : k' = (h2.tm).k₁
          · subst k'
            have hk0 : ¬(h2.tm).k₁ = (h2.tm).k₀ := by
              exact fun h₀ => h h₀.symm
            simp [mapCfg₂, stk₂, compk₁, h, hk0, haltList]
            intro a₁ _
            exact (compOutputAlphabet_invFun_no_reuse h1 h2 h a₁)
          · by_cases hk2 : k' = (h2.tm).k₀
            · subst k'
              simp [mapCfg₂, stk₂, compk₁, h, hk, haltList]
            · simp [mapCfg₂, stk₂, compk₁, h, hk, hk2, haltList]

/-- `eval` on `Polynomial ℕ` is monotone: coefficients and arguments are
nonnegative, so raising the input can only raise the value. -/
lemma Polynomial.eval_mono_nat {p : Polynomial ℕ} {n m : ℕ} (hnm : n ≤ m) :
    p.eval n ≤ p.eval m := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  apply Finset.sum_le_sum
  intro e he
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnm e)

/-- The combined machine's `outputsFun`: phase 1 runs `h1` (`mapCfg₁`), phase 2
runs `h2` (`mapCfg₂`), and the two phases meet at `mapCfg₁_halt_eq`; the total
time is bounded by `compTime`. -/
def comp_outputsFun (a : α) :
    TM2OutputsInTime (compMachine h1 h2)
      (List.map (compInputAlphabet h1 h2).invFun (eα a))
      (some (List.map (compOutputAlphabet h1 h2).invFun (eγ (g (f a)))))
      ((compTime h1 h2).eval (eα a).length) := by
  let n := (eα a).length
  let M := maxPushCount₁ h1
  let m₁ := (h1.time).eval n
  let m₂ := (h2.time).eval (eβ (f a)).length
  let init₁ := initList (h1.tm) (List.map h1.inputAlphabet.invFun (eα a))
  let halt₁ := haltList (h1.tm) (List.map h1.outputAlphabet.invFun (eβ (f a)))
  let init₂ := initList (h2.tm) (List.map h2.inputAlphabet.invFun (eβ (f a)))
  let halt₂ := haltList (h2.tm) (List.map h2.outputAlphabet.invFun (eγ (g (f a))))
  let initC := initList (compMachine h1 h2) (List.map (compInputAlphabet h1 h2).invFun (eα a))
  let haltC := haltList (compMachine h1 h2) (List.map (compOutputAlphabet h1 h2).invFun (eγ (g (f a))))
  change EvalsToInTime (compMachine h1 h2).step initC (some haltC) ((compTime h1 h2).eval n)

  -- phase 1
  have hr₁ : EvalsToInTime (h1.tm).step init₁ (some halt₁) m₁ := by
    exact h1.outputsFun a
  have hstop₁ : (h1.tm).step halt₁ = none := by
    rfl
  have hlift₁ :
      EvalsToInTime (compMachine h1 h2).step (mapCfg₁ h1 h2 init₁) (some (mapCfg₁ h1 h2 halt₁)) m₁ :=
    evalsToInTime_lift (mapCfg₁ h1 h2) hr₁ hstop₁ (stepC_sim₁ h1 h2)
  have hmid : mapCfg₁ h1 h2 halt₁ = mapCfg₂ h1 h2 init₂ := mapCfg₁_halt_eq h1 h2 a
  have hlift₁' :
      EvalsToInTime (compMachine h1 h2).step (mapCfg₁ h1 h2 init₁) (some (mapCfg₂ h1 h2 init₂)) m₁ := by
    rwa [hmid] at hlift₁

  -- phase 2
  have hr₂ : EvalsToInTime (h2.tm).step init₂ (some halt₂) m₂ := by
    exact h2.outputsFun (f a)
  have hstop₂ : (h2.tm).step halt₂ = none := by
    rfl
  have hlift₂ :
      EvalsToInTime (compMachine h1 h2).step (mapCfg₂ h1 h2 init₂) (some (mapCfg₂ h1 h2 halt₂)) m₂ :=
    evalsToInTime_lift (mapCfg₂ h1 h2) hr₂ hstop₂ (stepC_sim₂ h1 h2)
  have hend : mapCfg₂ h1 h2 halt₂ = haltC := mapCfg₂_halt_eq h1 h2 a
  have hlift₂' : EvalsToInTime (compMachine h1 h2).step (mapCfg₂ h1 h2 init₂) (some haltC) m₂ := by
    rwa [hend] at hlift₂

  -- chain the phases
  have hrun :
      EvalsToInTime (compMachine h1 h2).step (mapCfg₁ h1 h2 init₁) (some haltC) (m₂ + m₁) :=
    EvalsToInTime.trans (compMachine h1 h2).step m₁ m₂ (mapCfg₁ h1 h2 init₁) (mapCfg₂ h1 h2 init₂)
      (some haltC) hlift₁' hlift₂'
  have hinit : initC = mapCfg₁ h1 h2 init₁ := (mapCfg₁_init h1 h2 a).symm
  have hrun' : EvalsToInTime (compMachine h1 h2).step initC (some haltC) (m₂ + m₁) := by
    rw [hinit]
    exact hrun

  -- time bound
  have hsteps₁ : (h1.outputsFun a).toEvalsTo.steps ≤ m₁ := by
    simpa [m₁, n] using (h1.outputsFun a).steps_le_m
  have hlen₁ : (List.map h1.outputAlphabet.invFun (eβ (f a))).length = (eβ (f a)).length := by
    simp
  have hle₁ := evalsTo_out_len_le h1 a
  have hmul₁ : maxPushCount₁ h1 * (h1.outputsFun a).toEvalsTo.steps ≤ maxPushCount₁ h1 * m₁ := by
    exact Nat.mul_le_mul_left (maxPushCount₁ h1) hsteps₁
  have hL : (eβ (f a)).length ≤ n + M * m₁ := by
    dsimp [M, n]
    rw [hlen₁] at hle₁
    omega
  have hm₂ : m₂ ≤ (h2.time).eval (n + M * m₁) := by
    dsimp [m₂]
    exact Polynomial.eval_mono_nat hL
  have hcomp : (compTime h1 h2).eval n = m₁ + (h2.time).eval (n + M * m₁) := by
    dsimp [m₁, M, compTime]
    simp [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X, Polynomial.eval_natCast_mul]
  have hbound : m₂ + m₁ ≤ (compTime h1 h2).eval n := by
    omega
  exact { hrun' with steps_le_m := le_trans hrun'.steps_le_m hbound }

/-- The composition of two polytime TM2 machines is polytime.  This is Mathlib's
`proof_wanted TM2ComputableInPolyTime.comp`. -/
theorem TM2ComputableInPolyTime.comp_scratch
    (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  exact ⟨{ tm := compMachine h1 h2,
           inputAlphabet := compInputAlphabet h1 h2,
           outputAlphabet := compOutputAlphabet h1 h2,
           time := compTime h1 h2,
           outputsFun := comp_outputsFun h1 h2 }⟩

end ScratchComp

end Turing

end
