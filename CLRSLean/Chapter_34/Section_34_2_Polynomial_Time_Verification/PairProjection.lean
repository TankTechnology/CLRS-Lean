import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time

/-!
# Pair projection machine (for `P ⊆ NP`)

A TM2 machine computing `pr ↦ pr.2` from the pair-encoded input
`pairEncoding x y` (a single string with a `none` separator), in polynomial
time.  This is the "verifier ignores the certificate" construction behind
Theorem 34.2 (`P ⊆ NP`).

Main results:

- Construction `prjMachine`: three stacks (input/temp/output), phases
  `scan`/`copy₁`/`copy₂`/`fin`; the LIFO-stack double pass through `temp`
  outputs `y` in the right order.
- Phase lemmas `scan_phase`, `copy1_phase`, `copy2_phase`, `fin_step`.
- Theorem `prjComputableInPolyTime`: `pairEncoding x y ↦ y` is polytime.
-/

noncomputable section
open Computability StateTransition
open CLRS.Chapter34

namespace Turing

namespace Prj

inductive PrjK : Type
  | input | temp | output
deriving DecidableEq, Fintype, Inhabited

inductive PrjLabel : Type
  | scan | copy₁ | copy₂ | fin
deriving DecidableEq, Fintype, Inhabited

inductive PrjSt (Γ : Type) : Type
  | scanSym | sep | scanEmpty
  | copySym (a : Γ) | copyEnd
  | copy2Sym (a : Γ) | copy2End
deriving Fintype, Inhabited

variable (Γ : Type) [Fintype Γ] [Inhabited Γ]

abbrev Γk : PrjK → Type
  | PrjK.input => Option Γ
  | PrjK.temp => Γ
  | PrjK.output => Γ

def prog : PrjLabel → TM2.Stmt (Γk Γ) PrjLabel (PrjSt Γ)
  | PrjLabel.scan =>
      TM2.Stmt.pop PrjK.input (fun _ x =>
        match x with
        | some (some _) => PrjSt.scanSym
        | some none => PrjSt.sep
        | none => PrjSt.scanEmpty)
      (TM2.Stmt.goto (fun v =>
        match v with
        | PrjSt.scanSym => PrjLabel.scan
        | PrjSt.sep => PrjLabel.copy₁
        | _ => PrjLabel.fin))
  | PrjLabel.copy₁ =>
      TM2.Stmt.pop PrjK.input (fun _ x =>
        match x with
        | some (some a) => PrjSt.copySym a
        | _ => PrjSt.copyEnd)
      (TM2.Stmt.branch (fun v => match v with | PrjSt.copySym _ => True | _ => False)
        (TM2.Stmt.push PrjK.temp (fun v => match v with | PrjSt.copySym a => a | _ => default)
          (TM2.Stmt.goto (fun _ => PrjLabel.copy₁)))
        (TM2.Stmt.goto (fun _ => PrjLabel.copy₂)))
  | PrjLabel.copy₂ =>
      TM2.Stmt.pop PrjK.temp (fun _ x =>
        match x with
        | some a => PrjSt.copy2Sym a
        | none => PrjSt.copy2End)
      (TM2.Stmt.branch (fun v => match v with | PrjSt.copy2Sym _ => True | _ => False)
        (TM2.Stmt.push PrjK.output (fun v => match v with | PrjSt.copy2Sym a => a | _ => default)
          (TM2.Stmt.goto (fun _ => PrjLabel.copy₂)))
        (TM2.Stmt.goto (fun _ => PrjLabel.fin)))
  | PrjLabel.fin =>
      TM2.Stmt.load (fun _ => PrjSt.scanSym) TM2.Stmt.halt

abbrev prjMachine : FinTM2 where
  K := PrjK
  k₀ := PrjK.input
  k₁ := PrjK.output
  Γ := Γk Γ
  Λ := PrjLabel
  main := PrjLabel.scan
  σ := PrjSt Γ
  initialState := PrjSt.scanSym
  m := prog Γ

def prjInputAlphabet : (prjMachine Γ).Γ (prjMachine Γ).k₀ ≃ Option Γ := Equiv.refl _
def prjOutputAlphabet : (prjMachine Γ).Γ (prjMachine Γ).k₁ ≃ Γ := Equiv.refl _

def Sstep : (prjMachine Γ).Cfg → Option (prjMachine Γ).Cfg := (prjMachine Γ).step

@[simp] lemma Function.update_update_same {α : Type} [DecidableEq α] {β : α → Type}
    (f : ∀ a, β a) (a : α) (b c : β a) :
    Function.update (Function.update f a b) a c = Function.update f a c := by
  funext k
  by_cases hk : k = a
  · subst k
    simp [Function.update]
  · simp [Function.update, hk]

-- Phase 1: scan past `xs` and the separator.
lemma scan_phase {xs : List Γ} {rest : List (Option Γ)} {S : ∀ k : PrjK, List (Γk Γ k)}
    (h : S PrjK.input = List.map some xs ++ none :: rest) :
    (flip bind (Sstep Γ))^[xs.length + 1]
        (some (⟨some PrjLabel.scan, PrjSt.scanSym, S⟩ : (prjMachine Γ).Cfg))
      = some (⟨some PrjLabel.copy₁, PrjSt.sep, Function.update S PrjK.input rest⟩ : (prjMachine Γ).Cfg) := by
  induction xs generalizing S with
  | nil =>
      have hhead : (S PrjK.input).head? = some none := by
        rw [h]; simp
      have htail : (S PrjK.input).tail = rest := by
        rw [h]; simp
      simp [Sstep, prjMachine, prog, flip, hhead, htail]
  | cons a xs' ih =>
      have hhead : (S PrjK.input).head? = some (some a) := by
        rw [h]; simp
      have htail : (S PrjK.input).tail = List.map some xs' ++ none :: rest := by
        rw [h]; simp
      have hone : (flip bind (Sstep Γ)) (some (⟨some PrjLabel.scan, PrjSt.scanSym, S⟩ : (prjMachine Γ).Cfg))
          = some (⟨some PrjLabel.scan, PrjSt.scanSym,
              Function.update S PrjK.input (List.map some xs' ++ none :: rest)⟩ : (prjMachine Γ).Cfg) := by
        simp [Sstep, prjMachine, prog, flip, hhead, htail]
      rw [show ((a :: xs').length + 1) = (xs'.length + 1) + 1 by simp]
      rw [Function.iterate_succ_apply]
      rw [hone]
      have hih := ih (S := Function.update S PrjK.input (List.map some xs' ++ none :: rest))
        (by simpa [Function.update] using htail)
      calc
        (flip bind (Sstep Γ))^[xs'.length + 1]
              (some (⟨some PrjLabel.scan, PrjSt.scanSym,
                  Function.update S PrjK.input (List.map some xs' ++ none :: rest)⟩ : (prjMachine Γ).Cfg))
            = some (⟨some PrjLabel.copy₁, PrjSt.sep,
                Function.update (Function.update S PrjK.input (List.map some xs' ++ none :: rest))
                  PrjK.input rest⟩ : (prjMachine Γ).Cfg) := hih
        _ = some (⟨some PrjLabel.copy₁, PrjSt.sep, Function.update S PrjK.input rest⟩ : (prjMachine Γ).Cfg) := by
              simp [Function.update_update_same]

-- Updating a key, then updating a different key with its own current value, is redundant.
lemma update_other_redundant {S : ∀ k : PrjK, List (Γk Γ k)} (a : PrjK) (v : List (Γk Γ a)) (b : PrjK)
    (hb : b ≠ a) :
    Function.update (Function.update S a v) b (S b) = Function.update S a v := by
  funext k
  by_cases h1 : k = a
  · subst k
    have hne : a ≠ b := fun h => hb h.symm
    simp [Function.update, hne]
  · by_cases h2 : k = b
    · subst k
      simp [Function.update, h1]
    · simp [Function.update, h1, h2]

-- The full collapse after one symbol copy in the input→temp phase:
-- the final temp accumulates `D.reverse` (the remaining `ys'`) onto `a :: B`.
lemma copy1_cons_collapse {S : ∀ k : PrjK, List (Γk Γ k)} (a : Γ) (A C : List (Option Γ))
    (B D : List Γ) :
    Function.update (Function.update (Function.update (Function.update S PrjK.input A)
        PrjK.temp (a :: B)) PrjK.input C) PrjK.temp (D.reverse ++ (a :: B))
      = Function.update (Function.update S PrjK.input C) PrjK.temp ((a :: D).reverse ++ B) := by
  funext k
  by_cases h1 : k = PrjK.input <;> by_cases h2 : k = PrjK.temp <;> by_cases h3 : k = PrjK.output <;>
    simp [Function.update, h1, h2, h3, List.reverse_cons, List.cons_append, List.append_assoc]

-- The full collapse after one symbol copy in the temp→output phase.
lemma copy2_cons_collapse {S : ∀ k : PrjK, List (Γk Γ k)} (a : Γ) (A B C D : List Γ) :
    Function.update (Function.update (Function.update (Function.update S PrjK.temp A)
        PrjK.output (a :: B)) PrjK.temp C) PrjK.output (D.reverse ++ (a :: B))
      = Function.update (Function.update S PrjK.temp C) PrjK.output ((a :: D).reverse ++ B) := by
  funext k
  by_cases h1 : k = PrjK.input <;> by_cases h2 : k = PrjK.temp <;> by_cases h3 : k = PrjK.output <;>
    simp [Function.update, h1, h2, h3, List.reverse_cons, List.cons_append, List.append_assoc]

-- Phase 2: copy `ys` from input to temp (accumulating into the existing temp).
lemma copy1_phase {ys : List Γ} {S : ∀ k : PrjK, List (Γk Γ k)} (v : PrjSt Γ)
    (h : S PrjK.input = List.map some ys) :
    (flip bind (Sstep Γ))^[ys.length + 1]
        (some (⟨some PrjLabel.copy₁, v, S⟩ : (prjMachine Γ).Cfg))
      = some (⟨some PrjLabel.copy₂, PrjSt.copyEnd,
          Function.update (Function.update S PrjK.input []) PrjK.temp (ys.reverse ++ S PrjK.temp)⟩ : (prjMachine Γ).Cfg) := by
  induction ys generalizing S v with
  | nil =>
      have hhead : (S PrjK.input).head? = none := by
        rw [h]; simp
      have htail : (S PrjK.input).tail = [] := by
        rw [h]; simp
      have hrev : ([] : List Γ).reverse ++ S PrjK.temp = S PrjK.temp := by simp
      have hcollapse :
          Function.update (Function.update S PrjK.input []) PrjK.temp (S PrjK.temp) = Function.update S PrjK.input [] := by
        funext k
        by_cases h1 : k = PrjK.input
        · subst k
          simp [Function.update]
        · by_cases h2 : k = PrjK.temp
          · subst k
            simp [Function.update, h1]
          · simp [Function.update, h1, h2]
      simp [Sstep, prjMachine, prog, flip, hhead, htail]
      rw [hcollapse]
  | cons a ys' ih =>
      have hhead : (S PrjK.input).head? = some (some a) := by
        rw [h]; simp
      have htail : (S PrjK.input).tail = List.map some ys' := by
        rw [h]; simp
      have hone :
          (flip bind (Sstep Γ)) (some (⟨some PrjLabel.copy₁, v, S⟩ : (prjMachine Γ).Cfg))
            = some (⟨some PrjLabel.copy₁, PrjSt.copySym a,
                Function.update (Function.update S PrjK.input (List.map some ys')) PrjK.temp (a :: S PrjK.temp)⟩ : (prjMachine Γ).Cfg) := by
        simp [Sstep, prjMachine, prog, flip, hhead, htail]
      rw [show ((a :: ys').length + 1) = (ys'.length + 1) + 1 by simp]
      rw [Function.iterate_succ_apply]
      rw [hone]
      have hih := ih (v := PrjSt.copySym a)
        (S := Function.update (Function.update S PrjK.input (List.map some ys')) PrjK.temp (a :: S PrjK.temp))
        (by simp [Function.update])
      have hcollapse := @copy1_cons_collapse Γ _ _ S a (List.map some ys') [] (S PrjK.temp) ys'
      calc
        (flip bind (Sstep Γ))^[ys'.length + 1]
              (some (⟨some PrjLabel.copy₁, PrjSt.copySym a,
                  Function.update (Function.update S PrjK.input (List.map some ys')) PrjK.temp (a :: S PrjK.temp)⟩ : (prjMachine Γ).Cfg))
            = some (⟨some PrjLabel.copy₂, PrjSt.copyEnd,
                Function.update
                  (Function.update (Function.update (Function.update S PrjK.input (List.map some ys')) PrjK.temp (a :: S PrjK.temp))
                    PrjK.input []) PrjK.temp
                  (ys'.reverse ++ (a :: S PrjK.temp))⟩ : (prjMachine Γ).Cfg) := hih
        _ = some (⟨some PrjLabel.copy₂, PrjSt.copyEnd,
                Function.update (Function.update S PrjK.input []) PrjK.temp
                  ((a :: ys').reverse ++ S PrjK.temp)⟩ : (prjMachine Γ).Cfg) := by
              exact congrArg (fun stk => some (⟨some PrjLabel.copy₂, PrjSt.copyEnd, stk⟩ : (prjMachine Γ).Cfg)) hcollapse

-- Phase 3: copy `ys` from temp to output (accumulating into the existing output).
lemma copy2_phase {ys : List Γ} {S : ∀ k : PrjK, List (Γk Γ k)} (v : PrjSt Γ)
    (h : S PrjK.temp = ys) :
    (flip bind (Sstep Γ))^[ys.length + 1]
        (some (⟨some PrjLabel.copy₂, v, S⟩ : (prjMachine Γ).Cfg))
      = some (⟨some PrjLabel.fin, PrjSt.copy2End,
          Function.update (Function.update S PrjK.temp []) PrjK.output (ys.reverse ++ S PrjK.output)⟩ : (prjMachine Γ).Cfg) := by
  induction ys generalizing S v with
  | nil =>
      have hhead : (S PrjK.temp).head? = none := by
        rw [h]; simp
      have htail : (S PrjK.temp).tail = [] := by
        rw [h]; simp
      have hrev : ([] : List Γ).reverse ++ S PrjK.output = S PrjK.output := by simp
      have hcollapse :
          Function.update (Function.update S PrjK.temp []) PrjK.output (S PrjK.output) = Function.update S PrjK.temp [] := by
        funext k
        by_cases h1 : k = PrjK.temp
        · subst k
          simp [Function.update]
        · by_cases h2 : k = PrjK.output
          · subst k
            simp [Function.update, h1]
          · simp [Function.update, h1, h2]
      simp [Sstep, prjMachine, prog, flip, hhead, htail]
      rw [hcollapse]
  | cons a ys' ih =>
      have hhead : (S PrjK.temp).head? = some a := by
        rw [h]; simp
      have htail : (S PrjK.temp).tail = ys' := by
        rw [h]; simp
      have hone :
          (flip bind (Sstep Γ)) (some (⟨some PrjLabel.copy₂, v, S⟩ : (prjMachine Γ).Cfg))
            = some (⟨some PrjLabel.copy₂, PrjSt.copy2Sym a,
                Function.update (Function.update S PrjK.temp ys') PrjK.output (a :: S PrjK.output)⟩ : (prjMachine Γ).Cfg) := by
        simp [Sstep, prjMachine, prog, flip, hhead, htail]
      rw [show ((a :: ys').length + 1) = (ys'.length + 1) + 1 by simp]
      rw [Function.iterate_succ_apply]
      rw [hone]
      have hih := ih (v := PrjSt.copy2Sym a)
        (S := Function.update (Function.update S PrjK.temp ys') PrjK.output (a :: S PrjK.output))
        (by simp [Function.update])
      have hcollapse := @copy2_cons_collapse Γ _ _ S a ys' (S PrjK.output) [] ys'
      calc
        (flip bind (Sstep Γ))^[ys'.length + 1]
              (some (⟨some PrjLabel.copy₂, PrjSt.copy2Sym a,
                  Function.update (Function.update S PrjK.temp ys') PrjK.output (a :: S PrjK.output)⟩ : (prjMachine Γ).Cfg))
            = some (⟨some PrjLabel.fin, PrjSt.copy2End,
                Function.update
                  (Function.update (Function.update (Function.update S PrjK.temp ys') PrjK.output (a :: S PrjK.output))
                    PrjK.temp []) PrjK.output
                  (ys'.reverse ++ (a :: S PrjK.output))⟩ : (prjMachine Γ).Cfg) := hih
        _ = some (⟨some PrjLabel.fin, PrjSt.copy2End,
                Function.update (Function.update S PrjK.temp []) PrjK.output
                  ((a :: ys').reverse ++ S PrjK.output)⟩ : (prjMachine Γ).Cfg) := by
              exact congrArg (fun stk => some (⟨some PrjLabel.fin, PrjSt.copy2End, stk⟩ : (prjMachine Γ).Cfg)) hcollapse

-- The finishing label: reset the state and halt.
lemma fin_step {S : ∀ k : PrjK, List (Γk Γ k)} :
    (flip bind (Sstep Γ)) (some (⟨some PrjLabel.fin, PrjSt.copy2End, S⟩ : (prjMachine Γ).Cfg))
      = some (⟨none, PrjSt.scanSym, S⟩ : (prjMachine Γ).Cfg) := by
  simp [Sstep, prjMachine, prog, flip]

/-- The pair-projection machine computes `pr ↦ pr.2` in polynomial time. -/
def prjComputableInPolyTime :
    TM2ComputableInPolyTime (fun pr : List Γ × List Γ => pairEncoding pr.1 pr.2)
      (id : List Γ → List Γ) (fun pr => pr.2) where
  tm := prjMachine Γ
  inputAlphabet := prjInputAlphabet Γ
  outputAlphabet := prjOutputAlphabet Γ
  time := 2 * Polynomial.X + 4
  outputsFun := fun pr => by
    rcases pr with ⟨x, y⟩
    simp only [TM2OutputsInTime, prjInputAlphabet, prjOutputAlphabet, id, Prod.fst, Prod.snd]
    let init : (prjMachine Γ).Cfg := initList (prjMachine Γ) (pairEncoding x y)
    let C1 : (prjMachine Γ).Cfg := ⟨some PrjLabel.copy₁, PrjSt.sep,
        Function.update init.stk PrjK.input (List.map some y)⟩
    let C2 : (prjMachine Γ).Cfg := ⟨some PrjLabel.copy₂, PrjSt.copyEnd,
        Function.update (Function.update C1.stk PrjK.input []) PrjK.temp (y.reverse ++ C1.stk PrjK.temp)⟩
    let C3 : (prjMachine Γ).Cfg := ⟨some PrjLabel.fin, PrjSt.copy2End,
        Function.update (Function.update C2.stk PrjK.temp []) PrjK.output (y.reverse.reverse ++ C2.stk PrjK.output)⟩
    let C4 : (prjMachine Γ).Cfg := ⟨none, PrjSt.scanSym, C3.stk⟩
    have h0 : init.stk PrjK.input = List.map some x ++ none :: List.map some y := by
      simp [init, initList, pairEncoding]
    have htemp0 : init.stk PrjK.temp = [] := by
      simp [init, initList]
    let e1 : EvalsTo (Sstep Γ) init (some C1) := by
      refine ⟨x.length + 1, ?_⟩
      rw [show init = (⟨some PrjLabel.scan, PrjSt.scanSym, init.stk⟩ : (prjMachine Γ).Cfg) by rfl]
      change (flip bind (Sstep Γ))^[x.length + 1]
          (some (⟨some PrjLabel.scan, PrjSt.scanSym, init.stk⟩ : (prjMachine Γ).Cfg)) = some C1
      rw [show C1 = (⟨some PrjLabel.copy₁, PrjSt.sep, Function.update init.stk PrjK.input (List.map some y)⟩ : (prjMachine Γ).Cfg) by rfl]
      exact scan_phase (Γ := Γ) h0
    have h1 : C1.stk PrjK.input = List.map some y := by
      simp [C1, Function.update]
    let e2 : EvalsTo (Sstep Γ) C1 (some C2) := by
      refine ⟨y.length + 1, ?_⟩
      rw [show C1 = (⟨some PrjLabel.copy₁, PrjSt.sep, C1.stk⟩ : (prjMachine Γ).Cfg) by rfl]
      change (flip bind (Sstep Γ))^[y.length + 1]
          (some (⟨some PrjLabel.copy₁, PrjSt.sep, C1.stk⟩ : (prjMachine Γ).Cfg)) = some C2
      change (flip bind (Sstep Γ))^[y.length + 1]
          (some (⟨some PrjLabel.copy₁, PrjSt.sep, C1.stk⟩ : (prjMachine Γ).Cfg))
        = some (⟨some PrjLabel.copy₂, PrjSt.copyEnd,
            Function.update (Function.update C1.stk PrjK.input []) PrjK.temp (y.reverse ++ C1.stk PrjK.temp)⟩ : (prjMachine Γ).Cfg)
      exact copy1_phase (Γ := Γ) (v := PrjSt.sep) h1
    have ht1 : C1.stk PrjK.temp = [] := by
      simp [C1, htemp0, Function.update]
    have h2 : C2.stk PrjK.temp = y.reverse := by
      simp [C2, ht1, Function.update]
    let e3 : EvalsTo (Sstep Γ) C2 (some C3) := by
      refine ⟨y.reverse.length + 1, ?_⟩
      rw [show C2 = (⟨some PrjLabel.copy₂, PrjSt.copyEnd, C2.stk⟩ : (prjMachine Γ).Cfg) by rfl]
      change (flip bind (Sstep Γ))^[y.reverse.length + 1]
          (some (⟨some PrjLabel.copy₂, PrjSt.copyEnd, C2.stk⟩ : (prjMachine Γ).Cfg)) = some C3
      change (flip bind (Sstep Γ))^[y.reverse.length + 1]
          (some (⟨some PrjLabel.copy₂, PrjSt.copyEnd, C2.stk⟩ : (prjMachine Γ).Cfg))
        = some (⟨some PrjLabel.fin, PrjSt.copy2End,
            Function.update (Function.update C2.stk PrjK.temp []) PrjK.output (y.reverse.reverse ++ C2.stk PrjK.output)⟩ : (prjMachine Γ).Cfg)
      exact copy2_phase (Γ := Γ) (v := PrjSt.copyEnd) h2
    let e4 : EvalsTo (Sstep Γ) C3 (some C4) := by
      refine ⟨1, ?_⟩
      rw [show C3 = (⟨some PrjLabel.fin, PrjSt.copy2End, C3.stk⟩ : (prjMachine Γ).Cfg) by rfl]
      change (flip bind (Sstep Γ)) (some (⟨some PrjLabel.fin, PrjSt.copy2End, C3.stk⟩ : (prjMachine Γ).Cfg)) = some C4
      change (flip bind (Sstep Γ)) (some (⟨some PrjLabel.fin, PrjSt.copy2End, C3.stk⟩ : (prjMachine Γ).Cfg))
        = some (⟨none, PrjSt.scanSym, C3.stk⟩ : (prjMachine Γ).Cfg)
      exact fin_step (Γ := Γ) (S := C3.stk)
    let e1234 : EvalsTo (Sstep Γ) init (some C4) := by
      exact EvalsTo.trans (Sstep Γ) init C1 (some C2) e1 e2
        |> fun h12 => EvalsTo.trans (Sstep Γ) init C2 (some C3) h12 e3
        |> fun h123 => EvalsTo.trans (Sstep Γ) init C3 (some C4) h123 e4
    have hout0 : init.stk PrjK.output = [] := by
      simp [init, initList]
    have ho2 : C2.stk PrjK.output = [] := by
      simp [C2, C1, hout0, Function.update]
    have ho3 : C3.stk PrjK.output = y := by
      simp [C3, ho2, Function.update, List.reverse_reverse, List.append_nil]
    have hi3 : C3.stk PrjK.input = [] := by
      simp [C3, C2, Function.update]
    have ht3 : C3.stk PrjK.temp = [] := by
      simp [C3, Function.update]
    have hstk : C3.stk = (haltList (prjMachine Γ) y).stk := by
      funext k
      cases k with
      | input => simpa [haltList, hi3]
      | temp => simpa [haltList, ht3]
      | output => simpa [haltList, ho3]
    have hfinal : C4 = haltList (prjMachine Γ) y := by
      simp [C4, haltList, hstk]
    let efin : EvalsTo (Sstep Γ) init (some (haltList (prjMachine Γ) y)) := by
      simpa [hfinal] using e1234
    have htime : (2 * Polynomial.X + 4).eval (pairEncoding x y).length = 2 * (pairEncoding x y).length + 4 := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_natCast]
    have hlen_pe : (pairEncoding x y).length = x.length + y.length + 1 := by
      simp [pairEncoding]
      omega
    have hlen_rev : y.reverse.length = y.length := by
      simp
    have hsteps_le : e1234.steps ≤ 2 * (pairEncoding x y).length + 4 := by
      change 1 + (y.reverse.length + 1 + (y.length + 1 + (x.length + 1))) ≤ 2 * (pairEncoding x y).length + 4
      omega
    simpa [Sstep, init, prjInputAlphabet, prjOutputAlphabet, hfinal] using
      (⟨e1234, by
        rw [htime]
        exact hsteps_le⟩ : EvalsToInTime (Sstep Γ) init (some C4)
        ((2 * Polynomial.X + 4).eval (pairEncoding x y).length))

end Prj

end Turing

end
