import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B9_Junk

/-!
# Dev B10: the recursive descent (`parse_phase`)

The `parse_phase` run lemma: the recursive descent that reads `inp`, emits the reversed Tseitin clauses, pushes the value variable, and reaches `reduce`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- parse: the recursive descent (`parse_phase`)
--
-- The `parse_phase` lemma is the run lemma for the recursive descent.  For any
-- input `inp`, `decodeAux inp.length inp` extracts the first formula `f` and
-- the continuation `rest`; the machine reads `inp` from `rd`, emits the
-- reversed Tseitin clauses of `f` onto `o`, pushes `f`'s value variable onto
-- `val`, advances the counter past the auxiliary variables allocated for `f`,
-- and reaches `reduce` with the continuation `rest` on `in`.  Malformed input
-- (end of input, stray `endMark`, or a `varMark` with no index run) yields
-- `const false`, which the junk `const false` phases handle.
-- ============================================================

/-- Count the leading `endMark`s of a list, returning the count and the
suffix. -/
def endMarkRun : List FormulaSym → Nat × List FormulaSym
  | FormulaSym.endMark :: rest =>
      let (i, suf) := endMarkRun rest
      (i + 1, suf)
  | rest => (0, rest)

/-- `endMarkRun` splits a list at the first non-`endMark`. -/
lemma endMarkRun_spec (rest : List FormulaSym) :
    let (i, suf) := endMarkRun rest
    rest = List.replicate i FormulaSym.endMark ++ suf ∧ suf.head? ≠ some FormulaSym.endMark := by
  induction rest with
  | nil => simp [endMarkRun]
  | cons s rest' ih =>
      cases s with
      | endMark =>
          cases h : endMarkRun rest' with
          | mk i suf =>
              have hrest : rest' = List.replicate i FormulaSym.endMark ++ suf := by
                simpa [h] using ih.1
              have hsuf : suf.head? ≠ some FormulaSym.endMark := by
                simpa [h] using ih.2
              have hrun : endMarkRun (FormulaSym.endMark :: rest') = (i + 1, suf) := by
                rw [endMarkRun, h]
              rw [hrun]
              constructor
              · rw [hrest]
                rw [show FormulaSym.endMark :: (List.replicate i FormulaSym.endMark ++ suf) =
                    List.replicate (i + 1) FormulaSym.endMark ++ suf by
                      rw [show i + 1 = Nat.succ i by omega]
                      simp [List.replicate_succ, List.cons_append]]
              · simpa using hsuf
      | _ => simp [endMarkRun]

/-- `decodeVar` of a run of `k ≥ 1` `endMark`s yields the variable `k - 1`,
leaving the suffix untouched. -/
lemma decodeVar_endMarkRun (rest : List FormulaSym) (k : Nat) (suf : List FormulaSym)
    (hk : 1 ≤ k) (h : endMarkRun rest = (k, suf)) :
    decodeVar rest = (Formula.var (k - 1), suf) := by
  have hspec := endMarkRun_spec rest
  rw [h] at hspec
  have hrest : rest = List.replicate k FormulaSym.endMark ++ suf := by
    simpa using hspec.1
  have hsuf : ValidSuffix suf := by
    simpa [ValidSuffix] using hspec.2
  rw [hrest]
  have hk : k = (k - 1) + 1 := by omega
  rw [hk]
  exact decodeVar_enc (k - 1) hsuf

/-- A `var` decode means the input had a full unary index run: `decodeVar l =
(var i, rest)` implies `l` is `varEnc i` followed by a valid continuation. -/
lemma decodeVar_eq_var (l : List FormulaSym) (i : Nat) (rest : List FormulaSym)
    (h : decodeVar l = (Formula.var i, rest)) :
    l = List.replicate (i + 1) FormulaSym.endMark ++ rest ∧ rest.head? ≠ some FormulaSym.endMark := by
  have hl : l.head? = some FormulaSym.endMark := by
    by_contra hne
    cases l with
    | nil => simp [decodeVar] at h
    | cons s l' =>
        have hs : s ≠ FormulaSym.endMark := by
          intro hse
          apply hne
          simp [hse]
        simp [decodeVar, hs] at h
  cases hk : endMarkRun l with
  | mk k suf =>
      have hspec := endMarkRun_spec l
      rw [hk] at hspec
      have hk1 : 1 ≤ k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        rw [hk0'] at hspec
        have hsame : l = suf := by simpa using hspec.1
        have hne' : l.head? ≠ some FormulaSym.endMark := by
          rw [hsame]
          exact hspec.2
        exact hne' hl
      have hdec := decodeVar_endMarkRun l k suf hk1 hk
      rw [hdec] at h
      have hk' : k - 1 = i := by
        simpa using congrArg Prod.fst h
      have hsuf : suf = rest := congrArg Prod.snd h
      constructor
      · rw [hspec.1]
        rw [hsuf]
        rw [show k = i + 1 by omega]
      · rw [← hsuf]
        exact hspec.2

/-- The number of steps the machine takes to parse a formula `f` starting from
auxiliary index `c` (matching the phase lemma step counts). -/
def parseSteps : Formula → Nat → Nat
  | Formula.var i, c => i + 3
  | Formula.const b, c => if b then 2 * c + 4 else 2 * c + 5
  | Formula.not f, c =>
      let (_, y₁, c₁) := to3CNF' f c
      2 + parseSteps f c + (4 * c₁ + 3 * y₁ + 16)
  | Formula.and f g, c =>
      let (_, y₁, c₁) := to3CNF' f c
      let (_, y₂, c₂) := to3CNF' g c₁
      3 + parseSteps f c + parseSteps g c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)
  | Formula.or f g, c =>
      let (_, y₁, c₁) := to3CNF' f c
      let (_, y₂, c₂) := to3CNF' g c₁
      3 + parseSteps f c + parseSteps g c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)
  | Formula.iff f g, c =>
      let (_, y₁, c₁) := to3CNF' f c
      let (_, y₂, c₂) := to3CNF' g c₁
      3 + parseSteps f c + parseSteps g c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86)

/-- `decodeVarIdx` leaves a suffix no longer than its input. -/
lemma decodeVarIdx_suffix_le (i : Nat) (l : List FormulaSym) :
    (decodeVarIdx i l).2.length ≤ l.length := by
  induction l generalizing i with
  | nil => simp [decodeVarIdx]
  | cons s l' ih =>
      cases s with
      | endMark =>
          have h := ih (i + 1)
          simp [decodeVarIdx, List.length_cons]
          omega
      | _ => simp [decodeVarIdx]

/-- `decodeVar` leaves a suffix no longer than its input. -/
lemma decodeVar_suffix_le (l : List FormulaSym) :
    (decodeVar l).2.length ≤ l.length := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          have h := decodeVarIdx_suffix_le 0 l'
          simp [decodeVar, List.length_cons]
          omega
      | _ => simp [decodeVar]

lemma decodeAux_lit (b : Bool) (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.lit b :: l) = (Formula.const b, l) := by
  simp [decodeAux]

/-- `decodeAux` on the empty list is the junk `const false`. -/
lemma decodeAux_nil (b : Nat) :
    decodeAux b [] = (Formula.const false, []) := by
  cases b <;> simp [decodeAux]


/-- `decodeAux` on a `varMark` routes to `decodeVar`. -/
lemma decodeAux_varMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.varMark :: l) = decodeVar l := by
  simp [decodeAux]

/-- `decodeAux` on a stray `endMark` is the junk `const false`. -/
lemma decodeAux_endMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.endMark :: l) = (Formula.const false, l) := by
  simp [decodeAux]

/-- `decodeAux` on a `notMark` recurses with one less budget. -/
lemma decodeAux_notMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.notMark :: l) =
      (Formula.not (decodeAux n l).1, (decodeAux n l).2) := by
  simp [decodeAux]

/-- `decodeAux` on an `andMark` recurses with one less budget on both children. -/
lemma decodeAux_andMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.andMark :: l) =
      (Formula.and (decodeAux n l).1 (decodeAux n (decodeAux n l).2).1,
       (decodeAux n (decodeAux n l).2).2) := by
  simp [decodeAux]

/-- `decodeAux` on an `orMark` recurses with one less budget on both children. -/
lemma decodeAux_orMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.orMark :: l) =
      (Formula.or (decodeAux n l).1 (decodeAux n (decodeAux n l).2).1,
       (decodeAux n (decodeAux n l).2).2) := by
  simp [decodeAux]

/-- `decodeAux` on an `iffMark` recurses with one less budget on both children. -/
lemma decodeAux_iffMark (n : Nat) (l : List FormulaSym) :
    decodeAux (Nat.succ n) (FormulaSym.iffMark :: l) =
      (Formula.iff (decodeAux n l).1 (decodeAux n (decodeAux n l).2).1,
       (decodeAux n (decodeAux n l).2).2) := by
  simp [decodeAux]

/-- A non-empty input with a sufficient budget has `1 ≤ b`. -/
lemma budget_pos_of_cons (s : FormulaSym) (l : List FormulaSym) (b : Nat)
    (h : (s :: l).length ≤ b) : 1 ≤ b := by
  simp [List.length_cons] at h
  omega

/-- `decodeVarIdx` always yields a variable: it only ever counts `endMark`s. -/
lemma decodeVarIdx_is_var (i : Nat) (l : List FormulaSym) :
    ∃ k, (decodeVarIdx i l).1 = Formula.var k := by
  induction l generalizing i with
  | nil => refine ⟨i, ?_⟩; simp [decodeVarIdx]
  | cons s l' ih =>
      cases s with
      | endMark =>
          rcases ih (i + 1) with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          simp [decodeVarIdx] at hk ⊢
          exact hk
      | _ =>
          refine ⟨i, ?_⟩
          simp [decodeVarIdx]

/-- `decodeVar` never yields a `not` formula (only variables or the junk
`const false`). -/
lemma decodeVar_fst_ne_not (l : List FormulaSym) (f' : Formula) :
    (decodeVar l).1 ≠ Formula.not f' := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- `decodeVar` never yields `const true`. -/
lemma decodeVar_fst_ne_const_true (l : List FormulaSym) :
    (decodeVar l).1 ≠ Formula.const true := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- `decodeVar` never yields an `and`. -/
lemma decodeVar_fst_ne_and (l : List FormulaSym) (f' g' : Formula) :
    (decodeVar l).1 ≠ Formula.and f' g' := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- `decodeVar` never yields an `or`. -/
lemma decodeVar_fst_ne_or (l : List FormulaSym) (f' g' : Formula) :
    (decodeVar l).1 ≠ Formula.or f' g' := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- `decodeVar` never yields an `iff`. -/
lemma decodeVar_fst_ne_iff (l : List FormulaSym) (f' g' : Formula) :
    (decodeVar l).1 ≠ Formula.iff f' g' := by
  cases l with
  | nil => simp [decodeVar]
  | cons s l' =>
      cases s with
      | endMark =>
          rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
          rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
          rw [hk]
          simp
      | _ => simp [decodeVar]

/-- Compose two machine segments: `^[n₁] A = B` and `^[n₂] B = C` give
`^[n₂ + n₁] A = C`. -/
lemma step_comp {A B C : Option (mach).Cfg} (n₁ n₂ : Nat)
    (h₁ : (flip bind Sstep)^[n₁] A = B) (h₂ : (flip bind Sstep)^[n₂] B = C) :
    (flip bind Sstep)^[n₂ + n₁] A = C := by
  rw [Function.iterate_add_apply]
  rw [h₁]
  rw [h₂]

/-- Three-step composition. -/
lemma step_comp3 {A B C D : Option (mach).Cfg} (n₁ n₂ n₃ : Nat)
    (h₁ : (flip bind Sstep)^[n₁] A = B) (h₂ : (flip bind Sstep)^[n₂] B = C)
    (h₃ : (flip bind Sstep)^[n₃] C = D) :
    (flip bind Sstep)^[n₃ + (n₂ + n₁)] A = D := by
  rw [Function.iterate_add_apply]
  rw [step_comp n₁ n₂ h₁ h₂]
  rw [h₃]

/-- Compose a single step followed by `n₂` steps. -/
lemma step_comp_single {A : Option (mach).Cfg} {B C : (mach).Cfg} (n₂ : Nat)
    (h₁ : Sstep B = some C) (h₂ : (flip bind Sstep)^[n₂] (some C) = A) :
    (flip bind Sstep)^[n₂ + 1] (some B) = A := by
  rw [Function.iterate_add_apply]
  rw [show (flip bind Sstep)^[1] (some B) = Sstep B by simp [flip]]
  rw [h₁]
  exact h₂

/-- Compose `n₁` steps followed by a single step. -/
lemma step_single_comp {A C : Option (mach).Cfg} {B : (mach).Cfg} (n₁ : Nat)
    (h₁ : (flip bind Sstep)^[n₁] A = some B) (h₂ : Sstep B = some C) :
    (flip bind Sstep)^[1 + n₁] A = some C := by
  rw [show 1 + n₁ = Nat.succ n₁ by omega]
  rw [Function.iterate_succ_apply']
  rw [h₁]
  change Sstep B = some C
  exact h₂

/-- `decodeAux` never lengthens the continuation. -/
lemma decodeAux_suffix_le (n : Nat) (l : List FormulaSym) :
    (decodeAux n l).2.length ≤ l.length := by
  revert n
  let P : List FormulaSym → Prop := fun l => ∀ n : Nat, (decodeAux n l).2.length ≤ l.length
  change P l
  refine WellFounded.induction (measure (fun l : List FormulaSym => l.length)).wf l ?_
  intro l ih
  dsimp [P] at ih ⊢
  intro n
  cases h : l with
  | nil => cases n <;> simp [decodeAux]
  | cons s l' =>
      cases n with
      | zero => simp [decodeAux]
      | succ n' =>
          cases s with
          | lit bl => rw [decodeAux_lit bl n' l']; change l'.length ≤ l'.length + 1; omega
          | varMark =>
              have h := decodeVar_suffix_le l'
              rw [decodeAux_varMark n' l']
              change (decodeVar l').2.length ≤ l'.length + 1
              omega
          | endMark => rw [decodeAux_endMark n' l']; change l'.length ≤ l'.length + 1; omega
          | notMark =>
              have h1 := ih l' (by rw [h]; change l'.length < l'.length + 1; omega) n'
              rw [decodeAux_notMark n' l']
              change (decodeAux n' l').2.length ≤ l'.length + 1
              omega
          | andMark =>
              have h1 := ih l' (by rw [h]; change l'.length < l'.length + 1; omega) n'
              let X : List FormulaSym := (decodeAux n' l').2
              have hXlen : X.length ≤ l'.length := by simpa [X] using h1
              have h2 := ih X (by rw [h]; change (decodeAux n' l').2.length < l'.length + 1; omega) n'
              rw [decodeAux_andMark n' l']
              change (decodeAux n' X).2.length ≤ l'.length + 1
              omega
          | orMark =>
              have h1 := ih l' (by rw [h]; change l'.length < l'.length + 1; omega) n'
              let X : List FormulaSym := (decodeAux n' l').2
              have hXlen : X.length ≤ l'.length := by simpa [X] using h1
              have h2 := ih X (by rw [h]; change (decodeAux n' l').2.length < l'.length + 1; omega) n'
              rw [decodeAux_orMark n' l']
              change (decodeAux n' X).2.length ≤ l'.length + 1
              omega
          | iffMark =>
              have h1 := ih l' (by rw [h]; change l'.length < l'.length + 1; omega) n'
              let X : List FormulaSym := (decodeAux n' l').2
              have hXlen : X.length ≤ l'.length := by simpa [X] using h1
              have h2 := ih X (by rw [h]; change (decodeAux n' l').2.length < l'.length + 1; omega) n'
              rw [decodeAux_iffMark n' l']
              change (decodeAux n' X).2.length ≤ l'.length + 1
              omega

/-- The parse statement: from `rd` with input `inp`, the machine parses the
first formula `f = decodeAux b inp .1`, emits its reversed Tseitin clauses onto
`o`, pushes its value variable, advances the counter past the auxiliary
variables allocated for `f`, and reaches `reduce` with the continuation `rest`
on `in`.  The budget `b` is passed down (`b - 1` per connective level) and
stays at least the remaining input length. -/
lemma parse_phase (f : Formula) (b : Nat) (inp rest : List FormulaSym) (c : Nat) (V : List Bool)
    (F : List Frame) (T : List FormulaSym) (O U : List CNFSym) (hV : V.head? ≠ some true)
    (hbudget : inp.length ≤ b) (hdec : decodeAux b inp = (f, rest)) :
    let (cls, y, next) := to3CNF' f c
    ∀ v₀ : St, ∃ v₁ : St, (flip bind Sstep)^[parseSteps f c]
      (some (⟨some Label.rd, v₀, stk inp T c V F [] O U⟩ : (mach).Cfg))
      = some (⟨some Label.reduce, v₁, stk rest T next
          (false :: List.replicate (y + 1) true ++ V) F []
          ((encCNF cls).reverse ++ O) U⟩ : (mach).Cfg) := by
  -- Induct on the formula, reverting the state parameters so the induction
  -- hypothesis lets the machine's counter, value stack, and frame stack
  -- evolve through the recursive descent.
  revert hV hbudget hdec b inp rest c V F T O U
  induction f with
  | var i =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hdec' : decodeVar l = (Formula.var i, rest) := by
                    simpa [decodeAux] using hdec
                  have hspec := decodeVar_eq_var l i rest hdec'
                  have hinp : FormulaSym.varMark :: l = varEnc i ++ rest := by
                    rw [hspec.1]
                    rfl
                  rw [hinp]
                  intro v₀
                  exact var_phase i v₀ rest T c V F O U hspec.2
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                      (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                        exact decodeAux_notMark b' l] at hdec
                  cases hdec
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                      (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                  cases hdec
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                      (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                  cases hdec
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                      (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                  cases hdec
  | const bt =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases bt with
      | true =>
          cases inp with
          | nil =>
              rw [decodeAux_nil b] at hdec
              cases hdec
          | cons s l =>
              have hb := budget_pos_of_cons s l b hbudget
              cases s with
              | lit bl =>
                  cases bl with
                  | true =>
                              cases b with
                      | zero => omega
                      | succ b' =>
                          have hrest : l = rest := by
                            simpa [decodeAux] using congrArg Prod.snd hdec
                          subst rest
                          intro v₀
                          refine ⟨St.done, ?_⟩
                          have h1' : (flip bind Sstep)^[1] (some (⟨some Label.rd, v₀, stk (FormulaSym.lit true :: l) T c V F [] O U⟩ : (mach).Cfg))
                              = some (⟨some Label.const, St.rd (FormulaSym.lit true), stk l T c V F [] O U⟩ : (mach).Cfg) := by
                            simpa [flip] using rd_lit_step v₀ true l T c V F [] O U
                          have h2 := const_phase_true c l T V F O U
                          have hc : parseSteps (Formula.const true) c = (2 * c + 3) + 1 := by
                            unfold parseSteps
                            simp
                          rw [hc]
                          simpa [encCNF, forceTrue] using step_comp 1 (2 * c + 3) h1' h2
                  | false =>
                              cases b with
                      | zero => omega
                      | succ b' =>
                          rw [show decodeAux (Nat.succ b') (FormulaSym.lit false :: l) =
                              (Formula.const false, l) by exact decodeAux_lit false b' l] at hdec
                          cases hdec
              | varMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                            exact decodeAux_varMark b' l] at hdec
                      have hne := decodeVar_fst_ne_const_true l
                      rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                            exact (Prod.eta (decodeVar l)).symm] at hdec
                      exact (hne (congrArg Prod.fst hdec)).elim
              | endMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                          (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                      cases hdec
              | notMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                          (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                            exact decodeAux_notMark b' l] at hdec
                      cases hdec
              | andMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                          (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                      cases hdec
              | orMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                          (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                      cases hdec
              | iffMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                          (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                      cases hdec
      | false =>
          cases inp with
          | nil =>
              rw [decodeAux_nil b] at hdec
              have hrest : rest = [] := congrArg Prod.snd hdec.symm
              subst rest
              intro v₀
              refine ⟨St.done, ?_⟩
              simpa [parseSteps, encCNF, forceFalse] using junkEmpty_phase v₀ T c V F O U
          | cons s l =>
              have hb := budget_pos_of_cons s l b hbudget
              cases s with
              | lit bl =>
                  cases bl with
                  | false =>
                              cases b with
                      | zero => omega
                      | succ b' =>
                          have hrest : l = rest := by
                            simpa [decodeAux] using congrArg Prod.snd hdec
                          subst rest
                          intro v₀
                          refine ⟨St.done, ?_⟩
                          have h1' : (flip bind Sstep)^[1] (some (⟨some Label.rd, v₀, stk (FormulaSym.lit false :: l) T c V F [] O U⟩ : (mach).Cfg))
                              = some (⟨some Label.const, St.rd (FormulaSym.lit false), stk l T c V F [] O U⟩ : (mach).Cfg) := by
                            simpa [flip] using rd_lit_step v₀ false l T c V F [] O U
                          have h2 := const_phase_false c l T V F O U
                          have hc : parseSteps (Formula.const false) c = (2 * c + 4) + 1 := by
                            unfold parseSteps
                            simp
                          rw [hc]
                          simpa [encCNF, forceFalse] using step_comp 1 (2 * c + 4) h1' h2
                  | true =>
                              cases b with
                      | zero => omega
                      | succ b' =>
                          rw [show decodeAux (Nat.succ b') (FormulaSym.lit true :: l) =
                              (Formula.const true, l) by exact decodeAux_lit true b' l] at hdec
                          cases hdec
              | varMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      have hdec' : decodeVar l = (Formula.const false, rest) := by
                        simpa [decodeAux] using hdec
                      have hl : l.head? ≠ some FormulaSym.endMark := by
                        by_contra hne
                        cases l with
                        | nil => simp at hne
                        | cons s' l' =>
                            have hs' : s' = FormulaSym.endMark := by simpa using hne
                            have hdecv : decodeVar (FormulaSym.endMark :: l') = (Formula.const false, rest) := by
                              simpa [hs'] using hdec'
                            rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl] at hdecv
                            rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
                            have hfst : (decodeVarIdx 0 l').1 = Formula.const false := congrArg Prod.fst hdecv
                            rw [hk] at hfst
                            cases hfst
                      have hrest : rest = l := by
                        have hdec'' : decodeVar l = (Formula.const false, l) := by
                          cases l with
                          | nil => simp [decodeVar]
                          | cons s' l' =>
                              have hs' : s' ≠ FormulaSym.endMark := by
                                intro hse
                                apply hl
                                simp [hse]
                              simp [decodeVar, hs']
                        exact (congrArg Prod.snd (hdec''.symm.trans hdec')).symm
                      subst rest
                      intro v₀
                      refine ⟨St.done, ?_⟩
                      simpa [parseSteps, encCNF, forceFalse] using junkVar_phase v₀ l T c V F O U hl
              | endMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      have hrest : l = rest := by
                        simpa [decodeAux] using congrArg Prod.snd hdec
                      subst rest
                      intro v₀
                      refine ⟨St.done, ?_⟩
                      simpa [parseSteps, encCNF, forceFalse] using junkEnd_phase v₀ l T c V F O U
              | notMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                          (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                            exact decodeAux_notMark b' l] at hdec
                      cases hdec
              | andMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                          (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                      cases hdec
              | orMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                          (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                      cases hdec
              | iffMark =>
                      cases b with
                  | zero => omega
                  | succ b' =>
                      rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                          (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                           (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                      cases hdec
  | not f' ih =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hdec' : decodeAux b' l = (f', rest) := by
                    have hfst : (decodeAux b' l).1 = f' := by
                      simpa [decodeAux] using congrArg Prod.fst hdec
                    have hsnd : (decodeAux b' l).2 = rest := by
                      simpa [decodeAux] using congrArg Prod.snd hdec
                    exact Prod.ext hfst hsnd
                  have hbudget' : l.length ≤ b' := by
                    simp [List.length_cons] at hbudget
                    omega
                  have hparsec := ih b' l rest c V (Frame.not :: F) T O U hV hbudget' hdec'
                  intro v₀
                  rcases hparsec (St.rd FormulaSym.notMark) with ⟨v₁, hparsecv⟩
                  rcases hdec_f' : to3CNF' f' c with ⟨cls', y₁, c₁⟩
                  have h1 := rd_not_step v₀ l T c V F [] O U
                  have h2' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₁, stk rest T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.not :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.emitNot, St.emitNot, stk rest T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) F []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_not_step v₁ rest T c₁
                      (false :: List.replicate (y₁ + 1) true ++ V) F [] ((encCNF cls').reverse ++ O) U
                  have h3 := not_phase rest T c₁ y₁ V F ((encCNF cls').reverse ++ O) U hV
                  have hcomp1 := step_comp_single (parseSteps f' c) h1 hparsecv
                  have hcomp1' : (flip bind Sstep)^[parseSteps f' c + 1]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.notMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₁, stk rest T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.not :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f'] using hcomp1
                  have hcomp2 := step_comp (parseSteps f' c + 1) 1 hcomp1' h2'
                  have hcomp := step_comp (1 + (parseSteps f' c + 1)) (4 * c₁ + 3 * y₁ + 16) hcomp2 h3
                  have hc : parseSteps (Formula.not f') c = (4 * c₁ + 3 * y₁ + 16) + (1 + (parseSteps f' c + 1)) := by
                    conv_lhs =>
                      unfold parseSteps
                      rw [hdec_f']
                    simp
                    omega
                  rw [hc]
                  refine ⟨St.done, ?_⟩
                  simpa [encCNF, List.flatMap_append, List.reverse_append, List.append_assoc, to3CNF', hdec_f'] using hcomp
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                        exact decodeAux_varMark b' l] at hdec
                  -- decodeVar never yields a `not`
                  have hnot : (decodeVar l).1 ≠ Formula.not f' := by
                    cases l with
                    | nil => simp [decodeVar]
                    | cons s' l' =>
                        cases s' with
                        | endMark =>
                            rw [show decodeVar (FormulaSym.endMark :: l') = decodeVarIdx 0 l' by rfl]
                            rcases decodeVarIdx_is_var 0 l' with ⟨k, hk⟩
                            rw [hk]
                            simp
                        | _ => simp [decodeVar]
                  rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                        exact (Prod.eta (decodeVar l)).symm] at hdec
                  exact (hnot (congrArg Prod.fst hdec)).elim
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                      (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                  cases hdec
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                      (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                  cases hdec
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                      (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                  cases hdec
  | and f' g' ihf ihg =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hf' : (decodeAux b' l).1 = f' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_andMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.and f _ => f | _ => Formula.const false) h
                  have hg' : (decodeAux b' (decodeAux b' l).2).1 = g' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_andMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.and _ g => g | _ => Formula.const false) h
                  have hrest : (decodeAux b' (decodeAux b' l).2).2 = rest := by
                    have h := congrArg Prod.snd hdec
                    rw [decodeAux_andMark b' l] at h
                    exact h
                  let rest₁ := (decodeAux b' l).2
                  have hdec1 : decodeAux b' l = (f', rest₁) := Prod.ext hf' rfl
                  have hdec2 : decodeAux b' rest₁ = (g', rest) := by
                    simpa [rest₁] using Prod.ext hg' hrest
                  have hbudget₁ : l.length ≤ b' := by
                    simp [List.length_cons] at hbudget
                    omega
                  have hbudget₂ : rest₁.length ≤ b' := by
                    have hsuf := decodeAux_suffix_le b' l
                    have : rest₁.length ≤ l.length := by
                      simpa [rest₁] using hsuf
                    omega
                  have hparsec1 := ihf b' l rest₁ c V (Frame.and₁ :: F) T O U hV hbudget₁ hdec1
                  rcases hdec_f' : to3CNF' f' c with ⟨cls', y₁, c₁⟩
                  rcases hdec_g' : to3CNF' g' c₁ with ⟨cls'', y₂, c₂⟩
                  have hV' : (false :: List.replicate (y₁ + 1) true ++ V).head? ≠ some true := by
                    simp
                  have hparsec2 := ihg b' rest₁ rest c₁ (false :: List.replicate (y₁ + 1) true ++ V)
                    (Frame.and₂ :: F) T ((encCNF cls').reverse ++ O) U hV' hbudget₂ hdec2
                  intro v₀
                  rcases hparsec1 (St.rd FormulaSym.andMark) with ⟨v₁, hparsec1v⟩
                  rcases hparsec2 (St.and₁Done) with ⟨v₂, hparsec2v⟩
                  have h1 := rd_and_step v₀ l T c V F [] O U
                  have h2' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.and₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.rd, St.and₁Done, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.and₂ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_and₁_step v₁ rest₁ T c₁
                      (false :: List.replicate (y₁ + 1) true ++ V) F [] ((encCNF cls').reverse ++ O) U
                  have h5' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.and₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.emitAnd, St.emitAnd, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_and₂_step v₂ rest T c₂
                      (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U
                  have h6 := emitAnd_phase rest T c₂ y₁ y₂ V F ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U hV
                  have hcomp1 := step_comp_single (parseSteps f' c) h1 hparsec1v
                  have hcomp1' : (flip bind Sstep)^[parseSteps f' c + 1]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.andMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.and₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f'] using hcomp1
                  have hcomp2 := step_comp (parseSteps f' c + 1) 1 hcomp1' h2'
                  have hcomp3 := step_comp (1 + (parseSteps f' c + 1)) (parseSteps g' c₁) hcomp2 hparsec2v
                  have hcomp3' : (flip bind Sstep)^[parseSteps g' c₁ + (1 + (parseSteps f' c + 1))]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.andMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.and₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f', hdec_g'] using hcomp3
                  have hcomp4 := step_comp (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))) 1 hcomp3' h5'
                  have hcomp := step_comp (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))))
                    (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) hcomp4 h6
                  have hc : parseSteps (Formula.and f' g') c =
                      (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) + (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1)))) := by
                    have hm1 : (match (cls', y₁, c₁) with | (fst, y₁, c₁) => match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) =
    (match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) := by rfl
                    have hm2 :
                        (match (cls'', y₂, c₂) with
                          | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) =
                        3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) := by rfl
                    conv_lhs =>
                      unfold parseSteps
                      rw [hdec_f']
                      rw [hm1]
                      rw [hdec_g']
                      rw [hm2]
                    omega
                  rw [hc]
                  refine ⟨St.done, ?_⟩
                  simpa [encCNF, List.flatMap_append, List.reverse_append, List.append_assoc, to3CNF', hdec_f', hdec_g'] using hcomp
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                        exact decodeAux_varMark b' l] at hdec
                  have hne := decodeVar_fst_ne_and l f' g'
                  rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                        exact (Prod.eta (decodeVar l)).symm] at hdec
                  exact (hne (congrArg Prod.fst hdec)).elim
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                      (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                        exact decodeAux_notMark b' l] at hdec
                  cases hdec
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                      (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                  cases hdec
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                      (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                  cases hdec
  | or f' g' ihf ihg =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hf' : (decodeAux b' l).1 = f' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_orMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.or f _ => f | _ => Formula.const false) h
                  have hg' : (decodeAux b' (decodeAux b' l).2).1 = g' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_orMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.or _ g => g | _ => Formula.const false) h
                  have hrest : (decodeAux b' (decodeAux b' l).2).2 = rest := by
                    have h := congrArg Prod.snd hdec
                    rw [decodeAux_orMark b' l] at h
                    exact h
                  let rest₁ := (decodeAux b' l).2
                  have hdec1 : decodeAux b' l = (f', rest₁) := Prod.ext hf' rfl
                  have hdec2 : decodeAux b' rest₁ = (g', rest) := by
                    simpa [rest₁] using Prod.ext hg' hrest
                  have hbudget₁ : l.length ≤ b' := by
                    simp [List.length_cons] at hbudget
                    omega
                  have hbudget₂ : rest₁.length ≤ b' := by
                    have hsuf := decodeAux_suffix_le b' l
                    have : rest₁.length ≤ l.length := by
                      simpa [rest₁] using hsuf
                    omega
                  have hparsec1 := ihf b' l rest₁ c V (Frame.or₁ :: F) T O U hV hbudget₁ hdec1
                  rcases hdec_f' : to3CNF' f' c with ⟨cls', y₁, c₁⟩
                  rcases hdec_g' : to3CNF' g' c₁ with ⟨cls'', y₂, c₂⟩
                  have hV' : (false :: List.replicate (y₁ + 1) true ++ V).head? ≠ some true := by
                    simp
                  have hparsec2 := ihg b' rest₁ rest c₁ (false :: List.replicate (y₁ + 1) true ++ V)
                    (Frame.or₂ :: F) T ((encCNF cls').reverse ++ O) U hV' hbudget₂ hdec2
                  intro v₀
                  rcases hparsec1 (St.rd FormulaSym.orMark) with ⟨v₁, hparsec1v⟩
                  rcases hparsec2 (St.or₁Done) with ⟨v₂, hparsec2v⟩
                  have h1 := rd_or_step v₀ l T c V F [] O U
                  have h2' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.or₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.rd, St.or₁Done, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.or₂ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_or₁_step v₁ rest₁ T c₁
                      (false :: List.replicate (y₁ + 1) true ++ V) F [] ((encCNF cls').reverse ++ O) U
                  have h5' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.or₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.emitOr, St.emitOr, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_or₂_step v₂ rest T c₂
                      (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U
                  have h6 := emitOr_phase rest T c₂ y₁ y₂ V F ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U hV
                  have hcomp1 := step_comp_single (parseSteps f' c) h1 hparsec1v
                  have hcomp1' : (flip bind Sstep)^[parseSteps f' c + 1]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.orMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.or₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f'] using hcomp1
                  have hcomp2 := step_comp (parseSteps f' c + 1) 1 hcomp1' h2'
                  have hcomp3 := step_comp (1 + (parseSteps f' c + 1)) (parseSteps g' c₁) hcomp2 hparsec2v
                  have hcomp3' : (flip bind Sstep)^[parseSteps g' c₁ + (1 + (parseSteps f' c + 1))]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.orMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.or₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f', hdec_g'] using hcomp3
                  have hcomp4 := step_comp (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))) 1 hcomp3' h5'
                  have hcomp := step_comp (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))))
                    (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) hcomp4 h6
                  have hc : parseSteps (Formula.or f' g') c =
                      (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) + (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1)))) := by
                    have hm1 : (match (cls', y₁, c₁) with | (fst, y₁, c₁) => match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) =
    (match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) := by rfl
                    have hm2 :
                        (match (cls'', y₂, c₂) with
                          | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44)) =
                        3 + parseSteps f' c + parseSteps g' c₁ + (6 * c₂ + 3 * y₁ + 7 * y₂ + 44) := by rfl
                    conv_lhs =>
                      unfold parseSteps
                      rw [hdec_f']
                      rw [hm1]
                      rw [hdec_g']
                      rw [hm2]
                    omega
                  rw [hc]
                  refine ⟨St.done, ?_⟩
                  simpa [encCNF, List.flatMap_append, List.reverse_append, List.append_assoc, to3CNF', hdec_f', hdec_g'] using hcomp
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                        exact decodeAux_varMark b' l] at hdec
                  have hne := decodeVar_fst_ne_or l f' g'
                  rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                        exact (Prod.eta (decodeVar l)).symm] at hdec
                  exact (hne (congrArg Prod.fst hdec)).elim
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                      (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                        exact decodeAux_notMark b' l] at hdec
                  cases hdec
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                      (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                  cases hdec
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.iffMark :: l) =
                      (Formula.iff (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_iffMark b' l] at hdec
                  cases hdec
  | iff f' g' ihf ihg =>
      intro b inp rest c V F T O U hV hbudget hdec
      cases inp with
      | nil =>
          rw [decodeAux_nil b] at hdec
          cases hdec
      | cons s l =>
          have hb := budget_pos_of_cons s l b hbudget
          cases s with
          | iffMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  have hf' : (decodeAux b' l).1 = f' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_iffMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.iff f _ => f | _ => Formula.const false) h
                  have hg' : (decodeAux b' (decodeAux b' l).2).1 = g' := by
                    have h := congrArg Prod.fst hdec
                    rw [decodeAux_iffMark b' l] at h
                    simpa using congrArg (fun x => match x with | Formula.iff _ g => g | _ => Formula.const false) h
                  have hrest : (decodeAux b' (decodeAux b' l).2).2 = rest := by
                    have h := congrArg Prod.snd hdec
                    rw [decodeAux_iffMark b' l] at h
                    exact h
                  let rest₁ := (decodeAux b' l).2
                  have hdec1 : decodeAux b' l = (f', rest₁) := Prod.ext hf' rfl
                  have hdec2 : decodeAux b' rest₁ = (g', rest) := by
                    simpa [rest₁] using Prod.ext hg' hrest
                  have hbudget₁ : l.length ≤ b' := by
                    simp [List.length_cons] at hbudget
                    omega
                  have hbudget₂ : rest₁.length ≤ b' := by
                    have hsuf := decodeAux_suffix_le b' l
                    have : rest₁.length ≤ l.length := by
                      simpa [rest₁] using hsuf
                    omega
                  have hparsec1 := ihf b' l rest₁ c V (Frame.iff₁ :: F) T O U hV hbudget₁ hdec1
                  rcases hdec_f' : to3CNF' f' c with ⟨cls', y₁, c₁⟩
                  rcases hdec_g' : to3CNF' g' c₁ with ⟨cls'', y₂, c₂⟩
                  have hV' : (false :: List.replicate (y₁ + 1) true ++ V).head? ≠ some true := by
                    simp
                  have hparsec2 := ihg b' rest₁ rest c₁ (false :: List.replicate (y₁ + 1) true ++ V)
                    (Frame.iff₂ :: F) T ((encCNF cls').reverse ++ O) U hV' hbudget₂ hdec2
                  intro v₀
                  rcases hparsec1 (St.rd FormulaSym.iffMark) with ⟨v₁, hparsec1v⟩
                  rcases hparsec2 (St.iff₁Done) with ⟨v₂, hparsec2v⟩
                  have h1 := rd_iff_step v₀ l T c V F [] O U
                  have h2' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.iff₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.rd, St.iff₁Done, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.iff₂ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_iff₁_step v₁ rest₁ T c₁
                      (false :: List.replicate (y₁ + 1) true ++ V) F [] ((encCNF cls').reverse ++ O) U
                  have h5' : (flip bind Sstep)^[1]
                      (some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.iff₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg))
                      = some (⟨some Label.emitIff, St.emitIff, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    rw [Function.iterate_one]
                    simpa [flip] using reduce_iff₂_step v₂ rest T c₂
                      (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) F [] ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U
                  have h6 := emitIff_phase rest T c₂ y₁ y₂ V F ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U hV
                  have hcomp1 := step_comp_single (parseSteps f' c) h1 hparsec1v
                  have hcomp1' : (flip bind Sstep)^[parseSteps f' c + 1]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.iffMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₁, stk rest₁ T c₁
                          (false :: List.replicate (y₁ + 1) true ++ V) (Frame.iff₁ :: F) []
                          ((encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f'] using hcomp1
                  have hcomp2 := step_comp (parseSteps f' c + 1) 1 hcomp1' h2'
                  have hcomp3 := step_comp (1 + (parseSteps f' c + 1)) (parseSteps g' c₁) hcomp2 hparsec2v
                  have hcomp3' : (flip bind Sstep)^[parseSteps g' c₁ + (1 + (parseSteps f' c + 1))]
                      (some (⟨some Label.rd, v₀, stk (FormulaSym.iffMark :: l) T c V F [] O U⟩ : (mach).Cfg))
                      = some (⟨some Label.reduce, v₂, stk rest T c₂
                          (false :: List.replicate (y₂ + 1) true ++ (false :: List.replicate (y₁ + 1) true ++ V)) (Frame.iff₂ :: F) []
                          ((encCNF cls'').reverse ++ (encCNF cls').reverse ++ O) U⟩ : (mach).Cfg) := by
                    simpa [hdec_f', hdec_g'] using hcomp3
                  have hcomp4 := step_comp (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))) 1 hcomp3' h5'
                  have hcomp := step_comp (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1))))
                    (8 * c₂ + 7 * y₁ + 15 * y₂ + 86) hcomp4 h6
                  have hc : parseSteps (Formula.iff f' g') c =
                      (8 * c₂ + 7 * y₁ + 15 * y₂ + 86) + (1 + (parseSteps g' c₁ + (1 + (parseSteps f' c + 1)))) := by
                    have hm1 : (match (cls', y₁, c₁) with | (fst, y₁, c₁) => match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86)) =
    (match to3CNF' g' c₁ with | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86)) := by rfl
                    have hm2 :
                        (match (cls'', y₂, c₂) with
                          | (fst, y₂, c₂) => 3 + parseSteps f' c + parseSteps g' c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86)) =
                        3 + parseSteps f' c + parseSteps g' c₁ + (8 * c₂ + 7 * y₁ + 15 * y₂ + 86) := by rfl
                    conv_lhs =>
                      unfold parseSteps
                      rw [hdec_f']
                      rw [hm1]
                      rw [hdec_g']
                      rw [hm2]
                    omega
                  rw [hc]
                  refine ⟨St.done, ?_⟩
                  simpa [encCNF, List.flatMap_append, List.reverse_append, List.append_assoc, to3CNF', hdec_f', hdec_g'] using hcomp
          | lit bl =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.lit bl :: l) =
                      (Formula.const bl, l) by exact decodeAux_lit bl b' l] at hdec
                  cases hdec
          | varMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.varMark :: l) = decodeVar l by
                        exact decodeAux_varMark b' l] at hdec
                  have hne := decodeVar_fst_ne_iff l f' g'
                  rw [show decodeVar l = ((decodeVar l).1, (decodeVar l).2) by
                        exact (Prod.eta (decodeVar l)).symm] at hdec
                  exact (hne (congrArg Prod.fst hdec)).elim
          | endMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.endMark :: l) =
                      (Formula.const false, l) by exact decodeAux_endMark b' l] at hdec
                  cases hdec
          | notMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.notMark :: l) =
                      (Formula.not (decodeAux b' l).1, (decodeAux b' l).2) by
                        exact decodeAux_notMark b' l] at hdec
                  cases hdec
          | andMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.andMark :: l) =
                      (Formula.and (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_andMark b' l] at hdec
                  cases hdec
          | orMark =>
              cases b with
              | zero => omega
              | succ b' =>
                  rw [show decodeAux (Nat.succ b') (FormulaSym.orMark :: l) =
                      (Formula.or (decodeAux b' l).1 (decodeAux b' (decodeAux b' l).2).1,
                       (decodeAux b' (decodeAux b' l).2).2) by exact decodeAux_orMark b' l] at hdec
                  cases hdec

end TM3CNF

end Turing

end Chapter34

end CLRS
