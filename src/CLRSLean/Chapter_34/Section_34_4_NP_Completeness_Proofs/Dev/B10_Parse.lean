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

end TM3CNF

end Turing

end Chapter34

end CLRS
