import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B10_Parse

/-!
# Dev B10: the recursive descent (`parse_phase`)

Development split of `SatTo3CNFMachine`: `parse_phase`, the run lemma for the recursive descent that reads `inp`, emits the reversed Tseitin clauses, pushes the value variable, and reaches `reduce`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

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
                      simp [hdec_f', hdec_g']
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
                      simp [hdec_f', hdec_g']
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
                      simp [hdec_f', hdec_g']
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
