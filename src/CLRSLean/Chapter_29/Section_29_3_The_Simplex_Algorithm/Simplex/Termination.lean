import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Run
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.NoCycle

/-!
# 29.3 Finite termination and public SIMPLEX

The trace contains one dictionary per visited basis.  Bland's theorem makes
those bases distinct, so the number of all finite basis sets is a sufficient
fuel bound.  The public result consequently has no exhaustion constructor.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Dictionaries visited by the fuelled runner, including its input. -/
noncomputable def simplexTrace : ℕ → Dictionary m n → List (Dictionary m n)
  | 0, D => [D]
  | fuel + 1, D =>
      match D.simplexStep with
      | .optimal _ => [D]
      | .unbounded _ _ _ => [D]
      | .pivot e l _ hl =>
          D :: simplexTrace fuel
            (D.pivot l e hl.1.pivotCoefficient_pos.ne')

@[simp] theorem simplexTrace_head? (fuel : ℕ) (D : Dictionary m n) :
    (D.simplexTrace fuel).head? = some D := by
  cases fuel with
  | zero => simp [simplexTrace]
  | succ fuel =>
      cases hstep : D.simplexStep with
      | optimal _ => simp [simplexTrace, hstep]
      | unbounded _ _ _ => simp [simplexTrace, hstep]
      | pivot _ _ _ _ => simp [simplexTrace, hstep]

/-- The generated execution list is a chain of certified Bland pivots. -/
theorem simplexTrace_isChain (fuel : ℕ) (D : Dictionary m n) :
    (D.simplexTrace fuel).IsChain IsBlandPivot := by
  induction fuel generalizing D with
  | zero => simp [simplexTrace]
  | succ fuel ih =>
      cases hstep : D.simplexStep with
      | optimal _ => simp [simplexTrace, hstep]
      | unbounded _ _ _ => simp [simplexTrace, hstep]
      | pivot e l he hl =>
          let next := D.pivot l e hl.1.pivotCoefficient_pos.ne'
          rw [simplexTrace, hstep]
          apply (ih next).cons
          intro E hE
          rw [simplexTrace_head?] at hE
          have hEnext : E = next := by simpa using hE.symm
          subst E
          exact ⟨{
            entering := e
            leaving := l
            enteringIsBland := he
            leavingIsBland := hl
            next_eq := rfl
          }⟩

/-- Every exhausted run used all of its fuel for pivots. -/
theorem simplexTrace_length_of_isExhausted (fuel : ℕ)
    (D : Dictionary m n) (hexhausted : (D.simplexRun fuel).IsExhausted) :
    (D.simplexTrace fuel).length = fuel + 1 := by
  induction fuel generalizing D with
  | zero => simp [simplexTrace]
  | succ fuel ih =>
      cases hstep : D.simplexStep with
      | optimal _ =>
          simp [simplexRun, hstep, SimplexRunResult.IsExhausted] at hexhausted
      | unbounded _ _ _ =>
          simp [simplexRun, hstep, SimplexRunResult.IsExhausted] at hexhausted
      | pivot e l he hl =>
          let next := D.pivot l e hl.1.pivotCoefficient_pos.ne'
          have hrest : (next.simplexRun fuel).IsExhausted := by
            simpa [simplexRun, hstep, next] using hexhausted
          simp [simplexTrace, hstep, next, ih next hrest]

/-- A later member of a nonempty relation chain is transitively reachable
from its head. -/
theorem transGen_of_isChain_cons_mem {α : Type*} {r : α → α → Prop}
    {a b : α} {xs : List α} (hchain : (a :: xs).IsChain r)
    (hb : b ∈ xs) : Relation.TransGen r a b := by
  induction xs generalizing a with
  | nil => simp at hb
  | cons c cs ih =>
      have hac : r a c := hchain.rel_head
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Relation.TransGen.single hac
      · exact Relation.TransGen.head hac (ih hchain.tail hb)

/-- Feasibility and Bland no-cycling make the basis list of any chain
duplicate-free. -/
theorem basisList_nodup_of_isChain (D : Dictionary m n)
    (xs : List (Dictionary m n))
    (hchain : (D :: xs).IsChain IsBlandPivot)
    (hD : D.IsBasicFeasible) :
    ((D :: xs).map basicVariables).Nodup := by
  induction xs generalizing D with
  | nil => simp
  | cons E rest ih =>
      have hstep : IsBlandPivot D E := hchain.rel_head
      obtain ⟨p⟩ := hstep
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨F, hF, hbasis⟩ := List.mem_map.mp hmem
        have hpath : Relation.TransGen IsBlandPivot D F :=
          transGen_of_isChain_cons_mem hchain hF
        exact D.bland_no_repeated_basis hD hpath hbasis.symm
      · exact ih E hchain.tail (p.isBasicFeasible hD)

/-- The generated trace visits no basis twice. -/
theorem simplexTrace_basis_nodup (fuel : ℕ) (D : Dictionary m n)
    (hD : D.IsBasicFeasible) :
    ((D.simplexTrace fuel).map basicVariables).Nodup := by
  obtain ⟨xs, htrace⟩ : ∃ xs, D.simplexTrace fuel = D :: xs := by
    cases fuel with
    | zero => exact ⟨[], rfl⟩
    | succ fuel =>
        cases hstep : D.simplexStep with
        | optimal _ => exact ⟨[], by simp [simplexTrace, hstep]⟩
        | unbounded _ _ _ => exact ⟨[], by simp [simplexTrace, hstep]⟩
        | pivot e l he hl =>
            exact ⟨simplexTrace fuel
              (D.pivot l e hl.1.pivotCoefficient_pos.ne'),
              by simp [simplexTrace, hstep]⟩
  rw [htrace]
  exact basisList_nodup_of_isChain D xs
    (by simpa [htrace] using D.simplexTrace_isChain fuel) hD

/-- Number of finite subsets of the stable variable universe; this is a
simple sufficient bound on the number of possible bases. -/
def basisCount (m n : ℕ) : ℕ :=
  Fintype.card (Finset (LPVar m n))

/-- Every feasible generated trace fits in the finite basis universe. -/
theorem simplexTrace_length_le_basisCount (fuel : ℕ)
    (D : Dictionary m n) (hD : D.IsBasicFeasible) :
    (D.simplexTrace fuel).length ≤ basisCount m n := by
  have hnodup := D.simplexTrace_basis_nodup fuel hD
  have hbound := hnodup.length_le_card
  simpa [basisCount] using hbound

/-- At the finite basis bound, fuel exhaustion is impossible. -/
theorem simplexRun_basisCount_not_exhausted (D : Dictionary m n)
    (hD : D.IsBasicFeasible) :
    ¬(D.simplexRun (basisCount m n)).IsExhausted := by
  intro hexhausted
  have hlength := D.simplexTrace_length_of_isExhausted
    (basisCount m n) hexhausted
  have hbound := D.simplexTrace_length_le_basisCount (basisCount m n) hD
  rw [hlength] at hbound
  omega

/-- Correct public SIMPLEX outcomes for a fixed input dictionary. -/
inductive SimplexResult (D : Dictionary m n) where
  | optimal (assignment : LPVar m n → ℝ)
      (isOptimal : D.IsOptimalAssignment assignment)
  | unbounded (isUnbounded : D.IsUnbounded)

/-- Textbook SIMPLEX with Bland's rule.  Feasibility is supplied by the
initialization phase formalized in Section 29.5. -/
noncomputable def simplex (D : Dictionary m n) (hD : D.IsBasicFeasible) :
    SimplexResult D :=
  match hresult : D.simplexRun (basisCount m n) with
  | .optimal terminal _ =>
      .optimal terminal.basicAssignment (by
        have hopt := D.simplexRun_optimal_correct (basisCount m n) hD (by
          simp [hresult, SimplexRunResult.IsOptimal])
        simpa [hresult, SimplexRunResult.terminalDictionary] using hopt)
  | .unbounded _ _ _ _ =>
      .unbounded (D.simplexRun_unbounded_correct (basisCount m n) hD (by
        rw [hresult]
        trivial))
  | .exhausted _ =>
      False.elim (D.simplexRun_basisCount_not_exhausted hD (by
        rw [hresult]
        trivial))

/-- SIMPLEX returns either an optimal assignment or an unboundedness
certificate for every basic-feasible dictionary. -/
theorem simplex_optimal_or_unbounded (D : Dictionary m n)
    (hD : D.IsBasicFeasible) :
    (∃ x, D.IsOptimalAssignment x) ∨ D.IsUnbounded := by
  cases D.simplex hD with
  | optimal x hx => exact Or.inl ⟨x, hx⟩
  | unbounded h => exact Or.inr h

end Dictionary
end Chapter29
end CLRS
