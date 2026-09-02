import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Coefficients

/-!
# 29.3 Bland's anti-cycling theorem

This is the textbook greatest-fickle-variable proof.  Assuming a repeated
basis, it compares two equivalent objective expressions and constructs a
smaller-index minimum-ratio row, contradicting Bland's leaving tie break.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Bland-rule SIMPLEX never repeats a basis along a nonempty feasible pivot
trace. -/
theorem bland_no_repeated_basis {D F : Dictionary m n}
    (hD : D.IsBasicFeasible)
    (hcycle : Relation.TransGen IsBlandPivot D F) :
    D.basicVariables ≠ F.basicVariables := by
  intro hbasis
  let hne := fickleVariables_nonempty_of_cycle hcycle
  let ell := D.greatestFickle F hne
  have hellmem : ell ∈ D.fickleVariables F :=
    D.greatestFickle_mem F hne
  have hell : D.IsFickle F ell :=
    (D.mem_fickleVariables F ell).1 hellmem
  obtain ⟨E, hEon, hchange⟩ := hell

  have hsteps :
      (∃ (P P' : Dictionary m n) (p : BlandPivot P P'),
        BlandReachable D P ∧ BlandReachable P' F ∧
          ell = P.basicVar p.leaving) ∧
      (∃ (Q Q' : Dictionary m n) (q : BlandPivot Q Q'),
        BlandReachable D Q ∧ BlandReachable Q' F ∧
          ell = Q.nonbasicVar q.entering) := by
    rcases hchange with ⟨hellD, hellE⟩ | ⟨hellD, hellE⟩
    · have hellF : ell ∈ F.basicVariables := by
        rw [← hbasis]
        exact hellD
      obtain ⟨P, P', p, hDP, hP'E, hpell⟩ :=
        hEon.1.exists_leaving_of_mem_not_mem hellD hellE
      obtain ⟨Q, Q', q, hEQ, hQ'F, hqell⟩ :=
        hEon.2.exists_entering_of_not_mem_mem hellE hellF
      exact ⟨
        ⟨P, P', p, hDP, hP'E.trans hEon.2, hpell⟩,
        ⟨Q, Q', q, hEon.1.trans hEQ, hQ'F, hqell⟩⟩
    · have hellF : ell ∉ F.basicVariables := by
        rw [← hbasis]
        exact hellD
      obtain ⟨Q, Q', q, hDQ, hQ'E, hqell⟩ :=
        hEon.1.exists_entering_of_not_mem_mem hellD hellE
      obtain ⟨P, P', p, hEP, hP'F, hpell⟩ :=
        hEon.2.exists_leaving_of_mem_not_mem hellE hellF
      exact ⟨
        ⟨P, P', p, hEon.1.trans hEP, hP'F, hpell⟩,
        ⟨Q, Q', q, hDQ, hQ'E.trans hEon.2, hqell⟩⟩

  obtain ⟨⟨P, P', p, hDP, hP'F, hpell⟩,
    ⟨Q, Q', q, hDQ, hQ'F, hqell⟩⟩ := hsteps
  let hvar := P.nonbasicVar p.entering

  have hhfickle : D.IsFickle F hvar :=
    isFickle_entering hDP p hP'F
  have hhmem : hvar ∈ D.fickleVariables F :=
    (D.mem_fickleVariables F hvar).2 hhfickle
  have hhle : variableIndex hvar ≤ variableIndex ell :=
    D.variableIndex_le_greatestFickle F hne hhmem
  have hhne : hvar ≠ ell := by
    intro hheq
    have hbad : P.basicVar p.leaving = P.nonbasicVar p.entering :=
      hpell.symm.trans hheq.symm
    exact P.labels_basic_ne_nonbasic p.leaving p.entering hbad
  have hhidxne : variableIndex hvar ≠ variableIndex ell := by
    intro hidx
    exact hhne (variableIndex_injective hidx)
  have hhlt : variableIndex hvar < variableIndex ell :=
    lt_of_le_of_ne hhle hhidxne

  have hhltQ :
      variableIndex hvar < Q.nonbasicVariableIndex q.entering := by
    change variableIndex hvar < variableIndex (Q.nonbasicVar q.entering)
    rw [← hqell]
    exact hhlt
  have hhcoeff : Q.objectiveCoeff hvar ≤ 0 :=
    q.enteringIsBland.objectiveCoeff_nonpos_of_index_lt hhltQ
  have hPQ : P.Equivalent Q :=
    hDP.equivalent.symm.trans hDQ.equivalent
  have hidentity := hPQ.entering_coefficient_identity p.entering
  obtain ⟨i, hineg⟩ := P.exists_negative_coefficient_product Q p.entering
    hidentity p.enteringIsBland.1 hhcoeff

  let ivar := P.basicVar i
  have hicoeffne : Q.objectiveCoeff ivar ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hineg
    exact (lt_irrefl 0) hineg
  have hiQnot : ivar ∉ Q.basicVariables :=
    Q.not_mem_basicVariables_of_objectiveCoeff_ne_zero hicoeffne
  have hiPmem : ivar ∈ P.basicVariables :=
    P.basicVar_mem_basicVariables i
  have hifickle : D.IsFickle F ivar := by
    by_cases hiD : ivar ∈ D.basicVariables
    · exact ⟨Q,
        ⟨hDQ, (BlandReachable.single q).trans hQ'F⟩,
        Or.inl ⟨hiD, hiQnot⟩⟩
    · exact ⟨P,
        ⟨hDP, (BlandReachable.single p).trans hP'F⟩,
        Or.inr ⟨hiD, hiPmem⟩⟩
  have himem : ivar ∈ D.fickleVariables F :=
    (D.mem_fickleVariables F ivar).2 hifickle
  have hile : variableIndex ivar ≤ variableIndex ell :=
    D.variableIndex_le_greatestFickle F hne himem

  have hcoeffell : 0 < Q.objectiveCoeff ell := by
    rw [hqell, Q.objectiveCoeff_nonbasicVar]
    exact q.enteringIsBland.1
  have hine : ivar ≠ ell := by
    intro hieq
    have hibasic : P.basicVar i = P.basicVar p.leaving :=
      hieq.trans hpell
    have hirow : i = p.leaving := by
      have hslots := P.labels.injective hibasic
      exact Sum.inl_injective hslots
    have hpositive : 0 < Q.objectiveCoeff ivar * P.a i p.entering := by
      rw [hieq, hirow]
      exact mul_pos hcoeffell
        p.leavingIsBland.1.pivotCoefficient_pos
    exact (not_lt_of_ge hpositive.le) hineg
  have hiidxne : variableIndex ivar ≠ variableIndex ell := by
    intro hidx
    exact hine (variableIndex_injective hidx)
  have hilt : variableIndex ivar < variableIndex ell :=
    lt_of_le_of_ne hile hiidxne

  have hiltQ :
      variableIndex ivar < Q.nonbasicVariableIndex q.entering := by
    change variableIndex ivar < variableIndex (Q.nonbasicVar q.entering)
    rw [← hqell]
    exact hilt
  have hicoeff : Q.objectiveCoeff ivar ≤ 0 :=
    q.enteringIsBland.objectiveCoeff_nonpos_of_index_lt hiltQ
  have hia : 0 < P.a i p.entering := by
    by_contra hnot
    have hnonpos : P.a i p.entering ≤ 0 := le_of_not_gt hnot
    have hprod : 0 ≤ Q.objectiveCoeff ivar * P.a i p.entering :=
      mul_nonneg_of_nonpos_of_nonpos hicoeff hnonpos
    exact (not_lt_of_ge hprod) hineg

  have hPon : OnBlandPath D P F :=
    ⟨hDP, (BlandReachable.single p).trans hP'F⟩
  have hQon : OnBlandPath D Q F :=
    ⟨hDQ, (BlandReachable.single q).trans hQ'F⟩
  have hbasicPQ : P.basicAssignment = Q.basicAssignment :=
    (hPon.basicAssignment_eq_of_closedBasis hD hbasis).symm.trans
      (hQon.basicAssignment_eq_of_closedBasis hD hbasis)
  have hibzero : P.b i = 0 := by
    calc
      P.b i = P.basicAssignment ivar :=
        (P.basicAssignment_basicVar i).symm
      _ = Q.basicAssignment ivar := congrFun hbasicPQ ivar
      _ = 0 := Q.basicAssignment_eq_zero_of_not_mem_basicVariables hiQnot
  have hPfeasible : P.IsBasicFeasible := hDP.isBasicFeasible hD
  have himin : P.IsMinimumRatio p.entering i := by
    refine ⟨hia, ?_⟩
    intro k hk
    rw [hibzero, zero_div]
    exact div_nonneg (hPfeasible k) hk.le
  have hleaveIndex :
      P.basicVariableIndex p.leaving ≤ P.basicVariableIndex i :=
    p.leavingIsBland.2 i himin
  have hiIndex :
      P.basicVariableIndex i < P.basicVariableIndex p.leaving := by
    change variableIndex ivar < variableIndex (P.basicVar p.leaving)
    rw [← hpell]
    exact hilt
  exact (not_lt_of_ge hleaveIndex) hiIndex

/-- In particular, a feasible Bland-pivot relation has no directed cycle. -/
theorem bland_acyclic (D : Dictionary m n) (hD : D.IsBasicFeasible) :
    ¬Relation.TransGen IsBlandPivot D D := by
  intro hcycle
  exact D.bland_no_repeated_basis hD hcycle rfl

end Dictionary
end Chapter29
end CLRS
