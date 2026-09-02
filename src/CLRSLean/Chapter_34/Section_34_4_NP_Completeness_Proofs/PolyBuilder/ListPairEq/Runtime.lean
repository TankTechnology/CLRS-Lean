import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListPairEq.Run

/-! # Polynomial runtime of separated-list equality -/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.ListPairEq

theorem compareSteps_le {Γ : Type} [DecidableEq Γ]
    (left right : List Γ) :
    compareSteps left right ≤ 2 * (left.length + right.length) + 4 := by
  induction left generalizing right with
  | nil => cases right <;> simp [compareSteps]
  | cons left lefts ih =>
      cases right with
      | nil => simp [compareSteps]
      | cons right rights =>
          rw [compareSteps]
          have h := ih rights
          simp only [List.length_cons] at h ⊢
          omega

theorem steps_le_pair_length {Γ : Type} [DecidableEq Γ]
    (left right : List Γ) :
    steps left right ≤ 5 * (pairEncoding left right).length + 5 := by
  have h := compareSteps_le left.reverse right.reverse
  simp only [List.length_reverse] at h
  simp only [steps, pairEncoding, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  omega

/-- Equality of two lists over any fixed finite alphabet is decided by one
fixed linear-time TM2. -/
noncomputable def computableInPolyTime
    (Γ : Type) [Fintype Γ] [DecidableEq Γ] :
    _root_.Turing.TM2ComputableInPolyTime
      (fun input : List Γ × List Γ => pairEncoding input.1 input.2)
      _root_.Turing.TM2Comp.boolEncoding
      (fun input => decide (input.1 = input.2)) := by
  exact
    { tm := compile (program Γ)
      inputAlphabet := Equiv.refl _
      outputAlphabet := Equiv.refl _
      time := 5 * Polynomial.X + 5
      outputsFun := fun input => by
        rcases input with ⟨left, right⟩
        have builderRun := run left right
        have compiledRun := compile_evalsToInTime (program Γ) builderRun
        have htime : steps left right ≤
            (5 * Polynomial.X + 5).eval
              (pairEncoding left right).length := by
          have h := steps_le_pair_length left right
          simpa [Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X] using h
        have bounded : _root_.StateTransition.EvalsToInTime
            (compile (program Γ)).step
            (_root_.Turing.initList (compile (program Γ))
              (pairEncoding left right))
            (some (_root_.Turing.haltList (compile (program Γ))
              [decide (left = right)]))
            ((5 * Polynomial.X + 5).eval
              (pairEncoding left right).length) := by
          refine ⟨⟨compiledRun.steps, ?_⟩,
            compiledRun.steps_le_m.trans htime⟩
          convert compiledRun.evals_in_steps using 1
          all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]
          all_goals rfl
        simp only [_root_.Turing.TM2OutputsInTime]
        convert bounded using 1
        · congr 1
          change List.map id _ = _
          exact List.map_id _
        · simp only [_root_.Turing.TM2Comp.boolEncoding,
            Option.map_some, List.map_cons, List.map_nil]
          congr 2 }

end CLRS.Chapter34.Turing.PolyBuilder.ListPairEq
