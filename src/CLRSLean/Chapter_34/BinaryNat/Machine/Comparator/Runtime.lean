import CLRSLean.Chapter_34.BinaryNat.Machine.Comparator.Run

/-! # Polynomial runtime packaging for the fixed binary comparator -/

noncomputable section

namespace CLRS.Chapter34.Turing.BinaryNat.Comparator

open PolyBuilder

theorem compareSteps_le (left right : List Bool) (result : Bool) :
    compareSteps left right result ≤ 2 * (left.length + right.length) + 4 := by
  induction left generalizing right result with
  | nil =>
      induction right generalizing result with
      | nil => simp [compareSteps]
      | cons right rights ih =>
          rw [compareSteps]
          have h := ih (leCell false right result)
          simp only [List.length_cons, List.length_nil, Nat.zero_add] at h ⊢
          omega
  | cons left lefts ih =>
      cases right with
      | nil =>
          rw [compareSteps]
          have h := ih [] (leCell left false result)
          simp only [List.length_cons, List.length_nil] at h ⊢
          omega
      | cons right rights =>
          rw [compareSteps]
          have h := ih rights (leCell left right result)
          simp only [List.length_cons]
          omega

theorem steps_le_pair_length (left right : List Bool) :
    steps left right ≤ 5 * (CLRS.Chapter34.pairEncoding left right).length + 5 := by
  have hcompare := compareSteps_le left.reverse right.reverse true
  simp only [List.length_reverse] at hcompare
  simp only [steps, CLRS.Chapter34.pairEncoding, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  omega

/-- A genuine fixed TM2 compares arbitrary big-endian bit words in linear
time and emits one Boolean bit. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (fun input : List Bool × List Bool =>
        CLRS.Chapter34.pairEncoding input.1 input.2)
      _root_.Turing.TM2Comp.boolEncoding
      (fun input => leWords input.1 input.2) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 5 * Polynomial.X + 5
  outputsFun := fun input => by
    rcases input with ⟨left, right⟩
    have builderRun := run left right
    have compiledRun := compile_evalsToInTime program builderRun
    have htime : steps left right ≤
        (5 * Polynomial.X + 5).eval
          (CLRS.Chapter34.pairEncoding left right).length := by
      have h := steps_le_pair_length left right
      simpa [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] using h
    have bounded : _root_.StateTransition.EvalsToInTime
        (compile program).step
        (_root_.Turing.initList (compile program)
          (CLRS.Chapter34.pairEncoding left right))
        (some (_root_.Turing.haltList (compile program)
          [leWords left right]))
        ((5 * Polynomial.X + 5).eval
          (CLRS.Chapter34.pairEncoding left right).length) := by
      refine ⟨⟨compiledRun.steps, ?_⟩,
        compiledRun.steps_le_m.trans htime⟩
      convert compiledRun.evals_in_steps using 1
      all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg] <;> rfl
    simp only [_root_.Turing.TM2OutputsInTime]
    convert bounded using 1
    · congr 1
      change List.map id _ = _
      exact List.map_id _
    · simp only [Option.map_some]
      congr 2

end CLRS.Chapter34.Turing.BinaryNat.Comparator
