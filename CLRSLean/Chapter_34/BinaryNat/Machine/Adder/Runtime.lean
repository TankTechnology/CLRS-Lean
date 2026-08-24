import CLRSLean.Chapter_34.BinaryNat.Machine.Adder.Run

/-! # Polynomial runtime packaging for the fixed binary adder -/

noncomputable section

namespace CLRS.Chapter34.Turing.BinaryNat.Adder

open PolyBuilder

theorem addSteps_le (left right : List Bool) (carry : Bool) :
    addSteps left right carry ≤ 3 * (left.length + right.length) + 4 := by
  induction left generalizing right carry with
  | nil =>
      induction right generalizing carry with
      | nil => cases carry <;> simp [addSteps]
      | cons right rights ih =>
          rw [addSteps]
          have h := ih (addCell false right carry).2
          simp only [List.length_cons, List.length_nil, Nat.zero_add] at h ⊢
          omega
  | cons left lefts ih =>
      cases right with
      | nil =>
          rw [addSteps]
          have h := ih [] (addCell left false carry).2
          simp only [List.length_cons, List.length_nil] at h ⊢
          omega
      | cons right rights =>
          rw [addSteps]
          have h := ih rights (addCell left right carry).2
          simp only [List.length_cons]
          omega

theorem steps_le_pair_length (left right : List Bool) :
    steps left right ≤ 5 * (pairEncoding left right).length + 5 := by
  have hadd := addSteps_le left.reverse right.reverse false
  simp only [List.length_reverse] at hadd
  simp only [steps, pairEncoding, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  omega

/-- A genuine fixed TM2 adds two separated big-endian bit words in linear
time.  Numeric correctness and canonical-output preservation are established
in the semantic layer. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      (fun input : List Bool × List Bool => pairEncoding input.1 input.2)
      id (fun input => addWords input.1 input.2) where
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
          (pairEncoding left right).length := by
      have h := steps_le_pair_length left right
      simpa [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] using h
    have bounded : _root_.StateTransition.EvalsToInTime
        (compile program).step
        (_root_.Turing.initList (compile program) (pairEncoding left right))
        (some (_root_.Turing.haltList (compile program)
          (addWords left right)))
        ((5 * Polynomial.X + 5).eval
          (pairEncoding left right).length) := by
      refine ⟨⟨compiledRun.steps, ?_⟩,
        compiledRun.steps_le_m.trans htime⟩
      convert compiledRun.evals_in_steps using 1
      all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]
    simp only [_root_.Turing.TM2OutputsInTime]
    convert bounded using 1
    · congr 1
      change List.map id _ = _
      exact List.map_id _
    · simp only [id_eq, Option.map_some]
      congr 2
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.BinaryNat.Adder
