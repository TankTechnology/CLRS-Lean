import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DelimitedBinarySum.Run

/-! # Delimited binary sum: polynomial runtime -/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum

open _root_.Turing

theorem finishAdd_length_le (accumulator : List Bool) (carry : Bool)
    (work : List Bool) :
    (finishAdd accumulator carry work).length ≤
      accumulator.length + work.length + 1 := by
  induction accumulator generalizing carry work with
  | nil => cases carry <;> simp [finishAdd]
  | cons accumulatorBit accumulator ih =>
      rw [finishAdd]
      have h := ih
        (carry := (BinaryNat.Adder.addCell false accumulatorBit carry).2)
        (work := (BinaryNat.Adder.addCell false accumulatorBit carry).1 :: work)
      simp only [List.length_cons] at h ⊢
      omega

theorem finishSteps_le (accumulator : List Bool) (carry : Bool) :
    finishSteps accumulator carry ≤ 2 * accumulator.length + 2 := by
  induction accumulator generalizing carry with
  | nil => cases carry <;> simp [finishSteps]
  | cons accumulatorBit accumulator ih =>
      rw [finishSteps]
      have h := ih (BinaryNat.Adder.addCell false accumulatorBit carry).2
      simp only [List.length_cons] at h ⊢
      omega

private theorem quadratic_step {smaller larger extra : Nat}
    (hmeasure : smaller + 1 ≤ larger) (hextra : extra ≤ 5 * larger) :
    10 * smaller ^ 2 + extra ≤ 10 * larger ^ 2 := by
  nlinarith

/-- A quadratic envelope for every internal summation state.  Weighting each
unread symbol twice makes the measure drop even when a carry grows the current
accumulator at a delimiter. -/
theorem sumSteps_le (symbols : List (Option Bool))
    (accumulator : List Bool) (carry : Bool) (work : List Bool) :
    sumSteps symbols accumulator carry work ≤
      10 * (2 * symbols.length + accumulator.length + work.length + 1) ^ 2 := by
  induction symbols generalizing accumulator carry work with
  | nil =>
      let next := finishAdd accumulator carry work
      have hfinish := finishSteps_le accumulator carry
      have hnext := finishAdd_length_le accumulator carry work
      have hone : 1 ≤ accumulator.length + work.length + 1 := by omega
      have hsquare : accumulator.length + work.length + 1 ≤
          (accumulator.length + work.length + 1) ^ 2 := by
        nlinarith
      have hlinear :
          1 + finishSteps accumulator carry + (next.length + 1) +
              (2 * next.length + 2) ≤
            10 * (accumulator.length + work.length + 1) := by
        dsimp only [next] at hnext ⊢
        omega
      rw [sumSteps]
      calc
        1 + finishSteps accumulator carry + (next.length + 1) +
              (2 * next.length + 2) ≤
            10 * (accumulator.length + work.length + 1) := hlinear
        _ ≤ 10 * (accumulator.length + work.length + 1) ^ 2 := by
          exact Nat.mul_le_mul_left 10 hsquare
        _ = 10 * (2 * [].length + accumulator.length + work.length + 1) ^ 2 := by
          simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
  | cons field symbols ih =>
      cases field with
      | none =>
          let next := finishAdd accumulator carry work
          have hfinish := finishSteps_le accumulator carry
          have hnext := finishAdd_length_le accumulator carry work
          have hrec := ih next.reverse false []
          simp only [List.length_reverse, List.length_nil, Nat.add_zero] at hrec
          let smaller := 2 * symbols.length + next.length + 1
          let larger :=
            2 * (symbols.length + 1) + accumulator.length + work.length + 1
          have hmeasure : smaller + 1 ≤ larger := by
            dsimp only [smaller, larger, next]
            omega
          have hextra :
              1 + finishSteps accumulator carry + (next.length + 1) ≤
                5 * larger := by
            dsimp only [larger, next] at ⊢
            omega
          have hquad := quadratic_step hmeasure hextra
          rw [sumSteps]
          simp only [List.length_cons]
          change 1 + finishSteps accumulator carry + (next.length + 1) +
              sumSteps symbols next.reverse false [] ≤ 10 * larger ^ 2
          change sumSteps symbols next.reverse false [] ≤ 10 * smaller ^ 2 at hrec
          omega
      | some fieldBit =>
          cases accumulator with
          | nil =>
              let cell := BinaryNat.Adder.addCell fieldBit false carry
              have hrec := ih [] cell.2 (cell.1 :: work)
              simp only [List.length_nil, List.length_cons] at hrec
              let smaller := 2 * symbols.length + work.length + 2
              let larger := 2 * (symbols.length + 1) + work.length + 1
              have hmeasure : smaller + 1 ≤ larger := by
                dsimp only [smaller, larger]
                simp only [Nat.mul_add]
                omega
              have hextra : 3 ≤ 5 * larger := by
                dsimp only [larger]
                omega
              have hquad := quadratic_step hmeasure hextra
              rw [sumSteps]
              simp only [List.length_cons, List.length_nil]
              change 3 + sumSteps symbols [] cell.2 (cell.1 :: work) ≤
                10 * larger ^ 2
              change sumSteps symbols [] cell.2 (cell.1 :: work) ≤
                10 * smaller ^ 2 at hrec
              omega
          | cons accumulatorBit accumulator =>
              let cell := BinaryNat.Adder.addCell fieldBit accumulatorBit carry
              have hrec := ih accumulator cell.2 (cell.1 :: work)
              simp only [List.length_cons] at hrec
              let smaller :=
                2 * symbols.length + accumulator.length + work.length + 2
              let larger :=
                2 * (symbols.length + 1) + (accumulator.length + 1) +
                  work.length + 1
              have hmeasure : smaller + 1 ≤ larger := by
                dsimp only [smaller, larger]
                omega
              have hextra : 3 ≤ 5 * larger := by
                dsimp only [larger]
                omega
              have hquad := quadratic_step hmeasure hextra
              rw [sumSteps]
              simp only [List.length_cons]
              change 3 + sumSteps symbols accumulator cell.2
                  (cell.1 :: work) ≤ 10 * larger ^ 2
              change sumSteps symbols accumulator cell.2
                  (cell.1 :: work) ≤ 10 * smaller ^ 2 at hrec
              omega

theorem steps_le_input_length (input : List (Option Bool)) :
    steps input ≤ 50 * (input.length + 1) ^ 2 := by
  have hsum := sumSteps_le input.reverse [] false []
  simp only [List.length_reverse, List.length_nil, Nat.add_zero] at hsum
  simp only [steps]
  nlinarith

/-- One fixed TM2 sums every delimited compact-binary field in quadratic time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id sumDelimited where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 50 * (Polynomial.X + 1) ^ 2
  outputsFun := fun input => by
    have builderRun := run input
    have compiledRun := compile_evalsToInTime program builderRun
    have htime : steps input ≤
        (50 * (Polynomial.X + 1) ^ 2).eval input.length := by
      have h := steps_le_input_length input
      simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X] using h
    have bounded : EvalsToInTime (compile program).step
        (initList (compile program) input)
        (some (haltList (compile program) (sumDelimited input)))
        ((50 * (Polynomial.X + 1) ^ 2).eval input.length) := by
      refine ⟨⟨compiledRun.steps, ?_⟩,
        compiledRun.steps_le_m.trans htime⟩
      convert compiledRun.evals_in_steps using 1
      all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]
    simp only [TM2OutputsInTime]
    convert bounded using 1
    · congr 1
      change List.map id _ = _
      exact List.map_id _
    · simp only [id_eq, Option.map_some]
      congr 2
      change List.map id _ = _
      exact List.map_id _
    · simp [id]

end CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum
