import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SelectDelimitedFields.Run

/-! # Delimited-field selection: polynomial runtime -/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.SelectDelimitedFields

open _root_.Turing

/-- The field-filtering phase is linear in the two semantic input streams. -/
theorem filterSteps_le (flags : List Bool) (fields : List (Option Bool)) :
    filterSteps flags fields ≤
      2 * flags.length + 2 * fields.length + 2 := by
  induction flags generalizing fields with
  | nil =>
      simp [filterSteps]
      omega
  | cons flag flags ih =>
      rw [filterSteps]
      have hcurrent : currentSteps flag flags fields ≤
          2 * flags.length + 2 * fields.length + 2 := by
        induction fields with
        | nil =>
            simp [currentSteps]
            omega
        | cons field fields fieldIH =>
            cases field with
            | none =>
                cases flag <;>
                  simp only [currentSteps, Bool.false_eq_true, ↓reduceIte,
                    List.length_cons] <;>
                  have hfilter := ih fields <;> omega
            | some bit =>
                cases flag <;>
                  simp only [currentSteps, Bool.false_eq_true, ↓reduceIte,
                    List.length_cons] at fieldIH ⊢ <;> omega
      simp only [List.length_cons]
      omega

/-- The exact builder run fits a linear bound in its typed input encoding. -/
theorem run_steps_le_input_length (flags : List Bool)
    (fields : List (Option Bool)) :
    3 * flags.length + 2 * fields.length + filterSteps flags fields + 7 ≤
      5 * (inputEncoding (flags, fields)).length + 5 := by
  have hfilter := filterSteps_le flags fields
  simp only [inputEncoding, List.length_append, List.length_map,
    List.length_cons]
  omega

/-- A single fixed TM2 selects the Boolean-marked delimited fields in linear
time, including malformed inputs where one side ends early. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputEncoding id
      (fun input => selectFields input.1 input.2) where
  tm := compile program
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 5 * Polynomial.X + 5
  outputsFun := fun input => by
    rcases input with ⟨flags, fields⟩
    have builderRun := run flags fields
    have compiledRun := compile_evalsToInTime program builderRun
    have htime :
        3 * flags.length + 2 * fields.length + filterSteps flags fields + 7 ≤
          (5 * Polynomial.X + 5).eval
            (inputEncoding (flags, fields)).length := by
      have h := run_steps_le_input_length flags fields
      simpa [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] using h
    have bounded : EvalsToInTime (compile program).step
        (initList (compile program) (inputEncoding (flags, fields)))
        (some (haltList (compile program) (selectFields flags fields)))
        ((5 * Polynomial.X + 5).eval
          (inputEncoding (flags, fields)).length) := by
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

end CLRS.Chapter34.Turing.PolyBuilder.SelectDelimitedFields
