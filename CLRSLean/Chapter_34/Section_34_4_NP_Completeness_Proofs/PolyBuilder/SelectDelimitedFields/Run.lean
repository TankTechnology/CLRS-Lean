import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SelectDelimitedFields.Basic
import Mathlib.Tactic

/-! # Delimited-field selection: exact controller run -/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.SelectDelimitedFields

private theorem storedFlags_reverse (flags : List Bool) :
    storedFlags flags.reverse = (storedFlags flags).reverse := by
  simp [storedFlags]

private theorem storedFields_reverse (fields : List (Option Bool)) :
    storedFields fields.reverse = (storedFields fields).reverse := by
  simp [storedFields]

private def scan_run (flags : List Bool) (fields : List (Option Bool))
    (work : List (Option InputSym))
    (buffer₁ buffer₂ : Option (Option InputSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .scanFlags buffer₁ buffer₂ test
        ((flags.map InputSym.flag).map some ++
          none :: (fields.map InputSym.field).map some)
        [] work [])
      (some (cfg .transfer (some none) buffer₂ test
        ((fields.map InputSym.field).map some) []
        ((storedFlags flags).reverse ++ work) []))
      (2 * flags.length + 1) := by
  induction flags generalizing work buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [storedFlags, flip, step, program, cfg, stepOp]⟩,
        le_rfl⟩
  | cons flag flags ih =>
      let afterPop := cfg (.saveFlag flag) (some (some (.flag flag)))
        buffer₂ test
        ((flags.map InputSym.flag).map some ++
          none :: (fields.map InputSym.field).map some)
        [] work []
      let afterSave := cfg .scanFlags (some (some (.flag flag))) buffer₂ test
        ((flags.map InputSym.flag).map some ++
          none :: (fields.map InputSym.field).map some)
        [] (some (.flag flag) :: work) []
      have first : EvalsToInTime (step program)
          (cfg .scanFlags buffer₁ buffer₂ test
            (((flag :: flags).map InputSym.flag).map some ++
              none :: (fields.map InputSym.field).map some)
            [] work [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [flip, afterPop, step, program, cfg, stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterSave) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterSave, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (work := some (.flag flag) :: work)
        (buffer₁ := some (some (.flag flag)))
      let firstTwo := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * flags.length + 1) _ afterSave _ firstTwo rest
      simpa [storedFlags, List.reverse_cons, Nat.mul_succ,
        List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

private def transfer_run (items work₂ : List (Option InputSym))
    (input : List (Option InputSym)) (buffer₁ buffer₂ : Option (Option InputSym))
    (test : Bool) :
    EvalsToInTime (step program)
      (cfg .transfer buffer₁ buffer₂ test input [] items work₂)
      (some (cfg .nextField none buffer₂ test input [] []
        (items.reverse ++ work₂)))
      (items.length + 1) := by
  induction items generalizing work₂ buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons item items ih =>
      let after := cfg .transfer (some item) buffer₂ test input [] items
        (item :: work₂)
      have first : EvalsToInTime (step program)
          (cfg .transfer buffer₁ buffer₂ test input [] (item :: items) work₂)
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (work₂ := item :: work₂) (buffer₁ := some item)
      let full := EvalsToInTime.trans (step program)
        1 (items.length + 1) _ after _ first rest
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

private def drain_run (input : List (Option InputSym))
    (work : List (Option InputSym))
    (buffer₁ buffer₂ : Option (Option InputSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .drain buffer₁ buffer₂ test input [] work [])
      (some (cfg .restore none buffer₂ test [] [] work []))
      (input.length + 1) := by
  induction input generalizing buffer₁ with
  | nil =>
      exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  | cons symbol input ih =>
      let after := cfg .drain (some symbol) buffer₂ test input [] work []
      have first : EvalsToInTime (step program)
          (cfg .drain buffer₁ buffer₂ test (symbol :: input) [] work [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, step, program, cfg, stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₁ := some symbol)
      let full := EvalsToInTime.trans (step program)
        1 (input.length + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def clearFlags_run (flags : List Bool)
    (work : List (Option InputSym))
    (buffer₁ buffer₂ : Option (Option InputSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .clearFlags buffer₁ buffer₂ test [] [] work (storedFlags flags))
      (some (cfg .restore buffer₁ none test [] [] work []))
      (flags.length + 1) := by
  induction flags generalizing buffer₂ with
  | nil =>
      exact ⟨⟨1, by simp [storedFlags, flip, step, program, cfg, stepOp]⟩,
        le_rfl⟩
  | cons flag flags ih =>
      let item : Option InputSym := some (.flag flag)
      let after := cfg .clearFlags buffer₁ (some item) test [] [] work
        (storedFlags flags)
      have first : EvalsToInTime (step program)
          (cfg .clearFlags buffer₁ buffer₂ test [] [] work
            (storedFlags (flag :: flags)))
          (some after) 1 :=
        ⟨⟨1, by simp [storedFlags, flip, item, after, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some item)
      let full := EvalsToInTime.trans (step program)
        1 (flags.length + 1) _ after _ first rest
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

private def filter_run (flags : List Bool) :
    ∀ (fields : List (Option Bool)) (work : List (Option InputSym))
      (buffer₁ buffer₂ : Option (Option InputSym)) (test : Bool),
      EvalsToInTime (step program)
        (cfg .nextField buffer₁ buffer₂ test (storedFields fields) []
          work (storedFlags flags))
        (some (cfg .restore none none test [] []
          ((storedFields (selectFields flags fields)).reverse ++ work) []))
        (filterSteps flags fields) := by
  induction flags with
  | nil =>
      intro fields work buffer₁ buffer₂ test
      let after := cfg .drain buffer₁ none test (storedFields fields) [] work []
      have first : EvalsToInTime (step program)
          (cfg .nextField buffer₁ buffer₂ test (storedFields fields) []
            work (storedFlags []))
          (some after) 1 :=
        ⟨⟨1, by simp [storedFlags, flip, after, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := drain_run (storedFields fields) work buffer₁ none test
      let full := EvalsToInTime.trans (step program)
        1 ((storedFields fields).length + 1) _ after _ first rest
      simpa [filterSteps, selectFields, storedFields, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full
  | cons flag flags ih =>
      intro fields work buffer₁ buffer₂ test
      cases flag with
      | false =>
          let after := cfg (.scanField false) buffer₁
            (some (some (.flag false))) test (storedFields fields) [] work
            (storedFlags flags)
          have first : EvalsToInTime (step program)
              (cfg .nextField buffer₁ buffer₂ test (storedFields fields) []
                work (storedFlags (false :: flags)))
              (some after) 1 :=
            ⟨⟨1, by simp [storedFlags, flip, after, step, program, cfg,
              stepOp]⟩, le_rfl⟩
          have current : ∀ (remaining : List (Option Bool))
              (currentWork : List (Option InputSym))
              (currentBuffer₁ currentBuffer₂ : Option (Option InputSym)),
              EvalsToInTime (step program)
                (cfg (.scanField false) currentBuffer₁ currentBuffer₂ test
                  (storedFields remaining) [] currentWork (storedFlags flags))
                (some (cfg .restore none none test [] []
                  ((storedFields (selectCurrent false flags remaining)).reverse ++
                    currentWork) []))
                (currentSteps false flags remaining) := by
            intro remaining
            induction remaining with
            | nil =>
                intro currentWork currentBuffer₁ currentBuffer₂
                let afterEmpty := cfg .clearFlags none currentBuffer₂ test [] []
                  currentWork (storedFlags flags)
                have emptyStep : EvalsToInTime (step program)
                    (cfg (.scanField false) currentBuffer₁ currentBuffer₂
                      test (storedFields []) [] currentWork (storedFlags flags))
                    (some afterEmpty) 1 :=
                  ⟨⟨1, by simp [storedFields, flip, afterEmpty, step, program,
                    cfg, stepOp]⟩, le_rfl⟩
                have cleared := clearFlags_run flags currentWork none
                  currentBuffer₂ test
                let full := EvalsToInTime.trans (step program)
                  1 (flags.length + 1) _ afterEmpty _ emptyStep cleared
                simpa [currentSteps, selectCurrent, storedFields, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using full
            | cons field remaining fieldIH =>
                intro currentWork currentBuffer₁ currentBuffer₂
                cases field with
                | none =>
                    let afterPop := cfg .nextField
                      (some (some (.field none))) currentBuffer₂ test
                      (storedFields remaining) [] currentWork (storedFlags flags)
                    have popStep : EvalsToInTime (step program)
                        (cfg (.scanField false) currentBuffer₁ currentBuffer₂
                          test (storedFields (none :: remaining)) [] currentWork
                          (storedFlags flags))
                        (some afterPop) 1 :=
                      ⟨⟨1, by simp [storedFields, flip, afterPop, step,
                        program, cfg, stepOp]⟩, le_rfl⟩
                    have rest := ih remaining currentWork
                      (some (some (.field none))) currentBuffer₂ test
                    let full := EvalsToInTime.trans (step program)
                      1 (filterSteps flags remaining) _ afterPop _ popStep rest
                    simpa [afterPop, currentSteps, selectCurrent, storedFields,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
                | some bit =>
                    let afterPop := cfg (.scanField false)
                      (some (some (.field (some bit)))) currentBuffer₂ test
                      (storedFields remaining) [] currentWork (storedFlags flags)
                    have popStep : EvalsToInTime (step program)
                        (cfg (.scanField false) currentBuffer₁ currentBuffer₂
                          test (storedFields (some bit :: remaining)) [] currentWork
                          (storedFlags flags))
                        (some afterPop) 1 :=
                      ⟨⟨1, by simp [storedFields, flip, afterPop, step,
                        program, cfg, stepOp]⟩, le_rfl⟩
                    have rest := fieldIH currentWork
                      (some (some (.field (some bit)))) currentBuffer₂
                    let full := EvalsToInTime.trans (step program)
                      1 (currentSteps false flags remaining) _ afterPop _
                        popStep rest
                    simpa [afterPop, currentSteps, selectCurrent, storedFields,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
          have rest := current fields work buffer₁
            (some (some (.flag false)))
          let full := EvalsToInTime.trans (step program)
            1 (currentSteps false flags fields) _ after _ first rest
          simpa [filterSteps, selectFields, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full
      | true =>
          let after := cfg (.scanField true) buffer₁
            (some (some (.flag true))) test (storedFields fields) [] work
            (storedFlags flags)
          have first : EvalsToInTime (step program)
              (cfg .nextField buffer₁ buffer₂ test (storedFields fields) []
                work (storedFlags (true :: flags)))
              (some after) 1 :=
            ⟨⟨1, by simp [storedFlags, flip, after, step, program, cfg,
              stepOp]⟩, le_rfl⟩
          have current : ∀ (remaining : List (Option Bool))
              (currentWork : List (Option InputSym))
              (currentBuffer₁ currentBuffer₂ : Option (Option InputSym)),
              EvalsToInTime (step program)
                (cfg (.scanField true) currentBuffer₁ currentBuffer₂ test
                  (storedFields remaining) [] currentWork (storedFlags flags))
                (some (cfg .restore none none test [] []
                  ((storedFields (selectCurrent true flags remaining)).reverse ++
                    currentWork) []))
                (currentSteps true flags remaining) := by
            intro remaining
            induction remaining with
            | nil =>
                intro currentWork currentBuffer₁ currentBuffer₂
                let afterEmpty := cfg .clearFlags none currentBuffer₂ test [] []
                  currentWork (storedFlags flags)
                have emptyStep : EvalsToInTime (step program)
                    (cfg (.scanField true) currentBuffer₁ currentBuffer₂ test
                      (storedFields []) [] currentWork (storedFlags flags))
                    (some afterEmpty) 1 :=
                  ⟨⟨1, by simp [storedFields, flip, afterEmpty, step, program,
                    cfg, stepOp]⟩, le_rfl⟩
                have cleared := clearFlags_run flags currentWork none
                  currentBuffer₂ test
                let full := EvalsToInTime.trans (step program)
                  1 (flags.length + 1) _ afterEmpty _ emptyStep cleared
                simpa [currentSteps, selectCurrent, storedFields, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using full
            | cons field remaining fieldIH =>
                intro currentWork currentBuffer₁ currentBuffer₂
                cases field with
                | none =>
                    let afterPop := cfg (.saveField true none)
                      (some (some (.field none))) currentBuffer₂ test
                      (storedFields remaining) [] currentWork (storedFlags flags)
                    let afterSave := cfg .nextField
                      (some (some (.field none))) currentBuffer₂ test
                      (storedFields remaining) []
                      (some (.field none) :: currentWork) (storedFlags flags)
                    have popStep : EvalsToInTime (step program)
                        (cfg (.scanField true) currentBuffer₁ currentBuffer₂
                          test (storedFields (none :: remaining)) [] currentWork
                          (storedFlags flags))
                        (some afterPop) 1 :=
                      ⟨⟨1, by simp [storedFields, flip, afterPop, step,
                        program, cfg, stepOp]⟩, le_rfl⟩
                    have saveStep : EvalsToInTime (step program) afterPop
                        (some afterSave) 1 :=
                      ⟨⟨1, by simp [flip, afterPop, afterSave, step,
                        program, cfg, stepOp]⟩, le_rfl⟩
                    have rest := ih remaining (some (.field none) :: currentWork)
                      (some (some (.field none))) currentBuffer₂ test
                    let firstTwo := EvalsToInTime.trans (step program)
                      1 1 _ afterPop _ popStep saveStep
                    let full := EvalsToInTime.trans (step program)
                      2 (filterSteps flags remaining) _ afterSave _ firstTwo rest
                    simpa [afterPop, afterSave, currentSteps, selectCurrent,
                      storedFields, List.reverse_cons, List.append_assoc,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
                | some bit =>
                    let afterPop := cfg (.saveField true (some bit))
                      (some (some (.field (some bit)))) currentBuffer₂ test
                      (storedFields remaining) [] currentWork (storedFlags flags)
                    let afterSave := cfg (.scanField true)
                      (some (some (.field (some bit)))) currentBuffer₂ test
                      (storedFields remaining) []
                      (some (.field (some bit)) :: currentWork)
                      (storedFlags flags)
                    have popStep : EvalsToInTime (step program)
                        (cfg (.scanField true) currentBuffer₁ currentBuffer₂
                          test (storedFields (some bit :: remaining)) []
                          currentWork (storedFlags flags))
                        (some afterPop) 1 :=
                      ⟨⟨1, by simp [storedFields, flip, afterPop, step,
                        program, cfg, stepOp]⟩, le_rfl⟩
                    have saveStep : EvalsToInTime (step program) afterPop
                        (some afterSave) 1 :=
                      ⟨⟨1, by simp [flip, afterPop, afterSave, step,
                        program, cfg, stepOp]⟩, le_rfl⟩
                    have rest := fieldIH
                      (some (.field (some bit)) :: currentWork)
                      (some (some (.field (some bit)))) currentBuffer₂
                    let firstTwo := EvalsToInTime.trans (step program)
                      1 1 _ afterPop _ popStep saveStep
                    let full := EvalsToInTime.trans (step program)
                      2 (currentSteps true flags remaining) _ afterSave _
                        firstTwo rest
                    simpa [afterPop, afterSave, currentSteps, selectCurrent,
                      storedFields, List.reverse_cons, List.append_assoc,
                      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
          have rest := current fields work buffer₁
            (some (some (.flag true)))
          let full := EvalsToInTime.trans (step program)
            1 (currentSteps true flags fields) _ after _ first rest
          simpa [filterSteps, selectFields, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using full

private def restore_run (fields output : List (Option Bool))
    (buffer₁ buffer₂ : Option (Option InputSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .restore buffer₁ buffer₂ test [] output
        (storedFields fields) [])
      (some (haltCfg program (fields.reverse ++ output)))
      (2 * fields.length + 2) := by
  induction fields generalizing output buffer₁ with
  | nil =>
      exact ⟨⟨2, by simp [storedFields, Function.iterate_succ_apply, flip,
        step, program, cfg, stepOp, haltCfg]⟩, le_rfl⟩
  | cons field fields ih =>
      let afterPop := cfg (.emit field) (some (some (.field field))) buffer₂
        test [] output (storedFields fields) []
      let afterEmit := cfg .restore (some (some (.field field))) buffer₂ test
        [] (field :: output) (storedFields fields) []
      have first : EvalsToInTime (step program)
          (cfg .restore buffer₁ buffer₂ test [] output
            (storedFields (field :: fields)) [])
          (some afterPop) 1 :=
        ⟨⟨1, by simp [storedFields, flip, afterPop, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have second : EvalsToInTime (step program) afterPop
          (some afterEmit) 1 :=
        ⟨⟨1, by simp [flip, afterPop, afterEmit, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (output := field :: output)
        (buffer₁ := some (some (.field field)))
      let firstTwo := EvalsToInTime.trans (step program)
        1 1 _ afterPop _ first second
      let full := EvalsToInTime.trans (step program)
        2 (2 * fields.length + 2) _ afterEmit _ firstTwo rest
      simpa [List.reverse_cons, Nat.mul_succ, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Field selection never makes the flattened field stream longer. -/
theorem selectFields_length_le (flags : List Bool)
    (fields : List (Option Bool)) :
    (selectFields flags fields).length ≤ fields.length := by
  induction flags generalizing fields with
  | nil => simp [selectFields]
  | cons flag flags ih =>
      simp only [selectFields]
      induction fields with
      | nil => simp [selectCurrent]
      | cons field fields fieldIH =>
          cases field with
          | none =>
              cases flag with
              | false =>
                  simpa [selectCurrent] using Nat.le.step (ih fields)
              | true => simpa [selectCurrent] using Nat.succ_le_succ (ih fields)
          | some bit =>
              cases flag with
              | false =>
                  simpa [selectCurrent] using Nat.le.step fieldIH
              | true => simpa [selectCurrent] using Nat.succ_le_succ fieldIH

/-- Exact end-to-end run on the typed flag/field pair encoding. -/
def run (flags : List Bool) (fields : List (Option Bool)) :
    EvalsToInTime (step program)
      (initialCfg program (inputEncoding (flags, fields)))
      (some (haltCfg program (selectFields flags fields)))
      (3 * flags.length + 2 * fields.length +
        filterSteps flags fields + 7) := by
  have scanned := scan_run flags fields [] none none false
  have scanned' : EvalsToInTime (step program)
      (initialCfg program (inputEncoding (flags, fields)))
      (some (cfg .transfer (some none) none false
        (storedFields fields) [] (storedFlags flags).reverse []))
      (2 * flags.length + 1) := by
    simpa [initialCfg, inputEncoding, storedFields, Function.comp_def, program,
      cfg] using scanned
  have transferred := transfer_run (storedFlags flags).reverse []
    (storedFields fields) (some none) none false
  have transferred' : EvalsToInTime (step program)
      (cfg .transfer (some none) none false
        (storedFields fields) [] (storedFlags flags).reverse [])
      (some (cfg .nextField none none false
        (storedFields fields) [] [] (storedFlags flags)))
      (flags.length + 1) := by
    simpa [storedFlags, storedFlags_reverse] using transferred
  have filtered := filter_run flags fields [] none none false
  have restored := restore_run (selectFields flags fields).reverse [] none none false
  have restored' : EvalsToInTime (step program)
      (cfg .restore none none false [] []
        (storedFields (selectFields flags fields)).reverse [])
      (some (haltCfg program (selectFields flags fields)))
      (2 * (selectFields flags fields).length + 2) := by
    simpa [storedFields_reverse] using restored
  let firstTwoRaw := EvalsToInTime.trans (step program)
    (2 * flags.length + 1) (flags.length + 1) _ _ _ scanned' transferred'
  have firstTwo : EvalsToInTime (step program)
      (initialCfg program (inputEncoding (flags, fields)))
      (some (cfg .nextField none none false
        (storedFields fields) [] [] (storedFlags flags)))
      (3 * flags.length + 2) := by
    convert firstTwoRaw using 1
    omega
  let firstThreeRaw := EvalsToInTime.trans (step program)
    (3 * flags.length + 2) (filterSteps flags fields) _ _ _ firstTwo filtered
  have firstThree : EvalsToInTime (step program)
      (initialCfg program (inputEncoding (flags, fields)))
      (some (cfg .restore none none false [] []
        (storedFields (selectFields flags fields)).reverse []))
      (3 * flags.length + 2 + filterSteps flags fields) := by
    convert firstThreeRaw using 1 <;>
      simp [Nat.add_assoc, Nat.add_comm]
  let full := EvalsToInTime.trans (step program)
    (3 * flags.length + 2 + filterSteps flags fields)
    (2 * (selectFields flags fields).length + 2) _ _ _ firstThree restored'
  have hselected := selectFields_length_le flags fields
  exact ⟨full.toEvalsTo, by
    have := full.steps_le_m
    omega⟩

end CLRS.Chapter34.Turing.PolyBuilder.SelectDelimitedFields
