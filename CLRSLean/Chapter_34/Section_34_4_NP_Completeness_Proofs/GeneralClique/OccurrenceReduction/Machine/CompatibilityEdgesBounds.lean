import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesTermination
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: polynomial runtime

Every numeric quantity inspected by the compatibility controller is paid for
by an explicit unary block in its serialized row input.  The lemmas below
turn that representation invariant into a cubic bound for all pair scans,
conditional edge emissions, restoration passes, and cleanup.
-/

noncomputable section
namespace CLRS.Chapter34.Turing.TMClique
open PolyBuilder

private theorem entry_length_le_entries_length
    {entry : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hentry : entry ∈ entries) :
    (encodeIndexedOccurrenceEntry entry).length ≤
      (encodeIndexedOccurrenceEntries entries).length := by
  induction entries with
  | nil => simp at hentry
  | cons head entries ih =>
      simp only [List.mem_cons] at hentry
      simp only [encodeIndexedOccurrenceEntries, List.flatMap_cons,
        List.length_append]
      rcases hentry with rfl | hentry
      · omega
      · have htail := ih hentry
        change (encodeIndexedOccurrenceEntry entry).length ≤
          (entries.flatMap encodeIndexedOccurrenceEntry).length at htail
        omega

private theorem entry_fields_le_entries_length
    {entry : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hentry : entry ∈ entries) :
    entry.2 ≤ (encodeIndexedOccurrenceEntries entries).length ∧
    entry.1.clauseIndex ≤ (encodeIndexedOccurrenceEntries entries).length ∧
    occurrenceVariableCode entry.1.literal ≤
      (encodeIndexedOccurrenceEntries entries).length := by
  have hlength := entry_length_le_entries_length hentry
  rcases entry with ⟨⟨clause, position, literal⟩, vertex⟩
  cases literal <;>
    simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
      encodeUnaryFrame_length, occurrencePolarityCode,
      occurrenceVariableCode] at hlength ⊢ <;> omega

private theorem entries_length_le_encoding_length
    (entries : List (IndexedOccurrence × Nat)) :
    entries.length ≤ (encodeIndexedOccurrenceEntries entries).length := by
  induction entries with
  | nil => simp [encodeIndexedOccurrenceEntries]
  | cons entry entries ih =>
      change entries.length ≤
        (entries.flatMap encodeIndexedOccurrenceEntry).length at ih
      simp only [encodeIndexedOccurrenceEntries, List.flatMap_cons,
        List.length_cons, List.length_append]
      have hrow : 1 ≤ (encodeIndexedOccurrenceEntry entry).length := by
        rcases entry with ⟨⟨clause, position, literal⟩, vertex⟩
        cases literal <;>
          simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
            encodeUnaryFrame_length, occurrencePolarityCode,
            occurrenceVariableCode]
      omega

private theorem sum_map_le_mul {α : Type} (xs : List α) (f : α → Nat)
    (bound : Nat) (hbound : ∀ x ∈ xs, f x ≤ bound) :
    (xs.map f).sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := hbound x (by simp)
      have htail : ∀ y ∈ xs, f y ≤ bound := by
        intro y hy
        exact hbound y (by simp [hy])
      have hrest := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

private theorem current_steps_le {entry : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hentry : entry ∈ entries) :
    compatibilityEdgesCurrentRowSteps entry ≤
      10 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hfields := entry_fields_le_entries_length hentry
  rcases entry with ⟨⟨clause, position, literal⟩, vertex⟩
  cases literal <;>
    simp [compatibilityEdgesCurrentRowSteps, occurrencePolarityFlag,
      occurrenceVariableCode] at * <;> omega

private theorem prior_steps_le
    {current prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)}
    (hcurrent : current ∈ entries) (hprior : prior ∈ entries) :
    compatibilityEdgesPriorRowSteps current prior ≤
      30 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hc := entry_fields_le_entries_length hcurrent
  have hp := entry_fields_le_entries_length hprior
  rcases current with ⟨⟨cc, cpos, clit⟩, cv⟩
  rcases prior with ⟨⟨pc, ppos, plit⟩, pv⟩
  cases clit <;> cases plit <;>
    simp [compatibilityEdgesPriorRowSteps,
      compatibilityEdgesComparisonSteps, occurrencePolarityFlag,
      occurrenceVariableCode] at * <;> omega


private theorem restore_steps_le
    {prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hprior : prior ∈ entries) :
    compatibilityEdgesRestoreTaggedRowSteps prior ≤
      8 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hp := entry_fields_le_entries_length hprior
  rcases prior with ⟨⟨pc, ppos, plit⟩, pv⟩
  cases plit <;>
    simp [compatibilityEdgesRestoreTaggedRowSteps,
      occurrencePolarityCode, occurrenceVariableCode] at * <;> omega

private theorem emit_flagged_steps_le
    {prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)} (hprior : prior ∈ entries) :
    compatibilityEdgesEmitFlaggedRowSteps prior ≤
      8 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hp := entry_fields_le_entries_length hprior
  rcases prior with ⟨⟨pc, ppos, plit⟩, pv⟩
  cases plit <;>
    simp [compatibilityEdgesEmitFlaggedRowSteps,
      occurrencePolarityCode, occurrenceVariableCode] at * <;> omega

private theorem emit_edge_steps_le
    {current prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)}
    (hcurrent : current ∈ entries) (hprior : prior ∈ entries) :
    compatibilityEdgesEmitCompatibleEdgeSteps current.2 prior.2 ≤
      10 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hc := entry_fields_le_entries_length hcurrent
  have hp := entry_fields_le_entries_length hprior
  simp only [compatibilityEdgesEmitCompatibleEdgeSteps]
  omega

private theorem emit_prior_steps_le
    {current prior : IndexedOccurrence × Nat}
    {entries : List (IndexedOccurrence × Nat)}
    (hcurrent : current ∈ entries) (hprior : prior ∈ entries) :
    compatibilityEdgesEmitPriorRowSteps current prior ≤
      20 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  have hscan := emit_flagged_steps_le hprior
  have hedge := emit_edge_steps_le hcurrent hprior
  have hp := entry_fields_le_entries_length hprior
  simp only [compatibilityEdgesEmitPriorRowSteps]
  split <;> omega


private theorem encodeReversedOccurrenceEntries_length
    (entries : List (IndexedOccurrence × Nat)) :
    (encodeReversedOccurrenceEntries entries).length =
      (encodeIndexedOccurrenceEntries entries).length := by
  induction entries with
  | nil => simp [encodeReversedOccurrenceEntries,
      encodeIndexedOccurrenceEntries]
  | cons entry entries ih =>
      simp [encodeReversedOccurrenceEntries,
        encodeIndexedOccurrenceEntries]

/-- Reversing a row family preserves its serialized unary length. -/
theorem encodeIndexedOccurrenceEntries_reverse_length
    (entries : List (IndexedOccurrence × Nat)) :
    (encodeIndexedOccurrenceEntries entries.reverse).length =
      (encodeIndexedOccurrenceEntries entries).length := by
  simp [encodeIndexedOccurrenceEntries, List.length_flatMap,
    List.map_reverse]

private theorem outer_iteration_steps_le
    (current : IndexedOccurrence × Nat)
    (priors : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesOuterIterationSteps current priors ≤
      70 * ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) ^ 2 := by
  let entries := current :: priors
  let bound := (encodeIndexedOccurrenceEntries entries).length
  have hcurrent : current ∈ entries := by simp [entries]
  have hcurrentFields := entry_fields_le_entries_length hcurrent
  have hcurrentSteps := current_steps_le hcurrent
  have hpriorEach : ∀ prior ∈ priors,
      compatibilityEdgesPriorRowSteps current prior ≤ 30 * (bound + 1) := by
    intro prior hprior
    have : prior ∈ entries := by simp [entries, hprior]
    simpa [bound] using prior_steps_le hcurrent this
  have hpriorSum := sum_map_le_mul priors
    (compatibilityEdgesPriorRowSteps current) (30 * (bound + 1)) hpriorEach
  have hrestoreEach : ∀ prior ∈ priors.reverse,
      compatibilityEdgesRestoreTaggedRowSteps prior + 1 ≤
        9 * (bound + 1) := by
    intro prior hprior
    have hprior' : prior ∈ priors := by simpa using hprior
    have hmem : prior ∈ entries := by simp [entries, hprior']
    have hrestore := restore_steps_le hmem
    change compatibilityEdgesRestoreTaggedRowSteps prior ≤
      8 * (bound + 1) at hrestore
    omega
  have hrestoreSum := sum_map_le_mul priors.reverse
    (fun prior => compatibilityEdgesRestoreTaggedRowSteps prior + 1)
    (9 * (bound + 1)) hrestoreEach
  have hemitEach : ∀ prior ∈ priors,
      compatibilityEdgesEmitPriorRowSteps current prior ≤
        20 * (bound + 1) := by
    intro prior hprior
    have hmem : prior ∈ entries := by simp [entries, hprior]
    simpa [bound] using emit_prior_steps_le hcurrent hmem
  have hemitSum := sum_map_le_mul priors
    (compatibilityEdgesEmitPriorRowSteps current) (20 * (bound + 1))
    hemitEach
  have hentriesLength := entries_length_le_encoding_length entries
  have hpriorsLength : priors.length ≤ bound := by
    change entries.length ≤ bound at hentriesLength
    simp only [entries, List.length_cons] at hentriesLength
    omega
  have hreverseLength : priors.reverse.length ≤ bound := by
    simpa using hpriorsLength
  have hsymbols :
      (encodeReversedOccurrenceEntries priors.reverse).length ≤ bound := by
    rw [encodeReversedOccurrenceEntries_length,
      encodeIndexedOccurrenceEntries_reverse_length]
    simp [bound, entries, encodeIndexedOccurrenceEntries]
  simp only [compatibilityEdgesOuterIterationSteps,
    compatibilityEdgesPriorRowsSteps,
    compatibilityEdgesRestoreTaggedRowsSteps,
    compatibilityEdgesEmitPriorRowsSteps,
    compatibilityEdgesFinishIterationSteps]
  change _ ≤ 70 * (bound + 1) ^ 2
  nlinarith


private theorem outer_iterations_steps_le_mul
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesOuterIterationsSteps entries ≤
      entries.length *
        (70 * ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 2) := by
  induction entries with
  | nil => simp [compatibilityEdgesOuterIterationsSteps]
  | cons current priors ih =>
      have hfirst := outer_iteration_steps_le current priors
      have hencoding :
          (encodeIndexedOccurrenceEntries priors).length ≤
            (encodeIndexedOccurrenceEntries (current :: priors)).length := by
        simp [encodeIndexedOccurrenceEntries]
      have hpow :
          ((encodeIndexedOccurrenceEntries priors).length + 1) ^ 2 ≤
            ((encodeIndexedOccurrenceEntries (current :: priors)).length + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.add_le_add_right hencoding 1) 2
      have hrest : compatibilityEdgesOuterIterationsSteps priors ≤
          priors.length *
            (70 * ((encodeIndexedOccurrenceEntries
              (current :: priors)).length + 1) ^ 2) :=
        ih.trans (Nat.mul_le_mul_left priors.length
          (Nat.mul_le_mul_left 70 hpow))
      simp only [compatibilityEdgesOuterIterationsSteps, List.length_cons]
      nlinarith

/-- The complete outer-loop family has a cubic bound in the actual serialized
row-family length. -/
theorem compatibilityEdgesOuterIterationsSteps_le_input
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesOuterIterationsSteps entries ≤
      70 * ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 3 := by
  have hsteps := outer_iterations_steps_le_mul entries
  have hlength := entries_length_le_encoding_length entries
  have hsquare : 0 ≤
      ((encodeIndexedOccurrenceEntries entries).length + 1) ^ 2 :=
    Nat.zero_le _
  nlinarith


/-- Loading an arbitrary well-shaped row family is linear in its serialized
length. -/
theorem compatibilityEdgesLoadRowsSteps_le_input
    (entries : List (IndexedOccurrence × Nat)) :
    compatibilityEdgesLoadRowsSteps entries ≤
      4 * ((encodeIndexedOccurrenceEntries entries).length + 1) := by
  induction entries with
  | nil => simp [compatibilityEdgesLoadRowsSteps,
      encodeIndexedOccurrenceEntries]
  | cons entry entries ih =>
      change (entries.map compatibilityEdgesLoadRowSteps).sum ≤
        4 * ((entries.flatMap encodeIndexedOccurrenceEntry).length + 1) at ih
      have hrow : 1 ≤ (encodeIndexedOccurrenceEntry entry).length := by
        rcases entry with ⟨⟨clause, position, literal⟩, vertex⟩
        cases literal <;>
          simp [encodeIndexedOccurrenceEntry, indexedOccurrenceRowValues,
            encodeUnaryFrame_length, occurrencePolarityCode,
            occurrenceVariableCode]
      simp only [compatibilityEdgesLoadRowsSteps, List.map_cons,
        List.sum_cons, compatibilityEdgesLoadRowSteps,
        encodeIndexedOccurrenceEntries, List.flatMap_cons,
        List.length_append]
      omega

/-- The whole terminating compatibility controller has a cubic bound in the
actual canonical row input consumed by the fixed program. -/
theorem compatibilityEdgesSteps_le_input (formula : CNF) :
    compatibilityEdgesSteps formula ≤
      80 * ((encodeIndexedOccurrenceRows formula).length + 1) ^ 3 := by
  let entries := (indexedOccurrences formula).zipIdx
  let inputLength := (encodeIndexedOccurrenceRows formula).length
  have hencoding :
      (encodeIndexedOccurrenceEntries entries).length = inputLength := by
    simp [entries, inputLength, encodeIndexedOccurrenceEntries_zipIdx]
  have hreverse :
      (encodeIndexedOccurrenceEntries entries.reverse).length = inputLength := by
    rw [encodeIndexedOccurrenceEntries_reverse_length, hencoding]
  have hload := compatibilityEdgesLoadRowsSteps_le_input entries
  rw [hencoding] at hload
  have houter := compatibilityEdgesOuterIterationsSteps_le_input entries.reverse
  rw [hreverse] at houter
  have hlinear : inputLength + 1 ≤ (inputLength + 1) ^ 3 :=
    Nat.le_pow (by omega)
  simp only [compatibilityEdgesSteps]
  change compatibilityEdgesLoadRowsSteps entries +
      compatibilityEdgesOuterIterationsSteps entries.reverse + 3 ≤
    80 * (inputLength + 1) ^ 3
  nlinarith

end CLRS.Chapter34.Turing.TMClique
