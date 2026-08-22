import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRowsFormatTermination
import Mathlib.Tactic

/-!
# Formatting triangular pair rows: polynomial bounds
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

private theorem pairRowsFormatFieldSteps_le {lower upper : Nat}
    (hlower : lower < upper) :
    pairRowsFormatFieldSteps lower upper ≤ 7 * (upper + 1) := by
  simp [pairRowsFormatFieldSteps]
  omega

private theorem pairRowsFormatValuesSteps_le (values : List Nat)
    (upper : Nat) (hvalues : ∀ lower ∈ values, lower < upper) :
    pairRowsFormatValuesSteps values upper ≤
      values.length * (7 * (upper + 1)) := by
  induction values with
  | nil => simp [pairRowsFormatValuesSteps]
  | cons lower values ih =>
      have hlower := hvalues lower (by simp)
      have htail : ∀ value ∈ values, value < upper := by
        intro value hvalue
        exact hvalues value (by simp [hvalue])
      have hhead := pairRowsFormatFieldSteps_le hlower
      have hrest := ih htail
      simp only [pairRowsFormatValuesSteps, List.map_cons, List.sum_cons,
        List.length_cons]
      calc
        pairRowsFormatFieldSteps lower upper +
              (values.map fun value =>
                pairRowsFormatFieldSteps value upper).sum ≤
            7 * (upper + 1) +
              values.length * (7 * (upper + 1)) :=
          Nat.add_le_add hhead hrest
        _ = (values.length + 1) * (7 * (upper + 1)) := by ring

/-- A quadratic envelope for one formatted row. -/
theorem pairRowsFormatRowSteps_le (upper : Nat) :
    pairRowsFormatRowSteps upper ≤ 9 * (upper + 1) ^ 2 := by
  have hvalues := pairRowsFormatValuesSteps_le (List.range upper) upper
    (by simp)
  simp only [List.length_range] at hvalues
  simp only [pairRowsFormatRowSteps]
  nlinarith

/-- A coarse cubic envelope for a consecutive family of rows. -/
theorem pairRowsFormatRowsSteps_le (upper count : Nat) :
    pairRowsFormatRowsSteps upper count ≤
      count * (9 * (upper + count + 1) ^ 2) := by
  induction count generalizing upper with
  | zero => simp [pairRowsFormatRowsSteps]
  | succ count ih =>
      let total := upper + (count + 1) + 1
      have hrow := pairRowsFormatRowSteps_le upper
      have hupper : upper + 1 ≤ total := by
        simp [total]
      have hrow' : pairRowsFormatRowSteps upper ≤ 9 * total ^ 2 :=
        hrow.trans (Nat.mul_le_mul_left 9
          (Nat.pow_le_pow_left hupper 2))
      have hrest := ih (upper + 1)
      have hrest' : pairRowsFormatRowsSteps (upper + 1) count ≤
          count * (9 * total ^ 2) := by
        simpa [total, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hrest
      simp only [pairRowsFormatRowsSteps]
      calc
        pairRowsFormatRowSteps upper +
              pairRowsFormatRowsSteps (upper + 1) count ≤
            9 * total ^ 2 + count * (9 * total ^ 2) :=
          Nat.add_le_add hrow' hrest'
        _ = (count + 1) * (9 * total ^ 2) := by ring

/-- Cubic bound in the semantic occurrence count. -/
theorem pairRowsFormatRevSteps_le_count (count : Nat) :
    pairRowsFormatRevSteps count ≤ 12 * (count + 1) ^ 3 := by
  have hrows := pairRowsFormatRowsSteps_le 0 count
  have hcount : count ≤ count + 1 := by omega
  have hrows' : pairRowsFormatRowsSteps 0 count ≤
      9 * (count + 1) ^ 3 := by
    calc
      pairRowsFormatRowsSteps 0 count ≤
          count * (9 * (0 + count + 1) ^ 2) := hrows
      _ ≤ (count + 1) * (9 * (count + 1) ^ 2) :=
        by simpa only [Nat.zero_add] using
          Nat.mul_le_mul_right (9 * (count + 1) ^ 2) hcount
      _ = 9 * (count + 1) ^ 3 := by ring
  simp only [pairRowsFormatRevSteps]
  nlinarith [show count + 1 ≤ (count + 1) ^ 3 by
    exact Nat.le_pow (by omega)]

private theorem pairRowsFormat_count_le_streamFrom
    (current : Nat) (payload : List UnaryFrameSym) (count : Nat) :
    count ≤
      (unaryFrameAffinePrefixRowsStreamFrom current payload count).length := by
  induction count generalizing current payload with
  | zero => simp
  | succ count ih =>
      simp only [unaryFrameAffinePrefixRowsStreamFrom, List.length_append,
        List.length_cons, List.length_nil]
      have hrest := ih (current + 1)
        (payload ++ encodeUnaryFrameBlock current)
      omega

/-- The number of rows is bounded by the canonical stream length because every
row contains an explicit end marker. -/
theorem pairRowsFormat_count_le_input_length (count : Nat) :
    count ≤ (pairRowsFormatInput count).length := by
  rw [pairRowsFormatInput_eq_from]
  exact pairRowsFormat_count_le_streamFrom 0
    (encodeUnaryFrame (List.range 0)) count

/-- Cubic bound in the actual machine-input length. -/
theorem pairRowsFormatRevSteps_le_input (count : Nat) :
    pairRowsFormatRevSteps count ≤
      12 * ((pairRowsFormatInput count).length + 1) ^ 3 := by
  have hcount := pairRowsFormat_count_le_input_length count
  have hpow := Nat.pow_le_pow_left
    (Nat.add_le_add_right hcount 1) 3
  exact (pairRowsFormatRevSteps_le_count count).trans
    (Nat.mul_le_mul_left 12 hpow)

end TMClique
end Turing
end Chapter34
end CLRS
