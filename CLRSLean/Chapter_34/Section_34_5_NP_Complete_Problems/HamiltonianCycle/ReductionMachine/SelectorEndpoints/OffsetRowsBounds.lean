import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.SelectorEndpoints.OffsetRowsRun
import Mathlib.Tactic

/-!
# HAM-CYCLE selector endpoints: generic offset-row runtime bounds
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints

open PolyBuilder

def encodedMarkedRows (rows : List (List Nat)) : List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

private theorem fieldSteps_le (lower upper : Nat) :
    TMClique.pairRowsFormatFieldSteps lower upper ≤
      7 * (lower + 1) * (upper + 1) := by
  simp [TMClique.pairRowsFormatFieldSteps]
  nlinarith

private theorem valuesSteps_le (values : List Nat) (upper : Nat) :
    TMClique.pairRowsFormatValuesSteps values upper ≤
      7 * (encodeUnaryFrame values).length * (upper + 1) := by
  induction values with
  | nil => simp [TMClique.pairRowsFormatValuesSteps]
  | cons lower values ih =>
      have hfield := fieldSteps_le lower upper
      have hrest :
          (List.map (fun value =>
            TMClique.pairRowsFormatFieldSteps value upper) values).sum ≤
            7 * (List.map (fun value => value + 1) values).sum *
              (upper + 1) := by
        simpa [TMClique.pairRowsFormatValuesSteps] using ih
      simp only [TMClique.pairRowsFormatValuesSteps, List.map_cons,
        List.sum_cons, encodeUnaryFrame_length]
      calc
        _ ≤ 7 * (lower + 1) * (upper + 1) +
              7 * (List.map (fun value => value + 1) values).sum *
                (upper + 1) := Nat.add_le_add hfield hrest
        _ = 7 * (lower + 1 +
              (List.map (fun value => value + 1) values).sum) *
                (upper + 1) := by ring

private theorem rowSteps_le (values : List Nat) (upper : Nat) :
    offsetMarkedRowSteps values upper ≤
      9 * ((encodeUnaryFrame values).length + 1) * (upper + 1) := by
  have hvalues := valuesSteps_le values upper
  let payload := (encodeUnaryFrame values).length
  have hseven : 7 * payload * (upper + 1) ≤
      7 * (payload + 1) * (upper + 1) := by
    exact Nat.mul_le_mul_right (upper + 1)
      (Nat.mul_le_mul_left 7 (Nat.le_succ payload))
  have hpositive : 1 ≤ (payload + 1) * (upper + 1) := by
    have : 0 < (payload + 1) * (upper + 1) :=
      Nat.mul_pos (Nat.succ_pos payload) (Nat.succ_pos upper)
    omega
  have htwo : 2 ≤ 2 * (payload + 1) * (upper + 1) := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hpositive
  calc
    offsetMarkedRowSteps values upper =
        TMClique.pairRowsFormatValuesSteps values upper + 2 := rfl
    _ ≤ 7 * payload * (upper + 1) + 2 :=
      Nat.add_le_add_right (by simpa [payload] using hvalues) 2
    _ ≤ 7 * (payload + 1) * (upper + 1) +
          2 * (payload + 1) * (upper + 1) :=
      Nat.add_le_add hseven htwo
    _ = 9 * (payload + 1) * (upper + 1) := by ring

theorem offsetMarkedRowsSteps_le (base row : Nat)
    (rows : List (List Nat)) :
    offsetMarkedRowsSteps base row rows ≤
      9 * (encodedMarkedRows rows).length *
        (base + row + rows.length + 1) := by
  induction rows generalizing row with
  | nil => simp [offsetMarkedRowsSteps, encodedMarkedRows]
  | cons values rows ih =>
      let payload := (encodeUnaryFrame values).length + 1
      let remaining := (encodedMarkedRows rows).length
      let cap := base + row + (rows.length + 1) + 1
      have hrow := rowSteps_le values (base + row)
      have hupper : base + row + 1 ≤ cap := by
        simp [cap]
      have hrow' : offsetMarkedRowSteps values (base + row) ≤
          9 * payload * cap := by
        exact hrow.trans (Nat.mul_le_mul_left (9 * payload) hupper)
      have hrest := ih (row + 1)
      have hrest' : offsetMarkedRowsSteps base (row + 1) rows ≤
          9 * remaining * cap := by
        simpa [remaining, cap, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hrest
      simp only [offsetMarkedRowsSteps, encodedMarkedRows,
        List.flatMap_cons, List.length_append, List.length_cons]
      change offsetMarkedRowSteps values (base + row) +
          offsetMarkedRowsSteps base (row + 1) rows ≤
        9 * (payload + remaining) * cap
      calc
        _ ≤ 9 * payload * cap + 9 * remaining * cap :=
          Nat.add_le_add hrow' hrest'
        _ = 9 * (payload + remaining) * cap := by ring

private theorem rows_length_le_encodedMarkedRows
    (rows : List (List Nat)) :
    rows.length ≤ (encodedMarkedRows rows).length := by
  induction rows with
  | nil => rfl
  | cons values rows ih =>
      rw [encodedMarkedRows] at ih ⊢
      simp only [List.flatMap_cons, List.length_cons,
        List.length_append, List.length_nil] at *
      omega

theorem encodeOffsetRowsFamily_length (family : OffsetRowsFamily) :
    (encodeOffsetRowsFamily family).length =
      family.base + 1 + (encodedMarkedRows family.rows).length := by
  simp [encodeOffsetRowsFamily, encodedMarkedRows,
    encodeUnaryFrameBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem offsetRowsFormatRevSteps_le_input (family : OffsetRowsFamily) :
    offsetRowsFormatRevSteps family ≤
      20 * (encodeOffsetRowsFamily family).length ^ 2 + 20 := by
  let payload := (encodedMarkedRows family.rows).length
  let n := (encodeOffsetRowsFamily family).length
  have hn : n = family.base + 1 + payload := by
    simpa [n, payload] using encodeOffsetRowsFamily_length family
  have hrowCount := rows_length_le_encodedMarkedRows family.rows
  have hbase : family.base ≤ n := by omega
  have hcount : family.rows.length ≤ n := by omega
  have hcap : family.base + family.rows.length + 1 ≤ n := by
    omega
  have hpayload : payload ≤ n := by omega
  have hrows := offsetMarkedRowsSteps_le family.base 0 family.rows
  have hrows' : offsetMarkedRowsSteps family.base 0 family.rows ≤
      9 * n * n := by
    refine hrows.trans ?_
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_left 9 hpayload) hcap
  simp only [offsetRowsFormatRevSteps]
  nlinarith

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.SelectorEndpoints
