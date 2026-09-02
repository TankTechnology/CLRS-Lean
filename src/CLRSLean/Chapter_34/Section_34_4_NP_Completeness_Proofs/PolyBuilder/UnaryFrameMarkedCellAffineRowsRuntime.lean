import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedCellAffineRowsSimulation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Affine copies of one marked-cell row: polynomial-time interface
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

theorem encodeUnaryFrameMarkedCellAffineRows_length
    (family : UnaryFrameMarkedCellAffineRows) :
    (encodeUnaryFrameMarkedCellAffineRows family).length =
      family.step + family.count + 2 +
        (family.cells.map fun value => value + 2).sum := by
  simp [encodeUnaryFrameMarkedCellAffineRows, encodeUnaryFrame_length]
  omega

private theorem markedCellAffineRows_map_add_sum
    (amount : Nat) (cells : List Nat) :
    (cells.map fun value => value + amount).sum =
      cells.sum + cells.length * amount := by
  induction cells with
  | nil => simp
  | cons value rest ih =>
      simp [ih]
      ring

private theorem markedCellAffineRows_payload_length
    (cells : List Nat) :
    (cells.flatMap fun value =>
      encodeUnaryFrame [value] ++ [.frameEnd]).length =
        (cells.map fun value => value + 2).sum := by
  induction cells with
  | nil => rfl
  | cons value rest ih =>
      simp [encodeUnaryFrame, encodeUnaryFrameBlock, ih]
      omega

private theorem markedCellAffineRows_finalCells_length
    (amount remaining : Nat) (cells : List Nat) :
    (markedCellAffineRows_finalCells amount remaining cells).length =
      cells.length := by
  induction remaining generalizing cells with
  | zero => rfl
  | succ remaining ih =>
      simp [markedCellAffineRows_finalCells, ih]

private theorem markedCellAffineRows_finalCells_sum
    (amount remaining : Nat) (cells : List Nat) :
    (markedCellAffineRows_finalCells amount remaining cells).sum =
      cells.sum + remaining * cells.length * amount := by
  induction remaining generalizing cells with
  | zero => simp [markedCellAffineRows_finalCells]
  | succ remaining ih =>
      rw [markedCellAffineRows_finalCells, ih,
        markedCellAffineRows_map_add_sum]
      simp only [List.length_map]
      ring

private theorem markedCellAffineRows_scanCellsSteps_eq
    (amount : Nat) (cells : List Nat) :
    markedCellAffineRows_scanCellsSteps amount cells =
      3 * cells.sum + cells.length * (6 * amount + 5) + 1 := by
  induction cells with
  | nil => simp [markedCellAffineRows_scanCellsSteps]
  | cons value rest ih =>
      simp [markedCellAffineRows_scanCellsSteps, ih]
      ring

private theorem markedCellAffineRows_rowsSteps_le
    (amount remaining : Nat) (cells : List Nat) :
    markedCellAffineRows_rowsSteps amount remaining cells ≤
      remaining *
        (4 * (cells.sum + remaining * cells.length * amount) +
          cells.length * (6 * amount + 6) + 4) + 1 := by
  induction remaining generalizing cells with
  | zero => simp [markedCellAffineRows_rowsSteps]
  | succ remaining ih =>
      let next := cells.map fun value => value + amount
      have hrest := ih next
      rw [markedCellAffineRows_map_add_sum] at hrest
      simp only [markedCellAffineRows_rowsSteps]
      rw [markedCellAffineRows_scanCellsSteps_eq]
      simp only [encodeUnaryFrame_length]
      have hencode :
          (cells.map fun value => value + 1).sum =
            cells.sum + cells.length := by
        simpa using markedCellAffineRows_map_add_sum 1 cells
      rw [hencode]
      dsimp only [next] at hrest
      simp only [List.length_map] at hrest
      have hnextComm :
          (cells.map fun value => value + amount) =
            cells.map fun value => amount + value := by
        apply List.map_congr_left
        intro value _
        omega
      rw [hnextComm] at hrest
      ring_nf at hrest ⊢
      omega

/-- A coarse quartic envelope in the complete unary source length. -/
theorem unaryFrameMarkedCellAffineRowsRev_steps_le
    (family : UnaryFrameMarkedCellAffineRows) :
    unaryFrameMarkedCellAffineRowsRevSteps family ≤
      100 * (encodeUnaryFrameMarkedCellAffineRows family).length ^ 4 + 100 := by
  let n := (encodeUnaryFrameMarkedCellAffineRows family).length
  have hnEq : n = family.step + family.count + 2 +
      (family.cells.map fun value => value + 2).sum := by
    simpa [n] using encodeUnaryFrameMarkedCellAffineRows_length family
  have hn : 1 ≤ n := by omega
  have hnPos : 0 < n := by omega
  have hstep : family.step ≤ n := by omega
  have hcount : family.count ≤ n := by omega
  have hcellSumPart : family.cells.sum ≤
      (family.cells.map fun value => value + 2).sum := by
    induction family.cells with
    | nil => simp
    | cons value rest ih =>
        simp at ih ⊢
        omega
  have hcellsSum : family.cells.sum ≤ n := hcellSumPart.trans (by omega)
  have hcellLengthPart : family.cells.length ≤
      (family.cells.map fun value => value + 2).sum := by
    induction family.cells with
    | nil => simp
    | cons value rest ih =>
        simp at ih ⊢
        omega
  have hcellsLength : family.cells.length ≤ n :=
    hcellLengthPart.trans (by omega)
  rw [show (encodeUnaryFrameMarkedCellAffineRows family).length = n by rfl]
  cases hcountValue : family.count with
  | zero =>
      simp [unaryFrameMarkedCellAffineRowsRevSteps, hcountValue,
        markedCellAffineRows_cleanupSteps]
      have hpayload :
          (family.cells.flatMap fun value =>
            encodeUnaryFrame [value] ++ [.frameEnd]).length ≤ n := by
        rw [markedCellAffineRows_payload_length]
        omega
      have hn2 : n ≤ n ^ 2 := by
        simpa [pow_two] using Nat.le_mul_of_pos_right n hnPos
      have hn3 : n ^ 2 ≤ n ^ 3 := by
        calc
          n ^ 2 ≤ n ^ 2 * n := Nat.le_mul_of_pos_right (n ^ 2) hnPos
          _ = n ^ 3 := by ring
      have hn4 : n ^ 3 ≤ n ^ 4 := by
        calc
          n ^ 3 ≤ n ^ 3 * n := Nat.le_mul_of_pos_right (n ^ 3) hnPos
          _ = n ^ 4 := by ring
      calc
        _ ≤ 6 * n + 10 := by omega
        _ ≤ 100 * n ^ 4 + 100 := by omega
  | succ remaining =>
      have hremaining : remaining ≤ n := by omega
      have hproduct : remaining * family.cells.length * family.step ≤ n ^ 3 := by
        have h₁ := Nat.mul_le_mul hremaining hcellsLength
        have h₂ := Nat.mul_le_mul h₁ hstep
        simpa [pow_succ, pow_two, Nat.mul_assoc] using h₂
      have hbudget :
          4 * (family.cells.sum +
              remaining * family.cells.length * family.step) +
              family.cells.length * (6 * family.step + 6) + 4 ≤
            24 * n ^ 3 := by
        have hlengthStep := Nat.mul_le_mul hcellsLength hstep
        have hn2 : n ≤ n ^ 2 := by nlinarith
        have hn3 : n ^ 2 ≤ n ^ 3 := by nlinarith
        nlinarith
      have hrowsRaw := markedCellAffineRows_rowsSteps_le family.step remaining
        family.cells
      have hrows :
          markedCellAffineRows_rowsSteps family.step remaining family.cells ≤
            24 * n ^ 4 + 1 := by
        calc
          _ ≤ remaining *
              (4 * (family.cells.sum +
                  remaining * family.cells.length * family.step) +
                family.cells.length * (6 * family.step + 6) + 4) + 1 :=
            hrowsRaw
          _ ≤ n * (24 * n ^ 3) + 1 := by
            exact Nat.add_le_add_right
              (Nat.mul_le_mul hremaining hbudget) 1
          _ = 24 * n ^ 4 + 1 := by ring
      have hfirst := markedCellAffineRows_firstCopySteps_eq family.cells
      have hfirstBound :
          markedCellAffineRows_firstCopySteps family.cells ≤ 7 * n + 1 := by
        rw [hfirst, encodeUnaryFrame_length]
        have hencode :
            (family.cells.map fun value => value + 1).sum =
              family.cells.sum + family.cells.length := by
          simpa using markedCellAffineRows_map_add_sum 1 family.cells
        rw [hencode]
        omega
      have hfinalSum := markedCellAffineRows_finalCells_sum family.step remaining
        family.cells
      have hfinalLength := markedCellAffineRows_finalCells_length family.step
        remaining family.cells
      let finalCells := markedCellAffineRows_finalCells family.step remaining
        family.cells
      have hfinalEncode : (encodeUnaryFrame finalCells).length ≤ 3 * n ^ 3 := by
        rw [encodeUnaryFrame_length]
        have hencode : (finalCells.map fun value => value + 1).sum =
            finalCells.sum + finalCells.length := by
          simpa using markedCellAffineRows_map_add_sum 1 finalCells
        rw [hencode]
        dsimp only [finalCells]
        rw [hfinalSum, hfinalLength]
        have hnSquare : n ≤ n ^ 2 := by
          simpa [pow_two] using Nat.le_mul_of_pos_right n hnPos
        have hnCube : n ^ 2 ≤ n ^ 3 := by
          calc
            n ^ 2 ≤ n ^ 2 * n := Nat.le_mul_of_pos_right (n ^ 2) hnPos
            _ = n ^ 3 := by ring
        nlinarith
      dsimp only [finalCells] at hfinalEncode
      simp only [unaryFrameMarkedCellAffineRowsRevSteps, hcountValue]
      simp only [markedCellAffineRows_cleanupSteps, List.length_nil,
        Nat.zero_add, List.length_reverse]
      have hn2 : n ≤ n ^ 2 := by
        simpa [pow_two] using Nat.le_mul_of_pos_right n hnPos
      have hn3 : n ^ 2 ≤ n ^ 3 := by
        calc
          n ^ 2 ≤ n ^ 2 * n := Nat.le_mul_of_pos_right (n ^ 2) hnPos
          _ = n ^ 3 := by ring
      have hn4 : n ^ 3 ≤ n ^ 4 := by
        calc
          n ^ 3 ≤ n ^ 3 * n := Nat.le_mul_of_pos_right (n ^ 3) hnPos
          _ = n ^ 4 := by ring
      calc
        _ ≤ 24 * n ^ 4 + 3 * n ^ 3 + 12 * n + 15 := by omega
        _ ≤ 100 * n ^ 4 + 100 := by omega

/-- Concrete quartic-time TM2 for the reverse affine marked-row stream. -/
noncomputable def unaryFrameMarkedCellAffineRowsRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedCellAffineRows id
      (fun family => (unaryFrameMarkedCellAffineRowsStream family).reverse) where
  tm := compile unaryFrameMarkedCellAffineRowsRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 100 * Polynomial.X ^ 4 + 100
  outputsFun := fun family => by
    have builderRun := unaryFrameMarkedCellAffineRowsRev_runFrom family
    have compiledRun := compile_evalsToInTime
      unaryFrameMarkedCellAffineRowsRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedCellAffineRowsRevProgram).step
        (_root_.Turing.initList (compile unaryFrameMarkedCellAffineRowsRevProgram)
          (encodeUnaryFrameMarkedCellAffineRows family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedCellAffineRowsRevProgram)
          (unaryFrameMarkedCellAffineRowsStream family).reverse))
        (unaryFrameMarkedCellAffineRowsRevSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : unaryFrameMarkedCellAffineRowsRevSteps family ≤
        (100 * Polynomial.X ^ 4 + 100).eval
          (encodeUnaryFrameMarkedCellAffineRows family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameMarkedCellAffineRowsRev_steps_le family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameMarkedCellAffineRowsRevProgram).step
        (_root_.Turing.initList (compile unaryFrameMarkedCellAffineRowsRevProgram)
          (encodeUnaryFrameMarkedCellAffineRows family))
        (some (_root_.Turing.haltList
          (compile unaryFrameMarkedCellAffineRowsRevProgram)
          (unaryFrameMarkedCellAffineRowsStream family).reverse))
        ((100 * Polynomial.X ^ 4 + 100).eval
          (encodeUnaryFrameMarkedCellAffineRows family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward affine marked-row stream, obtained by one verified reversal pass. -/
noncomputable def unaryFrameMarkedCellAffineRowsStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameMarkedCellAffineRows id
      unaryFrameMarkedCellAffineRowsStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameMarkedCellAffineRowsRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
