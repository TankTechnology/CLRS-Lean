import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSource
import Mathlib.Tactic

/-!
# Affine progression source for the widened fallback

The canonical workspace row is split into a fixed number of progression
segments.  Runtime height controls only segment bases and counts; the segment
table itself depends solely on the fixed verifier machine.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Public height values followed by the fixed false overflow suffix. -/
theorem transitionWidenedFallbackStackHeightValues_eq_parts
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    transitionWidenedFallbackStackHeightValues tm seed k =
      List.range'
          (seed.rowBase + transitionEqPrefixWidth tm +
            cfgStackBitOffset tm seed.height k)
          (seed.height + 1) ++
        List.replicate (maxPushesPerStep tm) seed.start := by
  unfold transitionWidenedFallbackStackHeightValues workHeight
  rw [show seed.height + maxPushesPerStep tm + 1 =
      (seed.height + 1) + maxPushesPerStep tm by omega]
  rw [List.ofFn_add]
  congr 1
  · rw [← transitionEqOfFnAdd_eq_range]
    apply List.ofFn_inj.mpr
    funext index
    have hindex : index.val ≤ seed.height := Nat.le_of_lt_succ index.isLt
    simp [hindex]
    omega
  · rw [← List.ofFn_const (maxPushesPerStep tm) seed.start]
    apply List.ofFn_inj.mpr
    funext index
    simp
    omega

/-- One fixed blank vector used for every extra workspace cell. -/
def transitionWidenedFallbackBlankCellValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) : List Nat :=
  List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
    if symbol.val = (reachableAlphabet tm k).card then
      seed.start + 1
    else seed.start

/-- The blank one-hot vector is a false block followed by its final true
coordinate.  This is the exact two-progression decomposition used below. -/
theorem transitionWidenedFallbackBlankCellValues_eq_parts
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    transitionWidenedFallbackBlankCellValues tm seed k =
      List.replicate (reachableAlphabet tm k).card seed.start ++
        [seed.start + 1] := by
  unfold transitionWidenedFallbackBlankCellValues
  rw [show (reachableAlphabet tm k).card + 1 =
      (reachableAlphabet tm k).card + 1 by rfl]
  rw [List.ofFn_add]
  congr 1
  · rw [← List.ofFn_const (reachableAlphabet tm k).card seed.start]
    apply List.ofFn_inj.mpr
    funext symbol
    simp
    omega
  · simp [List.ofFn_succ]

/-- Public cell values followed by the fixed number of blank workspace cells.
-/
theorem transitionWidenedFallbackStackCellValues_eq_parts
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    transitionWidenedFallbackStackCellValues tm seed k =
      List.range'
          (seed.rowBase + transitionEqPrefixWidth tm +
            cfgStackBitOffset tm seed.height k + (seed.height + 1))
          (seed.height * ((reachableAlphabet tm k).card + 1)) ++
        (List.replicate (maxPushesPerStep tm)
          (transitionWidenedFallbackBlankCellValues tm seed k)).flatten := by
  unfold transitionWidenedFallbackStackCellValues workHeight
  rw [List.ofFn_add]
  rw [List.flatten_append]
  congr 1
  · rw [← transitionEqOfFnAdd_eq_range]
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext cell
    apply List.ofFn_inj.mpr
    funext symbol
    simp
    ring
  · apply congrArg List.flatten
    rw [← List.ofFn_const (maxPushesPerStep tm)
      (transitionWidenedFallbackBlankCellValues tm seed k)]
    apply List.ofFn_inj.mpr
    funext extra
    unfold transitionWidenedFallbackBlankCellValues
    apply List.ofFn_inj.mpr
    funext symbol
    simp

end CLRS.Chapter34.Turing.CookLevin
