import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat

/-!
# Fixed symbol counters for the SUBSET-SUM reduction

A counter is represented by a unary stream of `Unit` cells.  The controller
has one state and emits one cell exactly when the requested source symbol is
seen.  Instantiating the finite `target` parameter produces a genuine fixed
TM2, not an oracle for arithmetic on natural numbers.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

/-- One-state streaming specification that emits one tick per occurrence of
`target`. -/
def symbolCountSpec (target : CNFSym) :
    StatefulFlatMapSpec Unit CNFSym Unit where
  initial := ()
  action _ symbol := if symbol = target then ([()], ()) else ([], ())
  finish _ := []

/-- Unary occurrence count produced by the fixed streaming controller. -/
def symbolCountTicks (target : CNFSym) (input : List CNFSym) : List Unit :=
  rewriteStatefulFlatMap (symbolCountSpec target) input

private theorem symbolCountTicksFrom_eq
    (target : CNFSym) (input : List CNFSym) :
    rewriteStatefulFlatMapFrom (symbolCountSpec target) () input =
      List.replicate (input.count target) () := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      rw [rewriteStatefulFlatMapFrom]
      simp only [symbolCountSpec] at ih
      by_cases hsymbol : symbol = target
      · subst symbol
        simp [symbolCountSpec, ih, List.replicate_succ]
      · simp [symbolCountSpec, hsymbol, ih]

theorem symbolCountTicks_eq (target : CNFSym) (input : List CNFSym) :
    symbolCountTicks target input = List.replicate (input.count target) () := by
  simpa [symbolCountTicks, rewriteStatefulFlatMap, symbolCountSpec] using
    symbolCountTicksFrom_eq target input

/-- Each finite target symbol gives one fixed polynomial-time counting TM2. -/
noncomputable def symbolCountTicks_computableInPolyTime (target : CNFSym) :
    _root_.Turing.TM2ComputableInPolyTime id id (symbolCountTicks target) :=
  statefulFlatMap_computableInPolyTime (symbolCountSpec target)

end CLRS.Chapter34.Turing.SubsetSumReduction
