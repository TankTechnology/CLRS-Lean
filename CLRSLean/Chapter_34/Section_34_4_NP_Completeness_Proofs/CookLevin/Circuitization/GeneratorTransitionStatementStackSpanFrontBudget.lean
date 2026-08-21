import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextHead

/-!
# Front budgets for affine statement-stack spans

Each selected stack action removes at most two coordinates from the surviving
source interval.  Consequently the verifier's two-cells-per-action padding
leaves two readable height coordinates and one readable cell row after every
statement prefix.  These are exactly the coordinates consumed by subsequent
`pop` and `peek` phases.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One action increases total source removal by at most two in both compact
spans. -/
theorem TransitionStmtSelectedStackAction.evalAffineSpan_removalCount_le
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteSpanBlock)
    (action : TransitionStmtSelectedStackAction tm k) :
    (action.evalAffineSpan tm k labelOffset route).heightSpan.removalCount ≤
        route.heightSpan.removalCount + 2 ∧
      (action.evalAffineSpan tm k labelOffset route).cellSpan.removalCount ≤
        route.cellSpan.removalCount + 2 := by
  cases action with
  | push symbolOffsets =>
      constructor
      · have h := route.heightSpan.removalCount_dropTail_le 1
        simp only [TransitionStmtSelectedStackAction.evalAffineSpan,
          TransitionStackAffineRouteSpanBlock.push,
          TransitionRouteSpan.removalCount_prepend] at ⊢
        omega
      · have h := route.cellSpan.removalCount_dropTail_le 1
        simp only [TransitionStmtSelectedStackAction.evalAffineSpan,
          TransitionStackAffineRouteSpanBlock.push,
          TransitionRouteSpan.removalCount_prepend] at ⊢
        omega
  | pop heightWireOffset =>
      constructor
      · simpa [TransitionStmtSelectedStackAction.evalAffineSpan,
          TransitionStackAffineRouteSpanBlock.pop] using
          route.heightSpan.removalCount_dropHead_le 2
      · have h := route.cellSpan.removalCount_dropHead_le 1
        simp only [TransitionStmtSelectedStackAction.evalAffineSpan,
          TransitionStackAffineRouteSpanBlock.pop,
          TransitionRouteSpan.removalCount_append] at ⊢
        omega

/-- A complete affine-span fold removes at most two source coordinates per
selected action. -/
theorem transitionStmtSelectedStackAffineActionSpans_removalCount_le_from
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteSpanBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset route
        actions).heightSpan.removalCount ≤
        route.heightSpan.removalCount + 2 * actions.length ∧
      (transitionStmtSelectedStackAffineActionSpans tm k labelOffset route
        actions).cellSpan.removalCount ≤
        route.cellSpan.removalCount + 2 * actions.length := by
  induction actions generalizing route with
  | nil => simp [transitionStmtSelectedStackAffineActionSpans]
  | cons action rest ih =>
      let next := action.evalAffineSpan tm k labelOffset route
      have hrest := ih next
      have hstep := action.evalAffineSpan_removalCount_le tm k labelOffset route
      change
        (transitionStmtSelectedStackAffineActionSpans tm k labelOffset next
          rest).heightSpan.removalCount ≤
            route.heightSpan.removalCount + 2 * (action :: rest).length ∧
        (transitionStmtSelectedStackAffineActionSpans tm k labelOffset next
          rest).cellSpan.removalCount ≤
            route.cellSpan.removalCount + 2 * (action :: rest).length
      dsimp [next] at hrest ⊢
      omega

/-- Specialized removal bound from the identity route. -/
theorem transitionStmtSelectedStackAffineActionSpans_removalCount_le
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
        TransitionStackAffineRouteSpanBlock.identity
        actions).heightSpan.removalCount ≤ 2 * actions.length ∧
      (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
        TransitionStackAffineRouteSpanBlock.identity
        actions).cellSpan.removalCount ≤ 2 * actions.length := by
  simpa [TransitionStackAffineRouteSpanBlock.identity,
    TransitionRouteSpan.identity, TransitionRouteSpan.removalCount] using
    transitionStmtSelectedStackAffineActionSpans_removalCount_le_from tm k
      labelOffset TransitionStackAffineRouteSpanBlock.identity actions

/-- Workspace padding leaves the first two routed height positions readable.
-/
theorem transitionStmtSelectedStackAffineActionSpans_height_front_two
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (actions : List (TransitionStmtSelectedStackAction tm k))
    (hcapacity : 2 * actions.length + 1 ≤ workHeight tm seed.height) :
    let route := transitionStmtSelectedStackAffineActionSpans tm k
      labelOffset TransitionStackAffineRouteSpanBlock.identity actions
    let source := TransitionStackValueBlock.ofWires
      ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k)
    2 ≤ route.heightSpan.headValues.length +
      ((route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).middle
        source.heightValues).length := by
  dsimp only
  let route := transitionStmtSelectedStackAffineActionSpans tm k
    labelOffset TransitionStackAffineRouteSpanBlock.identity actions
  let source := TransitionStackValueBlock.ofWires
    ((arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase).stack k)
  change 2 ≤ route.heightSpan.headValues.length +
    ((route.heightSpan.map fun form =>
      affineUnaryTripleFormValue form
        (transitionTailAffineSeed seed)).middle
      source.heightValues).length
  have hrem :=
    (transitionStmtSelectedStackAffineActionSpans_removalCount_le tm k
      labelOffset actions).1
  change route.heightSpan.removalCount ≤ 2 * actions.length at hrem
  have hsource : source.heightValues.length = workHeight tm seed.height + 1 :=
    (TransitionStackValueBlock.hasShape_ofWires tm k
      (workHeight tm seed.height)
      ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k)).1
  have hmiddle :
      2 ≤ ((route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).middle
        source.heightValues).length := by
    apply (route.heightSpan.map fun form =>
      affineUnaryTripleFormValue form
        (transitionTailAffineSeed seed)).le_middle_length_of_budget
    simp only [TransitionRouteSpan.removalCount_map]
    rw [hsource]
    exact le_trans (by omega) (by omega : 2 * actions.length + 2 ≤
      workHeight tm seed.height + 1)
  omega

/-- Workspace padding leaves the routed top cell readable. -/
theorem transitionStmtSelectedStackAffineActionSpans_cell_front_one
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (actions : List (TransitionStmtSelectedStackAction tm k))
    (hcapacity : 2 * actions.length + 1 ≤ workHeight tm seed.height) :
    let route := transitionStmtSelectedStackAffineActionSpans tm k
      labelOffset TransitionStackAffineRouteSpanBlock.identity actions
    let source := TransitionStackValueBlock.ofWires
      ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k)
    1 ≤ route.cellSpan.headValues.length +
      ((route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).middle
        source.cellRows).length := by
  dsimp only
  let route := transitionStmtSelectedStackAffineActionSpans tm k
    labelOffset TransitionStackAffineRouteSpanBlock.identity actions
  let source := TransitionStackValueBlock.ofWires
    ((arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase).stack k)
  change 1 ≤ route.cellSpan.headValues.length +
    ((route.cellSpan.map fun forms =>
      affineUnaryTripleMap forms
        (transitionTailAffineSeed seed)).middle source.cellRows).length
  have hrem :=
    (transitionStmtSelectedStackAffineActionSpans_removalCount_le tm k
      labelOffset actions).2
  change route.cellSpan.removalCount ≤ 2 * actions.length at hrem
  have hsource : source.cellRows.length = workHeight tm seed.height :=
    (TransitionStackValueBlock.hasShape_ofWires tm k
      (workHeight tm seed.height)
      ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k)).2.1
  have hmiddle :
      1 ≤ ((route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).middle source.cellRows).length := by
    apply (route.cellSpan.map fun forms =>
      affineUnaryTripleMap forms
        (transitionTailAffineSeed seed)).le_middle_length_of_budget
    simp only [TransitionRouteSpan.removalCount_map]
    rw [hsource]
    omega
  omega

/-- The original height coordinate exposed at either of the first two routed
positions remains inside the public verifier row. -/
theorem transitionStmtSelectedStackAffineActionSpans_height_front_public
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (actions : List (TransitionStmtSelectedStackAction tm k))
    (position : Nat) (hposition : position < 2)
    (hpadding : 2 * actions.length + 1 ≤ seed.height) :
    let route := transitionStmtSelectedStackAffineActionSpans tm k
      labelOffset TransitionStackAffineRouteSpanBlock.identity actions
    route.heightSpan.sourceDrop +
        (position - route.heightSpan.headValues.length) < seed.height + 1 := by
  dsimp only
  have hdrop :=
    (transitionStmtSelectedStackAffineActionSpans_sourceDrop_le tm k
      labelOffset actions).1
  omega

/-- The original cell row exposed at the routed top remains strictly inside
the public verifier height. -/
theorem transitionStmtSelectedStackAffineActionSpans_cell_front_public
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (actions : List (TransitionStmtSelectedStackAction tm k))
    (hpadding : 2 * actions.length + 1 ≤ seed.height) :
    let route := transitionStmtSelectedStackAffineActionSpans tm k
      labelOffset TransitionStackAffineRouteSpanBlock.identity actions
    route.cellSpan.sourceDrop +
        (0 - route.cellSpan.headValues.length) < seed.height := by
  dsimp only
  have hdrop :=
    (transitionStmtSelectedStackAffineActionSpans_sourceDrop_le tm k
      labelOffset actions).2
  omega

end CLRS.Chapter34.Turing.CookLevin
