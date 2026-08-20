import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteCellSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixDrop

/-!
# Concrete prefix-deletion passes for stack-pop routes

A pop removes the first two height values and the first fixed-width cell row.
This module packages the two marked source streams, applies the reusable fixed
prefix controller, and identifies the result with the descriptor-level routes
already proved correct.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One marked widened height row per transition seed. -/
noncomputable def transitionStackRouteHeightSourceFrames
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  encodeUnaryFrameFixedPrefixDropInput
    (seeds.map fun seed =>
      transitionStackRouteFirstValues
        (transitionStackRouteHeightProgressions tm seed k))

/-- Concrete controller output after deleting the two height values consumed
by pop. -/
noncomputable def transitionStackRoutePopHeightSliceFrames
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixDrop 2
    (transitionStackRouteHeightSourceFrames tm k seeds)

/-- The controller output is exactly the carried descriptor-family drop for
every seed. -/
theorem transitionStackRoutePopHeightSliceFrames_eq
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) :
    transitionStackRoutePopHeightSliceFrames tm k seeds =
      encodeUnaryFrameFixedPrefixDropInput
        (seeds.map fun seed =>
          transitionStackRouteFirstValues
            (transitionStackRouteDropFamily 2
              (transitionStackRouteHeightProgressions tm seed k))) := by
  unfold transitionStackRoutePopHeightSliceFrames
    transitionStackRouteHeightSourceFrames
  rw [rewriteUnaryFrameFixedPrefixDrop_rows]
  unfold encodeUnaryFrameFixedPrefixDropOutput
    encodeUnaryFrameFixedPrefixDropInput
  rw [List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  congr 2
  rw [transitionStackRouteHeightDrop_values]
  rw [← transitionStackRouteHeightProgressions_values]

/-- One marked flattened widened-cell row per transition seed. -/
noncomputable def transitionStackRouteCellSourceFrames
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  encodeUnaryFrameFixedPrefixDropInput
    (seeds.map fun seed =>
      transitionStackRouteFirstValues
        (transitionStackRouteCellProgressions tm seed k))

/-- Concrete controller output after deleting the old top cell row. -/
noncomputable def transitionStackRoutePopCellSliceFrames
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) : List UnaryFrameSym :=
  rewriteUnaryFrameFixedPrefixDrop
    ((reachableAlphabet tm k).card + 1)
    (transitionStackRouteCellSourceFrames tm k seeds)

/-- The cell controller output is exactly the carried descriptor-family drop
by one machine-fixed symbol-row width. -/
theorem transitionStackRoutePopCellSliceFrames_eq
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List TransitionRowSeed) :
    transitionStackRoutePopCellSliceFrames tm k seeds =
      encodeUnaryFrameFixedPrefixDropInput
        (seeds.map fun seed =>
          transitionStackRouteFirstValues
            (transitionStackRouteDropFamily
              ((reachableAlphabet tm k).card + 1)
              (transitionStackRouteCellProgressions tm seed k))) := by
  unfold transitionStackRoutePopCellSliceFrames
    transitionStackRouteCellSourceFrames
  rw [rewriteUnaryFrameFixedPrefixDrop_rows]
  unfold encodeUnaryFrameFixedPrefixDropOutput
    encodeUnaryFrameFixedPrefixDropInput
  rw [List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro seed hseed
  congr 2
  unfold transitionStackRouteFirstValues
  rw [transitionStackRouteDropFamily_rows, List.map_drop]

/-- Any polynomial-time marked height source is closed under the concrete pop
slice controller. -/
noncomputable def
    transitionStackRoutePopHeightSliceFrames_computableInPolyTime_of_source
    {Γ : Type} (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List Γ → List TransitionRowSeed)
    (source : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRouteHeightSourceFrames tm k
        (seeds input))) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRoutePopHeightSliceFrames tm k
        (seeds input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedPrefixDrop_computableInPolyTime 2)
  simpa [Function.comp_def, transitionStackRoutePopHeightSliceFrames] using
    Classical.choice composed

/-- Any polynomial-time marked cell source is closed under deletion of one
fixed-width top cell row. -/
noncomputable def
    transitionStackRoutePopCellSliceFrames_computableInPolyTime_of_source
    {Γ : Type} (tm : _root_.Turing.FinTM2) (k : tm.K)
    (seeds : List Γ → List TransitionRowSeed)
    (source : _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRouteCellSourceFrames tm k
        (seeds input))) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => transitionStackRoutePopCellSliceFrames tm k
        (seeds input)) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (unaryFrameFixedPrefixDrop_computableInPolyTime
        ((reachableAlphabet tm k).card + 1))
  simpa [Function.comp_def, transitionStackRoutePopCellSliceFrames] using
    Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
