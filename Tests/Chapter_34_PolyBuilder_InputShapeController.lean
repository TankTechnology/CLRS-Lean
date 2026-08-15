import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.InputShapeController

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder
open StateTransition

#check AffineInputShapeScript
#check encodeAffineInputShapeScript
#check affineInputShapeGateStream
#check affineInputShape_run
#check affineInputShapeRev_steps_le

private def sample : AffineInputShapeScript :=
  { separatorSources := [2, 4]
    armFrames := [none, some { start := 9, wires := [1, 3] }]
    finalOrStart := 12
    finalOrWires := [7, 10] }

example (output : List CircuitSym) :
    EvalsToInTime (step affineInputShapeRevProgram)
      (affineInputShapeLoopCfg (encodeAffineInputShapeScript sample) output)
      (some (haltCfg affineInputShapeRevProgram
        ((affineInputShapeGateStream sample).reverse ++ output)))
      (affineInputShapeRevSteps sample) := by
  exact affineInputShape_run sample output

#print axioms affineInputShape_run
#print axioms affineInputShapeRev_steps_le
