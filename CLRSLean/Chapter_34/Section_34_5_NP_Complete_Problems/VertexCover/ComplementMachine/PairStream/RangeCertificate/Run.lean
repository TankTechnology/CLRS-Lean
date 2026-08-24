import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.RangeCertificate.Simulation
import Mathlib.Tactic

/-!
# Range-certificate controller: complete typed run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream.RangeCertificate

open PolyBuilder

/-- Exact cost of the complete reverse-output controller on a canonical graph
encoding. -/
def steps (I : CliqueInstance) : Nat :=
  phaseSteps 0 I.vertexCount + 3 * I.vertexCount +
    (graphSuffix I).length + 7

/-- The fixed controller emits the reverse of the canonical range certificate
from the original graph encoding. -/
def run (I : CliqueInstance) :
    EvalsToInTime (step program)
      (initialCfg program (encodeCliqueInstance I))
      (some (haltCfg program (rangeCertificate I).reverse))
      (steps I) := by
  let suffix := graphSuffix I
  let afterStart := cfg .pushCertificate (some .instanceMark) false
    (prependCliqueTicks I.vertexCount (.fieldSep :: suffix)) [] [] [] []
  let afterCertificate := cfg .scanVertexCount (some .instanceMark) false
    (prependCliqueTicks I.vertexCount (.fieldSep :: suffix))
    [.certificateMark] [] [] []
  have hstart : EvalsToInTime (step program)
      (initialCfg program (encodeCliqueInstance I))
      (some afterStart) 1 := by
    exact ⟨⟨1, by simp [afterStart, initialCfg, encodeCliqueInstance,
      suffix, graphSuffix, flip, step, program, cfg, stepOp]⟩, le_rfl⟩
  have hcertificate : EvalsToInTime (step program) afterStart
      (some afterCertificate) 1 := by
    exact ⟨⟨1, by simp [afterStart, afterCertificate, flip, step,
      program, cfg, stepOp]⟩, le_rfl⟩
  have hscan := scanVertexCount I.vertexCount suffix [.certificateMark] []
    (some .instanceMark)
  have hphases := phases 0 I.vertexCount (some .fieldSep) suffix
    [.certificateMark]
  have hfinish := finish I.vertexCount suffix
    ((rangeRowsFrom 0 I.vertexCount).reverse ++ [.certificateMark])
    (some .fieldSep) false
  let first := EvalsToInTime.trans (step program) 1 1 _ afterStart _
    hstart hcertificate
  let second := EvalsToInTime.trans (step program) 2
    (2 * I.vertexCount + 1) _ afterCertificate _ first hscan
  let third := EvalsToInTime.trans (step program) _
    (phaseSteps 0 I.vertexCount) _ _ _ second (by simpa using hphases)
  let full := EvalsToInTime.trans (step program) _
    (I.vertexCount + suffix.length + 4) _ _ _ third
      (by simpa using hfinish)
  convert full using 1
  · simp [rangeCertificate, rangeRowsFrom, encodeCliqueCertificate,
      List.range_eq_range']
  · simp [steps, suffix]
    omega

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream.RangeCertificate
